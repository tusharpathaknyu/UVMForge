"""
RTL Parser - Extract information from Verilog/SystemVerilog files
This is what makes VerifAI different from just using ChatGPT!
"""

import re
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple
from enum import Enum
from pathlib import Path


class PortDirection(Enum):
    INPUT = "input"
    OUTPUT = "output"
    INOUT = "inout"


class SignalType(Enum):
    WIRE = "wire"
    REG = "reg"
    LOGIC = "logic"
    INTEGER = "integer"


@dataclass
class Port:
    """Represents a module port"""
    name: str
    direction: PortDirection
    width: int = 1
    is_signed: bool = False
    signal_type: SignalType = SignalType.LOGIC
    msb: Optional[int] = None
    lsb: Optional[int] = None
    description: str = ""
    
    @property
    def width_str(self) -> str:
        if self.width == 1:
            return ""
        return f"[{self.msb}:{self.lsb}]"
    
    def __repr__(self):
        return f"{self.direction.value} {self.signal_type.value} {self.width_str} {self.name}"


@dataclass
class Parameter:
    """Represents a module parameter"""
    name: str
    value: str
    param_type: str = "parameter"  # parameter, localparam
    data_type: str = ""  # int, bit, logic, etc.
    description: str = ""


@dataclass
class FSMInfo:
    """Information about detected FSM"""
    state_reg: str
    states: List[str]
    num_states: int
    encoding: str = "unknown"  # one-hot, binary, gray


@dataclass
class ClockResetInfo:
    """Clock and reset signal information"""
    clock_signals: List[str]
    reset_signals: List[str]
    reset_polarity: Dict[str, str]  # signal -> "active_high" or "active_low"
    clock_edges: Dict[str, str]  # signal -> "posedge" or "negedge"


@dataclass
class ProtocolHint:
    """Hints about what protocol the RTL might be using"""
    protocol: str
    confidence: float  # 0.0 to 1.0
    matching_signals: List[str]
    reason: str


@dataclass
class ParsedRTL:
    """Complete parsed RTL information"""
    module_name: str
    ports: List[Port]
    parameters: List[Parameter]
    clocks: ClockResetInfo
    fsm: Optional[FSMInfo] = None
    protocol_hints: List[ProtocolHint] = field(default_factory=list)
    raw_content: str = ""
    file_path: str = ""
    
    @property
    def input_ports(self) -> List[Port]:
        return [p for p in self.ports if p.direction == PortDirection.INPUT]
    
    @property
    def output_ports(self) -> List[Port]:
        return [p for p in self.ports if p.direction == PortDirection.OUTPUT]
    
    @property
    def inout_ports(self) -> List[Port]:
        return [p for p in self.ports if p.direction == PortDirection.INOUT]
    
    def get_data_width(self) -> int:
        """Guess the data bus width from ports"""
        data_patterns = ['data', 'wdata', 'rdata', 'din', 'dout', 'dat']
        for port in self.ports:
            if any(p in port.name.lower() for p in data_patterns):
                return port.width
        return 32  # default
    
    def get_addr_width(self) -> int:
        """Guess the address width from ports"""
        addr_patterns = ['addr', 'address', 'adr']
        for port in self.ports:
            if any(p in port.name.lower() for p in addr_patterns):
                return port.width
        return 32  # default


class RTLParser:
    """
    Parser for Verilog/SystemVerilog RTL files.
    Extracts ports, parameters, FSMs, and protocol hints.
    """
    
    # Protocol signal patterns for detection
    PROTOCOL_PATTERNS = {
        'apb': {
            'signals': ['psel', 'penable', 'pwrite', 'paddr', 'pwdata', 'prdata', 'pready', 'pslverr'],
            'required': ['psel', 'penable'],
            'weight': 0.9
        },
        'axi4lite': {
            'signals': ['awaddr', 'awvalid', 'awready', 'wdata', 'wvalid', 'wready', 'araddr', 'arvalid', 'arready', 'rdata', 'rvalid', 'rready', 'bresp', 'bvalid', 'bready'],
            'required': ['awvalid', 'awready', 'arvalid', 'arready'],
            'weight': 0.95
        },
        'axi4': {
            'signals': ['awid', 'awaddr', 'awlen', 'awsize', 'awburst', 'awvalid', 'awready', 'arid', 'arlen', 'arsize', 'arburst'],
            'required': ['awlen', 'arlen'],  # AXI4 has burst length
            'weight': 0.95
        },
        'uart': {
            'signals': ['tx', 'rx', 'txd', 'rxd', 'uart_tx', 'uart_rx', 'baud', 'tx_data', 'rx_data', 'tx_valid', 'rx_valid'],
            'required': [],
            'weight': 0.7
        },
        'spi': {
            'signals': ['sclk', 'mosi', 'miso', 'ss', 'cs', 'spi_clk', 'spi_mosi', 'spi_miso', 'spi_cs', 'spi_ss'],
            'required': ['mosi', 'miso'],
            'weight': 0.8
        },
        'i2c': {
            'signals': ['sda', 'scl', 'i2c_sda', 'i2c_scl', 'sda_i', 'sda_o', 'scl_i', 'scl_o'],
            'required': ['sda', 'scl'],
            'weight': 0.85
        },
        'wishbone': {
            'signals': ['wb_cyc', 'wb_stb', 'wb_we', 'wb_ack', 'wb_adr', 'wb_dat_i', 'wb_dat_o', 'cyc_i', 'stb_i', 'ack_o'],
            'required': ['cyc', 'stb', 'ack'],
            'weight': 0.85
        }
    }
    
    # Common clock/reset patterns
    CLOCK_PATTERNS = [
        r'\bclk\b', r'\bclock\b', r'\bclk_i\b', r'\bsys_clk\b', r'\bpclk\b', r'\baclk\b',
        r'\bhclk\b', r'\bfclk\b', r'\bclk_in\b', r'\bmaster_clk\b'
    ]
    
    RESET_PATTERNS = [
        (r'\brst\b', 'active_high'),
        (r'\breset\b', 'active_high'),
        (r'\brst_n\b', 'active_low'),
        (r'\bresn\b', 'active_low'),
        (r'\breset_n\b', 'active_low'),
        (r'\brstn\b', 'active_low'),
        (r'\bareset_n\b', 'active_low'),
        (r'\bpreset_n\b', 'active_low'),
        (r'\bsys_rst\b', 'active_high'),
        (r'\bsys_rst_n\b', 'active_low'),
    ]
    
    def __init__(self):
        self.content = ""
        self.cleaned_content = ""
    
    def parse(self, rtl_content: str, file_path: str = "") -> ParsedRTL:
        """Parse RTL content and extract all information"""
        self.content = rtl_content
        self.cleaned_content = self._remove_comments(rtl_content)
        
        module_name = self._extract_module_name()
        parameters = self._extract_parameters()
        ports = self._extract_ports()
        clocks = self._detect_clocks_resets(ports)
        fsm = self._detect_fsm()
        protocol_hints = self._detect_protocol(ports)
        
        return ParsedRTL(
            module_name=module_name,
            ports=ports,
            parameters=parameters,
            clocks=clocks,
            fsm=fsm,
            protocol_hints=protocol_hints,
            raw_content=rtl_content,
            file_path=file_path
        )
    
    def parse_file(self, file_path: str) -> ParsedRTL:
        """Parse RTL from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"RTL file not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))
    
    def _remove_comments(self, content: str) -> str:
        """Remove single-line and multi-line comments"""
        # Remove single-line comments
        content = re.sub(r'//.*$', '', content, flags=re.MULTILINE)
        # Remove multi-line comments
        content = re.sub(r'/\*.*?\*/', '', content, flags=re.DOTALL)
        return content
    
    def _extract_module_name(self) -> str:
        """Extract module name"""
        match = re.search(r'\bmodule\s+(\w+)', self.cleaned_content)
        if match:
            return match.group(1)
        return "unknown_module"
    
    def _extract_parameters(self) -> List[Parameter]:
        """Extract module parameters"""
        parameters = []
        
        # Match parameter declarations in module header
        # parameter [type] NAME = VALUE
        param_pattern = r'\b(parameter|localparam)\s+(?:(\w+)\s+)?(\w+)\s*=\s*([^,;\)]+)'
        
        for match in re.finditer(param_pattern, self.cleaned_content, re.IGNORECASE):
            param_type = match.group(1)
            data_type = match.group(2) or ""
            name = match.group(3)
            value = match.group(4).strip()
            
            parameters.append(Parameter(
                name=name,
                value=value,
                param_type=param_type,
                data_type=data_type
            ))
        
        return parameters
    
    def _extract_ports(self) -> List[Port]:
        """Extract all module ports with their properties"""
        ports = []
        
        # Pattern for ANSI-style port declarations (most common in modern SV)
        # input/output/inout [wire/reg/logic] [signed] [width] name
        ansi_pattern = r'\b(input|output|inout)\s+(wire|reg|logic)?\s*(signed)?\s*(\[\s*(\d+|\w+)\s*:\s*(\d+|\w+)\s*\])?\s*(\w+)'
        
        for match in re.finditer(ansi_pattern, self.cleaned_content, re.IGNORECASE):
            direction_str = match.group(1).lower()
            signal_type_str = match.group(2) or "logic"
            is_signed = match.group(3) is not None
            msb_str = match.group(5)
            lsb_str = match.group(6)
            name = match.group(7)
            
            # Skip keywords that might match
            if name.lower() in ['input', 'output', 'inout', 'wire', 'reg', 'logic', 'module', 'endmodule']:
                continue
            
            direction = PortDirection(direction_str)
            signal_type = SignalType(signal_type_str.lower()) if signal_type_str else SignalType.LOGIC
            
            # Calculate width
            if msb_str and lsb_str:
                try:
                    msb = int(msb_str)
                    lsb = int(lsb_str)
                    width = abs(msb - lsb) + 1
                except ValueError:
                    # Parameter-based width
                    msb = None
                    lsb = None
                    width = 1  # Unknown, will need parameter resolution
            else:
                msb = None
                lsb = None
                width = 1
            
            ports.append(Port(
                name=name,
                direction=direction,
                width=width,
                is_signed=is_signed,
                signal_type=signal_type,
                msb=msb,
                lsb=lsb
            ))
        
        return ports
    
    def _detect_clocks_resets(self, ports: List[Port]) -> ClockResetInfo:
        """Detect clock and reset signals"""
        clocks = []
        resets = []
        reset_polarity = {}
        clock_edges = {}
        
        port_names = [p.name.lower() for p in ports]
        
        # Detect clocks
        for port in ports:
            port_lower = port.name.lower()
            for pattern in self.CLOCK_PATTERNS:
                if re.search(pattern, port_lower):
                    clocks.append(port.name)
                    # Default to posedge
                    clock_edges[port.name] = "posedge"
                    break
        
        # Detect resets
        for port in ports:
            port_lower = port.name.lower()
            for pattern, polarity in self.RESET_PATTERNS:
                if re.search(pattern, port_lower):
                    resets.append(port.name)
                    reset_polarity[port.name] = polarity
                    break
        
        # Try to detect clock edges from always blocks
        always_pattern = r'always\s*@\s*\(\s*(posedge|negedge)\s+(\w+)'
        for match in re.finditer(always_pattern, self.cleaned_content, re.IGNORECASE):
            edge = match.group(1).lower()
            signal = match.group(2)
            if signal in clocks or any(signal.lower() == c.lower() for c in clocks):
                clock_edges[signal] = edge
        
        return ClockResetInfo(
            clock_signals=clocks,
            reset_signals=resets,
            reset_polarity=reset_polarity,
            clock_edges=clock_edges
        )
    
    def _detect_fsm(self) -> Optional[FSMInfo]:
        """Detect FSM in the RTL"""
        # Look for state enum or parameter definitions
        state_patterns = [
            # typedef enum
            r'typedef\s+enum\s*(?:logic\s*\[[^\]]+\])?\s*\{([^}]+)\}\s*(\w*state\w*)',
            # localparam states
            r'localparam\s+(\w*STATE\w*|\w*ST_\w+)\s*=',
            # State register
            r'(\w*state\w*)\s*<=\s*(\w*STATE\w*|\w*ST_\w+|IDLE|INIT)',
        ]
        
        states = []
        state_reg = None
        
        # Look for enum states
        enum_match = re.search(r'typedef\s+enum[^{]*\{([^}]+)\}', self.cleaned_content, re.IGNORECASE)
        if enum_match:
            enum_content = enum_match.group(1)
            states = [s.strip().split('=')[0].strip() for s in enum_content.split(',') if s.strip()]
        
        # Look for parameter-based states
        if not states:
            param_states = re.findall(r'(?:parameter|localparam)\s+(\w*(?:STATE|ST_|IDLE|INIT)\w*)\s*=', 
                                      self.cleaned_content, re.IGNORECASE)
            states = list(set(param_states))
        
        # Find state register
        state_reg_match = re.search(r'(\w*state\w*)\s*<=', self.cleaned_content, re.IGNORECASE)
        if state_reg_match:
            state_reg = state_reg_match.group(1)
        
        if states and len(states) > 1:
            # Detect encoding
            encoding = "binary"
            if len(states) <= 8:
                # Check for one-hot pattern
                one_hot_pattern = re.search(r"[48]'b0*1|[48]'h[0-9a-f]", self.cleaned_content, re.IGNORECASE)
                if one_hot_pattern:
                    encoding = "one-hot"
            
            return FSMInfo(
                state_reg=state_reg or "state",
                states=states,
                num_states=len(states),
                encoding=encoding
            )
        
        return None
    
    def _detect_protocol(self, ports: List[Port]) -> List[ProtocolHint]:
        """Detect what protocol the RTL might be implementing"""
        hints = []
        port_names_lower = [p.name.lower() for p in ports]
        
        for protocol, info in self.PROTOCOL_PATTERNS.items():
            matching_signals = []
            required_found = 0
            
            for sig in info['signals']:
                # Check if any port contains this signal pattern
                for port_name in port_names_lower:
                    if sig in port_name:
                        matching_signals.append(sig)
                        break
            
            # Check required signals
            for req in info['required']:
                for port_name in port_names_lower:
                    if req in port_name:
                        required_found += 1
                        break
            
            if matching_signals:
                # Calculate confidence
                match_ratio = len(matching_signals) / len(info['signals'])
                required_ratio = required_found / len(info['required']) if info['required'] else 1.0
                confidence = match_ratio * required_ratio * info['weight']
                
                if confidence > 0.3:  # Threshold
                    hints.append(ProtocolHint(
                        protocol=protocol,
                        confidence=round(confidence, 2),
                        matching_signals=matching_signals,
                        reason=f"Found {len(matching_signals)}/{len(info['signals'])} protocol signals"
                    ))
        
        # Sort by confidence
        hints.sort(key=lambda x: x.confidence, reverse=True)
        return hints


def analyze_rtl(rtl_content: str, file_path: str = "") -> Dict:
    """
    Convenience function to analyze RTL and return a dictionary.
    """
    parser = RTLParser()
    parsed = parser.parse(rtl_content, file_path)
    
    return {
        'module_name': parsed.module_name,
        'ports': {
            'inputs': [{'name': p.name, 'width': p.width, 'signed': p.is_signed} for p in parsed.input_ports],
            'outputs': [{'name': p.name, 'width': p.width, 'signed': p.is_signed} for p in parsed.output_ports],
            'inouts': [{'name': p.name, 'width': p.width, 'signed': p.is_signed} for p in parsed.inout_ports],
        },
        'parameters': [{'name': p.name, 'value': p.value, 'type': p.param_type} for p in parsed.parameters],
        'clocks': parsed.clocks.clock_signals,
        'resets': {
            'signals': parsed.clocks.reset_signals,
            'polarity': parsed.clocks.reset_polarity
        },
        'fsm': {
            'detected': parsed.fsm is not None,
            'states': parsed.fsm.states if parsed.fsm else [],
            'state_reg': parsed.fsm.state_reg if parsed.fsm else None,
            'encoding': parsed.fsm.encoding if parsed.fsm else None
        },
        'protocol_hints': [
            {'protocol': h.protocol, 'confidence': h.confidence, 'reason': h.reason}
            for h in parsed.protocol_hints
        ],
        'data_width': parsed.get_data_width(),
        'addr_width': parsed.get_addr_width()
    }


@dataclass
class DesignComplexity:
    """Design complexity metrics"""
    total_ports: int
    input_count: int
    output_count: int
    data_width: int
    addr_width: int
    fsm_states: int
    parameter_count: int
    has_fsm: bool
    detected_protocol: str
    protocol_confidence: float
    complexity_score: str  # "low", "medium", "high"
    estimated_coverage_points: int


@dataclass
class VerificationChecklist:
    """Auto-generated verification checklist"""
    reset_tests: List[str]
    protocol_tests: List[str]
    fsm_tests: List[str]
    data_path_tests: List[str]
    edge_cases: List[str]
    corner_cases: List[str]


@dataclass
class ConstraintHint:
    """Constraint randomization hints for UVM sequences"""
    signal_name: str
    constraint_type: str  # "range", "enum", "distribution", "solve_order"
    constraint_code: str
    description: str


@dataclass
class WaveformDiagram:
    """ASCII waveform diagram for protocol visualization"""
    name: str
    description: str
    ascii_art: str
    signals: List[str]
    num_cycles: int


class WaveformGenerator:
    """Generates ASCII waveform diagrams for protocols"""
    
    PROTOCOL_WAVEFORMS = {
        'apb': {
            'write': '''
┌─────────────────────────────────────────────────────────────────┐
│  APB Write Transaction                                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  PCLK     ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──               │
│            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──               │
│                                                                 │
│  PSEL     ─────┐                          ┌─────                │
│                └──────────────────────────┘                     │
│                                                                 │
│  PENABLE  ───────────┐              ┌─────                      │
│                      └──────────────┘                           │
│                                                                 │
│  PWRITE   ─────┐                          ┌─────                │
│                └──────────────────────────┘                     │
│                                                                 │
│  PADDR    ═════╪══════════════════════════╪═════                │
│                │         ADDR             │                     │
│                                                                 │
│  PWDATA   ═════╪══════════════════════════╪═════                │
│                │         DATA             │                     │
│                                                                 │
│  PREADY   ─────────────────────┐    ┌─────                      │
│                                └────┘                           │
│                                                                 │
│            │IDLE│    SETUP    │  ACCESS   │IDLE│                │
└─────────────────────────────────────────────────────────────────┘''',
            'read': '''
┌─────────────────────────────────────────────────────────────────┐
│  APB Read Transaction                                           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  PCLK     ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──               │
│            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──               │
│                                                                 │
│  PSEL     ─────┐                          ┌─────                │
│                └──────────────────────────┘                     │
│                                                                 │
│  PENABLE  ───────────┐              ┌─────                      │
│                      └──────────────┘                           │
│                                                                 │
│  PWRITE   ───────────────────────────────────────               │
│                   (LOW for read)                                │
│                                                                 │
│  PADDR    ═════╪══════════════════════════╪═════                │
│                │         ADDR             │                     │
│                                                                 │
│  PRDATA   ═════════════════════╪══════════╪═════                │
│                                │   DATA   │                     │
│                                                                 │
│  PREADY   ─────────────────────┐    ┌─────                      │
│                                └────┘                           │
│                                                                 │
│            │IDLE│    SETUP    │  ACCESS   │IDLE│                │
└─────────────────────────────────────────────────────────────────┘'''
        },
        'axi4lite': {
            'write': '''
┌─────────────────────────────────────────────────────────────────┐
│  AXI4-Lite Write Transaction                                    │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ACLK     ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──         │
│            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──         │
│                                                                 │
│  AWVALID  ─────┐        ┌───────────────────────────            │
│                └────────┘                                       │
│                                                                 │
│  AWREADY  ───────────┐  ┌───────────────────────────            │
│                      └──┘                                       │
│                                                                 │
│  AWADDR   ═════╪════════╪═══════════════════════════            │
│                │  ADDR  │                                       │
│                                                                 │
│  WVALID   ───────────┐        ┌─────────────────────            │
│                      └────────┘                                 │
│                                                                 │
│  WREADY   ─────────────────┐  ┌─────────────────────            │
│                            └──┘                                 │
│                                                                 │
│  WDATA    ═══════════╪════════╪═════════════════════            │
│                      │  DATA  │                                 │
│                                                                 │
│  BVALID   ─────────────────────────┐        ┌───────            │
│                                    └────────┘                   │
│                                                                 │
│  BREADY   ─────────────────────────────┐    ┌───────            │
│                                        └────┘                   │
│                                                                 │
│            │ AW  │  W   │    B    │                             │
│            │PHASE│PHASE │  PHASE  │                             │
└─────────────────────────────────────────────────────────────────┘''',
            'read': '''
┌─────────────────────────────────────────────────────────────────┐
│  AXI4-Lite Read Transaction                                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  ACLK     ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──         │
│            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──         │
│                                                                 │
│  ARVALID  ─────┐        ┌───────────────────────────            │
│                └────────┘                                       │
│                                                                 │
│  ARREADY  ───────────┐  ┌───────────────────────────            │
│                      └──┘                                       │
│                                                                 │
│  ARADDR   ═════╪════════╪═══════════════════════════            │
│                │  ADDR  │                                       │
│                                                                 │
│  RVALID   ─────────────────────┐        ┌───────────            │
│                                └────────┘                       │
│                                                                 │
│  RREADY   ─────────────────────────┐    ┌───────────            │
│                                    └────┘                       │
│                                                                 │
│  RDATA    ═════════════════════╪════════╪═══════════            │
│                                │  DATA  │                       │
│                                                                 │
│            │  AR PHASE  │    R PHASE    │                       │
└─────────────────────────────────────────────────────────────────┘'''
        },
        'spi': {
            'transfer': '''
┌─────────────────────────────────────────────────────────────────┐
│  SPI Transfer (Mode 0: CPOL=0, CPHA=0)                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  CS_N     ────┐                                        ┌────    │
│               └────────────────────────────────────────┘        │
│                                                                 │
│  SCLK     ────────┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──   │
│                   └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──┘      │
│                                                                 │
│  MOSI     ════╪═══╪════╪════╪════╪════╪════╪════╪════╪════     │
│               │D7 │D6  │D5  │D4  │D3  │D2  │D1  │D0  │          │
│                                                                 │
│  MISO     ════╪═══╪════╪════╪════╪════╪════╪════╪════╪════     │
│               │D7 │D6  │D5  │D4  │D3  │D2  │D1  │D0  │          │
│                                                                 │
│           │ CS │      8-bit transfer (MSB first)      │ CS │    │
│           │ LOW│                                      │HIGH│    │
└─────────────────────────────────────────────────────────────────┘'''
        },
        'uart': {
            'transfer': '''
┌─────────────────────────────────────────────────────────────────┐
│  UART Frame (8N1: 8 data bits, No parity, 1 stop bit)           │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  TX/RX    ────┐     ┌───┬───┬───┬───┬───┬───┬───┬───┐   ┌────  │
│               │     │   │   │   │   │   │   │   │   │   │       │
│               └─────┴───┴───┴───┴───┴───┴───┴───┴───┴───┘       │
│               │START│ D0│ D1│ D2│ D3│ D4│ D5│ D6│ D7│STOP│      │
│               │ BIT │        DATA BITS (LSB first)   │ BIT│      │
│                                                                 │
│  Timing:  │<─────────── Bit Period = 1/Baud ────────────>│      │
│                                                                 │
│  Common baud rates: 9600, 19200, 38400, 57600, 115200           │
└─────────────────────────────────────────────────────────────────┘'''
        },
        'i2c': {
            'transfer': '''
┌─────────────────────────────────────────────────────────────────┐
│  I2C Write Transaction                                          │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  SCL     ────┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐     ┌──┐  ┌──┐  ┌────   │
│              └──┘  └──┘  └──┘  └──┘  └──...─┘  └──┘  └──┘       │
│                                                                 │
│  SDA     ──┐  ╔══════════════════════╗ ╔═══╗ ╔═════════╗  ┌──  │
│            └──╢  7-bit Address + W   ╟─╢ACK╟─╢  Data   ╟──┘     │
│               ╚══════════════════════╝ ╚═══╝ ╚═════════╝        │
│          │S │                          │ A │             │ P│   │
│          │T │     ADDRESS PHASE        │ C │ DATA PHASE  │ │   │
│          │A │                          │ K │             │S│   │
│          │R │                          │   │             │T│   │
│          │T │                          │   │             │O│   │
│                                                          │P│   │
│  START: SDA ↓ while SCL HIGH                                   │
│  STOP:  SDA ↑ while SCL HIGH                                   │
└─────────────────────────────────────────────────────────────────┘'''
        },
        'generic': {
            'handshake': '''
┌─────────────────────────────────────────────────────────────────┐
│  Generic Handshake Protocol                                     │
├─────────────────────────────────────────────────────────────────┤
│                                                                 │
│  CLK      ──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──┐  ┌──               │
│            └──┘  └──┘  └──┘  └──┘  └──┘  └──┘  └──               │
│                                                                 │
│  VALID    ─────┐              ┌─────────────────                │
│                └──────────────┘                                 │
│                                                                 │
│  READY    ───────────┐        ┌─────────────────                │
│                      └────────┘                                 │
│                                                                 │
│  DATA     ═════╪══════════════╪═════════════════                │
│                │    DATA      │                                 │
│                                                                 │
│           │    │   Transfer   │                                 │
│           │IDLE│   completes  │IDLE                             │
│           │    │   when both  │                                 │
│           │    │   HIGH       │                                 │
└─────────────────────────────────────────────────────────────────┘'''
        }
    }
    
    @classmethod
    def generate_for_protocol(cls, protocol: str) -> List[WaveformDiagram]:
        """Generate waveform diagrams for a detected protocol"""
        diagrams = []
        protocol_key = protocol.lower().replace('-', '').replace('_', '').replace('4lite', '4lite')
        
        # Normalize protocol names
        if 'apb' in protocol_key:
            protocol_key = 'apb'
        elif 'axi' in protocol_key:
            protocol_key = 'axi4lite'
        elif 'spi' in protocol_key:
            protocol_key = 'spi'
        elif 'uart' in protocol_key:
            protocol_key = 'uart'
        elif 'i2c' in protocol_key:
            protocol_key = 'i2c'
        else:
            protocol_key = 'generic'
        
        waveforms = cls.PROTOCOL_WAVEFORMS.get(protocol_key, cls.PROTOCOL_WAVEFORMS['generic'])
        
        for name, ascii_art in waveforms.items():
            diagrams.append(WaveformDiagram(
                name=f"{protocol}_{name}",
                description=f"{protocol.upper()} {name.replace('_', ' ').title()} timing diagram",
                ascii_art=ascii_art,
                signals=cls._extract_signals(ascii_art),
                num_cycles=8
            ))
        
        return diagrams
    
    @staticmethod
    def _extract_signals(ascii_art: str) -> List[str]:
        """Extract signal names from waveform diagram"""
        import re
        signals = []
        for line in ascii_art.split('\n'):
            match = re.match(r'│\s+(\w+)\s+', line)
            if match:
                signals.append(match.group(1))
        return list(set(signals))


class ConstraintGenerator:
    """Generates constraint randomization hints based on protocol and FSM"""
    
    @staticmethod
    def generate_constraints(parsed: 'ParsedRTL') -> List[ConstraintHint]:
        """Generate constraint hints based on RTL analysis"""
        hints = []
        protocol = parsed.protocol_hints[0].protocol if parsed.protocol_hints else "generic"
        
        # Data width constraints
        data_w = parsed.get_data_width()
        addr_w = parsed.get_addr_width()
        
        hints.append(ConstraintHint(
            signal_name="data",
            constraint_type="distribution",
            constraint_code=f"""constraint data_dist {{
    data dist {{
        0                      := 5,   // All zeros
        {(1 << data_w) - 1}    := 5,   // All ones  
        [1:{(1 << data_w) - 2}] := 90  // Random values
    }};
}}""",
            description=f"Distribution constraint for {data_w}-bit data"
        ))
        
        hints.append(ConstraintHint(
            signal_name="addr",
            constraint_type="range",
            constraint_code=f"""constraint addr_range {{
    addr inside {{[0:{(1 << addr_w) - 1}]}};
    addr[1:0] == 2'b00;  // Word-aligned
}}""",
            description=f"Address range and alignment constraint ({addr_w}-bit)"
        ))
        
        # Protocol-specific constraints
        if protocol == "apb":
            hints.append(ConstraintHint(
                signal_name="apb_txn",
                constraint_type="distribution",
                constraint_code="""constraint apb_txn_type {{
    pwrite dist {{ 1 := 50, 0 := 50 }};  // 50% writes, 50% reads
}}

constraint apb_back2back {{
    b2b_delay inside {[0:3]};  // Allow back-to-back with 0-3 cycle gap
}}""",
                description="APB transaction type and timing constraints"
            ))
        elif protocol == "axi4lite":
            hints.append(ConstraintHint(
                signal_name="axi_txn",
                constraint_type="distribution",
                constraint_code="""constraint axi_txn_type {{
    is_write dist {{ 1 := 50, 0 := 50 }};
}}

constraint axi_resp {{
    // Expect OKAY response most of the time
    expected_resp dist {{ 2'b00 := 95, 2'b10 := 5 }};
}}

constraint axi_strobe {{
    // Usually full word writes
    wstrb dist {{ 4'hF := 80, [4'h1:4'hE] := 20 }};
}}""",
                description="AXI4-Lite transaction and response constraints"
            ))
        elif protocol == "spi":
            hints.append(ConstraintHint(
                signal_name="spi_txn",
                constraint_type="range",
                constraint_code="""constraint spi_mode {{
    cpol inside {[0:1]};
    cpha inside {[0:1]};
}}

constraint spi_transfer {{
    tx_bytes inside {[1:16]};  // 1-16 byte transfers
}}""",
                description="SPI mode and transfer size constraints"
            ))
        elif protocol == "uart":
            hints.append(ConstraintHint(
                signal_name="uart_txn",
                constraint_type="enum",
                constraint_code="""constraint uart_baud {{
    baud_rate inside {{ 9600, 19200, 38400, 57600, 115200 }};
}}

constraint uart_frame {{
    data_bits inside {{ 7, 8 }};
    stop_bits inside {{ 1, 2 }};
    parity inside {{ NONE, EVEN, ODD }};
}}""",
                description="UART baud rate and frame format constraints"
            ))
        elif protocol == "i2c":
            hints.append(ConstraintHint(
                signal_name="i2c_txn",
                constraint_type="distribution",
                constraint_code="""constraint i2c_addr {{
    slave_addr inside {[7'h08:7'h77]};  // Valid 7-bit addresses
}}

constraint i2c_op {{
    is_read dist {{ 1 := 40, 0 := 60 }};  // Slightly more writes
}}

constraint i2c_len {{
    num_bytes inside {[1:32]};
}}""",
                description="I2C address and operation constraints"
            ))
        
        # FSM-based constraints
        if parsed.fsm and parsed.fsm.states:
            states = parsed.fsm.states
            states_list = ", ".join(states[:8])  # First 8 states
            hints.append(ConstraintHint(
                signal_name="fsm_state",
                constraint_type="enum",
                constraint_code=f"""constraint state_coverage {{
    // Ensure all states are exercised
    target_state inside {{ {states_list} }};
}}

constraint state_transitions {{
    // Weight interesting transitions higher
    soft prev_state != curr_state;  // Prefer state changes
}}""",
                description=f"FSM state coverage constraints ({len(states)} states)"
            ))
        
        return hints


class SimpleParsedRTL:
    """Simple wrapper for app.py compatibility"""
    def __init__(self, parsed: ParsedRTL):
        self._parsed = parsed
        self.module_name = parsed.module_name
        self.inputs = [p.name for p in parsed.input_ports]
        self.outputs = [p.name for p in parsed.output_ports]
        self.clocks = parsed.clocks.clock_signals
        self.resets = parsed.clocks.reset_signals
        self.fsm = {
            'states': parsed.fsm.states if parsed.fsm else [],
            'state_var': parsed.fsm.state_reg if parsed.fsm else None
        } if parsed.fsm else None
        self.ports = parsed.ports
        self.parameters = parsed.parameters
        
        # Add new computed properties
        self.complexity = self._compute_complexity(parsed)
        self.checklist = self._generate_checklist(parsed)
        self.waveforms = self._generate_waveforms(parsed)
        self.constraints = self._generate_constraints(parsed)
    
    def _generate_waveforms(self, parsed: ParsedRTL) -> List[WaveformDiagram]:
        """Generate protocol waveform diagrams"""
        protocol = parsed.protocol_hints[0].protocol if parsed.protocol_hints else "generic"
        return WaveformGenerator.generate_for_protocol(protocol)
    
    def _generate_constraints(self, parsed: ParsedRTL) -> List[ConstraintHint]:
        """Generate constraint randomization hints"""
        return ConstraintGenerator.generate_constraints(parsed)
    
    def _compute_complexity(self, parsed: ParsedRTL) -> DesignComplexity:
        """Compute design complexity metrics"""
        fsm_states = len(parsed.fsm.states) if parsed.fsm else 0
        protocol = parsed.protocol_hints[0].protocol if parsed.protocol_hints else "generic"
        confidence = parsed.protocol_hints[0].confidence if parsed.protocol_hints else 0.0
        
        # Calculate complexity score
        score_value = (
            len(parsed.ports) * 2 +
            fsm_states * 5 +
            len(parsed.parameters) * 1 +
            (10 if protocol != "generic" else 0)
        )
        
        if score_value < 20:
            complexity_score = "low"
        elif score_value < 50:
            complexity_score = "medium"
        else:
            complexity_score = "high"
        
        # Estimate coverage points
        est_coverage = (
            len(parsed.ports) * 4 +  # Per-port toggle coverage
            fsm_states * fsm_states +  # State transitions
            parsed.get_data_width() +  # Data values
            10  # Base
        )
        
        return DesignComplexity(
            total_ports=len(parsed.ports),
            input_count=len(parsed.input_ports),
            output_count=len(parsed.output_ports),
            data_width=parsed.get_data_width(),
            addr_width=parsed.get_addr_width(),
            fsm_states=fsm_states,
            parameter_count=len(parsed.parameters),
            has_fsm=parsed.fsm is not None,
            detected_protocol=protocol,
            protocol_confidence=confidence,
            complexity_score=complexity_score,
            estimated_coverage_points=est_coverage
        )
    
    def _generate_checklist(self, parsed: ParsedRTL) -> VerificationChecklist:
        """Generate verification checklist based on RTL analysis"""
        reset_tests = []
        protocol_tests = []
        fsm_tests = []
        data_path_tests = []
        edge_cases = []
        corner_cases = []
        
        # Reset tests
        for reset in parsed.clocks.reset_signals:
            polarity = parsed.clocks.reset_polarity.get(reset, "active_low")
            reset_tests.append(f"Verify all outputs go to default on {reset} assertion")
            reset_tests.append(f"Verify proper operation after {reset} de-assertion")
            reset_tests.append(f"Test reset during active transaction")
        
        if not reset_tests:
            reset_tests.append("Verify reset behavior (no reset signal detected)")
        
        # Protocol-specific tests
        protocol = parsed.protocol_hints[0].protocol if parsed.protocol_hints else "generic"
        if protocol == "apb":
            protocol_tests = [
                "Verify PREADY timing (must be valid in ACCESS phase)",
                "Verify back-to-back transactions",
                "Test PSLVERR error response",
                "Verify wait states with PREADY low",
                "Test PSEL deassert during transaction"
            ]
        elif protocol == "axi4lite":
            protocol_tests = [
                "Verify handshake completion (VALID-READY)",
                "Test write response (BRESP)",
                "Test read response (RRESP)",
                "Verify no data corruption on back-to-back",
                "Test outstanding transactions"
            ]
        elif protocol == "uart":
            protocol_tests = [
                "Verify baud rate accuracy",
                "Test start/stop bit timing",
                "Test parity (if enabled)",
                "Test frame error detection",
                "Test overrun error"
            ]
        elif protocol == "spi":
            protocol_tests = [
                "Verify clock polarity (CPOL)",
                "Verify clock phase (CPHA)",
                "Test chip select timing",
                "Verify MSB/LSB first",
                "Test multiple byte transfer"
            ]
        elif protocol == "i2c":
            protocol_tests = [
                "Verify START condition",
                "Verify STOP condition",
                "Test ACK/NACK response",
                "Test clock stretching",
                "Test repeated START"
            ]
        else:
            protocol_tests = [
                "Verify basic read operation",
                "Verify basic write operation",
                "Test control signals timing"
            ]
        
        # FSM tests
        if parsed.fsm and parsed.fsm.states:
            states = parsed.fsm.states
            fsm_tests.append(f"Verify all {len(states)} states are reachable")
            fsm_tests.append("Test all valid state transitions")
            fsm_tests.append("Test illegal state recovery")
            for state in states[:3]:  # First 3 states
                fsm_tests.append(f"Verify behavior in {state} state")
        else:
            fsm_tests.append("No FSM detected - verify sequential logic")
        
        # Data path tests
        data_w = parsed.get_data_width()
        addr_w = parsed.get_addr_width()
        data_path_tests = [
            f"Test all-zeros data (0x{'0'*((data_w+3)//4)})",
            f"Test all-ones data (0x{'F'*((data_w+3)//4)})",
            "Test alternating pattern (0xAA...)",
            "Test walking ones pattern",
            f"Test full address range (0 to 2^{addr_w}-1)"
        ]
        
        # Edge cases
        edge_cases = [
            "Transaction at reset edge",
            "Back-to-back transactions",
            "Maximum frequency operation",
            "Minimum timing margins"
        ]
        
        # Corner cases based on design
        if parsed.fsm:
            corner_cases.append("State transition during reset")
            corner_cases.append("Invalid state encoding")
        
        corner_cases.extend([
            "Bus contention scenarios",
            "Clock boundary crossing",
            "Power-on sequence"
        ])
        
        return VerificationChecklist(
            reset_tests=reset_tests,
            protocol_tests=protocol_tests,
            fsm_tests=fsm_tests,
            data_path_tests=data_path_tests,
            edge_cases=edge_cases,
            corner_cases=corner_cases
        )


def parse_rtl(rtl_content: str, file_path: str = "") -> SimpleParsedRTL:
    """
    Convenience function to parse RTL and return a simple object for app.py.
    """
    parser = RTLParser()
    parsed = parser.parse(rtl_content, file_path)
    return SimpleParsedRTL(parsed)


# Example usage and testing
if __name__ == "__main__":
    # Test with a sample APB slave
    sample_rtl = '''
    module apb_slave #(
        parameter DATA_WIDTH = 32,
        parameter ADDR_WIDTH = 8
    ) (
        input  logic                    pclk,
        input  logic                    preset_n,
        input  logic                    psel,
        input  logic                    penable,
        input  logic                    pwrite,
        input  logic [ADDR_WIDTH-1:0]   paddr,
        input  logic [DATA_WIDTH-1:0]   pwdata,
        output logic [DATA_WIDTH-1:0]   prdata,
        output logic                    pready,
        output logic                    pslverr
    );
    
        typedef enum logic [1:0] {
            IDLE   = 2'b00,
            SETUP  = 2'b01,
            ACCESS = 2'b10
        } state_t;
        
        state_t state, next_state;
        
        always_ff @(posedge pclk or negedge preset_n) begin
            if (!preset_n)
                state <= IDLE;
            else
                state <= next_state;
        end
        
    endmodule
    '''
    
    result = analyze_rtl(sample_rtl)
    import json
    print(json.dumps(result, indent=2))
