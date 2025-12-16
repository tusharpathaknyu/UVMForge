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
