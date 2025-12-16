"""
RTL-Aware Testbench Generator
Generates UVM testbenches that EXACTLY match your RTL ports and parameters.

This is the KILLER FEATURE - ChatGPT can't do this!
"""

from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any
from pathlib import Path
import os

from .rtl_parser import RTLParser, ParsedRTL, Port, PortDirection
from .spec_import import ParsedSpec, Register, BitField, AccessType, UnifiedSpecParser


@dataclass
class RTLAwareSpec:
    """Combined specification from RTL + optional register spec"""
    rtl: ParsedRTL
    registers: Optional[ParsedSpec] = None
    
    @property
    def module_name(self) -> str:
        return self.rtl.module_name
    
    @property
    def detected_protocol(self) -> str:
        if self.rtl.protocol_hints:
            return self.rtl.protocol_hints[0].protocol
        return "generic"
    
    @property
    def clock(self) -> str:
        if self.rtl.clocks.clock_signals:
            return self.rtl.clocks.clock_signals[0]
        return "clk"
    
    @property
    def reset(self) -> str:
        if self.rtl.clocks.reset_signals:
            return self.rtl.clocks.reset_signals[0]
        return "rst_n"
    
    @property
    def reset_active_low(self) -> bool:
        if self.reset in self.rtl.clocks.reset_polarity:
            return self.rtl.clocks.reset_polarity[self.reset] == "active_low"
        return "_n" in self.reset.lower()


class RTLAwareGenerator:
    """
    Generates UVM testbenches that match your actual RTL.
    
    Key differentiators from ChatGPT:
    1. Exact port matching - no typos, correct widths
    2. Correct clock/reset polarity from RTL analysis
    3. Register tests from IP-XACT/SystemRDL specs
    4. FSM-aware sequences if FSM detected
    """
    
    def __init__(self, output_dir: str = "./output"):
        self.output_dir = Path(output_dir)
        self.output_dir.mkdir(parents=True, exist_ok=True)
        self.rtl_parser = RTLParser()
        self.spec_parser = UnifiedSpecParser()
    
    def generate_from_rtl(
        self, 
        rtl_content: str,
        register_spec: Optional[str] = None,
        register_spec_file: Optional[str] = None
    ) -> Dict[str, str]:
        """
        Generate UVM testbench from RTL content.
        
        Args:
            rtl_content: Verilog/SystemVerilog source code
            register_spec: Optional register spec content (IP-XACT, SystemRDL, CSV)
            register_spec_file: Optional register spec filename (for format detection)
        
        Returns:
            Dictionary of filename -> content
        """
        # Parse RTL
        parsed_rtl = self.rtl_parser.parse(rtl_content)
        
        # Parse register spec if provided
        parsed_regs = None
        if register_spec:
            parsed_regs = self.spec_parser.parse(register_spec, register_spec_file or "")
        
        # Create combined spec
        spec = RTLAwareSpec(rtl=parsed_rtl, registers=parsed_regs)
        
        # Generate files
        return self._generate_files(spec)
    
    def generate_from_files(
        self,
        rtl_file: str,
        register_spec_file: Optional[str] = None
    ) -> Dict[str, str]:
        """Generate from file paths"""
        rtl_content = Path(rtl_file).read_text()
        
        register_spec = None
        if register_spec_file:
            register_spec = Path(register_spec_file).read_text()
        
        return self.generate_from_rtl(rtl_content, register_spec, register_spec_file)
    
    def _generate_files(self, spec: RTLAwareSpec) -> Dict[str, str]:
        """Generate all UVM files"""
        files = {}
        prefix = spec.module_name
        
        # Generate each component
        files[f"{prefix}_pkg.sv"] = self._gen_package(spec)
        files[f"{prefix}_if.sv"] = self._gen_interface(spec)
        files[f"{prefix}_seq_item.sv"] = self._gen_seq_item(spec)
        files[f"{prefix}_driver.sv"] = self._gen_driver(spec)
        files[f"{prefix}_monitor.sv"] = self._gen_monitor(spec)
        files[f"{prefix}_sequencer.sv"] = self._gen_sequencer(spec)
        files[f"{prefix}_agent.sv"] = self._gen_agent(spec)
        files[f"{prefix}_scoreboard.sv"] = self._gen_scoreboard(spec)
        files[f"{prefix}_coverage.sv"] = self._gen_coverage(spec)
        files[f"{prefix}_seq_lib.sv"] = self._gen_sequences(spec)
        files[f"{prefix}_env.sv"] = self._gen_env(spec)
        files[f"{prefix}_base_test.sv"] = self._gen_test(spec)
        files[f"top_tb.sv"] = self._gen_top_tb(spec)
        
        # If registers provided, generate register tests
        if spec.registers:
            files[f"{prefix}_reg_seq.sv"] = self._gen_register_sequences(spec)
        
        return files
    
    def _gen_package(self, spec: RTLAwareSpec) -> str:
        """Generate package with imports"""
        prefix = spec.module_name
        return f'''// VerifAI Generated - RTL-Aware Package
// Module: {prefix}
// Detected Protocol: {spec.detected_protocol}

package {prefix}_pkg;
    import uvm_pkg::*;
    `include "uvm_macros.svh"
    
    // RTL Parameters (extracted from source)
{self._gen_param_declarations(spec)}
    
    // Include all components
    `include "{prefix}_seq_item.sv"
    `include "{prefix}_driver.sv"
    `include "{prefix}_monitor.sv"
    `include "{prefix}_sequencer.sv"
    `include "{prefix}_agent.sv"
    `include "{prefix}_scoreboard.sv"
    `include "{prefix}_coverage.sv"
    `include "{prefix}_seq_lib.sv"
    `include "{prefix}_env.sv"
    `include "{prefix}_base_test.sv"
    
endpackage
'''
    
    def _gen_param_declarations(self, spec: RTLAwareSpec) -> str:
        """Generate parameter declarations from RTL"""
        lines = []
        for param in spec.rtl.parameters:
            lines.append(f"    parameter {param.name} = {param.value};")
        return '\n'.join(lines) if lines else "    // No parameters detected"
    
    def _gen_interface(self, spec: RTLAwareSpec) -> str:
        """Generate interface matching EXACT RTL ports"""
        prefix = spec.module_name
        rtl = spec.rtl
        
        # Generate port declarations
        signal_decls = []
        for port in rtl.ports:
            width_str = f"[{port.msb}:{port.lsb}]" if port.width > 1 else ""
            signed_str = "signed " if port.is_signed else ""
            signal_decls.append(f"    logic {signed_str}{width_str} {port.name};")
        
        # Generate clocking blocks
        clock = spec.clock
        reset = spec.reset
        
        # Separate driver vs monitor signals
        driver_signals = [p for p in rtl.ports if p.direction == PortDirection.INPUT and p.name not in [clock, reset]]
        monitor_signals = [p for p in rtl.ports if p.direction in [PortDirection.OUTPUT, PortDirection.INOUT]]
        
        driver_outputs = '\n'.join(f"        output {p.name};" for p in driver_signals)
        monitor_inputs = '\n'.join(f"        input {p.name};" for p in rtl.ports if p.name not in [clock, reset])
        
        return f'''// VerifAI Generated - RTL-Aware Interface
// Exact port matching from: {spec.rtl.file_path or spec.module_name}

interface {prefix}_if(input logic {clock});
    
    // === Signals (EXACT match to RTL ports) ===
{chr(10).join(signal_decls)}
    
    // === Clocking Blocks ===
    clocking driver_cb @(posedge {clock});
        default input #1step output #1ns;
{driver_outputs}
    endclocking
    
    clocking monitor_cb @(posedge {clock});
        default input #1step output #1ns;
{monitor_inputs}
    endclocking
    
    // === Modports ===
    modport driver_mp(clocking driver_cb, input {clock}, input {reset});
    modport monitor_mp(clocking monitor_cb, input {clock}, input {reset});
    
    // === Helper Tasks ===
    task automatic wait_cycles(int n);
        repeat(n) @(posedge {clock});
    endtask
    
    task automatic wait_reset();
        @({'negedge' if spec.reset_active_low else 'posedge'} {reset});
        @(posedge {clock});
    endtask
    
endinterface
'''
    
    def _gen_seq_item(self, spec: RTLAwareSpec) -> str:
        """Generate sequence item with fields matching RTL"""
        prefix = spec.module_name
        rtl = spec.rtl
        
        # Create fields for key signals
        fields = []
        constraints = []
        
        data_width = rtl.get_data_width()
        addr_width = rtl.get_addr_width()
        
        fields.append(f"    rand bit [{addr_width-1}:0] addr;")
        fields.append(f"    rand bit [{data_width-1}:0] data;")
        fields.append(f"    rand bit write;  // 1=write, 0=read")
        
        # Add register constraints if available
        if spec.registers:
            valid_addrs = [f"'h{r.address:X}" for r in spec.registers.all_registers]
            constraints.append(f"    constraint valid_addr_c {{ addr inside {{{', '.join(valid_addrs)}}}; }}")
        
        return f'''// VerifAI Generated - RTL-Aware Sequence Item
// Data Width: {data_width}, Address Width: {addr_width}

class {prefix}_seq_item extends uvm_sequence_item;
    `uvm_object_utils({prefix}_seq_item)
    
    // === Transaction Fields ===
{chr(10).join(fields)}
    
    // Response
    bit [{data_width-1}:0] rdata;
    bit error;
    
    // === Constraints ===
{chr(10).join(constraints) if constraints else '    // No register-based constraints'}
    
    function new(string name = "{prefix}_seq_item");
        super.new(name);
    endfunction
    
    function string convert2string();
        return $sformatf("%s addr=0x%0h data=0x%0h rdata=0x%0h",
                        write ? "WR" : "RD", addr, data, rdata);
    endfunction
    
    function void do_copy(uvm_object rhs);
        {prefix}_seq_item rhs_;
        super.do_copy(rhs);
        $cast(rhs_, rhs);
        addr = rhs_.addr;
        data = rhs_.data;
        write = rhs_.write;
        rdata = rhs_.rdata;
        error = rhs_.error;
    endfunction
    
endclass
'''
    
    def _gen_driver(self, spec: RTLAwareSpec) -> str:
        """Generate driver with protocol-aware driving"""
        prefix = spec.module_name
        protocol = spec.detected_protocol
        
        # Generate drive task based on detected protocol
        drive_task = self._gen_protocol_drive_task(spec)
        
        return f'''// VerifAI Generated - RTL-Aware Driver
// Detected Protocol: {protocol}

class {prefix}_driver extends uvm_driver #({prefix}_seq_item);
    `uvm_component_utils({prefix}_driver)
    
    virtual {prefix}_if vif;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual {prefix}_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        {prefix}_seq_item req;
        
        // Wait for reset
        vif.wait_reset();
        
        forever begin
            seq_item_port.get_next_item(req);
            drive_item(req);
            seq_item_port.item_done();
        end
    endtask
    
{drive_task}
    
endclass
'''
    
    def _gen_protocol_drive_task(self, spec: RTLAwareSpec) -> str:
        """Generate protocol-specific drive task"""
        protocol = spec.detected_protocol
        prefix = spec.module_name
        clock = spec.clock
        
        if protocol == 'apb':
            return f'''    task drive_item({prefix}_seq_item item);
        // APB Protocol (detected from RTL)
        @(posedge vif.{clock});
        vif.psel <= 1'b1;
        vif.paddr <= item.addr;
        vif.pwrite <= item.write;
        if (item.write) vif.pwdata <= item.data;
        
        @(posedge vif.{clock});
        vif.penable <= 1'b1;
        
        @(posedge vif.{clock});
        while (!vif.pready) @(posedge vif.{clock});
        
        if (!item.write) item.rdata = vif.prdata;
        item.error = vif.pslverr;
        
        vif.psel <= 1'b0;
        vif.penable <= 1'b0;
    endtask'''
        
        elif protocol == 'axi4lite':
            return f'''    task drive_item({prefix}_seq_item item);
        // AXI4-Lite Protocol (detected from RTL)
        if (item.write) begin
            // Write transaction
            fork
                begin // Write address channel
                    vif.awaddr <= item.addr;
                    vif.awvalid <= 1'b1;
                    @(posedge vif.{clock});
                    while (!vif.awready) @(posedge vif.{clock});
                    vif.awvalid <= 1'b0;
                end
                begin // Write data channel
                    vif.wdata <= item.data;
                    vif.wstrb <= '1;
                    vif.wvalid <= 1'b1;
                    @(posedge vif.{clock});
                    while (!vif.wready) @(posedge vif.{clock});
                    vif.wvalid <= 1'b0;
                end
            join
            // Wait for response
            while (!vif.bvalid) @(posedge vif.{clock});
            vif.bready <= 1'b1;
            @(posedge vif.{clock});
            vif.bready <= 1'b0;
        end else begin
            // Read transaction
            vif.araddr <= item.addr;
            vif.arvalid <= 1'b1;
            @(posedge vif.{clock});
            while (!vif.arready) @(posedge vif.{clock});
            vif.arvalid <= 1'b0;
            
            while (!vif.rvalid) @(posedge vif.{clock});
            item.rdata = vif.rdata;
            vif.rready <= 1'b1;
            @(posedge vif.{clock});
            vif.rready <= 1'b0;
        end
    endtask'''
        
        else:  # Generic
            return f'''    task drive_item({prefix}_seq_item item);
        // Generic Protocol - customize for your DUT
        @(posedge vif.{clock});
        
        // TODO: Add your protocol-specific driving logic
        // Detected ports: {', '.join(p.name for p in spec.rtl.input_ports[:5])}...
        
        `uvm_info("DRV", item.convert2string(), UVM_MEDIUM)
    endtask'''
    
    def _gen_monitor(self, spec: RTLAwareSpec) -> str:
        """Generate monitor"""
        prefix = spec.module_name
        clock = spec.clock
        
        return f'''// VerifAI Generated - RTL-Aware Monitor

class {prefix}_monitor extends uvm_monitor;
    `uvm_component_utils({prefix}_monitor)
    
    virtual {prefix}_if vif;
    uvm_analysis_port #({prefix}_seq_item) ap;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        if (!uvm_config_db#(virtual {prefix}_if)::get(this, "", "vif", vif))
            `uvm_fatal("NOVIF", "Virtual interface not found")
    endfunction
    
    task run_phase(uvm_phase phase);
        vif.wait_reset();
        
        forever begin
            {prefix}_seq_item item = {prefix}_seq_item::type_id::create("item");
            collect_transaction(item);
            ap.write(item);
        end
    endtask
    
    task collect_transaction({prefix}_seq_item item);
        // Monitor protocol transactions
        @(posedge vif.{clock});
        // TODO: Add protocol-specific monitoring
        `uvm_info("MON", item.convert2string(), UVM_HIGH)
    endtask
    
endclass
'''
    
    def _gen_sequencer(self, spec: RTLAwareSpec) -> str:
        prefix = spec.module_name
        return f'''// VerifAI Generated Sequencer

class {prefix}_sequencer extends uvm_sequencer #({prefix}_seq_item);
    `uvm_component_utils({prefix}_sequencer)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
endclass
'''
    
    def _gen_agent(self, spec: RTLAwareSpec) -> str:
        prefix = spec.module_name
        return f'''// VerifAI Generated Agent

class {prefix}_agent extends uvm_agent;
    `uvm_component_utils({prefix}_agent)
    
    {prefix}_driver    driver;
    {prefix}_monitor   monitor;
    {prefix}_sequencer sequencer;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        monitor = {prefix}_monitor::type_id::create("monitor", this);
        if (get_is_active() == UVM_ACTIVE) begin
            driver = {prefix}_driver::type_id::create("driver", this);
            sequencer = {prefix}_sequencer::type_id::create("sequencer", this);
        end
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        if (get_is_active() == UVM_ACTIVE)
            driver.seq_item_port.connect(sequencer.seq_item_export);
    endfunction
    
endclass
'''
    
    def _gen_scoreboard(self, spec: RTLAwareSpec) -> str:
        prefix = spec.module_name
        return f'''// VerifAI Generated Scoreboard

class {prefix}_scoreboard extends uvm_scoreboard;
    `uvm_component_utils({prefix}_scoreboard)
    
    uvm_analysis_imp #({prefix}_seq_item, {prefix}_scoreboard) ap;
    
    // Reference model storage
    bit [31:0] ref_mem[int];
    int pass_count, fail_count;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        ap = new("ap", this);
    endfunction
    
    function void write({prefix}_seq_item item);
        if (item.write) begin
            ref_mem[item.addr] = item.data;
            `uvm_info("SCB", $sformatf("WRITE: addr=0x%0h data=0x%0h", item.addr, item.data), UVM_MEDIUM)
        end else begin
            bit [31:0] expected = ref_mem.exists(item.addr) ? ref_mem[item.addr] : '0;
            if (item.rdata === expected) begin
                pass_count++;
                `uvm_info("SCB", $sformatf("PASS: addr=0x%0h exp=0x%0h got=0x%0h", 
                         item.addr, expected, item.rdata), UVM_MEDIUM)
            end else begin
                fail_count++;
                `uvm_error("SCB", $sformatf("FAIL: addr=0x%0h exp=0x%0h got=0x%0h",
                          item.addr, expected, item.rdata))
            end
        end
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info("SCB", $sformatf("Results: %0d PASS, %0d FAIL", pass_count, fail_count), UVM_LOW)
    endfunction
    
endclass
'''
    
    def _gen_coverage(self, spec: RTLAwareSpec) -> str:
        """Generate coverage with register-aware bins if spec provided"""
        prefix = spec.module_name
        data_width = spec.rtl.get_data_width()
        addr_width = spec.rtl.get_addr_width()
        
        # Generate register-specific coverage if available
        reg_bins = ""
        if spec.registers:
            bins = []
            for reg in spec.registers.all_registers:
                bins.append(f"            bins {reg.name.lower()} = {{{reg.address}}};")
            reg_bins = '\n'.join(bins)
        else:
            reg_bins = f"            bins addr_range[] = {{[0:$]}};"
        
        return f'''// VerifAI Generated Coverage

class {prefix}_coverage extends uvm_subscriber #({prefix}_seq_item);
    `uvm_component_utils({prefix}_coverage)
    
    covergroup {prefix}_cg with function sample({prefix}_seq_item item);
        option.per_instance = 1;
        
        // Address coverage
        addr_cp: coverpoint item.addr {{
{reg_bins}
        }}
        
        // Operation type
        op_cp: coverpoint item.write {{
            bins read = {{0}};
            bins write = {{1}};
        }}
        
        // Cross coverage
        addr_op_cross: cross addr_cp, op_cp;
        
    endgroup
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
        {prefix}_cg = new();
    endfunction
    
    function void write({prefix}_seq_item t);
        {prefix}_cg.sample(t);
    endfunction
    
    function void report_phase(uvm_phase phase);
        `uvm_info("COV", $sformatf("Coverage: %.2f%%", {prefix}_cg.get_coverage()), UVM_LOW)
    endfunction
    
endclass
'''
    
    def _gen_sequences(self, spec: RTLAwareSpec) -> str:
        """Generate sequences"""
        prefix = spec.module_name
        return f'''// VerifAI Generated Sequences

class {prefix}_base_seq extends uvm_sequence #({prefix}_seq_item);
    `uvm_object_utils({prefix}_base_seq)
    
    function new(string name = "{prefix}_base_seq");
        super.new(name);
    endfunction
    
endclass

// Random sequence
class {prefix}_random_seq extends {prefix}_base_seq;
    `uvm_object_utils({prefix}_random_seq)
    
    rand int num_items;
    constraint items_c {{ num_items inside {{[10:50]}}; }}
    
    function new(string name = "{prefix}_random_seq");
        super.new(name);
    endfunction
    
    task body();
        repeat(num_items) begin
            `uvm_do(req)
        end
    endtask
    
endclass

// Write-then-read sequence
class {prefix}_wr_rd_seq extends {prefix}_base_seq;
    `uvm_object_utils({prefix}_wr_rd_seq)
    
    function new(string name = "{prefix}_wr_rd_seq");
        super.new(name);
    endfunction
    
    task body();
        bit [31:0] test_addr;
        bit [31:0] test_data;
        
        repeat(10) begin
            test_addr = $urandom();
            test_data = $urandom();
            
            // Write
            `uvm_do_with(req, {{ addr == test_addr; data == test_data; write == 1; }})
            // Read back
            `uvm_do_with(req, {{ addr == test_addr; write == 0; }})
        end
    endtask
    
endclass
'''
    
    def _gen_register_sequences(self, spec: RTLAwareSpec) -> str:
        """Generate register-specific sequences from spec"""
        prefix = spec.module_name
        
        if not spec.registers:
            return ""
        
        # Generate register access tasks
        reg_tasks = []
        for reg in spec.registers.all_registers:
            reg_tasks.append(f'''
    // {reg.name} @ {reg.address_hex}
    task write_{reg.name.lower()}(bit [31:0] data);
        `uvm_do_with(req, {{ addr == 'h{reg.address:X}; this.data == data; write == 1; }})
    endtask
    
    task read_{reg.name.lower()}(output bit [31:0] data);
        `uvm_do_with(req, {{ addr == 'h{reg.address:X}; write == 0; }})
        data = req.rdata;
    endtask''')
        
        return f'''// VerifAI Generated Register Sequences
// Source: {spec.registers.source_format} - {spec.registers.source_file}
// Total Registers: {spec.registers.total_registers}

class {prefix}_reg_seq extends {prefix}_base_seq;
    `uvm_object_utils({prefix}_reg_seq)
    
    function new(string name = "{prefix}_reg_seq");
        super.new(name);
    endfunction
    
    // === Register Access Tasks ===
{''.join(reg_tasks)}
    
    // === Register Test ===
    task body();
        bit [31:0] rdata;
        
        `uvm_info("REG_SEQ", "Starting register test", UVM_LOW)
        
        // Test each register
{self._gen_reg_test_body(spec)}
        
        `uvm_info("REG_SEQ", "Register test complete", UVM_LOW)
    endtask
    
endclass
'''
    
    def _gen_reg_test_body(self, spec: RTLAwareSpec) -> str:
        """Generate register test body"""
        if not spec.registers:
            return ""
        
        lines = []
        for reg in spec.registers.all_registers:
            lines.append(f'''        // Test {reg.name}
        write_{reg.name.lower()}(32'hA5A5_A5A5);
        read_{reg.name.lower()}(rdata);
        `uvm_info("REG", $sformatf("{reg.name}: wrote=0x%0h read=0x%0h", 32'hA5A5_A5A5, rdata), UVM_MEDIUM)
''')
        return '\n'.join(lines)
    
    def _gen_env(self, spec: RTLAwareSpec) -> str:
        prefix = spec.module_name
        return f'''// VerifAI Generated Environment

class {prefix}_env extends uvm_env;
    `uvm_component_utils({prefix}_env)
    
    {prefix}_agent      agent;
    {prefix}_scoreboard scoreboard;
    {prefix}_coverage   coverage;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        agent = {prefix}_agent::type_id::create("agent", this);
        scoreboard = {prefix}_scoreboard::type_id::create("scoreboard", this);
        coverage = {prefix}_coverage::type_id::create("coverage", this);
    endfunction
    
    function void connect_phase(uvm_phase phase);
        super.connect_phase(phase);
        agent.monitor.ap.connect(scoreboard.ap);
        agent.monitor.ap.connect(coverage.analysis_export);
    endfunction
    
endclass
'''
    
    def _gen_test(self, spec: RTLAwareSpec) -> str:
        prefix = spec.module_name
        return f'''// VerifAI Generated Test

class {prefix}_base_test extends uvm_test;
    `uvm_component_utils({prefix}_base_test)
    
    {prefix}_env env;
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        env = {prefix}_env::type_id::create("env", this);
    endfunction
    
    task run_phase(uvm_phase phase);
        {prefix}_random_seq seq;
        
        phase.raise_objection(this);
        
        seq = {prefix}_random_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        phase.drop_objection(this);
    endtask
    
endclass

// Register test (if spec provided)
class {prefix}_reg_test extends {prefix}_base_test;
    `uvm_component_utils({prefix}_reg_test)
    
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction
    
    task run_phase(uvm_phase phase);
        {prefix}_reg_seq seq;
        
        phase.raise_objection(this);
        
        seq = {prefix}_reg_seq::type_id::create("seq");
        seq.start(env.agent.sequencer);
        
        phase.drop_objection(this);
    endtask
    
endclass
'''
    
    def _gen_top_tb(self, spec: RTLAwareSpec) -> str:
        """Generate top testbench with EXACT DUT instantiation"""
        prefix = spec.module_name
        rtl = spec.rtl
        clock = spec.clock
        reset = spec.reset
        
        # Generate DUT port connections
        dut_connections = []
        for port in rtl.ports:
            dut_connections.append(f"        .{port.name}({prefix}_vif.{port.name})")
        
        # Reset logic
        reset_active = "1'b0" if spec.reset_active_low else "1'b1"
        reset_inactive = "1'b1" if spec.reset_active_low else "1'b0"
        
        return f'''// VerifAI Generated Top Testbench
// DUT: {prefix}
// Ports: {len(rtl.ports)} (auto-extracted from RTL)

`timescale 1ns/1ps

module top_tb;
    import uvm_pkg::*;
    import {prefix}_pkg::*;
    
    // Clock generation
    logic {clock};
    initial begin
        {clock} = 0;
        forever #5 {clock} = ~{clock};  // 100MHz
    end
    
    // Reset generation
    logic {reset};
    initial begin
        {reset} = {reset_active};  // Assert reset
        repeat(10) @(posedge {clock});
        {reset} = {reset_inactive};  // De-assert reset
    end
    
    // Interface
    {prefix}_if {prefix}_vif(.{clock}({clock}));
    assign {prefix}_vif.{reset} = {reset};
    
    // DUT instantiation (EXACT port match)
    {prefix} dut (
{',{chr(10)}'.join(dut_connections)}
    );
    
    // UVM configuration
    initial begin
        uvm_config_db#(virtual {prefix}_if)::set(null, "*", "vif", {prefix}_vif);
        run_test("{prefix}_base_test");
    end
    
    // Waveform dump
    initial begin
        $dumpfile("{prefix}_tb.vcd");
        $dumpvars(0, top_tb);
    end
    
endmodule
'''
    
    def save_files(self, files: Dict[str, str], output_dir: Optional[str] = None) -> List[str]:
        """Save generated files to disk"""
        out_dir = Path(output_dir) if output_dir else self.output_dir
        out_dir.mkdir(parents=True, exist_ok=True)
        
        saved = []
        for filename, content in files.items():
            filepath = out_dir / filename
            filepath.write_text(content)
            saved.append(str(filepath))
        
        return saved


# Convenience function
def generate_from_rtl(rtl_content: str, register_spec: str = None) -> Dict[str, str]:
    """Generate UVM testbench from RTL content"""
    gen = RTLAwareGenerator()
    return gen.generate_from_rtl(rtl_content, register_spec)
