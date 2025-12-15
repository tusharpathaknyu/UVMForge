"""
Code Generator Engine - Renders UVM templates
"""

import os
from pathlib import Path
from typing import Dict, Any, List, Optional
from dataclasses import dataclass
from jinja2 import Environment, FileSystemLoader, select_autoescape

from .parser import ParsedSpec, AccessType


@dataclass
class GeneratedFile:
    """Represents a generated file"""
    filename: str
    content: str
    category: str  # "agent", "env", "sequence", "coverage", etc.


class UVMGenerator:
    """Generates UVM testbench files from parsed specifications"""
    
    def __init__(self, template_dir: Optional[str] = None):
        if template_dir is None:
            # Default to templates directory relative to this file
            template_dir = Path(__file__).parent.parent / "templates"
        
        self.template_dir = Path(template_dir)
        self.env = Environment(
            loader=FileSystemLoader(str(self.template_dir)),
            autoescape=select_autoescape(['html', 'xml']),
            trim_blocks=True,
            lstrip_blocks=True
        )
        
        # Add custom filters
        self.env.filters['hex'] = lambda x: f"'h{x:X}" if isinstance(x, int) else x
        self.env.filters['upper'] = str.upper
        self.env.filters['lower'] = str.lower
        self.env.filters['snake_case'] = self._to_snake_case
        
    def _to_snake_case(self, name: str) -> str:
        """Convert string to snake_case"""
        import re
        s1 = re.sub('(.)([A-Z][a-z]+)', r'\1_\2', name)
        return re.sub('([a-z0-9])([A-Z])', r'\1_\2', s1).lower()
    
    def generate(self, spec: ParsedSpec, output_dir: str) -> List[GeneratedFile]:
        """
        Generate all UVM files for the given specification.
        
        Args:
            spec: Parsed specification
            output_dir: Directory to write generated files
            
        Returns:
            List of generated files
        """
        output_path = Path(output_dir)
        output_path.mkdir(parents=True, exist_ok=True)
        
        # Build template context
        context = self._build_context(spec)
        
        # Get templates for the protocol
        templates = self._get_protocol_templates(spec.protocol)
        
        generated_files = []
        
        for template_info in templates:
            template_name = template_info["template"]
            output_name = template_info["output"].format(**context)
            category = template_info.get("category", "misc")
            
            # Check if template exists
            template_path = self.template_dir / template_name
            if not template_path.exists():
                print(f"  ⚠ Template not found: {template_name}")
                continue
            
            # Render template
            template = self.env.get_template(template_name)
            content = template.render(**context)
            
            # Write file
            output_file = output_path / output_name
            output_file.parent.mkdir(parents=True, exist_ok=True)
            output_file.write_text(content)
            
            generated_files.append(GeneratedFile(
                filename=output_name,
                content=content,
                category=category
            ))
        
        # Generate Makefile
        makefile_content = self._generate_makefile(spec, generated_files)
        makefile_path = output_path / "Makefile"
        makefile_path.write_text(makefile_content)
        generated_files.append(GeneratedFile(
            filename="Makefile",
            content=makefile_content,
            category="build"
        ))
        
        return generated_files
    
    def _build_context(self, spec: ParsedSpec) -> Dict[str, Any]:
        """Build the template context from parsed spec"""
        # Prefix for all components
        prefix = spec.protocol.lower()
        module = spec.module_name or f"{prefix}_dut"
        
        # Process registers for templates
        registers = []
        for reg in spec.registers:
            registers.append({
                "name": reg.name,
                "name_lower": reg.name.lower(),
                "address": reg.address,
                "address_hex": f"'h{reg.address:02X}",
                "access": reg.access.value,
                "is_readable": reg.access in [AccessType.RO, AccessType.RW],
                "is_writable": reg.access in [AccessType.RW, AccessType.WO, AccessType.W1C, AccessType.W1S],
                "reset_value": reg.reset_value,
                "reset_value_hex": f"'h{reg.reset_value:08X}",
                "width": reg.width,
                "description": reg.description or f"{reg.name} register"
            })
        
        return {
            # Protocol info
            "protocol": spec.protocol,
            "protocol_upper": spec.protocol.upper(),
            "prefix": prefix,
            "PREFIX": prefix.upper(),
            
            # Module info
            "module_name": module,
            "module_name_upper": module.upper(),
            
            # Signal widths
            "data_width": spec.data_width,
            "addr_width": spec.addr_width,
            "strb_width": spec.data_width // 8,
            
            # Clock/Reset
            "clock": spec.clock_name,
            "reset": spec.reset_name,
            "reset_active_low": spec.reset_active_low,
            "reset_active": f"!{spec.reset_name}" if spec.reset_active_low else spec.reset_name,
            
            # Registers
            "registers": registers,
            "has_registers": len(registers) > 0,
            "num_registers": len(registers),
            
            # Features
            "features": spec.features,
            "has_scoreboard": "scoreboard" in spec.features,
            "has_coverage": "coverage" in spec.features,
            "has_ral": "ral" in spec.features,
            
            # AXI-specific
            "axi_id_width": spec.axi_id_width,
            "axi_outstanding": spec.axi_outstanding,
            
            # APB-specific
            "apb_version": spec.apb_version,
            
            # UART-specific
            "baud_rate": spec.baud_rate,
            "data_bits": spec.data_bits,
            "stop_bits": spec.stop_bits,
            "parity": spec.parity,
            "has_rts_cts": spec.has_rts_cts,
            "has_tx_fifo": spec.has_tx_fifo,
            "has_rx_fifo": spec.has_rx_fifo,
            "fifo_depth": spec.fifo_depth,
            "bit_period_ns": int(1e9 / spec.baud_rate),
            "frame_bits": spec.data_bits + 1 + (1 if spec.parity != 'none' else 0) + int(spec.stop_bits),
            
            # SPI-specific
            "spi_mode": spec.spi_mode,
            "spi_num_slaves": spec.spi_num_slaves,
            "spi_msb_first": spec.spi_msb_first,
            "spi_clock_divider": spec.spi_clock_divider,
            "spi_cs_setup_time": spec.spi_cs_setup_time,
            "spi_cs_hold_time": spec.spi_cs_hold_time,
            "spi_supports_qspi": spec.spi_supports_qspi,
            
            # I2C-specific
            "i2c_speed_mode": spec.i2c_speed_mode,
            "i2c_address_bits": spec.i2c_address_bits,
            "i2c_clock_stretching": spec.i2c_clock_stretching,
            "i2c_multi_master": spec.i2c_multi_master,
        }
    
    def _get_protocol_templates(self, protocol: str) -> List[Dict[str, str]]:
        """Get list of templates for a protocol"""
        
        if protocol == "apb":
            return [
                {"template": "apb/apb_pkg.sv.j2", "output": "{prefix}_pkg.sv", "category": "package"},
                {"template": "apb/apb_interface.sv.j2", "output": "{prefix}_if.sv", "category": "interface"},
                {"template": "apb/apb_seq_item.sv.j2", "output": "{prefix}_seq_item.sv", "category": "agent"},
                {"template": "apb/apb_driver.sv.j2", "output": "{prefix}_driver.sv", "category": "agent"},
                {"template": "apb/apb_monitor.sv.j2", "output": "{prefix}_monitor.sv", "category": "agent"},
                {"template": "apb/apb_sequencer.sv.j2", "output": "{prefix}_sequencer.sv", "category": "agent"},
                {"template": "apb/apb_agent.sv.j2", "output": "{prefix}_agent.sv", "category": "agent"},
                {"template": "apb/apb_sequence_lib.sv.j2", "output": "{prefix}_seq_lib.sv", "category": "sequence"},
                {"template": "apb/apb_scoreboard.sv.j2", "output": "{prefix}_scoreboard.sv", "category": "scoreboard"},
                {"template": "apb/apb_coverage.sv.j2", "output": "{prefix}_coverage.sv", "category": "coverage"},
                {"template": "apb/apb_env.sv.j2", "output": "{prefix}_env.sv", "category": "env"},
                {"template": "apb/apb_base_test.sv.j2", "output": "{prefix}_base_test.sv", "category": "test"},
                {"template": "apb/apb_top_tb.sv.j2", "output": "top_tb.sv", "category": "top"},
            ]
        
        elif protocol == "axi4lite":
            return [
                {"template": "axi4lite/axi4lite_pkg.sv.j2", "output": "{prefix}_pkg.sv", "category": "package"},
                {"template": "axi4lite/axi4lite_interface.sv.j2", "output": "{prefix}_if.sv", "category": "interface"},
                {"template": "axi4lite/axi4lite_seq_item.sv.j2", "output": "{prefix}_seq_item.sv", "category": "agent"},
                {"template": "axi4lite/axi4lite_driver.sv.j2", "output": "{prefix}_driver.sv", "category": "agent"},
                {"template": "axi4lite/axi4lite_monitor.sv.j2", "output": "{prefix}_monitor.sv", "category": "agent"},
                {"template": "axi4lite/axi4lite_sequencer.sv.j2", "output": "{prefix}_sequencer.sv", "category": "agent"},
                {"template": "axi4lite/axi4lite_agent.sv.j2", "output": "{prefix}_agent.sv", "category": "agent"},
                {"template": "axi4lite/axi4lite_sequence_lib.sv.j2", "output": "{prefix}_seq_lib.sv", "category": "sequence"},
                {"template": "axi4lite/axi4lite_scoreboard.sv.j2", "output": "{prefix}_scoreboard.sv", "category": "scoreboard"},
                {"template": "axi4lite/axi4lite_coverage.sv.j2", "output": "{prefix}_coverage.sv", "category": "coverage"},
                {"template": "axi4lite/axi4lite_env.sv.j2", "output": "{prefix}_env.sv", "category": "env"},
                {"template": "axi4lite/axi4lite_base_test.sv.j2", "output": "{prefix}_base_test.sv", "category": "test"},
                {"template": "axi4lite/axi4lite_top_tb.sv.j2", "output": "top_tb.sv", "category": "top"},
            ]
        
        elif protocol == "uart":
            return [
                {"template": "uart/uart_pkg.sv.j2", "output": "{prefix}_pkg.sv", "category": "package"},
                {"template": "uart/uart_interface.sv.j2", "output": "{prefix}_if.sv", "category": "interface"},
                {"template": "uart/uart_seq_item.sv.j2", "output": "{prefix}_seq_item.sv", "category": "agent"},
                {"template": "uart/uart_driver.sv.j2", "output": "{prefix}_driver.sv", "category": "agent"},
                {"template": "uart/uart_monitor.sv.j2", "output": "{prefix}_monitor.sv", "category": "agent"},
                {"template": "uart/uart_sequencer.sv.j2", "output": "{prefix}_sequencer.sv", "category": "agent"},
                {"template": "uart/uart_agent.sv.j2", "output": "{prefix}_agent.sv", "category": "agent"},
                {"template": "uart/uart_sequence_lib.sv.j2", "output": "{prefix}_seq_lib.sv", "category": "sequence"},
                {"template": "uart/uart_scoreboard.sv.j2", "output": "{prefix}_scoreboard.sv", "category": "scoreboard"},
                {"template": "uart/uart_coverage.sv.j2", "output": "{prefix}_coverage.sv", "category": "coverage"},
                {"template": "uart/uart_env.sv.j2", "output": "{prefix}_env.sv", "category": "env"},
                {"template": "uart/uart_base_test.sv.j2", "output": "{prefix}_base_test.sv", "category": "test"},
                {"template": "uart/uart_top_tb.sv.j2", "output": "top_tb.sv", "category": "top"},
            ]
        
        elif protocol == "spi":
            return [
                {"template": "spi/spi_pkg.sv.j2", "output": "{prefix}_pkg.sv", "category": "package"},
                {"template": "spi/spi_interface.sv.j2", "output": "{prefix}_if.sv", "category": "interface"},
                {"template": "spi/spi_seq_item.sv.j2", "output": "{prefix}_seq_item.sv", "category": "agent"},
                {"template": "spi/spi_driver.sv.j2", "output": "{prefix}_driver.sv", "category": "agent"},
                {"template": "spi/spi_monitor.sv.j2", "output": "{prefix}_monitor.sv", "category": "agent"},
                {"template": "spi/spi_sequencer.sv.j2", "output": "{prefix}_sequencer.sv", "category": "agent"},
                {"template": "spi/spi_agent.sv.j2", "output": "{prefix}_agent.sv", "category": "agent"},
                {"template": "spi/spi_sequence_lib.sv.j2", "output": "{prefix}_seq_lib.sv", "category": "sequence"},
                {"template": "spi/spi_scoreboard.sv.j2", "output": "{prefix}_scoreboard.sv", "category": "scoreboard"},
                {"template": "spi/spi_coverage.sv.j2", "output": "{prefix}_coverage.sv", "category": "coverage"},
                {"template": "spi/spi_env.sv.j2", "output": "{prefix}_env.sv", "category": "env"},
                {"template": "spi/spi_base_test.sv.j2", "output": "{prefix}_base_test.sv", "category": "test"},
                {"template": "spi/spi_top_tb.sv.j2", "output": "top_tb.sv", "category": "top"},
            ]
        
        elif protocol == "i2c":
            return [
                {"template": "i2c/i2c_pkg.sv.j2", "output": "{prefix}_pkg.sv", "category": "package"},
                {"template": "i2c/i2c_interface.sv.j2", "output": "{prefix}_if.sv", "category": "interface"},
                {"template": "i2c/i2c_seq_item.sv.j2", "output": "{prefix}_seq_item.sv", "category": "agent"},
                {"template": "i2c/i2c_driver.sv.j2", "output": "{prefix}_driver.sv", "category": "agent"},
                {"template": "i2c/i2c_monitor.sv.j2", "output": "{prefix}_monitor.sv", "category": "agent"},
                {"template": "i2c/i2c_sequencer.sv.j2", "output": "{prefix}_sequencer.sv", "category": "agent"},
                {"template": "i2c/i2c_agent.sv.j2", "output": "{prefix}_agent.sv", "category": "agent"},
                {"template": "i2c/i2c_sequence_lib.sv.j2", "output": "{prefix}_seq_lib.sv", "category": "sequence"},
                {"template": "i2c/i2c_scoreboard.sv.j2", "output": "{prefix}_scoreboard.sv", "category": "scoreboard"},
                {"template": "i2c/i2c_coverage.sv.j2", "output": "{prefix}_coverage.sv", "category": "coverage"},
                {"template": "i2c/i2c_env.sv.j2", "output": "{prefix}_env.sv", "category": "env"},
                {"template": "i2c/i2c_base_test.sv.j2", "output": "{prefix}_base_test.sv", "category": "test"},
                {"template": "i2c/i2c_top_tb.sv.j2", "output": "top_tb.sv", "category": "top"},
            ]
        
        else:
            raise ValueError(f"Unsupported protocol: {protocol}")
    
    def _generate_makefile(self, spec: ParsedSpec, files: List[GeneratedFile]) -> str:
        """Generate a Makefile for simulation"""
        sv_files = [f.filename for f in files if f.filename.endswith('.sv')]
        
        # Build file list for Makefile (avoiding backslash in f-string)
        newline = '\n'
        backslash = '\\'
        file_lines = [f"    {f} {backslash}" for f in sv_files[:-1]]
        sv_files_section = newline.join(file_lines)
        last_file = sv_files[-1] if sv_files else ""
        
        return f'''# VerifAI Generated Makefile
# Protocol: {spec.protocol.upper()}
# Module: {spec.module_name}

# Simulator selection (override with: make SIM=questa)
SIM ?= verilator

# Source files
SV_FILES = {backslash}
{sv_files_section}
    {last_file}

# UVM settings
UVM_HOME ?= $(shell which vcs > /dev/null && echo "builtin" || echo "$(HOME)/uvm-1.2")
UVM_FLAGS = +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME={spec.protocol}_base_test

# Verilator flags
VERILATOR_FLAGS = --binary --timing -Wall -Wno-fatal

# VCS flags  
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps -ntb_opts uvm-1.2

# Questa flags
QUESTA_FLAGS = -sv -timescale 1ns/1ps +acc -coverage

.PHONY: all sim clean compile run

all: sim

# Verilator (free, open-source)
verilator: $(SV_FILES)
\tverilator $(VERILATOR_FLAGS) --top-module top_tb $(SV_FILES)
\t./obj_dir/Vtop_tb

# VCS
vcs: $(SV_FILES)
\tvcs $(VCS_FLAGS) -o simv $(SV_FILES)
\t./simv $(UVM_FLAGS)

# Questa/ModelSim
questa: $(SV_FILES)
\tvlib work
\tvlog $(QUESTA_FLAGS) $(SV_FILES)
\tvsim -c -do "run -all; quit" top_tb $(UVM_FLAGS)

# Generic sim target
sim:
ifeq ($(SIM),verilator)
\t$(MAKE) verilator
else ifeq ($(SIM),vcs)
\t$(MAKE) vcs
else ifeq ($(SIM),questa)
\t$(MAKE) questa
else
\t@echo "Unknown simulator: $(SIM)"
\t@echo "Supported: verilator, vcs, questa"
endif

clean:
\trm -rf obj_dir simv* work *.log *.vcd csrc DVEfiles
'''
