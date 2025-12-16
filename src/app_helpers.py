"""
Helper functions for VerifAI app
Extracted for testability
"""

import json
import io
import re
import zipfile
from typing import Dict, List, Any, Optional
from datetime import datetime

def generate_wavedrom(protocol: str) -> str:
    """Generate WaveDrom JSON for protocol timing diagrams"""
    wavedroms = {
        "apb": {
            "signal": [
                {"name": "PCLK", "wave": "p........"},
                {"name": "PSEL", "wave": "0.1....0."},
                {"name": "PENABLE", "wave": "0..1...0."},
                {"name": "PWRITE", "wave": "0.1....0."},
                {"name": "PADDR", "wave": "x.3....x.", "data": ["ADDR"]},
                {"name": "PWDATA", "wave": "x.4....x.", "data": ["DATA"]},
                {"name": "PREADY", "wave": "0....1.0."},
                {"name": "PRDATA", "wave": "x.....5x.", "data": ["RDATA"]}
            ],
            "head": {"text": "APB Write Transaction", "tick": 0}
        },
        "axi4lite": {
            "signal": [
                {"name": "ACLK", "wave": "p........."},
                {"name": "AWVALID", "wave": "0.1..0...."},
                {"name": "AWREADY", "wave": "0...10...."},
                {"name": "AWADDR", "wave": "x.3..x....", "data": ["ADDR"]},
                {"name": "WVALID", "wave": "0....1.0.."},
                {"name": "WREADY", "wave": "0.....10.."},
                {"name": "WDATA", "wave": "x....4.x..", "data": ["DATA"]},
                {"name": "BVALID", "wave": "0.......1."},
                {"name": "BREADY", "wave": "1........."}
            ],
            "head": {"text": "AXI4-Lite Write Transaction", "tick": 0}
        },
        "spi": {
            "signal": [
                {"name": "SCLK", "wave": "0.hlhlhlhl"},
                {"name": "CS_N", "wave": "10.......1"},
                {"name": "MOSI", "wave": "x.34567890", "data": ["7","6","5","4","3","2","1","0"]},
                {"name": "MISO", "wave": "x.90876543", "data": ["7","6","5","4","3","2","1","0"]}
            ],
            "head": {"text": "SPI Mode 0 Transfer (8-bit)", "tick": 0}
        },
        "uart": {
            "signal": [
                {"name": "TX", "wave": "1.0.3.4.5.6.7.8.9.0.1.1", "data": ["ST","0","1","2","3","4","5","6","7","SP"]}
            ],
            "head": {"text": "UART Frame (8N1)", "tick": 0},
            "foot": {"text": "Start bit, 8 data bits, Stop bit"}
        },
        "i2c": {
            "signal": [
                {"name": "SCL", "wave": "1.0h.l.h.l.h.l.h.l.h.l.h1"},
                {"name": "SDA", "wave": "1.0..3...4...5...6...0..1", "data": ["A6","A5","A4","ACK"]}
            ],
            "head": {"text": "I2C Start + Address", "tick": 0}
        }
    }
    return json.dumps(wavedroms.get(protocol.lower().replace("-", "").replace("4_", "4"), wavedroms["apb"]))


def calculate_quality_score(parsed: Any, generated_code: str) -> Dict[str, Any]:
    """Calculate testbench quality score"""
    score = 0
    breakdown = {}
    
    # Component completeness (40 points)
    components = ['interface', 'driver', 'monitor', 'scoreboard', 'coverage', 'agent', 'env', 'sequence', 'test']
    found = sum(1 for c in components if c in generated_code.lower())
    breakdown['completeness'] = int((found / len(components)) * 40)
    score += breakdown['completeness']
    
    # Protocol awareness (20 points)
    if parsed and hasattr(parsed, 'complexity') and parsed.complexity:
        if parsed.complexity.detected_protocol != "generic":
            breakdown['protocol'] = 20
        else:
            breakdown['protocol'] = 10
    else:
        breakdown['protocol'] = 5
    score += breakdown['protocol']
    
    # Coverage potential (20 points)
    if 'covergroup' in generated_code.lower() or 'coverpoint' in generated_code.lower():
        breakdown['coverage'] = 20
    elif 'coverage' in generated_code.lower():
        breakdown['coverage'] = 10
    else:
        breakdown['coverage'] = 5
    score += breakdown['coverage']
    
    # Code quality indicators (20 points)
    quality = 0
    if 'uvm_info' in generated_code.lower(): quality += 5
    if 'uvm_error' in generated_code.lower(): quality += 5
    if '`uvm_' in generated_code: quality += 5
    if 'virtual interface' in generated_code.lower(): quality += 5
    breakdown['quality'] = quality
    score += quality
    
    return {'score': min(score, 100), 'breakdown': breakdown}


def predict_bugs(parsed: Any) -> List[Dict[str, str]]:
    """Predict likely verification bugs based on RTL analysis"""
    bugs = []
    
    if parsed and hasattr(parsed, 'complexity') and parsed.complexity:
        cx = parsed.complexity
        protocol = cx.detected_protocol
        
        # Common protocol-specific bugs
        if protocol == "apb":
            bugs.append({
                'severity': 'high',
                'title': 'PREADY Timing',
                'description': 'APB slave may not handle PREADY deasserted case properly - ensure wait state testing'
            })
            bugs.append({
                'severity': 'medium', 
                'title': 'Back-to-Back Transactions',
                'description': 'Sequential transactions without idle cycles may cause data corruption'
            })
        elif protocol == "axi4lite":
            bugs.append({
                'severity': 'high',
                'title': 'Handshake Deadlock',
                'description': 'AXI VALID/READY handshake may deadlock if VALID waits for READY'
            })
            bugs.append({
                'severity': 'medium',
                'title': 'Outstanding Transactions',
                'description': 'Multiple outstanding transactions may cause response ordering issues'
            })
        elif protocol == "spi":
            bugs.append({
                'severity': 'high',
                'title': 'Clock Phase/Polarity',
                'description': 'SPI mode mismatch (CPOL/CPHA) causes bit-shifted data'
            })
        elif protocol == "uart":
            bugs.append({
                'severity': 'medium',
                'title': 'Baud Rate Mismatch',
                'description': 'Clock frequency drift may cause framing errors'
            })
        elif protocol == "i2c":
            bugs.append({
                'severity': 'high',
                'title': 'Clock Stretching',
                'description': 'Slave clock stretching not handled may cause data loss'
            })
        
        # FSM-related bugs
        if cx.has_fsm and cx.fsm_states > 2:
            bugs.append({
                'severity': 'high',
                'title': 'FSM Deadlock',
                'description': f'FSM with {cx.fsm_states} states may have unreachable states or deadlock conditions'
            })
        
        # Reset-related bugs
        if parsed.resets:
            bugs.append({
                'severity': 'medium',
                'title': 'Reset Race Condition',
                'description': 'Async reset release near clock edge may cause metastability'
            })
        
        # Data width bugs
        if cx.data_width >= 32:
            bugs.append({
                'severity': 'medium',
                'title': 'Data Bus Boundary',
                'description': f'{cx.data_width}-bit data may have byte lane issues on partial writes'
            })
    
    return bugs[:5]  # Return top 5 bugs


def create_testbench_zip(module_name: str, generated_code: str, parsed: Any) -> bytes:
    """Create ZIP file with testbench and scripts"""
    zip_buffer = io.BytesIO()
    
    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
        # Main testbench file
        zf.writestr(f"tb/{module_name}_tb_pkg.sv", generated_code)
        
        # Interface file
        interface_code = f'''// Auto-generated interface for {module_name}
interface {module_name}_if(input logic clk);
    // TODO: Add signals from generated testbench
    clocking cb @(posedge clk);
        // Add clocking block signals
    endclocking
    
    modport DRV(clocking cb);
    modport MON(clocking cb);
endinterface
'''
        zf.writestr(f"tb/{module_name}_if.sv", interface_code)
        
        # Makefile for VCS
        vcs_makefile = f'''# Makefile for VCS simulation
TB_TOP = {module_name}_tb_top
DUT = ../rtl/{module_name}.sv

# VCS flags
VCS_FLAGS = -full64 -sverilog -timescale=1ns/1ps
VCS_FLAGS += +define+UVM_NO_DEPRECATED
VCS_FLAGS += -ntb_opts uvm-1.2

# Compile
compile:
\tvcs $(VCS_FLAGS) -o simv \\
\t\t$(DUT) \\
\t\t{module_name}_tb_pkg.sv \\
\t\t{module_name}_if.sv \\
\t\t$(TB_TOP).sv

# Run
run:
\t./simv +UVM_TESTNAME={module_name}_base_test +UVM_VERBOSITY=UVM_MEDIUM

# Run with coverage
run_cov:
\t./simv +UVM_TESTNAME={module_name}_base_test -cm line+cond+fsm+tgl

# Clean
clean:
\trm -rf simv* csrc *.log *.vpd DVEfiles coverage*

.PHONY: compile run run_cov clean
'''
        zf.writestr("tb/Makefile.vcs", vcs_makefile)
        
        # Makefile for Questa
        questa_makefile = f'''# Makefile for Questa simulation
TB_TOP = {module_name}_tb_top
DUT = ../rtl/{module_name}.sv

# Questa flags
VLOG_FLAGS = -sv -timescale 1ns/1ps
VSIM_FLAGS = -c -do "run -all; quit"

# Compile
compile:
\tvlib work
\tvlog $(VLOG_FLAGS) +define+UVM_NO_DEPRECATED \\
\t\t$(DUT) \\
\t\t{module_name}_tb_pkg.sv \\
\t\t{module_name}_if.sv \\
\t\t$(TB_TOP).sv

# Run
run:
\tvsim $(VSIM_FLAGS) +UVM_TESTNAME={module_name}_base_test $(TB_TOP)

# GUI
gui:
\tvsim +UVM_TESTNAME={module_name}_base_test $(TB_TOP)

# Clean
clean:
\trm -rf work transcript *.wlf

.PHONY: compile run gui clean
'''
        zf.writestr("tb/Makefile.questa", questa_makefile)
        
        # README
        readme = f'''# {module_name} UVM Testbench
Generated by VerifAI - https://verifai-761803298484.us-central1.run.app

## Directory Structure
```
tb/
├── {module_name}_tb_pkg.sv    # Main testbench package
├── {module_name}_if.sv        # Interface
├── Makefile.vcs               # VCS build script
└── Makefile.questa            # Questa build script
```

## Quick Start

### VCS
```bash
cd tb
make -f Makefile.vcs compile
make -f Makefile.vcs run
```

### Questa
```bash
cd tb
make -f Makefile.questa compile
make -f Makefile.questa run
```

## Test Configuration
- Default test: {module_name}_base_test
- Verbosity: UVM_MEDIUM (configurable via +UVM_VERBOSITY)

## Generated Components
- Transaction/Sequence Item
- Driver
- Monitor  
- Agent
- Scoreboard
- Coverage Collector
- Environment
- Base Test
'''
        zf.writestr("README.md", readme)
    
    zip_buffer.seek(0)
    return zip_buffer.getvalue()


def validate_rtl_syntax(code: str) -> Dict[str, Any]:
    """Basic RTL syntax validation"""
    errors = []
    warnings = []
    
    if not code.strip():
        return {'valid': False, 'errors': ['Empty code'], 'warnings': []}
    
    # Check for module declaration
    if not re.search(r'\bmodule\s+\w+', code):
        errors.append("Missing module declaration")
    
    # Check for endmodule
    if 'module' in code.lower() and 'endmodule' not in code.lower():
        errors.append("Missing 'endmodule' keyword")
    
    # Check balanced parentheses
    if code.count('(') != code.count(')'):
        errors.append("Unbalanced parentheses")
    
    # Check balanced braces
    if code.count('{') != code.count('}'):
        errors.append("Unbalanced braces")
    
    # Check balanced begin/end
    begin_count = len(re.findall(r'\bbegin\b', code))
    end_count = len(re.findall(r'\bend\b', code))
    if begin_count != end_count:
        warnings.append(f"Possible unbalanced begin/end ({begin_count} begin, {end_count} end)")
    
    # Check for common typos
    if re.search(r'\bwire\s+reg\b|\breg\s+wire\b', code):
        errors.append("Invalid signal type combination")
    
    return {
        'valid': len(errors) == 0,
        'errors': errors,
        'warnings': warnings
    }


def get_protocol_comparison() -> Dict[str, Dict[str, str]]:
    """Return protocol comparison data"""
    return {
        'APB': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Config registers'},
        'AXI4-Lite': {'complexity': 'Medium', 'throughput': 'Medium', 'burst': '❌', 'pipelining': '✅', 'use_case': 'Memory-mapped I/O'},
        'AXI4': {'complexity': 'High', 'throughput': 'High', 'burst': '✅', 'pipelining': '✅', 'use_case': 'High-bandwidth'},
        'SPI': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Serial peripherals'},
        'I2C': {'complexity': 'Medium', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Low-speed devices'},
        'UART': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Debug/console'},
    }


def create_html_export(module_name: str, code: str, parsed: Any = None) -> str:
    """Create HTML export of testbench"""
    html = f'''<!DOCTYPE html>
<html>
<head>
    <title>{module_name} UVM Testbench - VerifAI</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; margin: 2rem; background: #f6f8fa; }}
        .container {{ max-width: 1000px; margin: 0 auto; background: white; padding: 2rem; border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }}
        h1 {{ color: #24292f; border-bottom: 2px solid #0969da; padding-bottom: 0.5rem; }}
        .meta {{ color: #57606a; margin-bottom: 1rem; }}
        pre {{ background: #f6f8fa; padding: 1rem; border-radius: 6px; overflow-x: auto; font-size: 0.85rem; border: 1px solid #d0d7de; }}
        .badge {{ display: inline-block; background: #ddf4ff; color: #0969da; padding: 0.2rem 0.6rem; border-radius: 12px; font-size: 0.8rem; margin-right: 0.5rem; }}
        .footer {{ margin-top: 2rem; color: #57606a; font-size: 0.85rem; border-top: 1px solid #e1e4e8; padding-top: 1rem; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>{module_name} UVM Testbench</h1>
        <div class="meta">
            <span class="badge">Generated by VerifAI</span>
            <span class="badge">{datetime.now().strftime("%Y-%m-%d %H:%M")}</span>
        </div>
        <pre><code>{code.replace("<", "&lt;").replace(">", "&gt;")}</code></pre>
        <div class="footer">
            Generated by <a href="https://verifai-761803298484.us-central1.run.app">VerifAI</a> - UVM Testbench Generator
        </div>
    </div>
</body>
</html>'''
    return html


# Common SVA assertion patterns library
SVA_LIBRARY = {
    'handshake': {
        'name': 'Valid-Ready Handshake',
        'description': 'Ensures proper valid/ready protocol',
        'code': '''property valid_ready_handshake(valid, ready, clk);
    @(posedge clk) valid |-> ##[0:$] ready;
endproperty''',
        'usage': 'AXI, custom interfaces'
    },
    'no_x_outputs': {
        'name': 'No X on Outputs',
        'description': 'Outputs should never be X after reset',
        'code': '''property no_x_after_reset(sig, rst_n, clk);
    @(posedge clk) $rose(rst_n) |-> ##1 !$isunknown(sig);
endproperty''',
        'usage': 'All designs'
    },
    'stable_until_ack': {
        'name': 'Stable Until Acknowledge',
        'description': 'Signal must remain stable until acknowledged',
        'code': '''property stable_until_ack(sig, ack, clk);
    @(posedge clk) $changed(sig) |-> ##[1:$] ack;
endproperty''',
        'usage': 'Request/grant protocols'
    },
    'one_hot': {
        'name': 'One-Hot Check',
        'description': 'Verifies signal is one-hot encoded',
        'code': '''property is_one_hot(sig, clk);
    @(posedge clk) $onehot(sig);
endproperty''',
        'usage': 'FSM states, arbitration'
    },
    'fifo_full': {
        'name': 'FIFO Full Protection',
        'description': 'No writes when FIFO is full',
        'code': '''property no_write_when_full(wr_en, full, clk);
    @(posedge clk) full |-> !wr_en;
endproperty''',
        'usage': 'FIFO interfaces'
    },
    'fifo_empty': {
        'name': 'FIFO Empty Protection',
        'description': 'No reads when FIFO is empty',
        'code': '''property no_read_when_empty(rd_en, empty, clk);
    @(posedge clk) empty |-> !rd_en;
endproperty''',
        'usage': 'FIFO interfaces'
    },
    'timeout': {
        'name': 'Response Timeout',
        'description': 'Response must come within N cycles',
        'code': '''property response_timeout(req, ack, clk);
    @(posedge clk) req |-> ##[1:16] ack;
endproperty''',
        'usage': 'Bus protocols'
    },
    'reset_values': {
        'name': 'Reset Value Check',
        'description': 'Verify outputs reset to correct values',
        'code': '''property reset_value_check(sig, rst_n, expected, clk);
    @(posedge clk) !rst_n |-> sig == expected;
endproperty''',
        'usage': 'All designs'
    }
}
