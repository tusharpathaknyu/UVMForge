# VerifAI - UVM Testbench Generator

## 📋 Table of Contents
1. [Project Overview](#project-overview)
2. [Features](#features)
3. [Live Demo](#live-demo)
4. [Installation](#installation)
5. [Usage Guide](#usage-guide)
6. [Tab-by-Tab Guide](#tab-by-tab-guide)
7. [Generated Code Structure](#generated-code-structure)
8. [API Reference](#api-reference)
9. [Troubleshooting](#troubleshooting)

---

## 🎯 Project Overview

**VerifAI** is an AI-powered UVM (Universal Verification Methodology) testbench generator that transforms RTL (Register Transfer Level) code into production-ready SystemVerilog verification environments. It dramatically reduces the time needed to create comprehensive UVM testbenches from days/weeks to seconds.

### What Problem Does It Solve?

Writing UVM testbenches is one of the most time-consuming tasks in hardware verification:
- A typical UVM testbench has **10+ components** (interface, driver, monitor, scoreboard, etc.)
- Each component requires **hundreds of lines** of boilerplate code
- Manual writing takes **days to weeks** for complex protocols
- Protocol-specific timing and coverage requirements need expert knowledge

**VerifAI solves this by:**
- Automatically detecting the protocol (APB, AXI, SPI, UART, I2C)
- Generating all UVM components with proper methodology
- Creating protocol-aware assertions and coverage
- Providing downloadable, simulator-ready packages

### Technology Stack

| Component | Technology |
|-----------|------------|
| Frontend | Streamlit (Python web framework) |
| Backend | Python 3.11+ |
| Parsing | Custom RTL parser with regex + AST |
| Deployment | Google Cloud Run (containerized) |
| Testing | pytest (212 tests) |

---

## ✨ Features

### Core Features

| Feature | Description |
|---------|-------------|
| **RTL to Testbench** | Paste Verilog/SystemVerilog code and get complete UVM testbench |
| **Protocol Detection** | Auto-detects APB, AXI4-Lite, UART, SPI, I2C protocols |
| **Protocol Templates** | Pre-built templates for common protocols |
| **Coverage Analysis** | Parse coverage reports and get gap analysis |
| **SVA Generation** | Generate SystemVerilog Assertions from RTL |
| **Register Map** | Import CSV/JSON specs, generate UVM RAL models |

### UI Features

| Feature | Description |
|---------|-------------|
| **Dark/Light Mode** | Toggle theme with 🌙/☀️ button |
| **Generation History** | Access previously generated testbenches |
| **File Upload** | Upload .v, .sv, .vh, .svh files directly |
| **Multi-format Download** | Download as .sv, .zip, or .html |
| **Protocol Timing Diagrams** | Visual ASCII waveforms for each protocol |

---

## 🌐 Live Demo

The application is deployed and accessible at:

**https://verifai-761803298484.us-central1.run.app**

No installation required - just open the URL and start generating testbenches!

---

## 🛠️ Installation

### Local Development Setup

```bash
# 1. Clone the repository
git clone https://github.com/tusharpathaknyu/VerifAI.git
cd VerifAI

# 2. Create virtual environment
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate

# 3. Install dependencies
pip install -r requirements.txt

# 4. Run the application
streamlit run app.py

# 5. Open browser to http://localhost:8501
```

### Requirements

```
Python >= 3.11
streamlit >= 1.28.0
google-generativeai >= 0.3.0  # Optional: for LLM features
```

### Running Tests

```bash
# Run all tests
python -m pytest tests/ -v

# Run with coverage
python -m pytest tests/ --cov=src --cov-report=html
```

---

## 📖 Usage Guide

### Quick Start (3 Steps)

1. **Open the App** → Go to https://verifai-761803298484.us-central1.run.app
2. **Paste RTL Code** → Use "Load APB Example" or paste your own Verilog
3. **Click Generate** → Download your complete UVM testbench

### Input Formats Supported

| Format | Extension | Example |
|--------|-----------|---------|
| Verilog | .v | `module dut(...); endmodule` |
| SystemVerilog | .sv | `module dut(...); endmodule` |
| Verilog Header | .vh | Include files |
| SV Header | .svh | Package/class definitions |

---

## 📑 Tab-by-Tab Guide

### Tab 1: RTL to Testbench

This is the main feature - converting RTL code to UVM testbenches.

#### Input Section (Left Column)

**File Upload:**
- Drag & drop or click "Browse files"
- Supports .v, .sv, .vh, .svh (up to 200MB)

**Sample Buttons:**
- `Load APB Example` - APB slave with FSM
- `Load AXI Example` - AXI4-Lite interface

**Code Input:**
- Paste your RTL directly in the text area
- Syntax validation happens automatically
- Green ✅ = valid, Red ❌ = errors shown

**Generate Button:**
- Click to analyze RTL and generate testbench
- Progress spinner shows during generation

#### Output Section (Right Column)

**Analysis Summary:**
- Module name and detected protocol
- Input/output count
- Complexity score (Low/Medium/High)
- Estimated coverage points

**Expandable Sections:**

1. **View Analysis Details**
   - Clock signals detected
   - Reset signals (active high/low)
   - FSM states if present
   - Protocol confidence percentage

2. **🔍 Signal Explorer**
   - Categorized list of all signals
   - Inputs, Outputs, Clocks, Resets

3. **Verification Checklist**
   - Auto-generated test scenarios
   - Reset tests, Protocol tests, FSM tests, Edge cases

4. **Interactive Protocol Timing**
   - ASCII waveform diagram
   - Shows signal relationships for detected protocol

5. **🔍 Predicted Verification Issues**
   - AI-predicted bugs to check for
   - Protocol-specific gotchas

6. **Constraint Randomization Hints**
   - Suggested constraints for sequences
   - Ready-to-use SystemVerilog code

**Generated Code:**

- **View Mode Toggle:**
  - `Full Code` - Single file with all components
  - `Component Tabs` - Separate tabs for each UVM component

- **Quality Score** (0-100):
  - Completeness (40 pts)
  - Protocol awareness (20 pts)
  - Coverage (20 pts)
  - UVM Best Practices (20 pts)

- **Testbench Complexity Analysis:**
  - Classes, Tasks, Covergroups, Constraints count
  - Complexity level indicator

- **Enhancement Suggestions:**
  - Priority-ranked improvements
  - Code examples for each suggestion

**Download Options:**
- 📄 `.sv` - Single SystemVerilog file
- 📦 `ZIP` - Complete package with run scripts
- 🌐 `HTML` - Formatted documentation
- `{}` `JSON` - Metadata export

---

### Tab 2: Protocol Templates

Generate testbenches for standard protocols without RTL input.

#### Configuration (Left Column)

**Protocol Comparison Guide** (expandable):
| Protocol | Complexity | Throughput | Burst | Pipelining | Use Case |
|----------|------------|------------|-------|------------|----------|
| APB | Low | Low | No | No | Config registers |
| AXI4-Lite | Medium | Medium | No | Yes | Register access |
| UART | Low | Low | N/A | No | Debug/console |
| SPI | Low | Medium | N/A | No | Flash/sensors |
| I2C | Medium | Low | N/A | No | Multi-device |

**Protocol Selection:**
- Dropdown with: APB, AXI4-Lite, UART, SPI, I2C

**Protocol-Specific Parameters:**

*APB:*
- Address Width: 8-32 bits
- Data Width: 8/16/32 bits

*AXI4-Lite:*
- Address Width: 8-32 bits
- Data Width: 32/64 bits

*UART:*
- Baud Rate: 9600-115200
- Parity: None/Even/Odd

*SPI:*
- SPI Mode: 0/1/2/3
- Data Width: 8/16/32 bits

*I2C:*
- Speed: Standard/Fast/Fast+
- Address Mode: 7-bit/10-bit

#### Output (Right Column)

**Protocol Timing Diagram:**
- ASCII waveform showing signal relationships
- Color-coded signal names

**Generated Code:**
- Complete UVM testbench for selected protocol
- Download as .sv or ZIP

---

### Tab 3: Coverage Analysis

Analyze coverage reports and get suggestions for improvement.

#### Input (Left Column)

**Load Sample Report:**
- Click to load a realistic sample coverage report
- Shows proper format for parsing

**Text Area:**
- Paste your coverage report
- Supports VCS URG, Questa, and simple text formats

**Supported Formats:**
```
=== Functional Coverage Report ===
Overall Coverage: 72%

Covergroup: apb_cg
  Coverpoint: addr_cp - 85%
    bin low_addr: 45 hits
    bin high_addr: 0 hits [UNCOVERED]
```

#### Output (Right Column)

**Overall Coverage Metric:**
- Percentage with progress bar
- Delta from 95% goal

**Coverage Gaps Identified:**
- Coverpoints below 90%
- Shows how much improvement needed

**Recommended Actions:**
- Specific bins to target
- Prioritized suggestions

**Generated Test Sequence:**
- Ready-to-use UVM sequence code
- Targets uncovered bins

---

### Tab 4: SVA Assertions

Generate SystemVerilog Assertions from RTL or natural language.

#### Input Modes

**From RTL Code:**
- Paste Verilog/SystemVerilog
- Uses `Load APB` or `Load AXI` buttons
- Generates protocol-aware assertions

**From Description:**
- Natural language input
- Example:
  ```
  - Request must be acknowledged within 4 cycles
  - Data valid only when enable is high
  - After reset, outputs zero for 2 cycles
  ```

#### SVA Pattern Library (Expandable)

Pre-built assertion patterns:
- **Handshake** - req/ack protocol
- **Stability** - signal holds value
- **Response** - timing requirements
- **Mutex** - mutual exclusion
- **FIFO** - pointer relationships
- **Reset** - initialization behavior
- **Data Integrity** - known value checks

#### Output

**Generated Assertions:**
- Property definitions
- Assert and cover directives
- Bind module for non-invasive integration

**Download:**
- Single .sv file with all assertions

---

### Tab 5: Register Map

Generate UVM Register Abstraction Layer (RAL) from specifications.

#### Input Formats

**CSV (Simple):**
```csv
name,address,width,access,reset,description
CTRL,0x00,32,RW,0x00000000,Control register
STATUS,0x04,32,RO,0x00000001,Status register
DATA,0x08,32,RW,0x00000000,Data register
```

**JSON:**
```json
{
  "registers": [
    {"name": "CTRL", "address": "0x00", "width": 32, "access": "RW", "reset": "0x0"}
  ]
}
```

**IP-XACT / SystemRDL:**
- Partial support for standard formats

#### Output

**Register Map Table:**
- Visual display of all registers
- Name, Address, Width, Access, Reset value

**Generated UVM RAL Model:**
- `uvm_reg` class for each register
- `uvm_reg_block` container
- Reset verification sequence
- Access test sequence

---

## 📁 Generated Code Structure

When you download the ZIP package, you get:

```
module_name_uvm_tb/
├── module_name_pkg.sv      # Package with all imports
├── module_name_if.sv       # Interface definition
├── module_name_seq_item.sv # Transaction class
├── module_name_driver.sv   # Driver component
├── module_name_monitor.sv  # Monitor component
├── module_name_agent.sv    # Agent wrapper
├── module_name_scoreboard.sv # Checker/scoreboard
├── module_name_coverage.sv # Functional coverage
├── module_name_env.sv      # Environment
├── module_name_seq_lib.sv  # Sequence library
├── module_name_test.sv     # Base test
├── module_name_tb_top.sv   # Top-level testbench
├── run_vcs.sh             # VCS simulation script
├── run_questa.sh          # Questa simulation script
└── Makefile               # Build automation
```

### UVM Component Hierarchy

```
uvm_test
  └── env
       ├── agent (active)
       │    ├── sequencer
       │    ├── driver ──► interface ──► DUT
       │    └── monitor ◄── interface
       ├── scoreboard
       │    └── analysis FIFOs
       └── coverage
            └── covergroups
```

---

## 🔧 API Reference

### Core Classes

#### RTLParser
```python
from src.rtl_parser import parse_rtl, RTLParser

# Simple usage
parsed = parse_rtl(rtl_code)
print(parsed.module_name)  # "apb_slave"
print(parsed.inputs)       # ["pclk", "presetn", ...]
print(parsed.outputs)      # ["prdata", "pready", ...]

# Advanced usage
parser = RTLParser()
full_parsed = parser.parse(rtl_code)
print(full_parsed.protocol_hints)  # [ProtocolHint(protocol='apb', confidence=0.95)]
```

#### RTLAwareGenerator
```python
from src.rtl_aware_gen import RTLAwareGenerator

generator = RTLAwareGenerator()
files = generator.generate_from_rtl(rtl_code)
# Returns dict: {"module_pkg.sv": "...", "module_if.sv": "...", ...}
```

#### SVAGenerator
```python
from src.sva_generator import SVAGenerator
from src.rtl_parser import RTLParser

parser = RTLParser()
parsed = parser.parse(rtl_code)

sva_gen = SVAGenerator(parsed)
sva_module = sva_gen.generate_all()
assertions_code = sva_module.to_sv()
```

#### CoverageAnalyzer
```python
from src.coverage_analyzer import CoverageAnalyzer

analyzer = CoverageAnalyzer()
report = analyzer.analyze(coverage_text)
print(report.total_coverage)  # 72.0
print(report.gaps)            # [CoverageGap(...), ...]
```

---

## ❓ Troubleshooting

### Common Issues

**"Syntax looks invalid" warning:**
- Check for missing semicolons
- Ensure module has `endmodule`
- Verify port declarations are complete

**Protocol not detected:**
- Ensure signal names follow conventions (psel, penable for APB)
- Add more ports - needs minimum signals to detect

**Code not visible in dark mode:**
- Refresh the page
- Toggle theme twice
- Clear browser cache

**Coverage showing 0%:**
- Ensure "Overall Coverage:" or "Total:" appears in report
- Format: `Overall Coverage: 72%`

**SVA generation error:**
- Use "Load APB Example" first to test
- Ensure complete module definition
- Check clock/reset signals exist

### Performance Tips

1. **Large RTL files:** Upload via file upload instead of paste
2. **Slow generation:** Normal for complex designs (5-10 seconds)
3. **Browser lag:** Use Chrome/Firefox for best performance

### Getting Help

- **GitHub Issues:** https://github.com/tusharpathaknyu/VerifAI/issues
- **Documentation:** This file + README.md

---

## 📊 Test Coverage

The project maintains high test coverage:

```
======================== 212 passed ========================
Tests cover:
- RTL parsing (40+ tests)
- Protocol detection (30+ tests)
- UVM generation (50+ tests)
- SVA generation (30+ tests)
- Coverage analysis (30+ tests)
- App helpers (32+ tests)
```

Run tests locally:
```bash
python -m pytest tests/ -v --tb=short
```

---

## 🚀 Deployment

### Deploy to Google Cloud Run

```bash
# Authenticate
gcloud auth login

# Deploy
gcloud run deploy verifai \
  --source . \
  --region us-central1 \
  --allow-unauthenticated \
  --memory 512Mi \
  --timeout 300
```

### Docker (Local)

```bash
# Build
docker build -t verifai .

# Run
docker run -p 8080:8080 verifai
```

---

## 📝 License

MIT License - See LICENSE file for details.

---

## 🙏 Acknowledgments

- UVM 1.2 methodology guidelines
- Streamlit for the web framework
- Google Cloud Run for hosting

---

*Last updated: December 16, 2025*
