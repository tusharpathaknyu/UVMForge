# VerifAI 🚀

<div align="center">

![VerifAI Banner](https://img.shields.io/badge/VerifAI-AI%20Powered%20UVM-blueviolet?style=for-the-badge)

**🤖 Transform Natural Language → Production-Ready UVM Testbenches**

[![Python 3.9+](https://img.shields.io/badge/Python-3.9+-blue.svg?style=flat-square&logo=python)](https://python.org)
[![Tests](https://img.shields.io/badge/Tests-38%20Passing-success?style=flat-square&logo=pytest)](tests/)
[![UVM 1.2](https://img.shields.io/badge/UVM-1.2%20Compatible-orange.svg?style=flat-square)](https://www.accellera.org/downloads/standards/uvm)
[![Protocols](https://img.shields.io/badge/Protocols-5%20Supported-blue?style=flat-square)](README.md#-protocol-support)
[![License: MIT](https://img.shields.io/badge/License-MIT-green.svg?style=flat-square)](LICENSE)
[![PRs Welcome](https://img.shields.io/badge/PRs-welcome-brightgreen.svg?style=flat-square)](CONTRIBUTING.md)

[Features](#-features) • [Quick Start](#-quick-start) • [Examples](#-examples) • [Roadmap](#-roadmap) • [Contributing](#-contributing)

</div>

---

## 🎬 Demo

```
📝 Input: "Create a UVM testbench for an APB slave memory controller with 
          STATUS, CONTROL, DATA, and CONFIG registers"

🚀 VerifAI generates in ~5 seconds:
   ├── apb_pkg.sv           (Package with imports)
   ├── apb_interface.sv     (Bus interface)
   ├── apb_seq_item.sv      (Transaction class)
   ├── apb_driver.sv        (Stimulus driver)
   ├── apb_monitor.sv       (Protocol monitor)
   ├── apb_sequencer.sv     (Sequence controller)
   ├── apb_agent.sv         (UVM agent)
   ├── apb_sequence_lib.sv  (Test sequences)
   ├── apb_scoreboard.sv    (Checker)
   ├── apb_coverage.sv      (Functional coverage)
   ├── apb_env.sv           (Environment)
   ├── apb_base_test.sv     (Base test)
   └── apb_top_tb.sv        (Top testbench)
```

## 🌟 Why VerifAI?

| Traditional Approach | With VerifAI |
|---------------------|--------------|
| ⏰ Days of boilerplate coding | ⚡ **5 seconds** generation |
| 🐛 Copy-paste errors | ✅ Consistent, tested templates |
| 📚 Reference manual lookup | 🤖 AI understands your intent |
| 🔄 Repetitive protocol code | 🎯 Focus on verification strategy |

## ✨ Features

### 🤖 AI-Powered Understanding
- Natural language specification parsing
- Intelligent protocol detection
- Context-aware code generation

### 📦 Protocol Support
| Protocol | Status | Features |
|----------|--------|----------|
| **APB** | ✅ Ready | Full APB3/APB4 support |
| **AXI4-Lite** | ✅ Ready | Read/Write channels |
| **UART** | ✅ Ready | TX/RX, baud rates, parity, error injection |
| **SPI** | ✅ Ready | All 4 modes, multi-slave, QSPI support |
| **I2C** | ✅ Ready | Standard/Fast/Fast+/High Speed, 7/10-bit addressing, clock stretching |
| AXI4 Full | 🔜 Coming | Burst, ID support |

### 🔌 Multiple LLM Backends
```
┌─────────────┬────────────┬───────────────┐
│   Provider  │    Cost    │    Quality    │
├─────────────┼────────────┼───────────────┤
│ Google Gemini │   Free*   │  ⭐⭐⭐⭐     │
│ OpenAI GPT-4  │   Paid    │  ⭐⭐⭐⭐⭐   │
│ Anthropic     │   Paid    │  ⭐⭐⭐⭐⭐   │
│ Ollama Local  │   Free    │  ⭐⭐⭐       │
└─────────────┴────────────┴───────────────┘
* Free tier available
```

### 🎯 Generated Code Quality
- ✅ UVM 1.2 / IEEE 1800.2 compliant
- ✅ Follows industry best practices
- ✅ Synthesizable interface definitions
- ✅ Complete functional coverage models
- ✅ Protocol-aware scoreboards
- ✅ Ready-to-run test sequences

---

## 🚀 Quick Start

### Installation

```bash
# Clone
git clone https://github.com/tusharpathaknyu/VerifAI.git
cd VerifAI

# Install dependencies
pip install -r requirements.txt

# Set up API key (choose one)
export GOOGLE_API_KEY="your-gemini-key"    # Recommended (free tier)
# OR
export OPENAI_API_KEY="your-openai-key"
# OR use Ollama for fully local operation
```

### Basic Usage

```bash
# 🎯 Quick generate (uses Gemini by default)
python verifai.py --spec "APB slave with 4 control registers" --llm gemini

# 📁 Output to specific directory
python verifai.py --spec "AXI4-Lite memory controller" --output ./my_tb

# 🔌 Generate UART testbench
python verifai.py --spec "UART controller with 115200 baud, 8N1" --llm gemini

# 🤖 Use different LLM
python verifai.py --spec "UART transmitter" --llm openai

# 💻 Fully local with Ollama (no API key needed)
python verifai.py --spec "SPI master" --llm ollama
```

### 🌐 Web UI (New!)

```bash
# Launch the Streamlit web interface
streamlit run app.py

# Opens at http://localhost:8501
```

Features:
- 🎨 Beautiful modern interface
- 📝 Template quick-select for common protocols
- 👁️ Live preview of generated code
- ⬇️ Download as ZIP or individual files

---

## 📚 Examples

### Example 1: APB Register Block

**Specification:**
```
Create a UVM testbench for an APB slave with:
- STATUS register at 0x00 (read-only, shows busy/done flags)
- CONTROL register at 0x04 (read-write, start/stop commands)
- DATA_IN register at 0x08 (write-only, 32-bit data input)
- DATA_OUT register at 0x0C (read-only, 32-bit result)
```

**Generated Coverage (excerpt):**
```systemverilog
covergroup apb_cov;
    // Address coverage
    addr_cp: coverpoint item.addr {
        bins status  = {32'h00};
        bins control = {32'h04};
        bins data_in = {32'h08};
        bins data_out = {32'h0C};
    }
    
    // Operation coverage
    operation_cp: coverpoint item.write {
        bins read  = {0};
        bins write = {1};
    }
    
    // Cross coverage
    addr_x_op: cross addr_cp, operation_cp;
endgroup
```

### Example 2: AXI4-Lite Memory

**Specification:**
```
AXI4-Lite memory controller testbench:
- 1KB address space
- 32-bit data width
- Verify read-after-write coherency
```

**Generated Scoreboard (excerpt):**
```systemverilog
class axi4lite_scoreboard extends uvm_scoreboard;
    // Reference memory model
    bit [31:0] mem [bit[31:0]];
    
    function void write(axi4lite_seq_item item);
        if (item.write) begin
            mem[item.addr] = item.data;
            `uvm_info("SCB", $sformatf("WRITE: addr=0x%08h data=0x%08h", 
                      item.addr, item.data), UVM_MEDIUM)
        end else begin
            if (mem.exists(item.addr)) begin
                if (item.data !== mem[item.addr])
                    `uvm_error("SCB", $sformatf("MISMATCH: addr=0x%08h exp=0x%08h got=0x%08h",
                              item.addr, mem[item.addr], item.data))
            end
        end
    endfunction
endclass
```

### Example 3: UART Controller 🆕

**Specification:**
```
UART controller testbench:
- 115200 baud rate
- 8 data bits, no parity, 1 stop bit (8N1)
- Error injection support
```

**Generated Driver (excerpt):**
```systemverilog
class uart_driver extends uvm_driver #(uart_seq_item);
    int bit_period_ns = 8680;  // ~115200 baud
    
    task drive_byte(logic [7:0] data, parity_type_e parity, bit frame_err, bit parity_err);
        // Start bit (low)
        vif.tx = 1'b0;
        #(bit_period_ns * 1ns);
        
        // Data bits (LSB first)
        for (int i = 0; i < 8; i++) begin
            vif.tx = data[i];
            #(bit_period_ns * 1ns);
        end
        
        // Stop bit
        vif.tx = frame_err ? 1'b0 : 1'b1;  // Inject frame error
        #(bit_period_ns * 1ns);
    endtask
endclass
```

### Example 4: I2C Master 🆕

**Specification:**
```
I2C master controller testbench:
- Standard mode (100kHz)
- 7-bit addressing
- Clock stretching support
- EEPROM read/write operations
```

**Generated Sequence (excerpt):**
```systemverilog
class i2c_eeprom_page_seq extends uvm_sequence #(i2c_seq_item);
    `uvm_object_utils(i2c_eeprom_page_seq)
    
    logic [6:0] eeprom_addr = 7'h50;
    logic [7:0] page_addr = 0;
    int page_size = 16;
    
    virtual task body();
        i2c_seq_item write_item, read_item;
        
        // Page write
        `uvm_do_with(write_item, {
            slave_addr == eeprom_addr;
            rw == I2C_WRITE;
            data.size() == page_size + 1;  // addr + data
        })
        
        // Page read with repeated start
        `uvm_do_with(read_item, {
            slave_addr == eeprom_addr;
            rw == I2C_READ;
            num_bytes == page_size;
        })
    endtask
endclass
```

---

## 🏗️ Architecture

```
┌─────────────────────────────────────────────────────────────┐
│                     User Specification                       │
│         "APB slave with STATUS and CONTROL registers"        │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                      🤖 LLM Parser                           │
│    ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────┐   │
│    │  Gemini  │  │  GPT-4   │  │ Claude   │  │  Ollama  │   │
│    └──────────┘  └──────────┘  └──────────┘  └──────────┘   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                    Structured Config                         │
│    { protocol: "apb", registers: [...], features: [...] }    │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   📝 Jinja2 Templates                        │
│    ┌────────────────────────────────────────────────────────┐   │
│    │  templates/apb/  │  templates/axi4lite/  │  ...    │   │
│    └────────────────────────────────────────────────────────┘   │
└─────────────────────────────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                  🎯 Generated UVM Testbench                  │
│   agent • driver • monitor • scoreboard • coverage • test   │
└─────────────────────────────────────────────────────────────┘
```

---

## 📁 Project Structure

```
VerifAI/
├── 📄 verifai.py              # CLI entry point
├── 📄 requirements.txt        # Dependencies
├── 📄 README.md               # This file
├── 📄 ROADMAP.md              # Development roadmap
│
├── 📁 src/
│   ├── parser.py              # NL → Structured spec
│   ├── generator.py           # Spec → UVM code
│   ├── llm_client.py          # Multi-LLM support
│   └── 📁 protocols/
│       ├── apb.py             # APB configuration
│       └── axi4lite.py        # AXI4-Lite configuration
│
├── 📁 templates/              # Jinja2 templates
│   ├── 📁 apb/                # 13 APB templates
│   └── 📁 axi4lite/           # 13 AXI4-Lite templates
│
├── 📁 examples/
│   └── 📁 apb_slave/          # Example DUT
│
└── 📁 tests/                  # Unit tests (coming soon)
```

---

## 🗺️ Roadmap

See [ROADMAP.md](ROADMAP.md) for detailed plans.

### Coming Soon
- [ ] 🧪 Comprehensive test suite
- [ ] 🌐 Web UI with Streamlit
- [ ] 📡 More protocols (AXI4, UART, SPI)
- [ ] 🔍 Auto-DUT analysis from RTL
- [ ] 📊 Coverage closure AI suggestions

---

## 🤝 Contributing

Contributions welcome! Areas where help is needed:

1. **Protocol Templates** - Add support for more bus protocols
2. **Test Cases** - Unit tests and integration tests
3. **Documentation** - Examples and tutorials
4. **LLM Prompts** - Improve parsing accuracy

```bash
# Fork & clone
git clone https://github.com/YOUR_USERNAME/VerifAI.git

# Create branch
git checkout -b feature/amazing-feature

# Make changes & test
python verifai.py --spec "test spec" --llm mock

# Submit PR
```

---

## 📜 License

MIT License - see [LICENSE](LICENSE) for details.

---

## 🙏 Acknowledgments

- UVM methodology by Accellera
- Inspired by the verification community
- Built with ❤️ for DV engineers

---

<div align="center">

**⭐ Star this repo if VerifAI saves you time!**

Made with 🤖 + ☕ by [Tushar Pathak](https://github.com/tusharpathaknyu)

</div>
