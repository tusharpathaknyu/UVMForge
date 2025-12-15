# VerifAI 🚀

**AI-Powered UVM Testbench Generator**

> Transform natural language specifications into production-ready UVM verification environments in seconds.

![License](https://img.shields.io/badge/license-MIT-blue.svg)
![Python](https://img.shields.io/badge/python-3.9+-green.svg)
![UVM](https://img.shields.io/badge/UVM-1.2-orange.svg)

## 🎯 What is VerifAI?

VerifAI is an AI-powered tool that generates complete UVM (Universal Verification Methodology) testbench environments from natural language descriptions. Stop writing boilerplate code—describe what you want, and let AI do the heavy lifting.

### Example

**Input:**
```
Create a UVM testbench for an APB slave with 4 registers:
- STATUS register at 0x00 (read-only)
- CONTROL register at 0x04 (read-write)  
- DATA register at 0x08 (read-write)
- CONFIG register at 0x0C (read-write)
```

**Output:** Complete UVM environment with:
- ✅ APB Agent (driver, monitor, sequencer)
- ✅ Scoreboard with protocol checking
- ✅ Functional coverage model
- ✅ Sequence library
- ✅ Register model (UVM RAL)
- ✅ Top-level testbench

## ✨ Features

- 🤖 **AI-Powered Generation** - Uses LLM to understand specs
- 📦 **Protocol Support** - APB, AXI4-Lite (more coming)
- 🎯 **Best Practices** - Generated code follows UVM methodology
- ⚡ **Instant Results** - Seconds, not days
- 🔧 **Customizable** - Template-based architecture
- 🆓 **Free Option** - Works with local LLMs (Ollama)

## 🚀 Quick Start

### Installation

```bash
# Clone the repository
git clone https://github.com/yourusername/VerifAI.git
cd VerifAI

# Install dependencies
pip install -r requirements.txt

# (Optional) Set up OpenAI API key for GPT
export OPENAI_API_KEY="your-key-here"
```

### Usage

```bash
# Interactive mode
python verifai.py

# CLI mode
python verifai.py --spec "APB slave with 4 registers" --protocol apb --output ./output

# From specification file
python verifai.py --spec-file my_spec.txt --protocol axi4lite
```

## 📁 Project Structure

```
VerifAI/
├── verifai.py              # Main entry point
├── requirements.txt        # Python dependencies
├── README.md
│
├── src/
│   ├── __init__.py
│   ├── parser.py           # Natural language parser
│   ├── generator.py        # Code generator engine
│   ├── llm_client.py       # LLM API client
│   └── protocols/          # Protocol definitions
│       ├── __init__.py
│       ├── apb.py
│       └── axi4lite.py
│
├── templates/              # UVM code templates (Jinja2)
│   ├── common/
│   │   ├── interface.sv.j2
│   │   ├── package.sv.j2
│   │   └── top_tb.sv.j2
│   ├── apb/
│   │   ├── apb_agent.sv.j2
│   │   ├── apb_driver.sv.j2
│   │   ├── apb_monitor.sv.j2
│   │   ├── apb_sequencer.sv.j2
│   │   ├── apb_seq_item.sv.j2
│   │   ├── apb_sequence_lib.sv.j2
│   │   ├── apb_scoreboard.sv.j2
│   │   ├── apb_coverage.sv.j2
│   │   ├── apb_env.sv.j2
│   │   └── apb_interface.sv.j2
│   └── axi4lite/
│       └── ... (similar structure)
│
├── examples/               # Example DUTs and generated outputs
│   ├── apb_register_block/
│   └── axi4lite_gpio/
│
└── tests/                  # Unit tests
    └── test_generator.py
```

## 🔧 Supported Protocols

| Protocol | Status | Features |
|----------|--------|----------|
| APB | ✅ Ready | Full agent, coverage, scoreboard |
| AXI4-Lite | ✅ Ready | Read/write channels, response checking |
| AXI4 | 🚧 Planned | Full AXI4 with bursts |
| AHB | 🚧 Planned | AHB-Lite support |

## 🤖 LLM Options

VerifAI supports multiple LLM backends:

| Provider | Cost | Setup |
|----------|------|-------|
| **Ollama (Local)** | Free | `ollama pull llama3.2` |
| **OpenAI GPT-4o-mini** | ~$0.01/generation | Set `OPENAI_API_KEY` |
| **Anthropic Claude** | ~$0.01/generation | Set `ANTHROPIC_API_KEY` |

## 📊 Demo

```
$ python verifai.py

╔═══════════════════════════════════════════════════════════╗
║                    🚀 VerifAI v1.0                        ║
║          AI-Powered UVM Testbench Generator               ║
╚═══════════════════════════════════════════════════════════╝

Enter your specification (or 'help' for examples):
> Create APB testbench for a register block with STATUS (0x00, RO), 
  CONTROL (0x04, RW), DATA (0x08, RW), CONFIG (0x0C, RW)

🔄 Parsing specification...
🤖 Generating UVM components...
📁 Writing files...

✅ Generated 12 files in ./output/apb_register_block/

Files created:
  ├── apb_pkg.sv
  ├── apb_interface.sv
  ├── apb_seq_item.sv
  ├── apb_driver.sv
  ├── apb_monitor.sv
  ├── apb_sequencer.sv
  ├── apb_agent.sv
  ├── apb_scoreboard.sv
  ├── apb_coverage.sv
  ├── apb_env.sv
  ├── apb_base_test.sv
  └── top_tb.sv

Run simulation: cd output/apb_register_block && make sim
```

## 🎓 Learning Resources

- [UVM Cookbook](https://verificationacademy.com/cookbook/uvm)
- [AMBA APB Protocol Spec](https://developer.arm.com/documentation/ihi0024/latest)
- [AMBA AXI4-Lite Protocol Spec](https://developer.arm.com/documentation/ihi0022/latest)

## 🤝 Contributing

Contributions are welcome! Please read our [Contributing Guide](CONTRIBUTING.md) first.

## 📄 License

MIT License - see [LICENSE](LICENSE) for details.

## 🙏 Acknowledgments

- UVM-1.2 Class Reference
- ARM AMBA Protocol Specifications
- The verification community

---

**Built with ❤️ for the verification community**

*Star ⭐ this repo if you find it useful!*
