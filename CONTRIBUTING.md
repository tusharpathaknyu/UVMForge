# Contributing to UVMForge 🤝

Thank you for your interest in contributing to UVMForge! This document provides guidelines and instructions for contributing.

## 📋 Table of Contents

- [Code of Conduct](#code-of-conduct)
- [Getting Started](#getting-started)
- [Development Setup](#development-setup)
- [How to Contribute](#how-to-contribute)
- [Pull Request Process](#pull-request-process)
- [Adding New Protocols](#adding-new-protocols)
- [Code Style](#code-style)
- [Testing](#testing)

---

## Code of Conduct

We are committed to providing a welcoming and inspiring community for all. Please be respectful and considerate in all interactions.

---

## Getting Started

### Prerequisites

- Python 3.9+
- Git
- Basic understanding of UVM (Universal Verification Methodology)
- Familiarity with Jinja2 templating

### Fork and Clone

```bash
# Fork the repository on GitHub, then:
git clone https://github.com/YOUR_USERNAME/UVMForge.git
cd UVMForge
git remote add upstream https://github.com/tusharpathaknyu/UVMForge.git
```

---

## Development Setup

### 1. Create Virtual Environment

```bash
python -m venv venv
source venv/bin/activate  # On Windows: venv\Scripts\activate
```

### 2. Install Dependencies

```bash
pip install -r requirements.txt
pip install pytest pytest-cov black isort flake8
```

### 3. Verify Setup

```bash
# Run tests
pytest tests/ -v

# Run the CLI
python uvmforge.py --help

# Start the web UI
streamlit run app.py
```

---

## How to Contribute

### 🐛 Bug Reports

1. Check existing issues to avoid duplicates
2. Use the bug report template
3. Include:
   - Python version
   - Operating system
   - Steps to reproduce
   - Expected vs actual behavior
   - Error messages/stack traces

### ✨ Feature Requests

1. Check existing issues/roadmap
2. Describe the use case
3. Provide examples if possible

### 🔧 Code Contributions

1. **Small fixes**: Direct PR is fine
2. **Large changes**: Open an issue first to discuss
3. **New protocols**: Follow the [Adding New Protocols](#adding-new-protocols) guide

---

## Pull Request Process

### 1. Create a Branch

```bash
git checkout -b feature/your-feature-name
# or
git checkout -b fix/your-bug-fix
```

### 2. Make Your Changes

- Follow the [Code Style](#code-style) guidelines
- Add/update tests as needed
- Update documentation if necessary

### 3. Run Tests

```bash
# Run all tests
pytest tests/ -v

# Run with coverage
pytest tests/ --cov=src --cov-report=html
```

### 4. Commit Your Changes

```bash
git add .
git commit -m "feat: add support for XYZ protocol"
# or
git commit -m "fix: resolve issue with ABC"
```

Follow [Conventional Commits](https://www.conventionalcommits.org/):
- `feat:` - New feature
- `fix:` - Bug fix
- `docs:` - Documentation
- `test:` - Adding tests
- `refactor:` - Code refactoring

### 5. Push and Create PR

```bash
git push origin feature/your-feature-name
```

Then create a Pull Request on GitHub.

---

## Adding New Protocols

Adding a new protocol (e.g., Wishbone, AHB) involves these steps:

### 1. Create Protocol Configuration

Create `src/protocols/your_protocol.py`:

```python
from dataclasses import dataclass

@dataclass
class YourProtocolConfig:
    """Configuration for Your Protocol"""
    some_param: int = 32
    another_param: bool = True
```

### 2. Create Templates

Create `templates/your_protocol/` directory with these 13 files:

```
templates/your_protocol/
├── your_protocol_pkg.sv.j2          # Package with types/params
├── your_protocol_interface.sv.j2    # Bus interface
├── your_protocol_seq_item.sv.j2     # Transaction class
├── your_protocol_driver.sv.j2       # Stimulus driver
├── your_protocol_monitor.sv.j2      # Protocol monitor
├── your_protocol_sequencer.sv.j2    # Sequencer
├── your_protocol_agent.sv.j2        # Agent wrapper
├── your_protocol_sequence_lib.sv.j2 # Test sequences
├── your_protocol_scoreboard.sv.j2   # Checker
├── your_protocol_coverage.sv.j2     # Functional coverage
├── your_protocol_env.sv.j2          # Environment
├── your_protocol_base_test.sv.j2    # Base test
└── your_protocol_top_tb.sv.j2       # Top testbench
```

### 3. Update Parser

In `src/parser.py`:

1. Add protocol-specific fields to `ParsedSpec` dataclass
2. Update `SYSTEM_PROMPT` to include your protocol
3. Add detection in `parse_quick()` method

### 4. Update Generator

In `src/generator.py`:

1. Add protocol context variables in `_build_context()`
2. Add template mappings in `_get_protocol_templates()`

### 5. Update LLM Client

In `src/llm_client.py`:

1. Add detection pattern in `MockLLMClient.generate()`

### 6. Add Tests

In `tests/test_uvmforge.py`:

```python
class TestYourProtocol:
    def test_protocol_detection(self):
        parser = SpecParser(llm_client=None)
        result = parser.quick_parse("Your Protocol testbench")
        assert result.get('protocol') == 'your_protocol'
    
    def test_generation(self, temp_output_dir):
        # Test file generation
        pass
```

### 7. Update Documentation

- Update README.md protocol support table
- Update ROADMAP.md
- Add example in `examples/`

---

## Code Style

### Python

- Follow PEP 8
- Use type hints where possible
- Maximum line length: 120 characters

```bash
# Format code
black src/ tests/ uvmforge.py --line-length 120

# Sort imports
isort src/ tests/ uvmforge.py

# Lint
flake8 src/ tests/ uvmforge.py --max-line-length=120
```

### SystemVerilog Templates

- Use consistent indentation (3 spaces)
- Follow UVM naming conventions
- Include descriptive comments
- Use `{{ variable }}` for Jinja2 placeholders

---

## Testing

### Run All Tests

```bash
pytest tests/ -v
```

### Run Specific Tests

```bash
# Run a specific test class
pytest tests/test_uvmforge.py::TestI2CProtocol -v

# Run a specific test
pytest tests/test_uvmforge.py::TestI2CProtocol::test_i2c_generation -v
```

### Test Coverage

```bash
pytest tests/ --cov=src --cov-report=html
open htmlcov/index.html
```

### Test Categories

| Category | Description |
|----------|-------------|
| `TestSpecParser` | Natural language parsing |
| `TestUVMGenerator` | Template rendering |
| `TestProtocolDetection` | Protocol identification |
| `TestRegisterParsing` | Register extraction |
| `TestIntegration` | End-to-end pipeline |
| `Test<Protocol>Protocol` | Protocol-specific tests |

---

## Project Structure

```
UVMForge/
├── src/
│   ├── parser.py          # NL specification parser
│   ├── generator.py       # UVM code generator
│   ├── llm_client.py      # Multi-LLM support
│   └── protocols/         # Protocol configurations
├── templates/
│   ├── apb/               # APB templates (13 files)
│   ├── axi4lite/          # AXI4-Lite templates
│   ├── uart/              # UART templates
│   ├── spi/               # SPI templates
│   └── i2c/               # I2C templates
├── tests/
│   └── test_uvmforge.py    # Test suite
├── examples/              # Generated examples
├── app.py                 # Streamlit web UI
└── uvmforge.py             # CLI entry point
```

---

## Questions?

- Open an issue on GitHub
- Check existing documentation
- Review closed issues for solutions

Thank you for contributing! 🎉
