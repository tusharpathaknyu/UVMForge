# RTL-Aware Example: APB GPIO Controller

This example demonstrates VerifAI's **RTL-Aware** generation capability.

## Files

| File | Description |
|------|-------------|
| `apb_gpio.sv` | Sample APB GPIO controller RTL |
| `apb_gpio_regs.csv` | Register specification in CSV format |
| `apb_gpio_regs.json` | Register specification in JSON format |

## What Makes This Different?

### Traditional (ChatGPT) Approach:
```
User: "Write me a UVM testbench for APB"
ChatGPT: *generates generic APB testbench with guessed ports*
```

### VerifAI RTL-Aware Approach:
```
User: *uploads apb_gpio.sv*
VerifAI: 
  ✓ Parses exact ports: pclk, preset_n, psel, penable, pwrite...
  ✓ Detects clock (pclk) and reset (preset_n, active-low)
  ✓ Detects APB protocol (95% confidence)
  ✓ Finds FSM: IDLE, SETUP, ACCESS states
  ✓ Extracts parameters: DATA_WIDTH=32, NUM_GPIOS=16
  → Generates testbench with EXACT port matching!
```

## How to Use

### Option 1: Web UI
1. Go to https://verifai-761803298484.us-central1.run.app
2. Click "RTL-Aware Mode" tab
3. Upload `apb_gpio.sv`
4. Optionally upload `apb_gpio_regs.csv` for register tests
5. Click Generate!

### Option 2: Python API
```python
from src.rtl_aware_gen import RTLAwareGenerator

# Read RTL
with open('examples/rtl_aware/apb_gpio.sv') as f:
    rtl_content = f.read()

# Read register spec (optional)
with open('examples/rtl_aware/apb_gpio_regs.csv') as f:
    reg_spec = f.read()

# Generate
generator = RTLAwareGenerator(output_dir='./output')
files = generator.generate_from_rtl(rtl_content, reg_spec, 'apb_gpio_regs.csv')

# Save
generator.save_files(files)
```

### Option 3: CLI
```bash
python -m src.rtl_aware_gen \
    --rtl examples/rtl_aware/apb_gpio.sv \
    --spec examples/rtl_aware/apb_gpio_regs.csv \
    --output ./output
```

## Generated Files

The RTL-aware generator creates:

1. **`apb_gpio_pkg.sv`** - Package with extracted parameters
2. **`apb_gpio_if.sv`** - Interface with EXACT port matching
3. **`apb_gpio_seq_item.sv`** - Transaction with correct widths
4. **`apb_gpio_driver.sv`** - Protocol-aware driver (APB detected!)
5. **`apb_gpio_monitor.sv`** - Protocol monitor
6. **`apb_gpio_agent.sv`** - UVM agent
7. **`apb_gpio_sequencer.sv`** - Sequencer
8. **`apb_gpio_scoreboard.sv`** - Checker
9. **`apb_gpio_coverage.sv`** - Coverage with register bins
10. **`apb_gpio_seq_lib.sv`** - Test sequences
11. **`apb_gpio_reg_seq.sv`** - Register-specific sequences (from CSV)
12. **`apb_gpio_env.sv`** - Environment
13. **`apb_gpio_base_test.sv`** - Base test
14. **`top_tb.sv`** - Top testbench with exact DUT instantiation

## Key Advantages

| Feature | ChatGPT | VerifAI RTL-Aware |
|---------|---------|-------------------|
| Port names | Guessed | Exact from RTL |
| Port widths | Generic | Exact from RTL |
| Clock name | "clk" | Detected (pclk) |
| Reset polarity | Guessed | Detected (active-low) |
| Protocol | Manual | Auto-detected |
| Parameters | None | Extracted |
| FSM states | None | Detected |
| Register tests | None | From spec file |

## Register Specification Formats

VerifAI supports multiple industry-standard formats:

### CSV (Simple)
```csv
Register Name,Address,Field Name,Bit Range,Access,Reset Value,Description
STATUS,0x00,BUSY,0,RO,0,Busy flag
```

### JSON (Flexible)
```json
{
    "registers": [
        {"name": "STATUS", "address": "0x00", "fields": [...]}
    ]
}
```

### IP-XACT (Industry Standard)
IEEE 1685 XML format - supports imports from Synopsys, Cadence, etc.

### SystemRDL (Semiconductor)
Popular in ASIC design companies.

---

**This is what makes VerifAI valuable - not just AI generation, but RTL-aware, spec-driven verification!**
