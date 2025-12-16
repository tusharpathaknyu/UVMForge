"""
VerifAI Web UI
==============
Streamlit-based web interface for VerifAI UVM testbench generator.

Features:
- Natural Language → UVM Testbench
- RTL Upload → Exact Port-Matched Testbench (NEW!)
- IP-XACT/SystemRDL/CSV Import → Register Tests (NEW!)
"""

import streamlit as st
import os
import sys
import tempfile
import zipfile
import io
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent / 'src'))

from src.parser import SpecParser, ParsedSpec
from src.generator import UVMGenerator
from src.llm_client import get_llm_client, MockLLMClient
from src.rtl_parser import RTLParser, analyze_rtl
from src.spec_import import UnifiedSpecParser, spec_to_dict
from src.rtl_aware_gen import RTLAwareGenerator

# Page configuration
st.set_page_config(
    page_title="VerifAI - AI UVM Generator",
    page_icon="🚀",
    layout="wide",
    initial_sidebar_state="expanded"
)

# Custom CSS
st.markdown("""
<style>
    .main-header {
        font-size: 3rem;
        font-weight: bold;
        background: linear-gradient(90deg, #667eea 0%, #764ba2 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        text-align: center;
        padding: 1rem 0;
    }
    .sub-header {
        text-align: center;
        color: #666;
        font-size: 1.2rem;
        margin-bottom: 2rem;
    }
    .stTextArea textarea {
        font-family: 'Monaco', 'Menlo', monospace;
    }
    .file-card {
        background: #f8f9fa;
        border-radius: 8px;
        padding: 1rem;
        margin: 0.5rem 0;
        border-left: 4px solid #667eea;
    }
    .success-box {
        background: #d4edda;
        border: 1px solid #c3e6cb;
        border-radius: 8px;
        padding: 1rem;
        color: #155724;
    }
    .protocol-badge {
        display: inline-block;
        padding: 0.25rem 0.75rem;
        border-radius: 20px;
        font-weight: bold;
        margin: 0.25rem;
    }
    .protocol-apb { background: #e3f2fd; color: #1565c0; }
    .protocol-axi { background: #f3e5f5; color: #7b1fa2; }
    .protocol-uart { background: #fff3e0; color: #ef6c00; }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown('<h1 class="main-header">🚀 VerifAI</h1>', unsafe_allow_html=True)
st.markdown('<p class="sub-header">AI-Powered UVM Testbench Generator | RTL-Aware | Spec Import</p>', unsafe_allow_html=True)

# Main tabs for different modes
main_tab1, main_tab2, main_tab3 = st.tabs([
    "📝 Natural Language Mode", 
    "🔌 RTL-Aware Mode (NEW!)", 
    "📋 Spec Import Mode (NEW!)"
])

# Sidebar
with st.sidebar:
    st.header("⚙️ Configuration")
    
    # LLM Selection
    llm_choice = st.selectbox(
        "🤖 LLM Provider",
        ["gemini", "openai", "anthropic", "ollama", "mock"],
        index=0,
        help="Select the AI model to parse your specification"
    )
    
    # API Key input (if needed)
    if llm_choice == "gemini":
        api_key = st.text_input(
            "Google API Key",
            type="password",
            value=os.getenv("GOOGLE_API_KEY", ""),
            help="Get your free API key from Google AI Studio"
        )
        if api_key:
            os.environ["GOOGLE_API_KEY"] = api_key
    elif llm_choice == "openai":
        api_key = st.text_input(
            "OpenAI API Key",
            type="password",
            value=os.getenv("OPENAI_API_KEY", ""),
        )
        if api_key:
            os.environ["OPENAI_API_KEY"] = api_key
    
    st.divider()
    
    # Protocol quick select
    st.header("📦 Protocol Templates")
    
    protocol_templates = {
        "APB Register Block": "Create a UVM testbench for an APB slave with STATUS register at 0x00 (read-only), CONTROL register at 0x04 (read-write), DATA register at 0x08 (read-write), and CONFIG register at 0x0C (read-write)",
        "AXI4-Lite Memory": "AXI4-Lite memory controller testbench with 1KB address space, 32-bit data width, and read-after-write verification",
        "UART 8N1": "UART controller testbench with 115200 baud rate, 8 data bits, no parity, 1 stop bit, with error injection support",
        "UART with Flow Control": "UART testbench with 9600 baud, even parity, RTS/CTS hardware flow control, 16-byte FIFO",
        "SPI Master Mode 0": "SPI master controller testbench in Mode 0 (CPOL=0, CPHA=0), 8-bit data width, single slave, MSB first",
        "SPI Multi-Slave": "SPI master with 4 slave devices, Mode 3, 16-bit transfers, with QSPI support",
        "I2C Master Standard": "I2C master controller testbench in standard mode (100kHz), 7-bit addressing, with clock stretching support",
        "I2C Fast Mode": "I2C master testbench in fast mode (400kHz), 7-bit addressing, multi-byte transfers to EEPROM at address 0x50",
    }
    
    selected_template = st.selectbox(
        "Quick Templates",
        ["Custom..."] + list(protocol_templates.keys())
    )
    
    st.divider()
    
    # Info
    st.header("ℹ️ About")
    st.markdown("""
    **VerifAI** transforms natural language 
    specifications into production-ready 
    UVM testbenches.
    
    **Supported Protocols:**
    - ✅ APB (APB3/APB4)
    - ✅ AXI4-Lite
    - ✅ UART
    - ✅ SPI
    - ✅ I2C (NEW!)
    
    [GitHub](https://github.com/tusharpathaknyu/VerifAI) | 
    [Documentation](#)
    """)

# =============================================================================
# TAB 1: Natural Language Mode (Original)
# =============================================================================
with main_tab1:
    # Main content
    col1, col2 = st.columns([1, 1])

with col1:
    st.header("📝 Specification")
    
    # Pre-fill with template if selected
    default_spec = ""
    if selected_template != "Custom...":
        default_spec = protocol_templates.get(selected_template, "")
    
    user_spec = st.text_area(
        "Describe your testbench in natural language:",
        value=default_spec,
        height=200,
        placeholder="Example: Create a UVM testbench for an APB slave with STATUS and CONTROL registers..."
    )
    
    # Generate button
    generate_btn = st.button("🚀 Generate UVM Testbench", type="primary", use_container_width=True)

with col2:
    st.header("📊 Parsed Specification")
    spec_placeholder = st.empty()

# Results section
if generate_btn and user_spec:
    with st.spinner("🤖 Parsing specification with AI..."):
        try:
            # Get LLM client
            if llm_choice == "mock":
                llm_client = MockLLMClient()
            else:
                llm_client = get_llm_client(llm_choice)
            
            # Parse specification
            parser = SpecParser(llm_client=llm_client)
            parsed_spec = parser.parse(user_spec)
            
            # Display parsed spec
            with spec_placeholder.container():
                col_a, col_b = st.columns(2)
                with col_a:
                    st.metric("Protocol", parsed_spec.protocol.upper())
                    st.metric("Data Width", f"{parsed_spec.data_width} bits")
                with col_b:
                    st.metric("Module", parsed_spec.module_name)
                    st.metric("Registers", len(parsed_spec.registers))
                
                if parsed_spec.registers:
                    st.subheader("📋 Registers")
                    reg_data = []
                    for reg in parsed_spec.registers:
                        reg_data.append({
                            "Name": reg.name,
                            "Address": f"0x{reg.address:02X}",
                            "Access": reg.access.value
                        })
                    st.table(reg_data)
            
        except Exception as e:
            st.error(f"❌ Error parsing specification: {str(e)}")
            st.stop()
    
    with st.spinner("⚙️ Generating UVM files..."):
        try:
            # Generate files
            template_dir = Path(__file__).parent / "templates"
            generator = UVMGenerator(str(template_dir))
            
            # Use temp directory
            with tempfile.TemporaryDirectory() as temp_dir:
                generated_files = generator.generate(parsed_spec, temp_dir)
                
                st.success(f"✅ Generated {len(generated_files)} files!")
                
                # Create tabs for different views
                tab1, tab2, tab3 = st.tabs(["📁 Files", "👁️ Preview", "⬇️ Download"])
                
                with tab1:
                    # Display generated files
                    cols = st.columns(3)
                    for i, gf in enumerate(generated_files):
                        with cols[i % 3]:
                            icon = "📦" if "pkg" in gf.filename else \
                                   "🔌" if "if" in gf.filename else \
                                   "🤖" if any(x in gf.filename for x in ["driver", "monitor", "agent"]) else \
                                   "📊" if any(x in gf.filename for x in ["scoreboard", "coverage"]) else \
                                   "🧪" if "test" in gf.filename else "📄"
                            st.markdown(f"""
                            <div class="file-card">
                                {icon} <strong>{gf.filename}</strong><br>
                                <small>{gf.category}</small>
                            </div>
                            """, unsafe_allow_html=True)
                
                with tab2:
                    # File preview
                    file_to_preview = st.selectbox(
                        "Select file to preview:",
                        [gf.filename for gf in generated_files]
                    )
                    
                    for gf in generated_files:
                        if gf.filename == file_to_preview:
                            st.code(gf.content, language="systemverilog")
                            break
                
                with tab3:
                    # Create ZIP for download
                    zip_buffer = io.BytesIO()
                    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
                        for gf in generated_files:
                            zf.writestr(gf.filename, gf.content)
                    
                    zip_buffer.seek(0)
                    
                    st.download_button(
                        label="📥 Download All Files (ZIP)",
                        data=zip_buffer,
                        file_name=f"{parsed_spec.module_name}_uvm_tb.zip",
                        mime="application/zip",
                        use_container_width=True
                    )
                    
                    st.markdown("---")
                    st.markdown("**Individual Files:**")
                    
                    for gf in generated_files:
                        st.download_button(
                            label=f"📄 {gf.filename}",
                            data=gf.content,
                            file_name=gf.filename,
                            mime="text/plain",
                            key=f"dl_{gf.filename}"
                        )
                
        except Exception as e:
            st.error(f"❌ Error generating files: {str(e)}")
            import traceback
            st.code(traceback.format_exc())

# =============================================================================
# TAB 2: RTL-Aware Mode (NEW!)
# =============================================================================
with main_tab2:
    st.markdown("""
    ### 🔌 RTL-Aware Testbench Generation
    
    **What makes this different from ChatGPT?**
    - ✅ **Exact port matching** - No typos, correct widths
    - ✅ **Auto-detects clock/reset** - Correct polarity
    - ✅ **Protocol detection** - Recognizes APB, AXI, SPI, I2C, UART
    - ✅ **FSM-aware** - Detects state machines in your design
    
    Upload your Verilog/SystemVerilog file and get a testbench that **exactly matches your DUT**.
    """)
    
    rtl_col1, rtl_col2 = st.columns([1, 1])
    
    with rtl_col1:
        st.subheader("📤 Upload RTL")
        
        rtl_upload = st.file_uploader(
            "Upload Verilog/SystemVerilog file",
            type=['v', 'sv', 'vh', 'svh'],
            help="Upload your DUT source file"
        )
        
        st.markdown("**Or paste RTL code:**")
        rtl_code = st.text_area(
            "RTL Code",
            height=300,
            placeholder="""module my_apb_slave #(
    parameter DATA_WIDTH = 32
) (
    input  logic        pclk,
    input  logic        preset_n,
    input  logic        psel,
    input  logic        penable,
    ...
);""",
            label_visibility="collapsed"
        )
        
        # Optional register spec
        st.subheader("📋 Optional: Register Spec")
        reg_spec_upload = st.file_uploader(
            "Upload register spec (IP-XACT, SystemRDL, CSV, JSON)",
            type=['xml', 'rdl', 'csv', 'json'],
            help="Optional: Import register definitions for register-specific tests"
        )
        
        generate_rtl_btn = st.button("🚀 Generate RTL-Aware Testbench", key="rtl_gen", use_container_width=True)
    
    with rtl_col2:
        st.subheader("📊 RTL Analysis")
        rtl_analysis_placeholder = st.empty()
    
    # Process RTL
    if generate_rtl_btn:
        rtl_content = ""
        if rtl_upload:
            rtl_content = rtl_upload.read().decode('utf-8')
        elif rtl_code:
            rtl_content = rtl_code
        
        if rtl_content:
            with st.spinner("🔍 Analyzing RTL..."):
                try:
                    # Analyze RTL
                    analysis = analyze_rtl(rtl_content)
                    
                    # Display analysis
                    with rtl_analysis_placeholder.container():
                        st.success(f"✅ Parsed module: **{analysis['module_name']}**")
                        
                        acol1, acol2, acol3 = st.columns(3)
                        with acol1:
                            st.metric("Input Ports", len(analysis['ports']['inputs']))
                        with acol2:
                            st.metric("Output Ports", len(analysis['ports']['outputs']))
                        with acol3:
                            st.metric("Parameters", len(analysis['parameters']))
                        
                        # Protocol hints
                        if analysis['protocol_hints']:
                            st.subheader("🎯 Detected Protocol")
                            for hint in analysis['protocol_hints'][:3]:
                                confidence_pct = int(hint['confidence'] * 100)
                                st.progress(confidence_pct / 100, text=f"{hint['protocol'].upper()}: {confidence_pct}% - {hint['reason']}")
                        
                        # Clock/Reset
                        st.subheader("⏰ Clock & Reset")
                        st.write(f"**Clocks:** {', '.join(analysis['clocks']) or 'None detected'}")
                        st.write(f"**Resets:** {', '.join(analysis['resets']['signals']) or 'None detected'}")
                        
                        # FSM
                        if analysis['fsm']['detected']:
                            st.subheader("🔄 FSM Detected")
                            st.write(f"**States:** {', '.join(analysis['fsm']['states'])}")
                        
                        # Ports table
                        st.subheader("📍 Ports")
                        port_data = []
                        for port in analysis['ports']['inputs'][:10]:
                            port_data.append({"Direction": "input", "Name": port['name'], "Width": port['width']})
                        for port in analysis['ports']['outputs'][:10]:
                            port_data.append({"Direction": "output", "Name": port['name'], "Width": port['width']})
                        st.dataframe(port_data, use_container_width=True)
                    
                    # Generate testbench
                    with st.spinner("⚙️ Generating RTL-aware testbench..."):
                        generator = RTLAwareGenerator()
                        
                        # Optional register spec
                        reg_spec_content = None
                        reg_spec_filename = None
                        if reg_spec_upload:
                            reg_spec_content = reg_spec_upload.read().decode('utf-8')
                            reg_spec_filename = reg_spec_upload.name
                        
                        files = generator.generate_from_rtl(rtl_content, reg_spec_content, reg_spec_filename)
                        
                        st.success(f"✅ Generated {len(files)} RTL-aware files!")
                        
                        # Preview and download
                        rtl_tab1, rtl_tab2 = st.tabs(["👁️ Preview", "⬇️ Download"])
                        
                        with rtl_tab1:
                            file_to_preview = st.selectbox(
                                "Select file:",
                                list(files.keys()),
                                key="rtl_preview"
                            )
                            st.code(files[file_to_preview], language="systemverilog")
                        
                        with rtl_tab2:
                            zip_buffer = io.BytesIO()
                            with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
                                for fname, content in files.items():
                                    zf.writestr(fname, content)
                            zip_buffer.seek(0)
                            
                            st.download_button(
                                label="📥 Download All Files (ZIP)",
                                data=zip_buffer,
                                file_name=f"{analysis['module_name']}_rtl_aware_tb.zip",
                                mime="application/zip",
                                use_container_width=True,
                                key="rtl_download"
                            )
                    
                except Exception as e:
                    st.error(f"❌ Error: {str(e)}")
                    import traceback
                    st.code(traceback.format_exc())
        else:
            st.warning("Please upload or paste RTL code")

# =============================================================================
# TAB 3: Spec Import Mode (NEW!)
# =============================================================================
with main_tab3:
    st.markdown("""
    ### 📋 Specification Import
    
    **Import industry-standard register specifications:**
    - 🔷 **IP-XACT** (IEEE 1685) - Industry standard
    - 🔷 **SystemRDL** - Popular in semiconductor companies
    - 🔷 **CSV** - Simple spreadsheet format
    - 🔷 **JSON** - Flexible custom format
    
    VerifAI generates:
    - Register access sequences for each register
    - Field-level coverage
    - Reset value verification
    - Access type checking (RO, RW, W1C, etc.)
    """)
    
    spec_col1, spec_col2 = st.columns([1, 1])
    
    with spec_col1:
        st.subheader("📤 Upload Specification")
        
        spec_format = st.selectbox(
            "Specification Format",
            ["Auto-Detect", "IP-XACT (XML)", "SystemRDL", "CSV", "JSON"]
        )
        
        spec_upload = st.file_uploader(
            "Upload specification file",
            type=['xml', 'rdl', 'csv', 'json'],
            help="Upload your register specification"
        )
        
        st.markdown("**Or use sample CSV:**")
        sample_csv = """Register Name,Address,Field Name,Bit Range,Access,Reset Value,Description
STATUS,0x00,BUSY,0,RO,0,Device busy flag
STATUS,0x00,ERROR,1,RO,0,Error flag  
STATUS,0x00,DONE,2,RO,0,Operation complete
CONTROL,0x04,START,0,RW,0,Start operation
CONTROL,0x04,RESET,1,W1C,0,Reset device
CONTROL,0x04,MODE,7:4,RW,0,Operation mode
DATA,0x08,VALUE,31:0,RW,0,Data register
CONFIG,0x0C,ENABLE,0,RW,0,Enable device
CONFIG,0x0C,INT_EN,1,RW,0,Interrupt enable"""
        
        if st.button("📋 Use Sample CSV"):
            st.session_state['sample_spec'] = sample_csv
        
        spec_content = st.text_area(
            "Or paste specification:",
            value=st.session_state.get('sample_spec', ''),
            height=200,
            placeholder="Paste IP-XACT XML, SystemRDL, CSV, or JSON here..."
        )
        
        parse_spec_btn = st.button("📊 Parse Specification", key="parse_spec", use_container_width=True)
    
    with spec_col2:
        st.subheader("📊 Parsed Registers")
        spec_analysis_placeholder = st.empty()
    
    # Process specification
    if parse_spec_btn:
        content = ""
        filename = ""
        
        if spec_upload:
            content = spec_upload.read().decode('utf-8')
            filename = spec_upload.name
        elif spec_content:
            content = spec_content
            filename = "input.csv" if ',' in content else "input.json"
        
        if content:
            with st.spinner("📊 Parsing specification..."):
                try:
                    parser = UnifiedSpecParser()
                    parsed = parser.parse(content, filename)
                    spec_dict = spec_to_dict(parsed)
                    
                    with spec_analysis_placeholder.container():
                        st.success(f"✅ Parsed: **{parsed.name}** ({parsed.source_format})")
                        
                        scol1, scol2, scol3 = st.columns(3)
                        with scol1:
                            st.metric("Total Registers", parsed.total_registers)
                        with scol2:
                            st.metric("Data Width", f"{parsed.data_width} bits")
                        with scol3:
                            st.metric("Register Blocks", len(parsed.register_blocks))
                        
                        # Register table
                        st.subheader("📋 Registers")
                        for block in parsed.register_blocks:
                            st.markdown(f"**Block: {block.name}** (Base: 0x{block.base_address:X})")
                            reg_data = []
                            for reg in block.registers:
                                reg_data.append({
                                    "Name": reg.name,
                                    "Address": reg.address_hex,
                                    "Width": reg.width,
                                    "Access": reg.access.value,
                                    "Fields": len(reg.fields)
                                })
                            st.dataframe(reg_data, use_container_width=True)
                            
                            # Field details (expandable)
                            with st.expander("📍 Field Details"):
                                for reg in block.registers:
                                    if reg.fields:
                                        st.markdown(f"**{reg.name}:**")
                                        field_data = []
                                        for f in reg.fields:
                                            field_data.append({
                                                "Field": f.name,
                                                "Bits": f"{f.msb}:{f.lsb}" if f.bit_width > 1 else str(f.bit_offset),
                                                "Access": f.access.value,
                                                "Reset": f"0x{f.reset_value:X}"
                                            })
                                        st.dataframe(field_data, use_container_width=True)
                    
                    st.divider()
                    
                    # Generate UVM from spec
                    st.subheader("🚀 Generate Register Tests")
                    st.info("💡 Combine with RTL upload in the RTL-Aware tab for complete testbench generation!")
                    
                    # Show JSON export
                    with st.expander("📄 Export as JSON"):
                        import json
                        st.code(json.dumps(spec_dict, indent=2), language="json")
                        st.download_button(
                            "📥 Download JSON",
                            json.dumps(spec_dict, indent=2),
                            f"{parsed.name}_registers.json",
                            "application/json"
                        )
                    
                except Exception as e:
                    st.error(f"❌ Error parsing specification: {str(e)}")
                    import traceback
                    st.code(traceback.format_exc())
        else:
            st.warning("Please upload or paste a specification")

# Footer
st.markdown("---")
st.markdown("""
<div style="text-align: center; color: #888; padding: 1rem;">
    Made with ❤️ by <a href="https://github.com/tusharpathaknyu">Tushar Pathak</a> | 
    <a href="https://github.com/tusharpathaknyu/VerifAI">⭐ Star on GitHub</a>
</div>
""", unsafe_allow_html=True)
