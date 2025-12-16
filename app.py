"""
VerifAI - UVM Testbench Generator
Generates production-ready UVM testbenches for common protocols
"""

import streamlit as st
import os
import google.generativeai as genai
from src.templates import PROTOCOL_TEMPLATES
from src.rtl_parser import parse_rtl
from src.spec_import import SpecParser
from src.rtl_aware_gen import RTLAwareGenerator
from src.coverage_analyzer import CoverageAnalyzer
from src.sva_generator import SVAGenerator

# Configure page
st.set_page_config(
    page_title="VerifAI - UVM Testbench Generator",
    page_icon="🔬",
    layout="wide"
)

# Custom CSS for cleaner look
st.markdown("""
<style>
    .main-header {
        font-size: 2.5rem;
        font-weight: 700;
        color: #1E3A5F;
        text-align: center;
        margin-bottom: 0.5rem;
    }
    .sub-header {
        font-size: 1.1rem;
        color: #666;
        text-align: center;
        margin-bottom: 2rem;
    }
    .feature-box {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        padding: 1.5rem;
        border-radius: 10px;
        color: white;
        margin-bottom: 1rem;
    }
    .protocol-badge {
        display: inline-block;
        background: #e8f4f8;
        padding: 0.3rem 0.8rem;
        border-radius: 15px;
        margin: 0.2rem;
        font-size: 0.85rem;
        color: #1E3A5F;
    }
    .stTabs [data-baseweb="tab-list"] {
        gap: 8px;
    }
    .stTabs [data-baseweb="tab"] {
        background-color: #f0f2f6;
        border-radius: 8px;
        padding: 10px 20px;
    }
    .sample-btn {
        background: #28a745;
        color: white;
        padding: 0.5rem 1rem;
        border-radius: 5px;
    }
</style>
""", unsafe_allow_html=True)

# Header
st.markdown('<h1 class="main-header">🔬 VerifAI</h1>', unsafe_allow_html=True)
st.markdown('''<p class="sub-header">
    Generate production-ready UVM testbenches for standard protocols. 
    Supports APB, AXI4-Lite, UART, SPI, and I2C with RTL-aware generation, 
    coverage analysis, and SVA assertion generation.
</p>''', unsafe_allow_html=True)

# Supported protocols display
st.markdown("**Supported Protocols:**")
protocols_html = ""
for proto in ["APB", "AXI4-Lite", "UART", "SPI", "I2C"]:
    protocols_html += f'<span class="protocol-badge">{proto}</span>'
st.markdown(protocols_html, unsafe_allow_html=True)

st.markdown("---")

# Configure Gemini (using environment variable)
def get_llm():
    """Get configured Gemini model"""
    api_key = os.environ.get("GEMINI_API_KEY", "")
    if api_key:
        genai.configure(api_key=api_key)
        return genai.GenerativeModel('gemini-1.5-flash')
    return None

# Helper function to generate with LLM
def generate_with_llm(prompt: str) -> str:
    """Generate response using Gemini"""
    model = get_llm()
    if not model:
        return "Error: API key not configured. Please contact administrator."
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e:
        return f"Error generating response: {str(e)}"

# Sample RTL code for demonstrations
SAMPLE_APB_RTL = '''module apb_slave (
    input  wire        pclk,
    input  wire        presetn,
    input  wire        psel,
    input  wire        penable,
    input  wire        pwrite,
    input  wire [31:0] paddr,
    input  wire [31:0] pwdata,
    output reg  [31:0] prdata,
    output reg         pready,
    output reg         pslverr
);
    // Internal registers
    reg [31:0] mem [0:255];
    
    // FSM states
    localparam IDLE   = 2'b00;
    localparam SETUP  = 2'b01;
    localparam ACCESS = 2'b10;
    
    reg [1:0] state, next_state;
    
    always @(posedge pclk or negedge presetn) begin
        if (!presetn)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    always @(*) begin
        case (state)
            IDLE:   next_state = psel ? SETUP : IDLE;
            SETUP:  next_state = ACCESS;
            ACCESS: next_state = psel ? SETUP : IDLE;
            default: next_state = IDLE;
        endcase
    end
    
    always @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            prdata <= 32'b0;
            pready <= 1'b0;
            pslverr <= 1'b0;
        end else if (state == ACCESS) begin
            pready <= 1'b1;
            if (pwrite)
                mem[paddr[9:2]] <= pwdata;
            else
                prdata <= mem[paddr[9:2]];
        end else begin
            pready <= 1'b0;
        end
    end
endmodule'''

SAMPLE_AXI_RTL = '''module axi_lite_slave (
    input  wire        aclk,
    input  wire        aresetn,
    // Write address channel
    input  wire        awvalid,
    output reg         awready,
    input  wire [31:0] awaddr,
    // Write data channel
    input  wire        wvalid,
    output reg         wready,
    input  wire [31:0] wdata,
    input  wire [3:0]  wstrb,
    // Write response channel
    output reg         bvalid,
    input  wire        bready,
    output reg  [1:0]  bresp,
    // Read address channel
    input  wire        arvalid,
    output reg         arready,
    input  wire [31:0] araddr,
    // Read data channel
    output reg         rvalid,
    input  wire        rready,
    output reg  [31:0] rdata,
    output reg  [1:0]  rresp
);
    reg [31:0] registers [0:15];
    
    // Write FSM
    localparam W_IDLE = 2'b00, W_ADDR = 2'b01, W_DATA = 2'b10, W_RESP = 2'b11;
    reg [1:0] w_state;
    reg [31:0] w_addr_reg;
    
    always @(posedge aclk or negedge aresetn) begin
        if (!aresetn) begin
            w_state <= W_IDLE;
            awready <= 1'b0;
            wready <= 1'b0;
            bvalid <= 1'b0;
        end else begin
            case (w_state)
                W_IDLE: begin
                    awready <= 1'b1;
                    if (awvalid && awready) begin
                        w_addr_reg <= awaddr;
                        awready <= 1'b0;
                        wready <= 1'b1;
                        w_state <= W_DATA;
                    end
                end
                W_DATA: begin
                    if (wvalid && wready) begin
                        registers[w_addr_reg[5:2]] <= wdata;
                        wready <= 1'b0;
                        bvalid <= 1'b1;
                        bresp <= 2'b00;
                        w_state <= W_RESP;
                    end
                end
                W_RESP: begin
                    if (bready && bvalid) begin
                        bvalid <= 1'b0;
                        awready <= 1'b1;
                        w_state <= W_IDLE;
                    end
                end
            endcase
        end
    end
endmodule'''

# Main tabs
tab1, tab2, tab3, tab4, tab5 = st.tabs([
    "📝 Protocol Generator",
    "🔍 RTL-Aware Generator", 
    "📄 Spec Import",
    "📊 Coverage Gap Analysis",
    "✅ SVA Generator"
])

# Tab 1: Protocol Generator
with tab1:
    st.subheader("Generate UVM Testbench from Protocol Template")
    st.write("Select a protocol and customize parameters to generate a complete UVM testbench.")
    
    col1, col2 = st.columns([1, 2])
    
    with col1:
        protocol = st.selectbox(
            "Select Protocol",
            ["APB", "AXI4-Lite", "UART", "SPI", "I2C"]
        )
        
        st.write("**Configuration:**")
        
        if protocol == "APB":
            addr_width = st.number_input("Address Width", 8, 64, 32)
            data_width = st.number_input("Data Width", 8, 64, 32)
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "AXI4-Lite":
            addr_width = st.number_input("Address Width", 8, 64, 32)
            data_width = st.selectbox("Data Width", [32, 64])
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "UART":
            baud_rate = st.selectbox("Baud Rate", [9600, 19200, 38400, 57600, 115200])
            data_bits = st.selectbox("Data Bits", [7, 8])
            parity = st.selectbox("Parity", ["none", "even", "odd"])
            config = {"baud_rate": baud_rate, "data_bits": data_bits, "parity": parity}
        elif protocol == "SPI":
            cpol = st.selectbox("CPOL", [0, 1])
            cpha = st.selectbox("CPHA", [0, 1])
            data_width = st.number_input("Data Width", 8, 32, 8)
            config = {"cpol": cpol, "cpha": cpha, "data_width": data_width}
        else:  # I2C
            speed = st.selectbox("Speed Mode", ["standard", "fast", "fast_plus"])
            addr_bits = st.selectbox("Address Bits", [7, 10])
            config = {"speed_mode": speed, "addr_bits": addr_bits}
        
        generate_btn = st.button("🚀 Generate Testbench", type="primary", key="gen_protocol")
    
    with col2:
        if generate_btn:
            with st.spinner("Generating UVM testbench..."):
                template = PROTOCOL_TEMPLATES.get(protocol.lower().replace("-", "_"), PROTOCOL_TEMPLATES.get("apb"))
                
                prompt = f"""Generate a complete UVM testbench for {protocol} protocol with these parameters:
{config}

Include:
1. Interface definition
2. Sequence item (transaction)
3. Driver
4. Monitor  
5. Agent
6. Scoreboard
7. Environment
8. Test with multiple sequences
9. Coverage collector

Use proper UVM methodology and SystemVerilog best practices.
Base structure:
{template}
"""
                result = generate_with_llm(prompt)
                st.code(result, language="systemverilog")
                st.download_button(
                    "📥 Download Testbench",
                    result,
                    f"{protocol.lower()}_tb.sv",
                    mime="text/plain"
                )

# Tab 2: RTL-Aware Generator  
with tab2:
    st.subheader("RTL-Aware Testbench Generation")
    st.write("Paste your RTL code to generate a testbench that matches your specific design signals, FSMs, and structure.")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        # Sample button
        if st.button("📋 Try Sample APB RTL", key="sample_apb"):
            st.session_state['rtl_input'] = SAMPLE_APB_RTL
        
        rtl_code = st.text_area(
            "Paste RTL Code (Verilog/SystemVerilog)",
            value=st.session_state.get('rtl_input', ''),
            height=400,
            placeholder="module my_design (\n    input clk,\n    input rst_n,\n    ...\n);"
        )
        
        analyze_btn = st.button("🔍 Analyze & Generate", type="primary", key="analyze_rtl")
    
    with col2:
        if analyze_btn and rtl_code:
            with st.spinner("Analyzing RTL..."):
                try:
                    parsed = parse_rtl(rtl_code)
                    
                    st.success("✅ RTL Analysis Complete")
                    
                    # Display analysis results
                    with st.expander("📊 Analysis Results", expanded=True):
                        st.write(f"**Module:** {parsed.module_name}")
                        st.write(f"**Inputs:** {len(parsed.inputs)}")
                        st.write(f"**Outputs:** {len(parsed.outputs)}")
                        
                        if parsed.clocks:
                            st.write(f"**Clocks:** {', '.join(parsed.clocks)}")
                        if parsed.resets:
                            st.write(f"**Resets:** {', '.join(parsed.resets)}")
                        if parsed.fsm:
                            st.write(f"**FSM Detected:** {parsed.fsm.get('states', 'N/A')}")
                    
                    # Generate testbench
                    generator = RTLAwareGenerator()
                    prompt = generator.generate_prompt(parsed)
                    result = generate_with_llm(prompt)
                    
                    st.subheader("Generated Testbench")
                    st.code(result, language="systemverilog")
                    st.download_button(
                        "📥 Download",
                        result,
                        f"{parsed.module_name}_tb.sv",
                        mime="text/plain"
                    )
                except Exception as e:
                    st.error(f"Error parsing RTL: {str(e)}")
        elif analyze_btn:
            st.warning("Please paste RTL code first")

# Tab 3: Spec Import
with tab3:
    st.subheader("Import from Specification")
    st.write("Parse protocol specifications or documentation to extract verification requirements.")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        spec_format = st.selectbox(
            "Specification Format",
            ["Plain Text", "Markdown", "JSON"]
        )
        
        spec_text = st.text_area(
            "Paste Specification",
            height=350,
            placeholder="""Example:
## APB Protocol Requirements
- All transactions must complete within 16 clock cycles
- PREADY must be asserted within 4 cycles of PENABLE
- PSLVERR indicates error condition
- Address must be aligned to data width"""
        )
        
        parse_btn = st.button("📄 Parse Specification", type="primary", key="parse_spec")
    
    with col2:
        if parse_btn and spec_text:
            with st.spinner("Parsing specification..."):
                try:
                    parser = SpecParser()
                    requirements = parser.parse(spec_text)
                    
                    st.success(f"✅ Extracted {len(requirements)} requirements")
                    
                    for i, req in enumerate(requirements, 1):
                        with st.expander(f"Requirement {i}: {req.get('title', 'Untitled')}", expanded=i<=3):
                            st.write(f"**Type:** {req.get('type', 'functional')}")
                            st.write(f"**Description:** {req.get('description', '')}")
                            if req.get('testable'):
                                st.write("✅ Testable")
                    
                    # Generate verification plan
                    if st.button("🚀 Generate Verification Plan", key="gen_vplan"):
                        prompt = f"""Based on these requirements, generate a UVM verification plan:
{requirements}

Include:
1. Test scenarios for each requirement
2. Coverage points
3. Assertions needed
4. Recommended sequences"""
                        result = generate_with_llm(prompt)
                        st.code(result, language="markdown")
                except Exception as e:
                    st.error(f"Error parsing spec: {str(e)}")
        elif parse_btn:
            st.warning("Please paste specification text first")

# Tab 4: Coverage Gap Analysis
with tab4:
    st.subheader("Coverage Gap Analysis")
    st.write("Analyze your coverage reports to identify gaps and get suggestions for additional tests.")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        coverage_format = st.selectbox(
            "Coverage Report Format",
            ["Text Summary", "UCD (Unified Coverage Database)", "CSV"]
        )
        
        coverage_text = st.text_area(
            "Paste Coverage Report",
            height=350,
            placeholder="""Example coverage summary:
=== Coverage Summary ===
Functional Coverage: 75%
  - apb_read_cg: 80%
  - apb_write_cg: 70%
  - error_cases_cg: 45%

Code Coverage: 82%
  - Line: 90%
  - Branch: 75%
  - Toggle: 80%

Uncovered bins:
  - apb_read_cg.burst_read: 0 hits
  - error_cases_cg.timeout: 0 hits
  - error_cases_cg.parity_error: 0 hits"""
        )
        
        analyze_cov_btn = st.button("📊 Analyze Coverage", type="primary", key="analyze_cov")
    
    with col2:
        if analyze_cov_btn and coverage_text:
            with st.spinner("Analyzing coverage..."):
                try:
                    analyzer = CoverageAnalyzer()
                    analysis = analyzer.analyze(coverage_text)
                    
                    # Display metrics
                    st.subheader("Coverage Metrics")
                    metrics = analysis.get('metrics', {})
                    
                    col_a, col_b = st.columns(2)
                    with col_a:
                        func_cov = metrics.get('functional', 0)
                        st.metric("Functional Coverage", f"{func_cov}%")
                    with col_b:
                        code_cov = metrics.get('code', 0)
                        st.metric("Code Coverage", f"{code_cov}%")
                    
                    # Show gaps
                    gaps = analysis.get('gaps', [])
                    if gaps:
                        st.subheader("Identified Gaps")
                        for gap in gaps:
                            st.warning(f"🔴 {gap}")
                    
                    # Generate suggestions
                    st.subheader("Suggested Tests")
                    suggestions = analysis.get('suggestions', [])
                    for i, sugg in enumerate(suggestions, 1):
                        st.info(f"{i}. {sugg}")
                    
                    # Option to generate test code
                    if st.button("🚀 Generate Tests for Gaps", key="gen_gap_tests"):
                        prompt = f"""Generate UVM test sequences to cover these gaps:
{gaps}

Suggestions:
{suggestions}

Provide complete UVM sequence code for each gap."""
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
                        
                except Exception as e:
                    st.error(f"Error analyzing coverage: {str(e)}")
        elif analyze_cov_btn:
            st.warning("Please paste coverage report first")

# Tab 5: SVA Generator
with tab5:
    st.subheader("SVA Assertion Generator")
    st.write("Generate SystemVerilog Assertions from RTL analysis or natural language descriptions.")
    
    col1, col2 = st.columns([1, 1])
    
    with col1:
        sva_mode = st.radio(
            "Generation Mode",
            ["From RTL", "From Description"],
            horizontal=True
        )
        
        if sva_mode == "From RTL":
            # Sample button
            if st.button("📋 Try Sample AXI RTL", key="sample_axi"):
                st.session_state['sva_rtl_input'] = SAMPLE_AXI_RTL
            
            sva_rtl = st.text_area(
                "RTL Code",
                value=st.session_state.get('sva_rtl_input', ''),
                height=300,
                placeholder="Paste RTL to generate protocol-aware assertions..."
            )
            gen_input = sva_rtl
        else:
            sva_desc = st.text_area(
                "Describe Assertions Needed",
                height=300,
                placeholder="""Example:
- Request must be acknowledged within 4 cycles
- Data valid should only be high when enable is high
- After reset, all outputs should be zero
- FIFO should never overflow"""
            )
            gen_input = sva_desc
        
        gen_sva_btn = st.button("✅ Generate Assertions", type="primary", key="gen_sva")
    
    with col2:
        if gen_sva_btn and gen_input:
            with st.spinner("Generating assertions..."):
                try:
                    if sva_mode == "From RTL":
                        parsed = parse_rtl(gen_input)
                        sva_gen = SVAGenerator()
                        assertions = sva_gen.generate_from_rtl(parsed)
                        
                        st.success(f"✅ Generated {len(assertions)} assertions")
                        
                        # Group by type
                        st.subheader("Generated Assertions")
                        
                        all_code = []
                        for a in assertions:
                            with st.expander(f"{a['type']}: {a['name']}", expanded=True):
                                st.code(a['code'], language="systemverilog")
                                st.write(f"*{a.get('description', '')}*")
                                all_code.append(f"// {a['name']}\n{a['code']}")
                        
                        combined = "\n\n".join(all_code)
                        st.download_button(
                            "📥 Download All Assertions",
                            combined,
                            f"{parsed.module_name}_sva.sv",
                            mime="text/plain"
                        )
                    else:
                        # Generate from description using LLM
                        prompt = f"""Generate SystemVerilog Assertions (SVA) for these requirements:
{gen_input}

For each assertion provide:
1. Property name
2. SVA property code
3. Assert and cover directives
4. Brief description

Use proper SVA syntax with ##, |=>, throughout, etc."""
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
                        st.download_button(
                            "📥 Download Assertions",
                            result,
                            "assertions.sv",
                            mime="text/plain"
                        )
                except Exception as e:
                    st.error(f"Error generating assertions: {str(e)}")
        elif gen_sva_btn:
            st.warning("Please provide RTL code or description first")

# Footer
st.markdown("---")
st.markdown("""
<div style="text-align: center; color: #666; font-size: 0.9rem;">
    <p><strong>VerifAI</strong> - UVM Testbench Generator</p>
    <p>Supports APB, AXI4-Lite, UART, SPI, I2C protocols</p>
    <p><a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank">GitHub</a></p>
</div>
""", unsafe_allow_html=True)
