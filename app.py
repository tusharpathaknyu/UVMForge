"""
VerifAI - UVM Testbench Generator
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

# Page config
st.set_page_config(
    page_title="VerifAI",
    page_icon=None,
    layout="wide",
    initial_sidebar_state="collapsed"
)

# Modern CSS
st.markdown("""
<style>
    /* Hide Streamlit branding */
    #MainMenu {visibility: hidden;}
    footer {visibility: hidden;}
    
    /* Modern dark theme */
    .stApp {
        background: linear-gradient(180deg, #0f0f1a 0%, #1a1a2e 100%);
    }
    
    /* Hero section */
    .hero {
        text-align: center;
        padding: 2rem 0;
        margin-bottom: 1rem;
    }
    .hero h1 {
        font-size: 3.5rem;
        font-weight: 800;
        background: linear-gradient(135deg, #667eea 0%, #764ba2 50%, #f093fb 100%);
        -webkit-background-clip: text;
        -webkit-text-fill-color: transparent;
        margin-bottom: 0.5rem;
    }
    .hero p {
        color: #a0a0b0;
        font-size: 1.2rem;
        max-width: 600px;
        margin: 0 auto;
    }
    
    /* Protocol chips */
    .chip-container {
        display: flex;
        justify-content: center;
        gap: 0.5rem;
        flex-wrap: wrap;
        margin: 1.5rem 0;
    }
    .chip {
        background: rgba(102, 126, 234, 0.15);
        border: 1px solid rgba(102, 126, 234, 0.3);
        color: #667eea;
        padding: 0.4rem 1rem;
        border-radius: 20px;
        font-size: 0.85rem;
        font-weight: 500;
    }
    
    /* Feature cards */
    .features {
        display: grid;
        grid-template-columns: repeat(4, 1fr);
        gap: 1rem;
        margin: 2rem 0;
    }
    .feature-card {
        background: rgba(255,255,255,0.03);
        border: 1px solid rgba(255,255,255,0.08);
        border-radius: 12px;
        padding: 1.2rem;
        text-align: center;
        transition: all 0.3s ease;
    }
    .feature-card:hover {
        border-color: rgba(102, 126, 234, 0.5);
        transform: translateY(-2px);
    }
    .feature-icon {
        font-size: 1.8rem;
        margin-bottom: 0.5rem;
    }
    .feature-title {
        color: #fff;
        font-weight: 600;
        font-size: 0.95rem;
        margin-bottom: 0.3rem;
    }
    .feature-desc {
        color: #888;
        font-size: 0.8rem;
    }
    
    /* Tabs styling */
    .stTabs [data-baseweb="tab-list"] {
        background: rgba(255,255,255,0.03);
        border-radius: 12px;
        padding: 0.5rem;
        gap: 0.5rem;
    }
    .stTabs [data-baseweb="tab"] {
        background: transparent;
        border-radius: 8px;
        color: #888;
        padding: 0.8rem 1.5rem;
        font-weight: 500;
    }
    .stTabs [aria-selected="true"] {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white !important;
    }
    
    /* Input areas */
    .stTextArea textarea {
        background: rgba(255,255,255,0.05) !important;
        border: 1px solid rgba(255,255,255,0.1) !important;
        border-radius: 10px !important;
        color: #e0e0e0 !important;
        font-family: 'Monaco', 'Menlo', monospace !important;
    }
    .stTextArea textarea:focus {
        border-color: #667eea !important;
        box-shadow: 0 0 0 1px #667eea !important;
    }
    
    /* Buttons */
    .stButton > button {
        background: linear-gradient(135deg, #667eea 0%, #764ba2 100%);
        color: white;
        border: none;
        border-radius: 8px;
        padding: 0.6rem 1.5rem;
        font-weight: 600;
        transition: all 0.3s ease;
    }
    .stButton > button:hover {
        transform: translateY(-1px);
        box-shadow: 0 4px 15px rgba(102, 126, 234, 0.4);
    }
    
    /* Secondary buttons */
    .stButton > button[kind="secondary"] {
        background: rgba(255,255,255,0.1);
        border: 1px solid rgba(255,255,255,0.2);
    }
    
    /* Code blocks */
    .stCodeBlock {
        border-radius: 10px !important;
    }
    
    /* Expanders */
    .streamlit-expanderHeader {
        background: rgba(255,255,255,0.05);
        border-radius: 8px;
    }
    
    /* Metrics */
    [data-testid="stMetricValue"] {
        color: #667eea;
    }
    
    /* Selectbox */
    .stSelectbox > div > div {
        background: rgba(255,255,255,0.05);
        border: 1px solid rgba(255,255,255,0.1);
        border-radius: 8px;
    }
    
    /* Success/Warning/Error messages */
    .stSuccess {
        background: rgba(46, 204, 113, 0.1);
        border: 1px solid rgba(46, 204, 113, 0.3);
        border-radius: 8px;
    }
    .stWarning {
        background: rgba(241, 196, 15, 0.1);
        border: 1px solid rgba(241, 196, 15, 0.3);
        border-radius: 8px;
    }
    
    /* Footer */
    .footer {
        text-align: center;
        padding: 2rem 0;
        color: #666;
        font-size: 0.85rem;
        border-top: 1px solid rgba(255,255,255,0.05);
        margin-top: 3rem;
    }
    .footer a {
        color: #667eea;
        text-decoration: none;
    }
    
    /* Download button */
    .stDownloadButton > button {
        background: rgba(46, 204, 113, 0.2);
        border: 1px solid rgba(46, 204, 113, 0.4);
        color: #2ecc71;
    }
    .stDownloadButton > button:hover {
        background: rgba(46, 204, 113, 0.3);
    }
    
    /* Analysis results card */
    .analysis-card {
        background: rgba(255,255,255,0.03);
        border: 1px solid rgba(255,255,255,0.08);
        border-radius: 12px;
        padding: 1rem;
        margin: 0.5rem 0;
    }
    .analysis-card h4 {
        color: #667eea;
        margin-bottom: 0.5rem;
    }
    
    /* Sample button */
    .sample-btn {
        background: rgba(102, 126, 234, 0.1) !important;
        border: 1px solid rgba(102, 126, 234, 0.3) !important;
        color: #667eea !important;
    }
</style>
""", unsafe_allow_html=True)

# Hero Section
st.markdown("""
<div class="hero">
    <h1>VerifAI</h1>
    <p>Generate production-ready UVM testbenches from RTL code. 
    Intelligent analysis, protocol detection, and assertion generation.</p>
</div>
""", unsafe_allow_html=True)

# Protocol chips
st.markdown("""
<div class="chip-container">
    <span class="chip">APB</span>
    <span class="chip">AXI4-Lite</span>
    <span class="chip">UART</span>
    <span class="chip">SPI</span>
    <span class="chip">I2C</span>
</div>
""", unsafe_allow_html=True)

# Feature cards
st.markdown("""
<div class="features">
    <div class="feature-card">
        <div class="feature-title">RTL Analysis</div>
        <div class="feature-desc">Auto-detect signals, FSMs, protocols</div>
    </div>
    <div class="feature-card">
        <div class="feature-title">UVM Generation</div>
        <div class="feature-desc">Complete testbench components</div>
    </div>
    <div class="feature-card">
        <div class="feature-title">Coverage Analysis</div>
        <div class="feature-desc">Identify gaps, suggest tests</div>
    </div>
    <div class="feature-card">
        <div class="feature-title">SVA Generator</div>
        <div class="feature-desc">Protocol-aware assertions</div>
    </div>
</div>
""", unsafe_allow_html=True)

# LLM setup
def get_llm():
    api_key = os.environ.get("GEMINI_API_KEY", "")
    if api_key:
        genai.configure(api_key=api_key)
        return genai.GenerativeModel('gemini-1.5-flash')
    return None

def generate_with_llm(prompt: str) -> str:
    model = get_llm()
    if not model:
        return "Error: API key not configured."
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e:
        return f"Error: {str(e)}"

# Sample RTL
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
    reg [31:0] mem [0:255];
    
    localparam IDLE   = 2'b00;
    localparam SETUP  = 2'b01;
    localparam ACCESS = 2'b10;
    
    reg [1:0] state, next_state;
    
    always @(posedge pclk or negedge presetn) begin
        if (!presetn) state <= IDLE;
        else state <= next_state;
    end
    
    always @(*) begin
        case (state)
            IDLE:   next_state = psel ? SETUP : IDLE;
            SETUP:  next_state = ACCESS;
            ACCESS: next_state = psel ? SETUP : IDLE;
            default: next_state = IDLE;
        endcase
    end
endmodule'''

SAMPLE_AXI_RTL = '''module axi_lite_slave (
    input  wire        aclk,
    input  wire        aresetn,
    input  wire        awvalid,
    output reg         awready,
    input  wire [31:0] awaddr,
    input  wire        wvalid,
    output reg         wready,
    input  wire [31:0] wdata,
    output reg         bvalid,
    input  wire        bready,
    output reg  [1:0]  bresp,
    input  wire        arvalid,
    output reg         arready,
    input  wire [31:0] araddr,
    output reg         rvalid,
    input  wire        rready,
    output reg  [31:0] rdata,
    output reg  [1:0]  rresp
);
    reg [31:0] registers [0:15];
    localparam W_IDLE = 2'b00, W_DATA = 2'b01, W_RESP = 2'b10;
    reg [1:0] w_state;
endmodule'''

# Main tabs
st.markdown("<br>", unsafe_allow_html=True)
tabs = st.tabs(["RTL-Aware Generator", "Protocol Templates", "Spec Import", "Coverage Analysis", "SVA Generator"])

# Tab 1: RTL-Aware Generator
with tabs[0]:
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.markdown("#### Paste Your RTL")
        
        # Sample buttons
        c1, c2, c3 = st.columns([1, 1, 2])
        with c1:
            if st.button("APB Sample", key="sample_apb", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_APB_RTL
        with c2:
            if st.button("AXI Sample", key="sample_axi", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_AXI_RTL
        
        rtl_code = st.text_area(
            "RTL Code",
            value=st.session_state.get('rtl_input', ''),
            height=350,
            placeholder="// Paste your Verilog/SystemVerilog code here...",
            label_visibility="collapsed"
        )
        
        analyze_btn = st.button("Analyze & Generate", type="primary", use_container_width=True)
    
    with col2:
        st.markdown("#### Generated Output")
        
        if analyze_btn and rtl_code:
            with st.spinner("Analyzing RTL..."):
                try:
                    parsed = parse_rtl(rtl_code)
                    
                    # Analysis summary
                    st.success(f"✓ Analyzed: **{parsed.module_name}**")
                    
                    c1, c2, c3 = st.columns(3)
                    c1.metric("Inputs", len(parsed.inputs))
                    c2.metric("Outputs", len(parsed.outputs))
                    c3.metric("FSM", "Yes" if parsed.fsm else "No")
                    
                    with st.expander("Analysis Details", expanded=False):
                        if parsed.clocks:
                            st.write(f"**Clocks:** {', '.join(parsed.clocks)}")
                        if parsed.resets:
                            st.write(f"**Resets:** {', '.join(parsed.resets)}")
                        if parsed.fsm:
                            st.write(f"**FSM States:** {parsed.fsm.get('states', [])}")
                    
                    # Generate testbench
                    generator = RTLAwareGenerator()
                    prompt = generator.generate_prompt(parsed)
                    result = generate_with_llm(prompt)
                    
                    st.code(result, language="systemverilog")
                    st.download_button("Download Testbench", result, f"{parsed.module_name}_tb.sv", use_container_width=True)
                    
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif analyze_btn:
            st.warning("Please paste RTL code first")
        else:
            st.info("Paste RTL code and click Analyze to generate a UVM testbench")

# Tab 2: Protocol Templates
with tabs[1]:
    col1, col2 = st.columns([1, 2])
    
    with col1:
        st.markdown("#### Configuration")
        
        protocol = st.selectbox("Protocol", ["APB", "AXI4-Lite", "UART", "SPI", "I2C"])
        
        if protocol == "APB":
            addr_width = st.slider("Address Width", 8, 64, 32)
            data_width = st.slider("Data Width", 8, 64, 32)
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "AXI4-Lite":
            addr_width = st.slider("Address Width", 8, 64, 32)
            data_width = st.selectbox("Data Width", [32, 64])
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "UART":
            baud_rate = st.selectbox("Baud Rate", [9600, 19200, 38400, 57600, 115200])
            data_bits = st.selectbox("Data Bits", [7, 8])
            config = {"baud_rate": baud_rate, "data_bits": data_bits}
        elif protocol == "SPI":
            cpol = st.selectbox("CPOL", [0, 1])
            cpha = st.selectbox("CPHA", [0, 1])
            config = {"cpol": cpol, "cpha": cpha}
        else:  # I2C
            speed = st.selectbox("Speed", ["Standard (100kHz)", "Fast (400kHz)", "Fast+ (1MHz)"])
            config = {"speed": speed}
        
        generate_btn = st.button("Generate", type="primary", use_container_width=True, key="gen_proto")
    
    with col2:
        st.markdown("#### Generated Testbench")
        
        if generate_btn:
            with st.spinner("Generating..."):
                template = PROTOCOL_TEMPLATES.get(protocol.lower().replace("-", "_").replace("4_", "4"), 
                                                  PROTOCOL_TEMPLATES.get("apb", ""))
                prompt = f"""Generate a complete UVM testbench for {protocol} protocol with config: {config}

Include: interface, sequence_item, driver, monitor, agent, scoreboard, env, test, coverage.
Use proper UVM methodology. Base template:
{template}"""
                result = generate_with_llm(prompt)
                st.code(result, language="systemverilog")
                st.download_button("Download", result, f"{protocol.lower()}_tb.sv", use_container_width=True)
        else:
            st.info("Configure protocol parameters and click Generate")

# Tab 3: Spec Import
with tabs[2]:
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.markdown("#### Specification Input")
        
        spec_format = st.selectbox("Format", ["Plain Text/Markdown", "JSON", "CSV"])
        
        spec_text = st.text_area(
            "Specification",
            height=300,
            placeholder="""Example:
## Protocol Requirements
- All transactions must complete within 16 cycles
- PREADY must assert within 4 cycles of PENABLE
- Address must be aligned to data width
- Error response for invalid addresses""",
            label_visibility="collapsed"
        )
        
        parse_btn = st.button("Parse & Extract", type="primary", use_container_width=True)
    
    with col2:
        st.markdown("#### Extracted Requirements")
        
        if parse_btn and spec_text:
            with st.spinner("Parsing..."):
                try:
                    parser = SpecParser()
                    requirements = parser.parse(spec_text)
                    
                    st.success(f"✓ Extracted **{len(requirements.registers) if hasattr(requirements, 'registers') else 0}** items")
                    
                    # Show as verification points
                    prompt = f"""Extract testable requirements from this spec and create a verification plan:
{spec_text}

List each requirement with:
1. ID
2. Description  
3. How to test it
4. Coverage point"""
                    result = generate_with_llm(prompt)
                    st.markdown(result)
                    
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif parse_btn:
            st.warning("Please paste specification first")
        else:
            st.info("Paste a protocol specification to extract verification requirements")

# Tab 4: Coverage Analysis
with tabs[3]:
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.markdown("#### Coverage Report")
        
        coverage_text = st.text_area(
            "Coverage Data",
            height=300,
            placeholder="""=== Coverage Summary ===
Functional Coverage: 75%
  - read_cg: 80%
  - write_cg: 70%
  - error_cg: 45%

Code Coverage: 82%
  - Line: 90%
  - Branch: 75%

Uncovered:
  - burst_read: 0 hits
  - timeout_error: 0 hits""",
            label_visibility="collapsed"
        )
        
        analyze_btn = st.button("Analyze Gaps", type="primary", use_container_width=True, key="cov_analyze")
    
    with col2:
        st.markdown("#### Analysis Results")
        
        if analyze_btn and coverage_text:
            with st.spinner("Analyzing..."):
                try:
                    analyzer = CoverageAnalyzer()
                    analysis = analyzer.analyze(coverage_text)
                    
                    # Metrics
                    metrics = analysis.get('metrics', {})
                    c1, c2 = st.columns(2)
                    c1.metric("Functional", f"{metrics.get('functional', 0)}%")
                    c2.metric("Code", f"{metrics.get('code', 0)}%")
                    
                    # Gaps
                    gaps = analysis.get('gaps', [])
                    if gaps:
                        st.markdown("**Identified Gaps:**")
                        for gap in gaps:
                            st.warning(gap)
                    
                    # Suggestions
                    suggestions = analysis.get('suggestions', [])
                    if suggestions:
                        st.markdown("**Suggested Tests:**")
                        for i, s in enumerate(suggestions, 1):
                            st.info(f"{i}. {s}")
                    
                    if st.button("Generate Tests for Gaps", use_container_width=True):
                        prompt = f"Generate UVM sequences to cover these gaps: {gaps}"
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
                        
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif analyze_btn:
            st.warning("Please paste coverage report first")
        else:
            st.info("Paste coverage report to identify gaps and get test suggestions")

# Tab 5: SVA Generator
with tabs[4]:
    col1, col2 = st.columns([1, 1])
    
    with col1:
        st.markdown("#### Input")
        
        sva_mode = st.radio("Mode", ["From RTL", "From Description"], horizontal=True)
        
        if sva_mode == "From RTL":
            c1, c2 = st.columns(2)
            with c1:
                if st.button("APB Sample", key="sva_apb"):
                    st.session_state['sva_input'] = SAMPLE_APB_RTL
            with c2:
                if st.button("AXI Sample", key="sva_axi"):
                    st.session_state['sva_input'] = SAMPLE_AXI_RTL
            
            sva_input = st.text_area(
                "RTL",
                value=st.session_state.get('sva_input', ''),
                height=280,
                placeholder="// Paste RTL code...",
                label_visibility="collapsed"
            )
        else:
            sva_input = st.text_area(
                "Description",
                height=300,
                placeholder="""Describe the assertions needed:
- Request must be acknowledged within 4 cycles
- Data valid only when enable is high
- After reset, all outputs should be zero
- No back-to-back writes allowed""",
                label_visibility="collapsed"
            )
        
        gen_btn = st.button("Generate Assertions", type="primary", use_container_width=True)
    
    with col2:
        st.markdown("#### Generated SVA")
        
        if gen_btn and sva_input:
            with st.spinner("Generating..."):
                try:
                    if sva_mode == "From RTL":
                        parsed = parse_rtl(sva_input)
                        sva_gen = SVAGenerator()
                        assertions = sva_gen.generate_from_rtl(parsed)
                        
                        st.success(f"✓ Generated **{len(assertions)}** assertions")
                        
                        all_code = []
                        for a in assertions:
                            with st.expander(f"**{a['name']}** ({a['type']})", expanded=False):
                                st.code(a['code'], language="systemverilog")
                            all_code.append(f"// {a['name']}\n{a['code']}")
                        
                        combined = "\n\n".join(all_code)
                        st.download_button("Download All", combined, f"{parsed.module_name}_sva.sv", use_container_width=True)
                    else:
                        prompt = f"""Generate SVA assertions for:
{sva_input}

For each, provide property name, SVA code with ##, |=>, throughout syntax, and assert/cover directives."""
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
                        st.download_button("Download", result, "assertions.sv", use_container_width=True)
                        
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif gen_btn:
            st.warning("Please provide input first")
        else:
            st.info("Provide RTL or description to generate SystemVerilog assertions")

# Footer
st.markdown("""
<div class="footer">
    <p>Built for hardware verification engineers</p>
    <p><a href="https://github.com/tusharpathaknyu/VerifAI">GitHub</a> · MIT License</p>
</div>
""", unsafe_allow_html=True)
