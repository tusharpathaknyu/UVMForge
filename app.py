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

st.set_page_config(
    page_title="VerifAI",
    page_icon=None,
    layout="wide",
    initial_sidebar_state="collapsed"
)

# Clean professional CSS
st.markdown("""
<style>
    /* Hide defaults */
    #MainMenu, footer, header {visibility: hidden;}
    .block-container {padding-top: 2rem; padding-bottom: 0;}
    
    /* Dark theme */
    .stApp {
        background: #0a0a0f;
    }
    
    /* Navigation */
    .nav {
        display: flex;
        justify-content: space-between;
        align-items: center;
        padding: 1rem 0;
        border-bottom: 1px solid rgba(255,255,255,0.06);
        margin-bottom: 2rem;
    }
    .logo {
        font-size: 1.4rem;
        font-weight: 700;
        color: #fff;
        letter-spacing: -0.5px;
    }
    .nav-links {
        display: flex;
        gap: 2rem;
    }
    .nav-links a {
        color: #888;
        text-decoration: none;
        font-size: 0.9rem;
        transition: color 0.2s;
    }
    .nav-links a:hover {
        color: #fff;
    }
    
    /* Hero */
    .hero {
        text-align: center;
        padding: 4rem 0 3rem;
    }
    .hero h1 {
        font-size: 3.2rem;
        font-weight: 700;
        color: #fff;
        margin-bottom: 1rem;
        letter-spacing: -1px;
    }
    .hero p {
        color: #666;
        font-size: 1.15rem;
        max-width: 500px;
        margin: 0 auto 2rem;
        line-height: 1.6;
    }
    
    /* Mode selector */
    .mode-selector {
        display: flex;
        justify-content: center;
        gap: 0.5rem;
        margin-bottom: 3rem;
    }
    .mode-btn {
        background: transparent;
        border: 1px solid rgba(255,255,255,0.1);
        color: #666;
        padding: 0.6rem 1.2rem;
        border-radius: 6px;
        font-size: 0.85rem;
        cursor: pointer;
        transition: all 0.2s;
    }
    .mode-btn:hover {
        border-color: rgba(255,255,255,0.2);
        color: #999;
    }
    .mode-btn.active {
        background: #fff;
        color: #000;
        border-color: #fff;
    }
    
    /* Main input area */
    .input-container {
        max-width: 900px;
        margin: 0 auto;
    }
    
    /* Text area styling */
    .stTextArea textarea {
        background: rgba(255,255,255,0.03) !important;
        border: 1px solid rgba(255,255,255,0.08) !important;
        border-radius: 12px !important;
        color: #e0e0e0 !important;
        font-family: 'SF Mono', 'Monaco', 'Menlo', monospace !important;
        font-size: 0.9rem !important;
        padding: 1rem !important;
    }
    .stTextArea textarea:focus {
        border-color: rgba(255,255,255,0.2) !important;
        box-shadow: none !important;
    }
    .stTextArea textarea::placeholder {
        color: #444 !important;
    }
    
    /* Buttons */
    .stButton > button {
        background: #fff;
        color: #000;
        border: none;
        border-radius: 8px;
        padding: 0.7rem 2rem;
        font-weight: 600;
        font-size: 0.9rem;
        transition: all 0.2s;
    }
    .stButton > button:hover {
        background: #e0e0e0;
        transform: translateY(-1px);
    }
    
    /* Secondary buttons */
    .stButton > button[kind="secondary"] {
        background: transparent;
        color: #888;
        border: 1px solid rgba(255,255,255,0.1);
    }
    .stButton > button[kind="secondary"]:hover {
        background: rgba(255,255,255,0.05);
        color: #fff;
    }
    
    /* Tabs - minimal */
    .stTabs [data-baseweb="tab-list"] {
        background: transparent;
        gap: 0;
        border-bottom: 1px solid rgba(255,255,255,0.08);
        justify-content: center;
    }
    .stTabs [data-baseweb="tab"] {
        background: transparent;
        color: #555;
        padding: 1rem 1.5rem;
        font-size: 0.9rem;
        border-bottom: 2px solid transparent;
        margin-bottom: -1px;
    }
    .stTabs [aria-selected="true"] {
        color: #fff !important;
        background: transparent !important;
        border-bottom: 2px solid #fff;
    }
    .stTabs [data-baseweb="tab"]:hover {
        color: #999;
    }
    
    /* Results area */
    .stCodeBlock {
        border-radius: 12px !important;
    }
    pre {
        background: rgba(255,255,255,0.03) !important;
        border: 1px solid rgba(255,255,255,0.08) !important;
    }
    
    /* Metrics */
    [data-testid="stMetricValue"] {
        color: #fff;
        font-size: 1.5rem;
    }
    [data-testid="stMetricLabel"] {
        color: #555;
    }
    
    /* Download button */
    .stDownloadButton > button {
        background: transparent;
        color: #888;
        border: 1px solid rgba(255,255,255,0.1);
    }
    .stDownloadButton > button:hover {
        background: rgba(255,255,255,0.05);
        color: #fff;
        border-color: rgba(255,255,255,0.2);
    }
    
    /* Selectbox */
    .stSelectbox > div > div {
        background: rgba(255,255,255,0.03);
        border: 1px solid rgba(255,255,255,0.08);
        border-radius: 8px;
    }
    
    /* Expander */
    .streamlit-expanderHeader {
        background: rgba(255,255,255,0.03);
        border-radius: 8px;
        color: #888;
    }
    
    /* Footer */
    .footer {
        position: fixed;
        bottom: 0;
        left: 0;
        right: 0;
        padding: 1rem 2rem;
        display: flex;
        justify-content: space-between;
        align-items: center;
        font-size: 0.8rem;
        color: #444;
        background: linear-gradient(transparent, #0a0a0f);
    }
    .footer a {
        color: #555;
        text-decoration: none;
    }
    .footer a:hover {
        color: #888;
    }
    
    /* Radio buttons horizontal */
    .stRadio > div {
        flex-direction: row;
        gap: 1rem;
    }
    .stRadio label {
        color: #888 !important;
    }
    
    /* Slider */
    .stSlider > div > div {
        color: #888;
    }
    
    /* Success/warning/info */
    .stSuccess, .stWarning, .stInfo {
        background: rgba(255,255,255,0.03);
        border: 1px solid rgba(255,255,255,0.08);
        border-radius: 8px;
    }
    
    /* Columns spacing */
    [data-testid="column"] {
        padding: 0 1rem;
    }
</style>
""", unsafe_allow_html=True)

# Navigation
st.markdown("""
<div class="nav">
    <div class="logo">VerifAI</div>
    <div class="nav-links">
        <a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank">GitHub</a>
    </div>
</div>
""", unsafe_allow_html=True)

# Hero
st.markdown("""
<div class="hero">
    <h1>UVM Testbench Generator</h1>
    <p>Generate production-ready verification components from RTL. 
    Supports APB, AXI4-Lite, UART, SPI, and I2C.</p>
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
SAMPLE_APB = '''module apb_slave (
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
    localparam IDLE = 2'b00, SETUP = 2'b01, ACCESS = 2'b10;
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

SAMPLE_AXI = '''module axi_lite_slave (
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

# Tabs
tabs = st.tabs(["Generate from RTL", "Protocol Templates", "Coverage Analysis", "SVA Assertions"])

# Tab 1: RTL-Aware Generator
with tabs[0]:
    col1, col2 = st.columns([1, 1], gap="large")
    
    with col1:
        # Sample buttons row
        c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
        with c1:
            if st.button("Load APB", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_APB
        with c2:
            if st.button("Load AXI", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_AXI
        
        rtl_code = st.text_area(
            "RTL Code",
            value=st.session_state.get('rtl_input', ''),
            height=400,
            placeholder="// Paste your Verilog or SystemVerilog RTL here...\n\nmodule my_design (\n    input  wire clk,\n    input  wire rst_n,\n    ...\n);",
            label_visibility="collapsed"
        )
        
        generate_btn = st.button("Generate Testbench", type="primary", use_container_width=True)
    
    with col2:
        if generate_btn and rtl_code:
            with st.spinner("Analyzing..."):
                try:
                    parsed = parse_rtl(rtl_code)
                    
                    st.markdown(f"**Module:** `{parsed.module_name}`")
                    
                    c1, c2, c3 = st.columns(3)
                    c1.metric("Inputs", len(parsed.inputs))
                    c2.metric("Outputs", len(parsed.outputs))
                    c3.metric("FSM", "Detected" if parsed.fsm else "None")
                    
                    generator = RTLAwareGenerator()
                    prompt = generator.generate_prompt(parsed)
                    result = generate_with_llm(prompt)
                    
                    st.code(result, language="systemverilog")
                    st.download_button("Download", result, f"{parsed.module_name}_tb.sv", use_container_width=True)
                    
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif generate_btn:
            st.warning("Paste RTL code first")
        else:
            st.markdown("""
            <div style="color: #444; padding: 2rem; text-align: center;">
                <p style="font-size: 1rem; margin-bottom: 0.5rem;">Paste RTL code and generate</p>
                <p style="font-size: 0.85rem;">Supports Verilog and SystemVerilog</p>
            </div>
            """, unsafe_allow_html=True)

# Tab 2: Protocol Templates
with tabs[1]:
    col1, col2 = st.columns([1, 2], gap="large")
    
    with col1:
        protocol = st.selectbox("Protocol", ["APB", "AXI4-Lite", "UART", "SPI", "I2C"], label_visibility="collapsed")
        
        st.markdown("<br>", unsafe_allow_html=True)
        
        if protocol == "APB":
            addr_width = st.slider("Address Width", 8, 64, 32)
            data_width = st.slider("Data Width", 8, 64, 32)
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "AXI4-Lite":
            addr_width = st.slider("Address Width", 8, 64, 32)
            data_width = st.selectbox("Data Width", [32, 64])
            config = {"addr_width": addr_width, "data_width": data_width}
        elif protocol == "UART":
            baud = st.selectbox("Baud Rate", [9600, 19200, 38400, 57600, 115200])
            config = {"baud_rate": baud}
        elif protocol == "SPI":
            cpol = st.selectbox("CPOL", [0, 1])
            cpha = st.selectbox("CPHA", [0, 1])
            config = {"cpol": cpol, "cpha": cpha}
        else:
            speed = st.selectbox("Speed", ["Standard", "Fast", "Fast+"])
            config = {"speed": speed}
        
        st.markdown("<br>", unsafe_allow_html=True)
        gen_btn = st.button("Generate", type="primary", use_container_width=True, key="proto_gen")
    
    with col2:
        if gen_btn:
            with st.spinner("Generating..."):
                template = PROTOCOL_TEMPLATES.get(protocol.lower().replace("-", "_").replace("4_", "4"), 
                                                  PROTOCOL_TEMPLATES.get("apb", ""))
                prompt = f"""Generate a complete UVM testbench for {protocol} protocol.
Configuration: {config}
Include: interface, sequence_item, driver, monitor, agent, scoreboard, env, test, coverage.
{template}"""
                result = generate_with_llm(prompt)
                st.code(result, language="systemverilog")
                st.download_button("Download", result, f"{protocol.lower()}_tb.sv", use_container_width=True)
        else:
            st.markdown("""
            <div style="color: #444; padding: 3rem; text-align: center;">
                <p>Select a protocol and configure parameters</p>
            </div>
            """, unsafe_allow_html=True)

# Tab 3: Coverage Analysis
with tabs[2]:
    col1, col2 = st.columns([1, 1], gap="large")
    
    with col1:
        coverage_text = st.text_area(
            "Coverage Report",
            height=350,
            placeholder="Paste your coverage report here...\n\nExample:\nFunctional Coverage: 75%\n  - read_cg: 80%\n  - write_cg: 70%\n\nUncovered bins:\n  - burst_read: 0 hits",
            label_visibility="collapsed"
        )
        
        analyze_btn = st.button("Analyze", type="primary", use_container_width=True, key="cov_btn")
    
    with col2:
        if analyze_btn and coverage_text:
            with st.spinner("Analyzing..."):
                try:
                    analyzer = CoverageAnalyzer()
                    analysis = analyzer.analyze(coverage_text)
                    
                    metrics = analysis.get('metrics', {})
                    c1, c2 = st.columns(2)
                    c1.metric("Functional", f"{metrics.get('functional', 0)}%")
                    c2.metric("Code", f"{metrics.get('code', 0)}%")
                    
                    gaps = analysis.get('gaps', [])
                    if gaps:
                        st.markdown("**Gaps:**")
                        for gap in gaps:
                            st.text(f"• {gap}")
                    
                    suggestions = analysis.get('suggestions', [])
                    if suggestions:
                        st.markdown("**Suggestions:**")
                        for s in suggestions:
                            st.text(f"• {s}")
                            
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif analyze_btn:
            st.warning("Paste coverage report first")
        else:
            st.markdown("""
            <div style="color: #444; padding: 3rem; text-align: center;">
                <p>Paste coverage report to identify gaps</p>
            </div>
            """, unsafe_allow_html=True)

# Tab 4: SVA Generator
with tabs[3]:
    col1, col2 = st.columns([1, 1], gap="large")
    
    with col1:
        mode = st.radio("Input type", ["RTL Code", "Description"], horizontal=True, label_visibility="collapsed")
        
        if mode == "RTL Code":
            c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
            with c1:
                if st.button("Load APB", key="sva_apb"):
                    st.session_state['sva_input'] = SAMPLE_APB
            with c2:
                if st.button("Load AXI", key="sva_axi"):
                    st.session_state['sva_input'] = SAMPLE_AXI
            
            sva_input = st.text_area(
                "Input",
                value=st.session_state.get('sva_input', ''),
                height=320,
                placeholder="// Paste RTL code...",
                label_visibility="collapsed"
            )
        else:
            sva_input = st.text_area(
                "Input",
                height=350,
                placeholder="Describe the assertions needed:\n\n• Request acknowledged within 4 cycles\n• Data valid only when enable is high\n• After reset, outputs are zero",
                label_visibility="collapsed"
            )
        
        sva_btn = st.button("Generate Assertions", type="primary", use_container_width=True)
    
    with col2:
        if sva_btn and sva_input:
            with st.spinner("Generating..."):
                try:
                    if mode == "RTL Code":
                        parsed = parse_rtl(sva_input)
                        sva_gen = SVAGenerator()
                        assertions = sva_gen.generate_from_rtl(parsed)
                        
                        all_code = [f"// {a['name']}\n{a['code']}" for a in assertions]
                        combined = "\n\n".join(all_code)
                        
                        st.code(combined, language="systemverilog")
                        st.download_button("Download", combined, f"{parsed.module_name}_sva.sv", use_container_width=True)
                    else:
                        prompt = f"""Generate SVA assertions for:
{sva_input}

Provide property name, SVA code with ##, |=>, throughout syntax."""
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
                        st.download_button("Download", result, "assertions.sv", use_container_width=True)
                        
                except Exception as e:
                    st.error(f"Error: {str(e)}")
        elif sva_btn:
            st.warning("Provide input first")
        else:
            st.markdown("""
            <div style="color: #444; padding: 3rem; text-align: center;">
                <p>Generate protocol-aware assertions from RTL or description</p>
            </div>
            """, unsafe_allow_html=True)

# Footer
st.markdown("""
<div class="footer">
    <span>Built by Tushar Pathak</span>
    <a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank">View on GitHub</a>
</div>
""", unsafe_allow_html=True)
