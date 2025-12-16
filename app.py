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
    page_title="VerifAI - UVM Generator",
    page_icon=None,
    layout="wide",
    initial_sidebar_state="collapsed"
)

# Professional clean CSS
st.markdown("""
<style>
    /* Hide defaults */
    #MainMenu, footer, header {visibility: hidden;}
    .block-container {padding: 1.5rem 3rem 5rem; max-width: 1200px;}
    
    /* Clean light/dark theme */
    .stApp {
        background: #fafbfc;
    }
    
    /* Navigation */
    .nav {
        display: flex;
        justify-content: space-between;
        align-items: center;
        padding: 0.8rem 0;
        border-bottom: 1px solid #e1e4e8;
        margin-bottom: 2rem;
    }
    .logo {
        font-size: 1.3rem;
        font-weight: 700;
        color: #24292f;
        letter-spacing: -0.3px;
    }
    .logo span {
        color: #0969da;
    }
    .nav-links {
        display: flex;
        gap: 1.5rem;
        align-items: center;
    }
    .nav-link {
        color: #57606a;
        text-decoration: none;
        font-size: 0.9rem;
        transition: color 0.2s;
    }
    .nav-link:hover {
        color: #0969da;
    }
    
    /* Hero - compact */
    .hero {
        text-align: center;
        padding: 1.5rem 0 1rem;
    }
    .hero h1 {
        font-size: 2rem;
        font-weight: 700;
        color: #24292f;
        margin-bottom: 0.5rem;
    }
    .hero p {
        color: #57606a;
        font-size: 1rem;
        max-width: 500px;
        margin: 0 auto;
    }
    
    /* How it works */
    .steps {
        display: flex;
        justify-content: center;
        gap: 3rem;
        margin: 1.5rem 0 2rem;
        padding: 1rem 0;
    }
    .step {
        text-align: center;
        max-width: 180px;
    }
    .step-num {
        width: 28px;
        height: 28px;
        background: #0969da;
        color: white;
        border-radius: 50%;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        font-size: 0.85rem;
        font-weight: 600;
        margin-bottom: 0.5rem;
    }
    .step-title {
        font-weight: 600;
        color: #24292f;
        font-size: 0.9rem;
        margin-bottom: 0.25rem;
    }
    .step-desc {
        color: #57606a;
        font-size: 0.8rem;
    }
    
    /* Tabs */
    .stTabs [data-baseweb="tab-list"] {
        background: white;
        border: 1px solid #d0d7de;
        border-radius: 8px;
        padding: 4px;
        gap: 4px;
    }
    .stTabs [data-baseweb="tab"] {
        background: transparent;
        color: #57606a;
        padding: 0.6rem 1.2rem;
        font-size: 0.9rem;
        border-radius: 6px;
        font-weight: 500;
    }
    .stTabs [aria-selected="true"] {
        background: #0969da !important;
        color: white !important;
    }
    .stTabs [data-baseweb="tab"]:hover {
        background: #f6f8fa;
    }
    
    /* Cards */
    .card {
        background: white;
        border: 1px solid #d0d7de;
        border-radius: 8px;
        padding: 1.25rem;
    }
    .card-title {
        font-weight: 600;
        color: #24292f;
        font-size: 0.95rem;
        margin-bottom: 1rem;
        padding-bottom: 0.5rem;
        border-bottom: 1px solid #e1e4e8;
    }
    
    /* Text area */
    .stTextArea textarea {
        background: white !important;
        border: 1px solid #d0d7de !important;
        border-radius: 8px !important;
        color: #24292f !important;
        font-family: 'SF Mono', 'Monaco', monospace !important;
        font-size: 0.85rem !important;
    }
    .stTextArea textarea:focus {
        border-color: #0969da !important;
        box-shadow: 0 0 0 3px rgba(9, 105, 218, 0.1) !important;
    }
    
    /* Buttons */
    .stButton > button {
        background: #0969da !important;
        color: white !important;
        border: none !important;
        border-radius: 6px !important;
        padding: 0.6rem 1.5rem !important;
        font-weight: 600 !important;
        font-size: 0.9rem !important;
        transition: background 0.2s !important;
    }
    .stButton > button:hover {
        background: #0860ca !important;
    }
    
    /* Secondary buttons */
    div[data-testid="column"] .stButton > button {
        background: #f6f8fa !important;
        color: #24292f !important;
        border: 1px solid #d0d7de !important;
        padding: 0.4rem 0.8rem !important;
        font-size: 0.8rem !important;
        font-weight: 500 !important;
    }
    div[data-testid="column"] .stButton > button:hover {
        background: #f3f4f6 !important;
        border-color: #0969da !important;
    }
    
    /* Download button */
    .stDownloadButton > button {
        background: #2da44e !important;
        color: white !important;
        border: none !important;
    }
    .stDownloadButton > button:hover {
        background: #2c974b !important;
    }
    
    /* Code blocks */
    pre {
        background: #f6f8fa !important;
        border: 1px solid #d0d7de !important;
        border-radius: 8px !important;
    }
    
    /* Metrics */
    [data-testid="stMetricValue"] {
        color: #0969da;
        font-size: 1.5rem !important;
    }
    [data-testid="stMetricLabel"] {
        color: #57606a;
    }
    
    /* Selectbox */
    .stSelectbox > div > div {
        background: white !important;
        border: 1px solid #d0d7de !important;
        border-radius: 6px !important;
    }
    
    /* Slider */
    .stSlider > div > div > div {
        background: #0969da !important;
    }
    
    /* Success/warning */
    .stSuccess {
        background: #dafbe1 !important;
        border: 1px solid #82e596 !important;
        color: #1a7f37 !important;
        border-radius: 6px !important;
    }
    .stWarning {
        background: #fff8c5 !important;
        border: 1px solid #d4a72c !important;
        color: #9a6700 !important;
        border-radius: 6px !important;
    }
    .stInfo {
        background: #ddf4ff !important;
        border: 1px solid #54aeff !important;
        color: #0969da !important;
        border-radius: 6px !important;
    }
    .stError {
        background: #ffebe9 !important;
        border: 1px solid #ff8182 !important;
        color: #cf222e !important;
        border-radius: 6px !important;
    }
    
    /* Footer */
    .footer {
        position: fixed;
        bottom: 0;
        left: 0;
        right: 0;
        padding: 0.8rem 3rem;
        display: flex;
        justify-content: space-between;
        align-items: center;
        font-size: 0.8rem;
        background: white;
        border-top: 1px solid #e1e4e8;
    }
    .footer a {
        color: #0969da;
        text-decoration: none;
    }
    .footer a:hover {
        text-decoration: underline;
    }
    
    /* Placeholder */
    .placeholder {
        background: #f6f8fa;
        border: 1px dashed #d0d7de;
        border-radius: 8px;
        padding: 2rem;
        text-align: center;
        color: #57606a;
    }
    
    /* Analysis badge */
    .badge {
        display: inline-block;
        background: #ddf4ff;
        color: #0969da;
        padding: 0.2rem 0.6rem;
        border-radius: 12px;
        font-size: 0.75rem;
        font-weight: 500;
        margin-left: 0.5rem;
    }
    .badge-success {
        background: #dafbe1;
        color: #1a7f37;
    }
    
    /* Features bar */
    .features-bar {
        display: flex;
        justify-content: center;
        flex-wrap: wrap;
        gap: 0.5rem;
        margin-bottom: 1.5rem;
        padding: 0.75rem;
        background: white;
        border: 1px solid #d0d7de;
        border-radius: 8px;
    }
    .feature-item {
        background: #f6f8fa;
        color: #57606a;
        padding: 0.3rem 0.7rem;
        border-radius: 4px;
        font-size: 0.75rem;
        font-weight: 500;
    }
    
    /* Mobile responsiveness */
    @media (max-width: 768px) {
        .block-container {
            padding: 1rem !important;
        }
        .steps {
            flex-direction: column;
            gap: 1rem;
        }
        .hero h1 {
            font-size: 1.5rem;
        }
        .footer {
            padding: 0.8rem 1rem;
            font-size: 0.75rem;
        }
    }
    
    /* Expander */
    .streamlit-expanderHeader {
        background: #f6f8fa !important;
        border-radius: 6px !important;
        font-weight: 500;
    }
</style>
""", unsafe_allow_html=True)

# Navigation
st.markdown("""
<div class="nav">
    <div class="logo">Verif<span>AI</span></div>
    <div class="nav-links">
        <a href="#" class="nav-link">Documentation</a>
        <a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank" class="nav-link">GitHub</a>
    </div>
</div>
""", unsafe_allow_html=True)

# Hero
st.markdown("""
<div class="hero">
    <h1>UVM Testbench Generator</h1>
    <p>Generate production-ready UVM verification components from RTL code in seconds</p>
</div>
""", unsafe_allow_html=True)

# How it works - more compact
st.markdown("""
<div class="steps">
    <div class="step">
        <div class="step-num">1</div>
        <div class="step-title">Paste RTL</div>
        <div class="step-desc">Your Verilog/SV code</div>
    </div>
    <div class="step">
        <div class="step-num">2</div>
        <div class="step-title">Analyze</div>
        <div class="step-desc">Auto-detect protocol</div>
    </div>
    <div class="step">
        <div class="step-num">3</div>
        <div class="step-title">Generate</div>
        <div class="step-desc">Complete UVM testbench</div>
    </div>
</div>
""", unsafe_allow_html=True)

# What you get
st.markdown("""
<div class="features-bar">
    <span class="feature-item">Interface</span>
    <span class="feature-item">Driver</span>
    <span class="feature-item">Monitor</span>
    <span class="feature-item">Scoreboard</span>
    <span class="feature-item">Coverage</span>
    <span class="feature-item">Sequences</span>
    <span class="feature-item">Tests</span>
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
        return "Error: API key not configured. Please contact administrator."
    try:
        response = model.generate_content(prompt)
        return response.text
    except Exception as e:
        return f"Error: {str(e)}"

# Sample RTL
SAMPLE_APB = '''module apb_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input  wire                    pclk,
    input  wire                    presetn,
    input  wire                    psel,
    input  wire                    penable,
    input  wire                    pwrite,
    input  wire [ADDR_WIDTH-1:0]   paddr,
    input  wire [DATA_WIDTH-1:0]   pwdata,
    output reg  [DATA_WIDTH-1:0]   prdata,
    output reg                     pready,
    output reg                     pslverr
);
    // Memory array
    reg [DATA_WIDTH-1:0] mem [0:255];
    
    // FSM States
    localparam IDLE   = 2'b00;
    localparam SETUP  = 2'b01;
    localparam ACCESS = 2'b10;
    
    reg [1:0] state, next_state;
    
    // State register
    always @(posedge pclk or negedge presetn) begin
        if (!presetn)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always @(*) begin
        case (state)
            IDLE:    next_state = psel ? SETUP : IDLE;
            SETUP:   next_state = ACCESS;
            ACCESS:  next_state = psel ? SETUP : IDLE;
            default: next_state = IDLE;
        endcase
    end
    
    // Output logic
    always @(posedge pclk or negedge presetn) begin
        if (!presetn) begin
            prdata  <= {DATA_WIDTH{1'b0}};
            pready  <= 1'b0;
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

SAMPLE_AXI = '''module axi_lite_slave #(
    parameter ADDR_WIDTH = 32,
    parameter DATA_WIDTH = 32
)(
    input  wire                    aclk,
    input  wire                    aresetn,
    // Write Address Channel
    input  wire                    awvalid,
    output reg                     awready,
    input  wire [ADDR_WIDTH-1:0]   awaddr,
    // Write Data Channel
    input  wire                    wvalid,
    output reg                     wready,
    input  wire [DATA_WIDTH-1:0]   wdata,
    input  wire [DATA_WIDTH/8-1:0] wstrb,
    // Write Response Channel
    output reg                     bvalid,
    input  wire                    bready,
    output reg  [1:0]              bresp,
    // Read Address Channel
    input  wire                    arvalid,
    output reg                     arready,
    input  wire [ADDR_WIDTH-1:0]   araddr,
    // Read Data Channel
    output reg                     rvalid,
    input  wire                    rready,
    output reg  [DATA_WIDTH-1:0]   rdata,
    output reg  [1:0]              rresp
);
    // Register file
    reg [DATA_WIDTH-1:0] registers [0:15];
    
    // Write FSM
    localparam W_IDLE = 2'b00;
    localparam W_DATA = 2'b01;
    localparam W_RESP = 2'b10;
    
    reg [1:0] w_state;
    reg [ADDR_WIDTH-1:0] w_addr;
endmodule'''

# Tabs
tabs = st.tabs(["RTL to Testbench", "Protocol Templates", "Coverage Analysis", "SVA Assertions"])

# Tab 1: RTL to Testbench
with tabs[0]:
    col1, col2 = st.columns([1, 1], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Input RTL Code</div>', unsafe_allow_html=True)
        
        # Sample buttons
        c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
        with c1:
            if st.button("Load APB Example", key="ex_apb", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_APB
        with c2:
            if st.button("Load AXI Example", key="ex_axi", use_container_width=True):
                st.session_state['rtl_input'] = SAMPLE_AXI
        
        rtl_code = st.text_area(
            "RTL",
            value=st.session_state.get('rtl_input', ''),
            height=400,
            placeholder="// Paste your Verilog/SystemVerilog RTL here\n// We'll auto-detect the protocol and generate a matching UVM testbench",
            label_visibility="collapsed"
        )
        
        if st.button("Generate Testbench", type="primary", use_container_width=True, key="gen_tb"):
            if rtl_code.strip():
                with st.spinner("Analyzing RTL and generating testbench..."):
                    try:
                        parsed = parse_rtl(rtl_code)
                        st.session_state['parsed'] = parsed
                        
                        generator = RTLAwareGenerator()
                        prompt = generator.generate_prompt(parsed)
                        result = generate_with_llm(prompt)
                        st.session_state['tb_result'] = result
                        st.session_state['gen_success'] = True
                    except Exception as e:
                        st.session_state['gen_error'] = str(e)
                        st.session_state['gen_success'] = False
            else:
                st.warning("Please paste your RTL code first")
    
    with col2:
        st.markdown('<div class="card-title">Generated Output</div>', unsafe_allow_html=True)
        
        if st.session_state.get('gen_success') and st.session_state.get('parsed'):
            parsed = st.session_state['parsed']
            
            # Analysis summary with protocol detection
            protocol_info = ""
            if hasattr(parsed, 'complexity') and parsed.complexity:
                protocol = parsed.complexity.detected_protocol
                confidence = parsed.complexity.protocol_confidence
                if protocol != "generic":
                    protocol_info = f" - Detected **{protocol.upper()}** ({int(confidence*100)}% confidence)"
            
            st.success(f"Analyzed **{parsed.module_name}**{protocol_info}")
            
            # Metrics row - enhanced
            c1, c2, c3, c4 = st.columns(4)
            c1.metric("Inputs", len(parsed.inputs))
            c2.metric("Outputs", len(parsed.outputs))
            
            if hasattr(parsed, 'complexity') and parsed.complexity:
                c3.metric("Complexity", parsed.complexity.complexity_score.title())
                c4.metric("Est. Coverage Pts", parsed.complexity.estimated_coverage_points)
            else:
                c3.metric("Clocks", len(parsed.clocks) if parsed.clocks else 0)
                c4.metric("FSM", "Yes" if parsed.fsm else "No")
            
            # Show detected info - enhanced
            with st.expander("View Analysis Details"):
                if parsed.clocks:
                    st.write(f"**Clock signals:** `{', '.join(parsed.clocks)}`")
                if parsed.resets:
                    st.write(f"**Reset signals:** `{', '.join(parsed.resets)}`")
                if parsed.fsm:
                    states = parsed.fsm.get('states', [])
                    if states:
                        st.write(f"**FSM States:** {', '.join(states)}")
                st.write(f"**Input signals:** `{', '.join(parsed.inputs[:5])}{'...' if len(parsed.inputs) > 5 else ''}`")
                st.write(f"**Output signals:** `{', '.join(parsed.outputs[:5])}{'...' if len(parsed.outputs) > 5 else ''}`")
                
                # Show complexity details
                if hasattr(parsed, 'complexity') and parsed.complexity:
                    cx = parsed.complexity
                    st.write(f"**Data Width:** {cx.data_width} bits")
                    st.write(f"**Address Width:** {cx.addr_width} bits")
                    if cx.fsm_states > 0:
                        st.write(f"**FSM States:** {cx.fsm_states}")
            
            # Verification Checklist
            if hasattr(parsed, 'checklist') and parsed.checklist:
                with st.expander("Verification Checklist"):
                    cl = parsed.checklist
                    
                    st.markdown("**Reset Tests:**")
                    for test in cl.reset_tests[:3]:
                        st.markdown(f"- {test}")
                    
                    st.markdown("**Protocol Tests:**")
                    for test in cl.protocol_tests[:4]:
                        st.markdown(f"- {test}")
                    
                    if cl.fsm_tests and cl.fsm_tests[0] != "No FSM detected - verify sequential logic":
                        st.markdown("**FSM Tests:**")
                        for test in cl.fsm_tests[:3]:
                            st.markdown(f"- {test}")
                    
                    st.markdown("**Edge Cases:**")
                    for test in cl.edge_cases[:3]:
                        st.markdown(f"- {test}")
            
            # Generated code
            if st.session_state.get('tb_result'):
                st.code(st.session_state['tb_result'], language="systemverilog")
                
                c1, c2 = st.columns(2)
                with c1:
                    st.download_button(
                        "Download Testbench",
                        st.session_state['tb_result'],
                        f"{parsed.module_name}_tb.sv",
                        use_container_width=True
                    )
        
        elif st.session_state.get('gen_error'):
            st.error(f"Error: {st.session_state['gen_error']}")
            st.info("Make sure your RTL code is valid Verilog or SystemVerilog")
        
        else:
            st.markdown("""
            <div class="placeholder">
                <p><strong>Generated testbench will appear here</strong></p>
                <p style="font-size: 0.85rem; margin-top: 0.5rem; margin-bottom: 1rem;">
                    Includes: interface, driver, monitor, agent, scoreboard, env, coverage, and test
                </p>
                <pre style="text-align: left; font-size: 0.75rem; background: #f6f8fa; padding: 1rem; border-radius: 6px; overflow-x: auto;">
<span style="color: #6a737d;">// Example output preview:</span>
<span style="color: #d73a49;">interface</span> apb_if(<span style="color: #d73a49;">input logic</span> pclk);
  <span style="color: #d73a49;">logic</span> psel, penable, pwrite;
  <span style="color: #d73a49;">logic</span> [31:0] paddr, pwdata, prdata;
  ...
<span style="color: #d73a49;">endinterface</span>

<span style="color: #d73a49;">class</span> apb_driver <span style="color: #d73a49;">extends</span> uvm_driver;
  ...
<span style="color: #d73a49;">endclass</span></pre>
            </div>
            """, unsafe_allow_html=True)

# Tab 2: Protocol Templates
with tabs[1]:
    col1, col2 = st.columns([1, 2], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Protocol Configuration</div>', unsafe_allow_html=True)
        
        protocol = st.selectbox("Select Protocol", ["APB", "AXI4-Lite", "UART", "SPI", "I2C"])
        
        st.markdown("**Parameters:**")
        
        if protocol == "APB":
            addr_w = st.select_slider("Address Width (bits)", [8, 12, 16, 20, 24, 32], value=32)
            data_w = st.select_slider("Data Width (bits)", [8, 16, 32], value=32)
            config = {"addr_width": addr_w, "data_width": data_w, "protocol": "APB"}
        elif protocol == "AXI4-Lite":
            addr_w = st.select_slider("Address Width (bits)", [8, 12, 16, 20, 24, 32], value=32)
            data_w = st.selectbox("Data Width (bits)", [32, 64])
            config = {"addr_width": addr_w, "data_width": data_w, "protocol": "AXI4-Lite"}
        elif protocol == "UART":
            baud = st.selectbox("Baud Rate", [9600, 19200, 38400, 57600, 115200])
            parity = st.selectbox("Parity", ["None", "Even", "Odd"])
            config = {"baud_rate": baud, "parity": parity, "protocol": "UART"}
        elif protocol == "SPI":
            mode = st.selectbox("SPI Mode", [0, 1, 2, 3])
            width = st.select_slider("Data Width (bits)", [8, 16, 32], value=8)
            config = {"mode": mode, "data_width": width, "protocol": "SPI"}
        else:  # I2C
            speed = st.selectbox("Speed Mode", ["Standard (100kHz)", "Fast (400kHz)", "Fast+ (1MHz)"])
            addr_mode = st.selectbox("Address Mode", ["7-bit", "10-bit"])
            config = {"speed": speed, "addr_mode": addr_mode, "protocol": "I2C"}
        
        st.markdown("")
        if st.button("Generate", type="primary", use_container_width=True, key="gen_proto"):
            with st.spinner(f"Generating {protocol} testbench..."):
                template = PROTOCOL_TEMPLATES.get(protocol.lower().replace("-", "_").replace("4_", "4"), 
                                                  PROTOCOL_TEMPLATES.get("apb", ""))
                prompt = f"""Generate a complete, production-ready UVM testbench for {protocol} protocol.

Configuration: {config}

Include these components with full implementation:
1. Interface with clocking blocks
2. Transaction/sequence_item class
3. Driver with proper protocol timing
4. Monitor with coverage sampling
5. Agent (active/passive configurable)
6. Scoreboard with checking
7. Environment
8. Coverage collector with functional coverage
9. Base test and example test sequence

Use UVM 1.2 methodology. Add comments explaining key sections.
{template}"""
                result = generate_with_llm(prompt)
                st.session_state['proto_result'] = result
    
    with col2:
        st.markdown('<div class="card-title">Generated Testbench</div>', unsafe_allow_html=True)
        
        if st.session_state.get('proto_result'):
            st.code(st.session_state['proto_result'], language="systemverilog")
            st.download_button(
                "Download Testbench",
                st.session_state['proto_result'],
                f"{protocol.lower().replace('-', '_')}_uvm_tb.sv",
                use_container_width=True
            )
        else:
            st.markdown(f"""
            <div class="placeholder">
                <p><strong>Select a protocol and configure parameters</strong></p>
                <p style="font-size: 0.85rem; margin-top: 0.5rem;">
                    Generates complete UVM testbench with all components
                </p>
            </div>
            """, unsafe_allow_html=True)

# Tab 3: Coverage Analysis
with tabs[2]:
    col1, col2 = st.columns([1, 1], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Coverage Report Input</div>', unsafe_allow_html=True)
        
        st.markdown("Paste your coverage report to identify gaps and get suggestions for improving coverage.")
        
        cov_text = st.text_area(
            "Coverage",
            height=350,
            placeholder="""Example format:

=== Functional Coverage Report ===
Total: 75%

Group: apb_cg
  - read_cp: 85%
  - write_cp: 70%
  - burst_cp: 45%
  - error_cp: 20%

Uncovered bins:
  - burst_cp.burst_4: 0 hits
  - error_cp.timeout: 0 hits""",
            label_visibility="collapsed"
        )
        
        if st.button("Analyze Coverage", type="primary", use_container_width=True, key="analyze"):
            if cov_text.strip():
                with st.spinner("Analyzing coverage report..."):
                    try:
                        analyzer = CoverageAnalyzer()
                        analysis = analyzer.analyze(cov_text)
                        st.session_state['cov_result'] = analysis
                    except Exception as e:
                        st.error(f"Error analyzing coverage: {str(e)}")
            else:
                st.warning("Please paste your coverage report first")
    
    with col2:
        st.markdown('<div class="card-title">Analysis Results</div>', unsafe_allow_html=True)
        
        if st.session_state.get('cov_result'):
            analysis = st.session_state['cov_result']
            metrics = analysis.get('metrics', {})
            
            # Metrics
            c1, c2 = st.columns(2)
            func_cov = metrics.get('functional', 0)
            code_cov = metrics.get('code', 0)
            c1.metric("Functional Coverage", f"{func_cov}%", 
                      delta=f"{func_cov-100}% from goal" if func_cov < 100 else "Goal met!")
            c2.metric("Code Coverage", f"{code_cov}%",
                      delta=f"{code_cov-100}% from goal" if code_cov < 100 else "Goal met!")
            
            # Gaps
            gaps = analysis.get('gaps', [])
            if gaps:
                st.markdown("**Coverage Gaps Identified:**")
                for gap in gaps:
                    st.warning(gap)
            
            # Suggestions
            suggestions = analysis.get('suggestions', [])
            if suggestions:
                st.markdown("**Recommended Actions:**")
                for i, s in enumerate(suggestions, 1):
                    st.info(f"{i}. {s}")
            
            # Generate tests button
            if gaps:
                if st.button("Generate Tests for Gaps", use_container_width=True, key="gen_cov_tests"):
                    with st.spinner("Generating test sequences..."):
                        prompt = f"""Generate UVM test sequences to cover these gaps:
{gaps}

Create targeted sequences that will hit the uncovered bins."""
                        result = generate_with_llm(prompt)
                        st.code(result, language="systemverilog")
        else:
            st.markdown("""
            <div class="placeholder">
                <p><strong>Coverage analysis will appear here</strong></p>
                <p style="font-size: 0.85rem; margin-top: 0.5rem;">
                    Identifies gaps and suggests tests to improve coverage
                </p>
            </div>
            """, unsafe_allow_html=True)

# Tab 4: SVA Generator
with tabs[3]:
    col1, col2 = st.columns([1, 1], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Assertion Input</div>', unsafe_allow_html=True)
        
        mode = st.radio("Input Type", ["From RTL Code", "From Description"], horizontal=True)
        
        if mode == "From RTL Code":
            c1, c2, c3, c4 = st.columns([1, 1, 1, 1])
            with c1:
                if st.button("Load APB", key="sva_apb"):
                    st.session_state['sva_input'] = SAMPLE_APB
            with c2:
                if st.button("Load AXI", key="sva_axi"):
                    st.session_state['sva_input'] = SAMPLE_AXI
            
            sva_input = st.text_area(
                "RTL",
                value=st.session_state.get('sva_input', ''),
                height=320,
                placeholder="// Paste RTL code to generate protocol-aware assertions",
                label_visibility="collapsed"
            )
        else:
            sva_input = st.text_area(
                "Description",
                height=350,
                placeholder="""Describe the assertions you need:

- Request must be acknowledged within 4 clock cycles
- Data valid signal should only be high when enable is asserted
- After reset, all outputs should be zero for at least 2 cycles
- Back-to-back transactions must have 1 cycle gap
- FIFO full flag should prevent writes""",
                label_visibility="collapsed"
            )
        
        if st.button("Generate Assertions", type="primary", use_container_width=True, key="gen_sva"):
            if sva_input.strip():
                with st.spinner("Generating SVA assertions..."):
                    try:
                        if mode == "From RTL Code":
                            parsed = parse_rtl(sva_input)
                            sva_gen = SVAGenerator()
                            assertions = sva_gen.generate_from_rtl(parsed)
                            combined = "\n\n".join([f"// {a['name']}: {a.get('description', '')}\n{a['code']}" for a in assertions])
                            st.session_state['sva_result'] = combined
                            st.session_state['sva_module'] = parsed.module_name
                            st.session_state['sva_count'] = len(assertions)
                        else:
                            prompt = f"""Generate SystemVerilog Assertions (SVA) for these requirements:

{sva_input}

For each assertion, provide:
1. Property name (descriptive)
2. SVA property using proper syntax (##, |=>, |->)
3. Assert and cover directives
4. Brief comment explaining what it checks

Use immediate and concurrent assertions as appropriate."""
                            result = generate_with_llm(prompt)
                            st.session_state['sva_result'] = result
                            st.session_state['sva_module'] = "custom"
                            st.session_state['sva_count'] = result.count('assert property') + result.count('assert(')
                    except Exception as e:
                        st.error(f"Error: {str(e)}")
            else:
                st.warning("Please provide input first")
    
    with col2:
        st.markdown('<div class="card-title">Generated Assertions</div>', unsafe_allow_html=True)
        
        if st.session_state.get('sva_result'):
            count = st.session_state.get('sva_count', 0)
            st.success(f"Generated {count} assertions")
            
            st.code(st.session_state['sva_result'], language="systemverilog")
            st.download_button(
                "Download Assertions",
                st.session_state['sva_result'],
                f"{st.session_state.get('sva_module', 'assertions')}_sva.sv",
                use_container_width=True
            )
        else:
            st.markdown("""
            <div class="placeholder">
                <p><strong>SVA assertions will appear here</strong></p>
                <p style="font-size: 0.85rem; margin-top: 0.5rem;">
                    Generates protocol-aware assertions from RTL or natural language
                </p>
            </div>
            """, unsafe_allow_html=True)

# Footer
st.markdown("""
<div class="footer">
    <span style="color: #57606a;">Built by Tushar Pathak</span>
    <a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank">View on GitHub</a>
</div>
""", unsafe_allow_html=True)
