"""
VerifAI - UVM Testbench Generator
"""

import streamlit as st
import streamlit.components.v1 as components
import os
import io
import zipfile
import json
import re
import time
import hashlib
from datetime import datetime
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

# Initialize session state for new features
if 'dark_mode' not in st.session_state:
    st.session_state['dark_mode'] = False
if 'generation_history' not in st.session_state:
    st.session_state['generation_history'] = []
if 'favorite_templates' not in st.session_state:
    st.session_state['favorite_templates'] = []
if 'generation_stats' not in st.session_state:
    st.session_state['generation_stats'] = {'total': 0, 'protocols': {}, 'avg_time': 0}

# Theme colors based on dark mode
def get_theme_colors():
    if st.session_state.get('dark_mode', False):
        return {
            'bg': '#0d1117',
            'card': '#161b22',
            'border': '#30363d',
            'text': '#c9d1d9',
            'text_muted': '#8b949e',
            'primary': '#58a6ff',
            'success': '#3fb950',
            'warning': '#d29922',
            'error': '#f85149'
        }
    return {
        'bg': '#fafbfc',
        'card': '#ffffff',
        'border': '#d0d7de',
        'text': '#24292f',
        'text_muted': '#57606a',
        'primary': '#0969da',
        'success': '#2da44e',
        'warning': '#d4a72c',
        'error': '#cf222e'
    }

theme = get_theme_colors()

# Professional clean CSS with dynamic theming
st.markdown(f"""
<style>
    /* Hide defaults */
    #MainMenu, footer, header {{visibility: hidden;}}
    .block-container {{padding: 1.5rem 3rem 5rem; max-width: 1200px;}}
    
    /* Theme-aware styling */
    .stApp {{
        background: {theme['bg']};
    }}
    
    /* Navigation */
    .nav {{
        display: flex;
        justify-content: space-between;
        align-items: center;
        padding: 0.8rem 0;
        border-bottom: 1px solid {theme['border']};
        margin-bottom: 2rem;
    }}
    .logo {{
        font-size: 1.3rem;
        font-weight: 700;
        color: {theme['text']};
        letter-spacing: -0.3px;
    }}
    .logo span {{
        color: {theme['primary']};
    }}
    .nav-links {{
        display: flex;
        gap: 1.5rem;
        align-items: center;
    }}
    .nav-link {{
        color: {theme['text_muted']};
        text-decoration: none;
        font-size: 0.9rem;
        transition: color 0.2s;
    }}
    .nav-link:hover {{
        color: {theme['primary']};
    }}
    
    /* Theme toggle button */
    .theme-toggle {{
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 20px;
        padding: 0.4rem 0.8rem;
        font-size: 0.8rem;
        cursor: pointer;
        display: inline-flex;
        align-items: center;
        gap: 0.3rem;
        color: {theme['text_muted']};
        transition: all 0.2s;
    }}
    .theme-toggle:hover {{
        border-color: {theme['primary']};
        color: {theme['primary']};
    }}
    
    /* Hero - compact */
    .hero {{
        text-align: center;
        padding: 1.5rem 0 1rem;
    }}
    .hero h1 {{
        font-size: 2rem;
        font-weight: 700;
        color: {theme['text']};
        margin-bottom: 0.5rem;
    }}
    .hero p {{
        color: {theme['text_muted']};
        font-size: 1rem;
        max-width: 500px;
        margin: 0 auto;
    }}
    
    /* How it works */
    .steps {{
        display: flex;
        justify-content: center;
        gap: 3rem;
        margin: 1.5rem 0 2rem;
        padding: 1rem 0;
    }}
    .step {{
        text-align: center;
        max-width: 180px;
    }}
    .step-num {{
        width: 28px;
        height: 28px;
        background: {theme['primary']};
        color: white;
        border-radius: 50%;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        font-size: 0.85rem;
        font-weight: 600;
        margin-bottom: 0.5rem;
    }}
    .step-title {{
        font-weight: 600;
        color: {theme['text']};
        font-size: 0.9rem;
        margin-bottom: 0.25rem;
    }}
    .step-desc {{
        color: {theme['text_muted']};
        font-size: 0.8rem;
    }}
    
    /* Tabs */
    .stTabs [data-baseweb="tab-list"] {{
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 8px;
        padding: 4px;
        gap: 4px;
    }}
    .stTabs [data-baseweb="tab"] {{
        background: transparent;
        color: {theme['text_muted']};
        padding: 0.6rem 1.2rem;
        font-size: 0.9rem;
        border-radius: 6px;
        font-weight: 500;
    }}
    .stTabs [aria-selected="true"] {{
        background: {theme['primary']} !important;
        color: white !important;
    }}
    .stTabs [data-baseweb="tab"]:hover {{
        background: {theme['bg']};
    }}
    
    /* Cards */
    .card {{
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 8px;
        padding: 1.25rem;
    }}
    .card-title {{
        font-weight: 600;
        color: {theme['text']};
        font-size: 0.95rem;
        margin-bottom: 1rem;
        padding-bottom: 0.5rem;
        border-bottom: 1px solid {theme['border']};
    }}
    
    /* Text area */
    .stTextArea textarea {{
        background: {theme['card']} !important;
        border: 1px solid {theme['border']} !important;
        border-radius: 8px !important;
        color: {theme['text']} !important;
        font-family: 'SF Mono', 'Monaco', monospace !important;
        font-size: 0.85rem !important;
    }}
    .stTextArea textarea:focus {{
        border-color: {theme['primary']} !important;
        box-shadow: 0 0 0 3px rgba(9, 105, 218, 0.1) !important;
    }}
    
    /* Buttons */
    .stButton > button {{
        background: {theme['primary']} !important;
        color: white !important;
        border: none !important;
        border-radius: 6px !important;
        padding: 0.6rem 1.5rem !important;
        font-weight: 600 !important;
        font-size: 0.9rem !important;
        transition: all 0.2s !important;
    }}
    .stButton > button:hover {{
        filter: brightness(0.9) !important;
        transform: translateY(-1px);
    }}
    
    /* Secondary buttons */
    div[data-testid="column"] .stButton > button {{
        background: {theme['bg']} !important;
        color: {theme['text']} !important;
        border: 1px solid {theme['border']} !important;
        padding: 0.4rem 0.8rem !important;
        font-size: 0.8rem !important;
        font-weight: 500 !important;
    }}
    div[data-testid="column"] .stButton > button:hover {{
        background: {theme['card']} !important;
        border-color: {theme['primary']} !important;
    }}
    
    /* Download button */
    .stDownloadButton > button {{
        background: {theme['success']} !important;
        color: white !important;
        border: none !important;
    }}
    .stDownloadButton > button:hover {{
        filter: brightness(0.9) !important;
    }}
    
    /* Code blocks */
    pre {{
        background: {theme['bg']} !important;
        border: 1px solid {theme['border']} !important;
        border-radius: 8px !important;
    }}
    
    /* Metrics */
    [data-testid="stMetricValue"] {{
        color: {theme['primary']};
        font-size: 1.5rem !important;
    }}
    [data-testid="stMetricLabel"] {{
        color: {theme['text_muted']};
    }}
    
    /* Selectbox */
    .stSelectbox > div > div {{
        background: {theme['card']} !important;
        border: 1px solid {theme['border']} !important;
        border-radius: 6px !important;
    }}
    
    /* Slider */
    .stSlider > div > div > div {{
        background: {theme['primary']} !important;
    }}
    
    /* Alerts */
    .stSuccess {{
        background: {theme['success']}20 !important;
        border: 1px solid {theme['success']}80 !important;
        color: {theme['success']} !important;
        border-radius: 6px !important;
    }}
    .stWarning {{
        background: {theme['warning']}20 !important;
        border: 1px solid {theme['warning']}80 !important;
        color: {theme['warning']} !important;
        border-radius: 6px !important;
    }}
    .stInfo {{
        background: {theme['primary']}20 !important;
        border: 1px solid {theme['primary']}80 !important;
        color: {theme['primary']} !important;
        border-radius: 6px !important;
    }}
    .stError {{
        background: {theme['error']}20 !important;
        border: 1px solid {theme['error']}80 !important;
        color: {theme['error']} !important;
        border-radius: 6px !important;
    }}
    
    /* Footer */
    .footer {{
        position: fixed;
        bottom: 0;
        left: 0;
        right: 0;
        padding: 0.8rem 3rem;
        display: flex;
        justify-content: space-between;
        align-items: center;
        font-size: 0.8rem;
        background: {theme['card']};
        border-top: 1px solid {theme['border']};
    }}
    .footer a {{
        color: {theme['primary']};
        text-decoration: none;
    }}
    .footer a:hover {{
        text-decoration: underline;
    }}
    
    /* Placeholder */
    .placeholder {{
        background: {theme['bg']};
        border: 1px dashed {theme['border']};
        border-radius: 8px;
        padding: 2rem;
        text-align: center;
        color: {theme['text_muted']};
    }}
    
    /* Analysis badge */
    .badge {{
        display: inline-block;
        background: {theme['primary']}20;
        color: {theme['primary']};
        padding: 0.2rem 0.6rem;
        border-radius: 12px;
        font-size: 0.75rem;
        font-weight: 500;
        margin-left: 0.5rem;
    }}
    .badge-success {{
        background: {theme['success']}20;
        color: {theme['success']};
    }}
    
    /* Features bar */
    .features-bar {{
        display: flex;
        justify-content: center;
        flex-wrap: wrap;
        gap: 0.5rem;
        margin-bottom: 1.5rem;
        padding: 0.75rem;
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 8px;
    }}
    .feature-item {{
        background: {theme['bg']};
        color: {theme['text_muted']};
        padding: 0.3rem 0.7rem;
        border-radius: 4px;
        font-size: 0.75rem;
        font-weight: 500;
    }}
    
    /* Waveform diagram styling */
    .waveform-container {{
        background: #1e1e1e;
        color: #00ff00;
        font-family: 'SF Mono', 'Monaco', 'Consolas', monospace;
        font-size: 0.7rem;
        line-height: 1.2;
        padding: 1rem;
        border-radius: 8px;
        overflow-x: auto;
        white-space: pre;
        border: 1px solid #333;
    }}
    .waveform-title {{
        color: #00ff00;
        font-weight: bold;
        margin-bottom: 0.5rem;
    }}
    
    /* Constraint code styling */
    .constraint-box {{
        background: {theme['bg']};
        border: 1px solid {theme['border']};
        border-radius: 6px;
        padding: 0.75rem;
        margin-bottom: 0.5rem;
    }}
    .constraint-title {{
        font-weight: 600;
        color: {theme['text']};
        font-size: 0.85rem;
        margin-bottom: 0.25rem;
    }}
    .constraint-desc {{
        color: {theme['text_muted']};
        font-size: 0.75rem;
        margin-bottom: 0.5rem;
    }}
    
    /* Mobile responsiveness */
    @media (max-width: 768px) {{
        .block-container {{
            padding: 1rem !important;
        }}
        .steps {{
            flex-direction: column;
            gap: 1rem;
        }}
        .hero h1 {{
            font-size: 1.5rem;
        }}
        .footer {{
            padding: 0.8rem 1rem;
            font-size: 0.75rem;
        }}
    }}
    
    /* Expander */
    .streamlit-expanderHeader {{
        background: {theme['bg']} !important;
        border-radius: 6px !important;
        font-weight: 500;
    }}
    
    /* Quality Score Gauge */
    .quality-gauge {{
        text-align: center;
        padding: 1rem;
    }}
    .score-circle {{
        width: 80px;
        height: 80px;
        border-radius: 50%;
        display: inline-flex;
        align-items: center;
        justify-content: center;
        font-size: 1.5rem;
        font-weight: 700;
        color: white;
        margin-bottom: 0.5rem;
    }}
    .score-high {{ background: linear-gradient(135deg, {theme['success']}, #1a7f37); }}
    .score-medium {{ background: linear-gradient(135deg, {theme['warning']}, #9a6700); }}
    .score-low {{ background: linear-gradient(135deg, {theme['error']}, #a40e26); }}
    
    /* Bug prediction card */
    .bug-card {{
        background: {theme['warning']}20;
        border: 1px solid {theme['warning']}80;
        border-radius: 8px;
        padding: 0.75rem 1rem;
        margin-bottom: 0.5rem;
    }}
    .bug-card-high {{
        background: {theme['error']}20;
        border-color: {theme['error']}80;
    }}
    .bug-title {{
        font-weight: 600;
        color: {theme['warning']};
        font-size: 0.85rem;
    }}
    .bug-card-high .bug-title {{
        color: {theme['error']};
    }}
    .bug-desc {{
        color: {theme['text_muted']};
        font-size: 0.8rem;
        margin-top: 0.25rem;
    }}
    
    /* Stats grid */
    .stats-grid {{
        display: grid;
        grid-template-columns: repeat(4, 1fr);
        gap: 0.75rem;
        margin-bottom: 1rem;
    }}
    .stat-box {{
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 8px;
        padding: 0.75rem;
        text-align: center;
    }}
    .stat-value {{
        font-size: 1.25rem;
        font-weight: 700;
        color: {theme['primary']};
    }}
    .stat-label {{
        font-size: 0.7rem;
        color: {theme['text_muted']};
        text-transform: uppercase;
        letter-spacing: 0.5px;
    }}
    
    /* Copy button */
    .copy-btn {{
        position: relative;
        display: inline-flex;
        align-items: center;
        gap: 0.3rem;
        background: {theme['bg']};
        border: 1px solid {theme['border']};
        border-radius: 4px;
        padding: 0.3rem 0.6rem;
        font-size: 0.75rem;
        cursor: pointer;
        color: {theme['text_muted']};
        transition: all 0.2s;
    }}
    .copy-btn:hover {{
        background: {theme['card']};
        color: {theme['primary']};
        border-color: {theme['primary']};
    }}
    
    /* History item */
    .history-item {{
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 8px;
        padding: 0.75rem 1rem;
        margin-bottom: 0.5rem;
        display: flex;
        justify-content: space-between;
        align-items: center;
        transition: all 0.2s;
    }}
    .history-item:hover {{
        border-color: {theme['primary']};
        box-shadow: 0 2px 8px rgba(0,0,0,0.05);
    }}
    .history-name {{
        font-weight: 600;
        color: {theme['text']};
        font-size: 0.9rem;
    }}
    .history-meta {{
        color: {theme['text_muted']};
        font-size: 0.75rem;
        margin-top: 0.2rem;
    }}
    .history-time {{
        color: {theme['text_muted']};
        font-size: 0.75rem;
    }}
    
    /* Protocol comparison table */
    .proto-table {{
        width: 100%;
        border-collapse: collapse;
        font-size: 0.85rem;
    }}
    .proto-table th, .proto-table td {{
        padding: 0.6rem;
        text-align: left;
        border-bottom: 1px solid {theme['border']};
    }}
    .proto-table th {{
        background: {theme['bg']};
        font-weight: 600;
        color: {theme['text']};
    }}
    .proto-table td {{
        color: {theme['text_muted']};
    }}
    .proto-check {{ color: {theme['success']}; }}
    .proto-x {{ color: {theme['error']}; }}
    
    /* Keyboard shortcuts */
    .kbd {{
        display: inline-block;
        background: {theme['bg']};
        border: 1px solid {theme['border']};
        border-radius: 4px;
        padding: 0.1rem 0.4rem;
        font-size: 0.75rem;
        font-family: monospace;
        color: {theme['text_muted']};
    }}
    
    /* Syntax validation indicator */
    .syntax-valid {{
        color: {theme['success']};
        font-size: 0.8rem;
        display: inline-flex;
        align-items: center;
        gap: 0.3rem;
    }}
    .syntax-invalid {{
        color: {theme['error']};
        font-size: 0.8rem;
        display: inline-flex;
        align-items: center;
        gap: 0.3rem;
    }}
    
    /* Performance metrics bar */
    .perf-bar {{
        display: flex;
        gap: 1rem;
        padding: 0.5rem 1rem;
        background: {theme['card']};
        border: 1px solid {theme['border']};
        border-radius: 6px;
        margin-top: 1rem;
        font-size: 0.8rem;
    }}
    .perf-item {{
        display: flex;
        align-items: center;
        gap: 0.3rem;
        color: {theme['text_muted']};
    }}
    .perf-value {{
        font-weight: 600;
        color: {theme['primary']};
    }}
</style>
""", unsafe_allow_html=True)

# ============== HELPER FUNCTIONS ==============

def validate_rtl_syntax(code: str) -> dict:
    """Basic RTL syntax validation"""
    errors = []
    warnings = []
    
    if not code.strip():
        return {'valid': False, 'errors': ['Empty code'], 'warnings': []}
    
    # Check for module declaration
    if not re.search(r'\bmodule\s+\w+', code):
        errors.append("Missing module declaration")
    
    # Check for endmodule
    if 'module' in code.lower() and 'endmodule' not in code.lower():
        errors.append("Missing 'endmodule' keyword")
    
    # Check balanced parentheses
    if code.count('(') != code.count(')'):
        errors.append("Unbalanced parentheses")
    
    # Check balanced braces
    if code.count('{') != code.count('}'):
        errors.append("Unbalanced braces")
    
    # Check balanced begin/end
    begin_count = len(re.findall(r'\bbegin\b', code))
    end_count = len(re.findall(r'\bend\b', code))
    if begin_count != end_count:
        warnings.append(f"Possible unbalanced begin/end ({begin_count} begin, {end_count} end)")
    
    # Check for common typos
    if re.search(r'\bwire\s+reg\b|\breg\s+wire\b', code):
        errors.append("Invalid signal type combination")
    
    return {
        'valid': len(errors) == 0,
        'errors': errors,
        'warnings': warnings
    }

def add_to_history(name: str, protocol: str, code: str, generation_time: float):
    """Add generation to history"""
    history_item = {
        'id': hashlib.md5(f"{name}{datetime.now()}".encode()).hexdigest()[:8],
        'name': name,
        'protocol': protocol,
        'code': code,
        'timestamp': datetime.now().isoformat(),
        'time_display': datetime.now().strftime("%I:%M %p"),
        'generation_time': round(generation_time, 2)
    }
    
    # Keep only last 10 items
    history = st.session_state.get('generation_history', [])
    history.insert(0, history_item)
    st.session_state['generation_history'] = history[:10]
    
    # Update stats
    stats = st.session_state.get('generation_stats', {'total': 0, 'protocols': {}, 'avg_time': 0})
    stats['total'] += 1
    stats['protocols'][protocol] = stats['protocols'].get(protocol, 0) + 1
    total_time = stats['avg_time'] * (stats['total'] - 1) + generation_time
    stats['avg_time'] = total_time / stats['total']
    st.session_state['generation_stats'] = stats

def get_protocol_comparison():
    """Return protocol comparison data"""
    return {
        'APB': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Config registers'},
        'AXI4-Lite': {'complexity': 'Medium', 'throughput': 'Medium', 'burst': '❌', 'pipelining': '✅', 'use_case': 'Memory-mapped I/O'},
        'AXI4': {'complexity': 'High', 'throughput': 'High', 'burst': '✅', 'pipelining': '✅', 'use_case': 'High-bandwidth'},
        'SPI': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Serial peripherals'},
        'I2C': {'complexity': 'Medium', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Low-speed devices'},
        'UART': {'complexity': 'Low', 'throughput': 'Low', 'burst': '❌', 'pipelining': '❌', 'use_case': 'Debug/console'},
    }

def render_copy_button(text: str, key: str) -> None:
    """Render a copy-to-clipboard button using JavaScript"""
    escaped_text = text.replace('`', '\\`').replace('$', '\\$')
    html = f'''
    <button onclick="navigator.clipboard.writeText(`{escaped_text}`).then(() => {{ 
        this.innerHTML = '✓ Copied!'; 
        setTimeout(() => this.innerHTML = '📋 Copy', 2000);
    }})" class="copy-btn">📋 Copy</button>
    '''
    components.html(html, height=35)

def create_html_export(module_name: str, code: str, parsed) -> str:
    """Create HTML export of testbench"""
    html = f'''<!DOCTYPE html>
<html>
<head>
    <title>{module_name} UVM Testbench - VerifAI</title>
    <style>
        body {{ font-family: -apple-system, BlinkMacSystemFont, 'Segoe UI', sans-serif; margin: 2rem; background: #f6f8fa; }}
        .container {{ max-width: 1000px; margin: 0 auto; background: white; padding: 2rem; border-radius: 8px; box-shadow: 0 2px 8px rgba(0,0,0,0.1); }}
        h1 {{ color: #24292f; border-bottom: 2px solid #0969da; padding-bottom: 0.5rem; }}
        .meta {{ color: #57606a; margin-bottom: 1rem; }}
        pre {{ background: #f6f8fa; padding: 1rem; border-radius: 6px; overflow-x: auto; font-size: 0.85rem; border: 1px solid #d0d7de; }}
        .badge {{ display: inline-block; background: #ddf4ff; color: #0969da; padding: 0.2rem 0.6rem; border-radius: 12px; font-size: 0.8rem; margin-right: 0.5rem; }}
        .footer {{ margin-top: 2rem; color: #57606a; font-size: 0.85rem; border-top: 1px solid #e1e4e8; padding-top: 1rem; }}
    </style>
</head>
<body>
    <div class="container">
        <h1>{module_name} UVM Testbench</h1>
        <div class="meta">
            <span class="badge">Generated by VerifAI</span>
            <span class="badge">{datetime.now().strftime("%Y-%m-%d %H:%M")}</span>
        </div>
        <pre><code>{code.replace("<", "&lt;").replace(">", "&gt;")}</code></pre>
        <div class="footer">
            Generated by <a href="https://verifai-761803298484.us-central1.run.app">VerifAI</a> - UVM Testbench Generator
        </div>
    </div>
</body>
</html>'''
    return html

# Common SVA assertion patterns library
SVA_LIBRARY = {
    'handshake': {
        'name': 'Valid-Ready Handshake',
        'description': 'Ensures proper valid/ready protocol',
        'code': '''property valid_ready_handshake(valid, ready, clk);
    @(posedge clk) valid |-> ##[0:$] ready;
endproperty''',
        'usage': 'AXI, custom interfaces'
    },
    'no_x_outputs': {
        'name': 'No X on Outputs',
        'description': 'Outputs should never be X after reset',
        'code': '''property no_x_after_reset(sig, rst_n, clk);
    @(posedge clk) $rose(rst_n) |-> ##1 !$isunknown(sig);
endproperty''',
        'usage': 'All designs'
    },
    'stable_until_ack': {
        'name': 'Stable Until Acknowledge',
        'description': 'Signal must remain stable until acknowledged',
        'code': '''property stable_until_ack(sig, ack, clk);
    @(posedge clk) $changed(sig) |-> ##[1:$] ack;
endproperty''',
        'usage': 'Request/grant protocols'
    },
    'one_hot': {
        'name': 'One-Hot Check',
        'description': 'Verifies signal is one-hot encoded',
        'code': '''property is_one_hot(sig, clk);
    @(posedge clk) $onehot(sig);
endproperty''',
        'usage': 'FSM states, arbitration'
    },
    'fifo_full': {
        'name': 'FIFO Full Protection',
        'description': 'No writes when FIFO is full',
        'code': '''property no_write_when_full(wr_en, full, clk);
    @(posedge clk) full |-> !wr_en;
endproperty''',
        'usage': 'FIFO interfaces'
    },
    'fifo_empty': {
        'name': 'FIFO Empty Protection',
        'description': 'No reads when FIFO is empty',
        'code': '''property no_read_when_empty(rd_en, empty, clk);
    @(posedge clk) empty |-> !rd_en;
endproperty''',
        'usage': 'FIFO interfaces'
    },
    'timeout': {
        'name': 'Response Timeout',
        'description': 'Response must come within N cycles',
        'code': '''property response_timeout(req, ack, clk);
    @(posedge clk) req |-> ##[1:16] ack;
endproperty''',
        'usage': 'Bus protocols'
    },
    'reset_values': {
        'name': 'Reset Value Check',
        'description': 'Verify outputs reset to correct values',
        'code': '''property reset_value_check(sig, rst_n, expected, clk);
    @(posedge clk) !rst_n |-> sig == expected;
endproperty''',
        'usage': 'All designs'
    }
}

def generate_wavedrom(protocol: str) -> str:
    """Generate WaveDrom JSON for protocol timing diagrams"""
    wavedroms = {
        "apb": {
            "signal": [
                {"name": "PCLK", "wave": "p........"},
                {"name": "PSEL", "wave": "0.1....0."},
                {"name": "PENABLE", "wave": "0..1...0."},
                {"name": "PWRITE", "wave": "0.1....0."},
                {"name": "PADDR", "wave": "x.3....x.", "data": ["ADDR"]},
                {"name": "PWDATA", "wave": "x.4....x.", "data": ["DATA"]},
                {"name": "PREADY", "wave": "0....1.0."},
                {"name": "PRDATA", "wave": "x.....5x.", "data": ["RDATA"]}
            ],
            "head": {"text": "APB Write Transaction", "tick": 0}
        },
        "axi4lite": {
            "signal": [
                {"name": "ACLK", "wave": "p........."},
                {"name": "AWVALID", "wave": "0.1..0...."},
                {"name": "AWREADY", "wave": "0...10...."},
                {"name": "AWADDR", "wave": "x.3..x....", "data": ["ADDR"]},
                {"name": "WVALID", "wave": "0....1.0.."},
                {"name": "WREADY", "wave": "0.....10.."},
                {"name": "WDATA", "wave": "x....4.x..", "data": ["DATA"]},
                {"name": "BVALID", "wave": "0.......1."},
                {"name": "BREADY", "wave": "1........."}
            ],
            "head": {"text": "AXI4-Lite Write Transaction", "tick": 0}
        },
        "spi": {
            "signal": [
                {"name": "SCLK", "wave": "0.hlhlhlhl"},
                {"name": "CS_N", "wave": "10.......1"},
                {"name": "MOSI", "wave": "x.34567890", "data": ["7","6","5","4","3","2","1","0"]},
                {"name": "MISO", "wave": "x.90876543", "data": ["7","6","5","4","3","2","1","0"]}
            ],
            "head": {"text": "SPI Mode 0 Transfer (8-bit)", "tick": 0}
        },
        "uart": {
            "signal": [
                {"name": "TX", "wave": "1.0.3.4.5.6.7.8.9.0.1.1", "data": ["ST","0","1","2","3","4","5","6","7","SP"]}
            ],
            "head": {"text": "UART Frame (8N1)", "tick": 0},
            "foot": {"text": "Start bit, 8 data bits, Stop bit"}
        },
        "i2c": {
            "signal": [
                {"name": "SCL", "wave": "1.0h.l.h.l.h.l.h.l.h.l.h1"},
                {"name": "SDA", "wave": "1.0..3...4...5...6...0..1", "data": ["A6","A5","A4","ACK"]}
            ],
            "head": {"text": "I2C Start + Address", "tick": 0}
        }
    }
    return json.dumps(wavedroms.get(protocol.lower().replace("-", "").replace("4_", "4"), wavedroms["apb"]))

def render_wavedrom(wavedrom_json: str, height: int = 150) -> None:
    """Render WaveDrom waveform using embedded JavaScript"""
    html = f'''
    <div id="waveform"></div>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/3.1.0/skins/default.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/3.1.0/wavedrom.min.js"></script>
    <script>
        var wave = {wavedrom_json};
        WaveDrom.RenderWaveForm(document.getElementById("waveform"), wave, "default");
    </script>
    '''
    components.html(html, height=height)

def calculate_quality_score(parsed, generated_code: str) -> dict:
    """Calculate testbench quality score"""
    score = 0
    breakdown = {}
    
    # Component completeness (40 points)
    components = ['interface', 'driver', 'monitor', 'scoreboard', 'coverage', 'agent', 'env', 'sequence', 'test']
    found = sum(1 for c in components if c in generated_code.lower())
    breakdown['completeness'] = int((found / len(components)) * 40)
    score += breakdown['completeness']
    
    # Protocol awareness (20 points)
    if hasattr(parsed, 'complexity') and parsed.complexity:
        if parsed.complexity.detected_protocol != "generic":
            breakdown['protocol'] = 20
        else:
            breakdown['protocol'] = 10
    else:
        breakdown['protocol'] = 5
    score += breakdown['protocol']
    
    # Coverage potential (20 points)
    if 'covergroup' in generated_code.lower() or 'coverpoint' in generated_code.lower():
        breakdown['coverage'] = 20
    elif 'coverage' in generated_code.lower():
        breakdown['coverage'] = 10
    else:
        breakdown['coverage'] = 5
    score += breakdown['coverage']
    
    # Code quality indicators (20 points)
    quality = 0
    if 'uvm_info' in generated_code.lower(): quality += 5
    if 'uvm_error' in generated_code.lower(): quality += 5
    if '`uvm_' in generated_code: quality += 5
    if 'virtual interface' in generated_code.lower(): quality += 5
    breakdown['quality'] = quality
    score += quality
    
    return {'score': min(score, 100), 'breakdown': breakdown}

def predict_bugs(parsed) -> list:
    """Predict likely verification bugs based on RTL analysis"""
    bugs = []
    
    if hasattr(parsed, 'complexity') and parsed.complexity:
        cx = parsed.complexity
        protocol = cx.detected_protocol
        
        # Common protocol-specific bugs
        if protocol == "apb":
            bugs.append({
                'severity': 'high',
                'title': 'PREADY Timing',
                'description': 'APB slave may not handle PREADY deasserted case properly - ensure wait state testing'
            })
            bugs.append({
                'severity': 'medium', 
                'title': 'Back-to-Back Transactions',
                'description': 'Sequential transactions without idle cycles may cause data corruption'
            })
        elif protocol == "axi4lite":
            bugs.append({
                'severity': 'high',
                'title': 'Handshake Deadlock',
                'description': 'AXI VALID/READY handshake may deadlock if VALID waits for READY'
            })
            bugs.append({
                'severity': 'medium',
                'title': 'Outstanding Transactions',
                'description': 'Multiple outstanding transactions may cause response ordering issues'
            })
        elif protocol == "spi":
            bugs.append({
                'severity': 'high',
                'title': 'Clock Phase/Polarity',
                'description': 'SPI mode mismatch (CPOL/CPHA) causes bit-shifted data'
            })
        elif protocol == "uart":
            bugs.append({
                'severity': 'medium',
                'title': 'Baud Rate Mismatch',
                'description': 'Clock frequency drift may cause framing errors'
            })
        elif protocol == "i2c":
            bugs.append({
                'severity': 'high',
                'title': 'Clock Stretching',
                'description': 'Slave clock stretching not handled may cause data loss'
            })
        
        # FSM-related bugs
        if cx.has_fsm and cx.fsm_states > 2:
            bugs.append({
                'severity': 'high',
                'title': 'FSM Deadlock',
                'description': f'FSM with {cx.fsm_states} states may have unreachable states or deadlock conditions'
            })
        
        # Reset-related bugs
        if parsed.resets:
            bugs.append({
                'severity': 'medium',
                'title': 'Reset Race Condition',
                'description': 'Async reset release near clock edge may cause metastability'
            })
        
        # Data width bugs
        if cx.data_width >= 32:
            bugs.append({
                'severity': 'medium',
                'title': 'Data Bus Boundary',
                'description': f'{cx.data_width}-bit data may have byte lane issues on partial writes'
            })
    
    return bugs[:5]  # Return top 5 bugs

def create_testbench_zip(module_name: str, generated_code: str, parsed) -> bytes:
    """Create ZIP file with testbench and scripts"""
    zip_buffer = io.BytesIO()
    
    with zipfile.ZipFile(zip_buffer, 'w', zipfile.ZIP_DEFLATED) as zf:
        # Main testbench file
        zf.writestr(f"tb/{module_name}_tb_pkg.sv", generated_code)
        
        # Interface file (extract from generated or create placeholder)
        interface_code = f'''// Auto-generated interface for {module_name}
interface {module_name}_if(input logic clk);
    // TODO: Add signals from generated testbench
    clocking cb @(posedge clk);
        // Add clocking block signals
    endclocking
    
    modport DRV(clocking cb);
    modport MON(clocking cb);
endinterface
'''
        zf.writestr(f"tb/{module_name}_if.sv", interface_code)
        
        # Makefile for VCS
        vcs_makefile = f'''# Makefile for VCS simulation
TB_TOP = {module_name}_tb_top
DUT = ../rtl/{module_name}.sv

# VCS flags
VCS_FLAGS = -full64 -sverilog -timescale=1ns/1ps
VCS_FLAGS += +define+UVM_NO_DEPRECATED
VCS_FLAGS += -ntb_opts uvm-1.2

# Compile
compile:
\tvcs $(VCS_FLAGS) -o simv \\
\t\t$(DUT) \\
\t\t{module_name}_tb_pkg.sv \\
\t\t{module_name}_if.sv \\
\t\t$(TB_TOP).sv

# Run
run:
\t./simv +UVM_TESTNAME={module_name}_base_test +UVM_VERBOSITY=UVM_MEDIUM

# Run with coverage
run_cov:
\t./simv +UVM_TESTNAME={module_name}_base_test -cm line+cond+fsm+tgl

# Clean
clean:
\trm -rf simv* csrc *.log *.vpd DVEfiles coverage*

.PHONY: compile run run_cov clean
'''
        zf.writestr("tb/Makefile.vcs", vcs_makefile)
        
        # Makefile for Questa
        questa_makefile = f'''# Makefile for Questa simulation
TB_TOP = {module_name}_tb_top
DUT = ../rtl/{module_name}.sv

# Questa flags
VLOG_FLAGS = -sv -timescale 1ns/1ps
VSIM_FLAGS = -c -do "run -all; quit"

# Compile
compile:
\tvlib work
\tvlog $(VLOG_FLAGS) +define+UVM_NO_DEPRECATED \\
\t\t$(DUT) \\
\t\t{module_name}_tb_pkg.sv \\
\t\t{module_name}_if.sv \\
\t\t$(TB_TOP).sv

# Run
run:
\tvsim $(VSIM_FLAGS) +UVM_TESTNAME={module_name}_base_test $(TB_TOP)

# GUI
gui:
\tvsim +UVM_TESTNAME={module_name}_base_test $(TB_TOP)

# Clean
clean:
\trm -rf work transcript *.wlf

.PHONY: compile run gui clean
'''
        zf.writestr("tb/Makefile.questa", questa_makefile)
        
        # README
        readme = f'''# {module_name} UVM Testbench
Generated by VerifAI - https://verifai-761803298484.us-central1.run.app

## Directory Structure
```
tb/
├── {module_name}_tb_pkg.sv    # Main testbench package
├── {module_name}_if.sv        # Interface
├── Makefile.vcs               # VCS build script
└── Makefile.questa            # Questa build script
```

## Quick Start

### VCS
```bash
cd tb
make -f Makefile.vcs compile
make -f Makefile.vcs run
```

### Questa
```bash
cd tb
make -f Makefile.questa compile
make -f Makefile.questa run
```

## Test Configuration
- Default test: {module_name}_base_test
- Verbosity: UVM_MEDIUM (configurable via +UVM_VERBOSITY)

## Generated Components
- Transaction/Sequence Item
- Driver
- Monitor  
- Agent
- Scoreboard
- Coverage Collector
- Environment
- Base Test
'''
        zf.writestr("README.md", readme)
    
    zip_buffer.seek(0)
    return zip_buffer.getvalue()

# Navigation with dark mode toggle
nav_col1, nav_col2, nav_col3 = st.columns([2, 6, 2])
with nav_col1:
    st.markdown(f"""<div class="logo">Verif<span>AI</span></div>""", unsafe_allow_html=True)
with nav_col3:
    col_a, col_b = st.columns(2)
    with col_a:
        if st.button("🌙" if not st.session_state.get('dark_mode') else "☀️", key="theme_toggle", help="Toggle dark/light mode"):
            st.session_state['dark_mode'] = not st.session_state.get('dark_mode', False)
            st.rerun()
    with col_b:
        if st.button("📜", key="history_btn", help="View generation history"):
            st.session_state['show_history'] = not st.session_state.get('show_history', False)

# Show history panel if toggled
if st.session_state.get('show_history', False):
    with st.expander("📜 Generation History", expanded=True):
        history = st.session_state.get('generation_history', [])
        if history:
            for item in history:
                col1, col2, col3 = st.columns([3, 1, 1])
                with col1:
                    st.markdown(f"**{item['name']}** - {item['protocol']}")
                with col2:
                    st.caption(item['time_display'])
                with col3:
                    if st.button("Load", key=f"load_{item['id']}"):
                        st.session_state['tb_result'] = item['code']
                        st.session_state['show_history'] = False
                        st.rerun()
        else:
            st.info("No generation history yet. Generate a testbench to see it here!")

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
tabs = st.tabs(["RTL to Testbench", "Protocol Templates", "Coverage Analysis", "SVA Assertions", "Register Map"])

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
        
        # Real-time syntax validation
        if rtl_code.strip():
            validation = validate_rtl_syntax(rtl_code)
            if validation['valid']:
                st.markdown('<div class="syntax-valid">✅ Syntax looks valid</div>', unsafe_allow_html=True)
            else:
                for err in validation['errors']:
                    st.markdown(f'<div class="syntax-invalid">❌ {err}</div>', unsafe_allow_html=True)
        
        # Keyboard shortcut hint
        st.markdown('<small style="color: #57606a;">💡 Tip: Paste RTL and click Generate or use <span class="kbd">Cmd+Enter</span></small>', unsafe_allow_html=True)
        
        if st.button("Generate Testbench", type="primary", use_container_width=True, key="gen_tb"):
            if rtl_code.strip():
                # Validate syntax first
                validation = validate_rtl_syntax(rtl_code)
                if not validation['valid']:
                    for err in validation['errors']:
                        st.error(f"⚠️ {err}")
                    st.stop()
                
                if validation['warnings']:
                    for warn in validation['warnings']:
                        st.warning(f"⚡ {warn}")
                
                with st.spinner("Analyzing RTL and generating testbench..."):
                    try:
                        start_time = time.time()
                        parsed = parse_rtl(rtl_code)
                        st.session_state['parsed'] = parsed
                        
                        generator = RTLAwareGenerator()
                        prompt = generator.generate_prompt(parsed)
                        result = generate_with_llm(prompt)
                        
                        generation_time = time.time() - start_time
                        st.session_state['tb_result'] = result
                        st.session_state['gen_success'] = True
                        st.session_state['generation_time'] = generation_time
                        
                        # Add to history
                        protocol = "generic"
                        if hasattr(parsed, 'complexity') and parsed.complexity:
                            protocol = parsed.complexity.detected_protocol
                        add_to_history(parsed.module_name, protocol, result, generation_time)
                        
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
            
            # Waveform Diagrams - Interactive WaveDrom
            if hasattr(parsed, 'complexity') and parsed.complexity:
                protocol = parsed.complexity.detected_protocol
                if protocol != "generic":
                    with st.expander("Interactive Protocol Timing", expanded=True):
                        wavedrom_json = generate_wavedrom(protocol)
                        render_wavedrom(wavedrom_json, height=180)
            
            # Bug Prediction - NEW FEATURE
            bugs = predict_bugs(parsed)
            if bugs:
                with st.expander("🔍 Predicted Verification Issues", expanded=True):
                    st.markdown("*AI-predicted bugs to verify against:*")
                    for bug in bugs:
                        severity_class = "bug-card-high" if bug['severity'] == 'high' else ""
                        st.markdown(f'''<div class="bug-card {severity_class}">
                            <div class="bug-title">⚠️ {bug['title']}</div>
                            <div class="bug-desc">{bug['description']}</div>
                        </div>''', unsafe_allow_html=True)
            
            # Constraint Hints
            if hasattr(parsed, 'constraints') and parsed.constraints:
                with st.expander("Constraint Randomization Hints"):
                    for hint in parsed.constraints:
                        st.markdown(f'<div class="constraint-box"><div class="constraint-title">{hint.signal_name}</div><div class="constraint-desc">{hint.description}</div></div>', unsafe_allow_html=True)
                        st.code(hint.constraint_code, language="systemverilog")
            
            # Generated code with Quality Score
            if st.session_state.get('tb_result'):
                # Calculate and show quality score
                quality = calculate_quality_score(parsed, st.session_state['tb_result'])
                score = quality['score']
                score_class = "score-high" if score >= 80 else ("score-medium" if score >= 60 else "score-low")
                
                col_score, col_breakdown = st.columns([1, 3])
                with col_score:
                    st.markdown(f'''<div class="quality-gauge">
                        <div class="score-circle {score_class}">{score}</div>
                        <div style="font-weight: 600; color: #24292f;">Quality Score</div>
                    </div>''', unsafe_allow_html=True)
                
                with col_breakdown:
                    bd = quality['breakdown']
                    st.markdown(f'''<div class="stats-grid">
                        <div class="stat-box"><div class="stat-value">{bd.get("completeness", 0)}/40</div><div class="stat-label">Completeness</div></div>
                        <div class="stat-box"><div class="stat-value">{bd.get("protocol", 0)}/20</div><div class="stat-label">Protocol</div></div>
                        <div class="stat-box"><div class="stat-value">{bd.get("coverage", 0)}/20</div><div class="stat-label">Coverage</div></div>
                        <div class="stat-box"><div class="stat-value">{bd.get("quality", 0)}/20</div><div class="stat-label">UVM Best Practices</div></div>
                    </div>''', unsafe_allow_html=True)
                
                st.code(st.session_state['tb_result'], language="systemverilog")
                
                # Performance metrics
                if st.session_state.get('generation_time'):
                    gen_time = st.session_state['generation_time']
                    lines = len(st.session_state['tb_result'].split('\n'))
                    st.markdown(f'''<div class="perf-bar">
                        <div class="perf-item">⏱️ Generated in <span class="perf-value">{gen_time:.1f}s</span></div>
                        <div class="perf-item">📝 <span class="perf-value">{lines}</span> lines</div>
                        <div class="perf-item">📊 <span class="perf-value">{score}/100</span> quality</div>
                    </div>''', unsafe_allow_html=True)
                
                # Download options - expanded
                c1, c2, c3, c4 = st.columns(4)
                with c1:
                    st.download_button(
                        "📄 .sv",
                        st.session_state['tb_result'],
                        f"{parsed.module_name}_tb.sv",
                        use_container_width=True
                    )
                with c2:
                    # ZIP with simulator scripts
                    zip_data = create_testbench_zip(parsed.module_name, st.session_state['tb_result'], parsed)
                    st.download_button(
                        "📦 ZIP",
                        zip_data,
                        f"{parsed.module_name}_uvm_tb.zip",
                        mime="application/zip",
                        use_container_width=True
                    )
                with c3:
                    # HTML export
                    html_data = create_html_export(parsed.module_name, st.session_state['tb_result'], parsed)
                    st.download_button(
                        "🌐 HTML",
                        html_data,
                        f"{parsed.module_name}_tb.html",
                        mime="text/html",
                        use_container_width=True
                    )
                with c4:
                    # JSON metadata
                    json_data = json.dumps({
                        'module': parsed.module_name,
                        'protocol': parsed.complexity.detected_protocol if hasattr(parsed, 'complexity') and parsed.complexity else 'generic',
                        'inputs': parsed.inputs,
                        'outputs': parsed.outputs,
                        'quality_score': score,
                        'generated_at': datetime.now().isoformat()
                    }, indent=2)
                    st.download_button(
                        "📋 JSON",
                        json_data,
                        f"{parsed.module_name}_meta.json",
                        mime="application/json",
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
        
        # Protocol comparison table
        with st.expander("📊 Protocol Comparison Guide", expanded=False):
            comparison = get_protocol_comparison()
            st.markdown('''<table class="proto-table">
                <tr><th>Protocol</th><th>Complexity</th><th>Throughput</th><th>Burst</th><th>Pipeline</th><th>Use Case</th></tr>
            ''' + ''.join([f'''<tr>
                <td><strong>{p}</strong></td>
                <td>{d['complexity']}</td>
                <td>{d['throughput']}</td>
                <td>{d['burst']}</td>
                <td>{d['pipelining']}</td>
                <td>{d['use_case']}</td>
            </tr>''' for p, d in comparison.items()]) + '</table>', unsafe_allow_html=True)
        
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
        
        # Show interactive protocol waveform
        with st.expander("Interactive Protocol Timing", expanded=True):
            protocol_key = protocol.lower().replace('-', '').replace('4_', '4')
            wavedrom_json = generate_wavedrom(protocol_key)
            render_wavedrom(wavedrom_json, height=180)
        
        if st.session_state.get('proto_result'):
            st.code(st.session_state['proto_result'], language="systemverilog")
            
            c1, c2 = st.columns(2)
            with c1:
                st.download_button(
                    "📄 Download .sv",
                    st.session_state['proto_result'],
                    f"{protocol.lower().replace('-', '_')}_uvm_tb.sv",
                    use_container_width=True
                )
            with c2:
                # ZIP download for protocol template
                zip_data = create_testbench_zip(
                    protocol.lower().replace('-', '_'),
                    st.session_state['proto_result'],
                    None
                )
                st.download_button(
                    "📦 Download ZIP",
                    zip_data,
                    f"{protocol.lower().replace('-', '_')}_uvm_tb.zip",
                    mime="application/zip",
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
        
        # SVA Library Browser
        with st.expander("📚 SVA Pattern Library", expanded=False):
            st.markdown("*Click to copy common assertion patterns:*")
            for key, sva in SVA_LIBRARY.items():
                with st.container():
                    st.markdown(f"**{sva['name']}** - {sva['description']}")
                    st.caption(f"Usage: {sva['usage']}")
                    st.code(sva['code'], language="systemverilog")
                    if st.button(f"Copy {key}", key=f"copy_sva_{key}"):
                        st.session_state['sva_clipboard'] = sva['code']
                        st.success("Copied to clipboard!")
        
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

# Tab 5: Register Map
with tabs[4]:
    col1, col2 = st.columns([1, 1], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Register Specification</div>', unsafe_allow_html=True)
        
        st.markdown("Import register specifications from IP-XACT, SystemRDL, CSV, or JSON formats.")
        
        spec_format = st.selectbox("Format", ["CSV (Simple)", "JSON", "IP-XACT XML", "SystemRDL"])
        
        if spec_format == "CSV (Simple)":
            sample_spec = """name,address,width,access,reset,description
CTRL,0x00,32,RW,0x00000000,Control register
STATUS,0x04,32,RO,0x00000001,Status register
DATA,0x08,32,RW,0x00000000,Data register
IRQ_EN,0x0C,32,RW,0x00000000,Interrupt enable
IRQ_STATUS,0x10,32,RO,0x00000000,Interrupt status"""
        elif spec_format == "JSON":
            sample_spec = """{
  "name": "my_peripheral",
  "registers": [
    {"name": "CTRL", "address": "0x00", "width": 32, "access": "RW", "reset": "0x0"},
    {"name": "STATUS", "address": "0x04", "width": 32, "access": "RO", "reset": "0x1"},
    {"name": "DATA", "address": "0x08", "width": 32, "access": "RW", "reset": "0x0"}
  ]
}"""
        else:
            sample_spec = "<!-- Paste your IP-XACT or SystemRDL here -->"
        
        reg_spec = st.text_area(
            "Spec",
            height=300,
            value=sample_spec,
            label_visibility="collapsed"
        )
        
        if st.button("Parse & Generate", type="primary", use_container_width=True, key="gen_reg"):
            if reg_spec.strip():
                with st.spinner("Parsing register specification..."):
                    try:
                        parsed_spec = SpecParser().parse(reg_spec, f"regs.{spec_format.split()[0].lower()}")
                        st.session_state['reg_spec'] = parsed_spec
                        
                        # Generate register tests
                        prompt = f"""Generate UVM register model and test sequences for these registers:

Registers: {[(r.name, r.address, r.access.value if hasattr(r.access, 'value') else r.access) for r in parsed_spec.registers[:10]]}

Generate:
1. uvm_reg class for each register
2. uvm_reg_block containing all registers
3. Register access sequences (write/read tests)
4. Reset value verification sequence

Use UVM RAL (Register Abstraction Layer) methodology."""
                        result = generate_with_llm(prompt)
                        st.session_state['reg_result'] = result
                    except Exception as e:
                        st.error(f"Error parsing: {str(e)}")
            else:
                st.warning("Please provide register specification")
    
    with col2:
        st.markdown('<div class="card-title">Register Map & Tests</div>', unsafe_allow_html=True)
        
        if st.session_state.get('reg_spec'):
            spec = st.session_state['reg_spec']
            
            st.success(f"Parsed {len(spec.registers)} registers")
            
            # Display register table
            st.markdown("**Register Map:**")
            reg_data = []
            for reg in spec.registers[:10]:
                access = reg.access.value if hasattr(reg.access, 'value') else str(reg.access)
                reg_data.append({
                    "Name": reg.name,
                    "Address": f"0x{reg.address:04X}" if isinstance(reg.address, int) else reg.address,
                    "Width": reg.width,
                    "Access": access,
                    "Reset": f"0x{reg.reset_value:08X}" if isinstance(reg.reset_value, int) else reg.reset_value
                })
            
            st.dataframe(reg_data, use_container_width=True, hide_index=True)
            
            if st.session_state.get('reg_result'):
                st.markdown("**Generated UVM Register Model:**")
                st.code(st.session_state['reg_result'], language="systemverilog")
                st.download_button(
                    "Download Register Model",
                    st.session_state['reg_result'],
                    "reg_model.sv",
                    use_container_width=True
                )
        else:
            st.markdown("""
            <div class="placeholder">
                <p><strong>Register map will appear here</strong></p>
                <p style="font-size: 0.85rem; margin-top: 0.5rem;">
                    Import IP-XACT, SystemRDL, CSV, or JSON register specs
                </p>
            </div>
            """, unsafe_allow_html=True)

# Footer with stats
stats = st.session_state.get('generation_stats', {'total': 0, 'protocols': {}, 'avg_time': 0})
stats_text = ""
if stats['total'] > 0:
    stats_text = f" | 📊 {stats['total']} generations this session"
    if stats['avg_time'] > 0:
        stats_text += f" | ⏱️ Avg {stats['avg_time']:.1f}s"

st.markdown(f"""
<div class="footer">
    <span style="color: {theme['text_muted']};">Built by Tushar Pathak{stats_text}</span>
    <div>
        <a href="https://github.com/tusharpathaknyu/VerifAI" target="_blank">GitHub</a>
        <span style="color: {theme['text_muted']}; margin: 0 0.5rem;">|</span>
        <a href="#" onclick="alert('Keyboard Shortcuts:\\n\\nCtrl+Enter: Generate\\nCtrl+S: Download\\nCtrl+H: Toggle History')">⌨️ Shortcuts</a>
    </div>
</div>
""", unsafe_allow_html=True)
