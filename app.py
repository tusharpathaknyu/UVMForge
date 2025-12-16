"""
UVMForge - UVM Testbench Generator
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
from src.app_helpers import (
    generate_wavedrom, calculate_quality_score, predict_bugs,
    create_testbench_zip, validate_rtl_syntax, get_protocol_comparison,
    create_html_export, SVA_LIBRARY, parse_uvm_components,
    analyze_testbench_complexity, get_signal_explorer_data,
    generate_enhancement_suggestions
)

st.set_page_config(
    page_title="UVMForge - UVM Generator",
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
    
    /* Code blocks - ensure ALL code is visible with syntax highlighting */
    pre {{
        background: #1e1e2e !important;
        border: 1px solid {theme['border']} !important;
        border-radius: 8px !important;
        color: #cdd6f4 !important;
        padding: 1rem !important;
    }}
    pre code {{
        color: #cdd6f4 !important;
        background: transparent !important;
    }}
    code {{
        color: #cdd6f4 !important;
    }}
    .stCodeBlock {{
        background: #1e1e2e !important;
    }}
    .stCodeBlock pre {{
        background: #1e1e2e !important;
        color: #cdd6f4 !important;
    }}
    .stCodeBlock code {{
        color: #cdd6f4 !important;
    }}
    [data-testid="stCode"] {{
        background: #1e1e2e !important;
    }}
    [data-testid="stCode"] pre {{
        color: #cdd6f4 !important;
        background: #1e1e2e !important;
    }}
    [data-testid="stCode"] code {{
        color: #cdd6f4 !important;
    }}
    /* Syntax highlighting colors - Catppuccin Mocha theme */
    .hljs-keyword, .hljs-type {{ color: #cba6f7 !important; }}
    .hljs-string {{ color: #a6e3a1 !important; }}
    .hljs-number {{ color: #fab387 !important; }}
    .hljs-comment {{ color: #6c7086 !important; }}
    .hljs-function {{ color: #89b4fa !important; }}
    .hljs-class {{ color: #f9e2af !important; }}
    .hljs-variable {{ color: #f38ba8 !important; }}
    .hljs-operator {{ color: #89dceb !important; }}
    .token, .token span {{ color: #cdd6f4 !important; }}
    /* Force all code text visible */
    pre * {{ color: inherit !important; }}
    code * {{ color: inherit !important; }}
    
    /* File uploader - fix visibility */
    [data-testid="stFileUploader"] {{
        background: {theme['card']} !important;
        border: 2px dashed {theme['border']} !important;
        border-radius: 8px !important;
        padding: 1rem !important;
    }}
    [data-testid="stFileUploader"] label {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploader"] p, [data-testid="stFileUploader"] span {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploader"] small {{
        color: {theme['text_muted']} !important;
    }}
    [data-testid="stFileUploader"] section {{
        background: {theme['card']} !important;
    }}
    [data-testid="stFileUploader"] section > div {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzone"] {{
        background: {theme['card']} !important;
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzone"] div {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzone"] span {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzoneInstructions"] {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzoneInstructions"] div {{
        color: {theme['text']} !important;
    }}
    [data-testid="stFileUploaderDropzoneInstructions"] span {{
        color: {theme['text']} !important;
    }}
    .uploadedFile {{
        color: {theme['text']} !important;
    }}
    /* File uploader button - fix text visibility */
    [data-testid="stFileUploaderDropzone"] button {{
        background: {theme['primary']} !important;
        color: white !important;
        border: none !important;
    }}
    [data-testid="stFileUploaderDropzone"] button span {{
        color: white !important;
    }}
    [data-testid="baseButton-secondary"] {{
        color: white !important;
        background: {theme['primary']} !important;
    }}
    [data-testid="baseButton-secondary"] p {{
        color: white !important;
    }}
    /* Select dropdown - add visual indicator */
    .stSelectbox [data-baseweb="select"] {{
        background: {theme['card']} !important;
        border: 1px solid {theme['border']} !important;
    }}
    .stSelectbox [data-baseweb="select"]:after {{
        content: ' ▼';
        color: {theme['text_muted']};
    }}
    .stSelectbox svg {{
        fill: {theme['text']} !important;
    }}
    .stSelectbox [data-baseweb="select"] > div {{
        color: {theme['text']} !important;
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
    .stSelectbox label, .stSlider label, .stTextInput label, .stTextArea label {{
        color: {theme['text']} !important;
        font-weight: 500 !important;
    }}
    
    /* Slider */
    .stSlider > div > div > div {{
        background: {theme['primary']} !important;
    }}
    .stSlider [data-baseweb="slider"] > div {{
        color: {theme['text']} !important;
    }}
    
    /* Radio buttons - comprehensive fix */
    .stRadio label {{
        color: {theme['text']} !important;
    }}
    .stRadio > div {{
        color: {theme['text']} !important;
    }}
    .stRadio [data-baseweb="radio"] {{
        color: {theme['text']} !important;
    }}
    .stRadio [data-baseweb="radio"] label {{
        color: {theme['text']} !important;
    }}
    .stRadio div[role="radiogroup"] label {{
        color: {theme['text']} !important;
    }}
    .stRadio div[role="radiogroup"] > label > div:last-child {{
        color: {theme['text']} !important;
    }}
    [data-baseweb="radio"] > div:last-child {{
        color: {theme['text']} !important;
    }}
    
    /* All labels and text */
    label, .stMarkdown p, .stMarkdown strong {{
        color: {theme['text']} !important;
    }}
    
    /* Expander styling - ensure visible text */
    .streamlit-expanderHeader {{
        color: {theme['text']} !important;
        background: {theme['card']} !important;
    }}
    .streamlit-expanderHeader p, .streamlit-expanderHeader span {{
        color: {theme['text']} !important;
    }}
    [data-testid="stExpander"] {{
        border: 1px solid {theme['border']} !important;
        border-radius: 8px !important;
        background: {theme['card']} !important;
    }}
    [data-testid="stExpander"] summary {{
        color: {theme['text']} !important;
        background: {theme['card']} !important;
        padding: 0.75rem !important;
    }}
    [data-testid="stExpander"] summary span, [data-testid="stExpander"] summary p {{
        color: {theme['text']} !important;
    }}
    [data-testid="stExpander"] > div {{
        background: {theme['card']} !important;
    }}
    details {{
        background: {theme['card']} !important;
    }}
    details summary {{
        color: {theme['text']} !important;
        background: {theme['card']} !important;
    }}
    details[open] summary {{
        border-bottom: 1px solid {theme['border']} !important;
    }}
    
    /* List items inside expanders */
    .stMarkdown ul li, .stMarkdown ol li {{
        color: {theme['text']} !important;
    }}
    
    /* All text elements */
    p, span, div {{
        color: inherit;
    }}
    .element-container p, .element-container span {{
        color: {theme['text']};
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

# ============== LOCAL HELPER FUNCTIONS (not in app_helpers) ==============

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

def render_wavedrom(wavedrom_json: str, height: int = 150, key: str = "wave") -> None:
    """Render WaveDrom waveform as static SVG-like ASCII diagram for reliability"""
    import json as json_lib
    
    try:
        wave_data = json_lib.loads(wavedrom_json) if isinstance(wavedrom_json, str) else wavedrom_json
        signals = wave_data.get('signal', [])
        title = wave_data.get('head', {}).get('text', 'Protocol Timing')
        
        # Build ASCII waveform
        lines = [f"<div style='background: #1a1a2e; color: #00ff88; font-family: monospace; padding: 15px; border-radius: 8px; overflow-x: auto;'>"]
        lines.append(f"<div style='color: #00d4ff; font-weight: bold; margin-bottom: 10px;'>{title}</div>")
        lines.append("<pre style='margin: 0; line-height: 1.4;'>")
        
        for sig in signals:
            name = sig.get('name', '???')
            wave = sig.get('wave', '')
            data = sig.get('data', [])
            
            # Convert wave notation to ASCII
            wave_chars = []
            data_idx = 0
            for char in wave:
                if char == 'p':  # positive clock
                    wave_chars.append('_|‾|')
                elif char == 'n':  # negative clock
                    wave_chars.append('‾|_|')
                elif char == 'h':  # high
                    wave_chars.append('‾‾‾‾')
                elif char == 'l':  # low
                    wave_chars.append('____')
                elif char == '0':  # low
                    wave_chars.append('____')
                elif char == '1':  # high
                    wave_chars.append('‾‾‾‾')
                elif char == 'x':  # unknown
                    wave_chars.append('XXXX')
                elif char == '.':  # continue
                    if wave_chars:
                        wave_chars.append(wave_chars[-1] if wave_chars else '____')
                    else:
                        wave_chars.append('____')
                elif char.isdigit():  # data value
                    label = data[data_idx] if data_idx < len(data) else f'D{char}'
                    data_idx += 1
                    wave_chars.append(f'={label[:3]:^3}=')
                else:
                    wave_chars.append('    ')
            
            wave_str = ''.join(wave_chars)
            lines.append(f"<span style='color: #ffd93d;'>{name:12}</span> │ <span style='color: #6bcb77;'>{wave_str}</span>")
        
        lines.append("</pre></div>")
        html = '\n'.join(lines)
        components.html(html, height=height)
        
    except Exception as e:
        # Fallback: show simple message
        st.markdown(f"*Timing diagram for this protocol*")

def render_wavedrom_js_disabled(wavedrom_json: str, height: int = 150, key: str = "wave") -> None:
    """Original JS-based WaveDrom renderer (disabled due to iframe issues)"""
    import random
    unique_id = f"waveform_{key}_{random.randint(10000, 99999)}"
    import json as json_lib
    json_str = wavedrom_json if isinstance(wavedrom_json, str) else json_lib.dumps(wavedrom_json)
    
    html = f'''
    <div id="{unique_id}" style="background: white; padding: 10px; border-radius: 8px; min-height: 100px;">
        <p style="color: #666; text-align: center;">Loading waveform...</p>
    </div>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/3.1.0/skins/default.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/wavedrom/3.1.0/wavedrom.min.js"></script>
    <script>
    (function() {{
        function renderWave() {{
            try {{
                var container = document.getElementById("{unique_id}");
                if (!container) return;
                var wave = {json_str};
                container.innerHTML = '';
                WaveDrom.RenderWaveForm(container, wave, "default");
            }} catch(e) {{
                console.error("WaveDrom error:", e);
                var container = document.getElementById("{unique_id}");
                if (container) {{
                    container.innerHTML = '<p style="color: #d73a49; text-align: center;">Error rendering waveform</p>';
                }}
            }}
        }}
        
        // Try multiple times to ensure scripts are loaded
        if (typeof WaveDrom !== 'undefined') {{
            renderWave();
        }} else {{
            setTimeout(renderWave, 200);
            setTimeout(renderWave, 500);
            setTimeout(renderWave, 1000);
        }}
    }})();
    </script>
    '''
    components.html(html, height=height)
    # Note: This function is disabled, use render_wavedrom instead

# Navigation with dark mode toggle
nav_col1, nav_col2, nav_col3 = st.columns([2, 6, 2])
with nav_col1:
    st.markdown(f"""<div class="logo">UVM<span>Forge</span></div>""", unsafe_allow_html=True)
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

def generate_uvm_reg_model(registers: list) -> str:
    """Generate UVM Register Model from register list"""
    reg_classes = []
    reg_instances = []
    
    for reg in registers:
        name = reg.get('name', 'REG').upper()
        addr = reg.get('address', '0x00')
        width = reg.get('width', 32)
        access = reg.get('access', 'RW').upper()
        reset = reg.get('reset_value', '0x0')
        
        # Convert address to integer if string
        if isinstance(addr, str):
            addr_int = int(addr, 16) if addr.startswith('0x') else int(addr)
        else:
            addr_int = addr
        
        uvm_access = 'RW' if access in ['RW', 'WR'] else ('RO' if access == 'RO' else ('WO' if access == 'WO' else 'RW'))
        
        reg_classes.append(f'''// Register: {name}
class {name.lower()}_reg extends uvm_reg;
    `uvm_object_utils({name.lower()}_reg)
    
    rand uvm_reg_field value;
    
    function new(string name = "{name.lower()}_reg");
        super.new(name, {width}, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        value = uvm_reg_field::type_id::create("value");
        value.configure(this, {width}, 0, "{uvm_access}", 0, {reset}, 1, 1, 1);
    endfunction
endclass
''')
        
        reg_instances.append(f'''        {name.lower()} = {name.lower()}_reg::type_id::create("{name.lower()}");
        {name.lower()}.configure(this);
        {name.lower()}.build();
        default_map.add_reg({name.lower()}, 'h{addr_int:04X}, "{uvm_access}");''')
    
    return f'''// ==================== UVM Register Model ====================
// Auto-generated by UVMForge
// Registers: {len(registers)}

`include "uvm_macros.svh"
import uvm_pkg::*;

{chr(10).join(reg_classes)}

// Register Block
class reg_block extends uvm_reg_block;
    `uvm_object_utils(reg_block)
    
    // Register instances
{chr(10).join([f"    rand {reg.get('name', 'REG').lower()}_reg {reg.get('name', 'REG').lower()};" for reg in registers])}
    
    function new(string name = "reg_block");
        super.new(name, UVM_NO_COVERAGE);
    endfunction
    
    virtual function void build();
        default_map = create_map("default_map", 0, 4, UVM_LITTLE_ENDIAN);
        
{chr(10).join(reg_instances)}
    endfunction
endclass

// ==================== Register Test Sequence ====================
class reg_reset_test_seq extends uvm_reg_sequence;
    `uvm_object_utils(reg_reset_test_seq)
    
    reg_block model;
    
    function new(string name = "reg_reset_test_seq");
        super.new(name);
    endfunction
    
    task body();
        uvm_status_e status;
        uvm_reg_data_t value;
        uvm_reg regs[$];
        
        model.get_registers(regs);
        
        `uvm_info(get_type_name(), "Starting reset value verification", UVM_MEDIUM)
        
        foreach(regs[i]) begin
            regs[i].read(status, value);
            if (value !== regs[i].get_reset())
                `uvm_error(get_type_name(), $sformatf("Reset mismatch: %s expected 0x%0h, got 0x%0h",
                    regs[i].get_name(), regs[i].get_reset(), value))
            else
                `uvm_info(get_type_name(), $sformatf("%s reset value OK: 0x%0h",
                    regs[i].get_name(), value), UVM_HIGH)
        end
    endtask
endclass

// ==================== Register Access Test ====================
class reg_access_test_seq extends uvm_reg_sequence;
    `uvm_object_utils(reg_access_test_seq)
    
    reg_block model;
    
    function new(string name = "reg_access_test_seq");
        super.new(name);
    endfunction
    
    task body();
        uvm_status_e status;
        uvm_reg_data_t wdata, rdata;
        uvm_reg regs[$];
        
        model.get_registers(regs);
        
        foreach(regs[i]) begin
            if (regs[i].get_rights() inside {{"RW", "WO"}}) begin
                wdata = $urandom();
                regs[i].write(status, wdata);
                regs[i].read(status, rdata);
                `uvm_info(get_type_name(), $sformatf("Tested %s: wrote 0x%0h, read 0x%0h",
                    regs[i].get_name(), wdata, rdata), UVM_MEDIUM)
            end
        end
    endtask
endclass
'''

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
        
        # File upload option
        upload_col, _ = st.columns([1, 1])
        with upload_col:
            uploaded_file = st.file_uploader(
                "Upload RTL file",
                type=['v', 'sv', 'vh', 'svh'],
                help="Upload .v, .sv, .vh, or .svh files",
                label_visibility="collapsed"
            )
        
        if uploaded_file is not None:
            file_content = uploaded_file.read().decode('utf-8')
            st.session_state['rtl_input'] = file_content
            st.success(f"✅ Loaded: {uploaded_file.name}")
        
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
            height=350,
            placeholder="// Paste your Verilog/SystemVerilog RTL here or upload a file above\n// We'll auto-detect the protocol and generate a matching UVM testbench",
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
                        
                        # Generate testbench using RTLAwareGenerator
                        generator = RTLAwareGenerator()
                        generated_files = generator.generate_from_rtl(rtl_code)
                        
                        # Combine all generated files into one result
                        result_parts = []
                        for filename, content in generated_files.items():
                            result_parts.append(f"// ==================== {filename} ====================\n{content}")
                        result = "\n\n".join(result_parts)
                        
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
            
            # Interactive Signal Explorer
            with st.expander("🔍 Signal Explorer", expanded=False):
                sig_data = get_signal_explorer_data(parsed)
                
                # Signal filter
                sig_filter = st.selectbox("Filter by type", ["All", "Inputs", "Outputs", "Clocks", "Resets"], key="sig_filter")
                
                # Display signals in a table-like format
                if sig_filter == "All" or sig_filter == "Inputs":
                    if sig_data['inputs']:
                        st.markdown("**📥 Inputs**")
                        for sig in sig_data['inputs'][:10]:
                            cat_badge = "🔧" if sig['category'] == 'control' else "📊"
                            st.markdown(f"- `{sig['name']}` {cat_badge} ({sig['width']} bit{'s' if sig['width'] > 1 else ''})")
                
                if sig_filter == "All" or sig_filter == "Outputs":
                    if sig_data['outputs']:
                        st.markdown("**📤 Outputs**")
                        for sig in sig_data['outputs'][:10]:
                            cat_badge = "🔧" if sig['category'] == 'control' else "📊"
                            st.markdown(f"- `{sig['name']}` {cat_badge} ({sig['width']} bit{'s' if sig['width'] > 1 else ''})")
                
                if sig_filter == "All" or sig_filter == "Clocks":
                    if sig_data['clocks']:
                        st.markdown("**⏰ Clocks**")
                        for sig in sig_data['clocks']:
                            st.markdown(f"- `{sig['name']}`")
                
                if sig_filter == "All" or sig_filter == "Resets":
                    if sig_data['resets']:
                        st.markdown("**🔄 Resets**")
                        for sig in sig_data['resets']:
                            active = "active-low" if sig.get('active_low') else "active-high"
                            st.markdown(f"- `{sig['name']}` ({active})")
            
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
                if protocol and protocol != "generic":
                    with st.expander("Interactive Protocol Timing", expanded=True):
                        wavedrom_json = generate_wavedrom(protocol)
                        render_wavedrom(wavedrom_json, height=200, key=f"wave_{protocol}")
            
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
                
                # Testbench Complexity Analysis
                tb_metrics = analyze_testbench_complexity(st.session_state['tb_result'])
                with st.expander("📊 Testbench Complexity Analysis", expanded=False):
                    m1, m2, m3, m4 = st.columns(4)
                    m1.metric("Classes", tb_metrics['classes'])
                    m2.metric("Tasks", tb_metrics['tasks'])
                    m3.metric("Covergroups", tb_metrics['covergroups'])
                    m4.metric("Constraints", tb_metrics['constraints'])
                    st.markdown(f"**Complexity Level:** {tb_metrics['complexity_level']} ({tb_metrics['complexity_score']}/10)")
                    st.progress(tb_metrics['complexity_score'] / 10)
                
                # Enhancement Suggestions
                suggestions = generate_enhancement_suggestions(parsed, st.session_state['tb_result'])
                if suggestions:
                    with st.expander("💡 Enhancement Suggestions", expanded=False):
                        for sug in suggestions:
                            priority_color = "#d73a49" if sug['priority'] == 'high' else ("#bf8700" if sug['priority'] == 'medium' else "#57606a")
                            st.markdown(f'''<div style="border-left: 3px solid {priority_color}; padding-left: 10px; margin-bottom: 10px;">
                                <strong>{sug['title']}</strong> <span style="color: {priority_color}; font-size: 0.8em;">({sug['priority'].upper()})</span><br/>
                                <span style="color: #57606a;">{sug['description']}</span>
                            </div>''', unsafe_allow_html=True)
                            with st.expander(f"Show example for {sug['title']}", expanded=False):
                                st.code(sug['example'], language="systemverilog")
                
                # UVM Component Tabs View
                components_dict = parse_uvm_components(st.session_state['tb_result'])
                
                # Always show the code first (default view)
                st.markdown("### Generated Code")
                
                if len(components_dict) > 1:
                    view_mode = st.radio("View Mode", ["Full Code", "Component Tabs"], horizontal=True, key="view_mode")
                    
                    if view_mode == "Component Tabs":
                        comp_tabs = st.tabs(list(components_dict.keys()))
                        for idx, (filename, content) in enumerate(components_dict.items()):
                            with comp_tabs[idx]:
                                st.code(content, language="systemverilog")
                                st.download_button(
                                    f"📄 Download {filename}",
                                    content,
                                    filename,
                                    key=f"dl_{filename}",
                                    use_container_width=True
                                )
                    else:
                        st.code(st.session_state['tb_result'], language="systemverilog")
                else:
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
                try:
                    # Use RTLAwareGenerator with protocol-specific sample RTL
                    generator = RTLAwareGenerator()
                    
                    # Create minimal protocol-specific RTL for generation
                    if protocol == "APB":
                        sample_rtl = f'''module {protocol.lower()}_dut #(
    parameter ADDR_WIDTH = {config.get('addr_width', 32)},
    parameter DATA_WIDTH = {config.get('data_width', 32)}
)(
    input wire pclk, input wire presetn,
    input wire psel, input wire penable, input wire pwrite,
    input wire [ADDR_WIDTH-1:0] paddr,
    input wire [DATA_WIDTH-1:0] pwdata,
    output reg [DATA_WIDTH-1:0] prdata,
    output reg pready, output reg pslverr
);
    reg [DATA_WIDTH-1:0] mem [0:255];
endmodule'''
                    elif protocol == "AXI4-Lite":
                        sample_rtl = f'''module axi4lite_dut #(
    parameter ADDR_WIDTH = {config.get('addr_width', 32)},
    parameter DATA_WIDTH = {config.get('data_width', 32)}
)(
    input wire aclk, input wire aresetn,
    input wire awvalid, output wire awready, input wire [ADDR_WIDTH-1:0] awaddr,
    input wire wvalid, output wire wready, input wire [DATA_WIDTH-1:0] wdata,
    output wire bvalid, input wire bready, output wire [1:0] bresp,
    input wire arvalid, output wire arready, input wire [ADDR_WIDTH-1:0] araddr,
    output wire rvalid, input wire rready, output wire [DATA_WIDTH-1:0] rdata
);
endmodule'''
                    elif protocol == "UART":
                        sample_rtl = f'''module uart_dut #(
    parameter BAUD_RATE = {config.get('baud_rate', 115200)}
)(
    input wire clk, input wire rst_n,
    input wire tx_valid, input wire [7:0] tx_data, output wire tx_ready,
    output wire rx_valid, output wire [7:0] rx_data,
    output wire tx, input wire rx
);
endmodule'''
                    elif protocol == "SPI":
                        sample_rtl = f'''module spi_dut #(
    parameter DATA_WIDTH = {config.get('data_width', 8)},
    parameter SPI_MODE = {config.get('mode', 0)}
)(
    input wire clk, input wire rst_n,
    output wire sclk, output wire mosi, input wire miso, output wire cs_n,
    input wire [DATA_WIDTH-1:0] tx_data, output wire [DATA_WIDTH-1:0] rx_data,
    input wire start, output wire done
);
endmodule'''
                    else:  # I2C
                        sample_rtl = '''module i2c_dut (
    input wire clk, input wire rst_n,
    inout wire sda, output wire scl,
    input wire [7:0] addr, input wire [7:0] data_in, output wire [7:0] data_out,
    input wire start, input wire rw, output wire done, output wire ack
);
endmodule'''
                    
                    generated_files = generator.generate_from_rtl(sample_rtl)
                    
                    # Combine all generated files
                    result_parts = []
                    for filename, content in generated_files.items():
                        result_parts.append(f"// ==================== {filename} ====================\n{content}")
                    result = "\n\n".join(result_parts)
                    st.session_state['proto_result'] = result
                except Exception as e:
                    st.session_state['proto_result'] = f"// Error generating testbench: {str(e)}"
    
    with col2:
        st.markdown('<div class="card-title">Generated Testbench</div>', unsafe_allow_html=True)
        
        # Show interactive protocol waveform - Always visible
        protocol_key = protocol.lower().replace('-', '').replace('4_', '4')
        st.markdown(f"**{protocol} Protocol Timing Diagram:**")
        wavedrom_json = generate_wavedrom(protocol_key)
        render_wavedrom(wavedrom_json, height=200, key=f"proto_{protocol_key}")
        
        if st.session_state.get('proto_result'):
            st.markdown("**Generated Code:**")
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
            st.info("👆 Configure parameters on the left and click **Generate** to create a testbench")

# Tab 3: Coverage Analysis
# Sample coverage report for template
SAMPLE_COVERAGE_REPORT = '''=== Functional Coverage Report ===
Overall Coverage: 72%

Covergroup: apb_cg (Instance: env.agent.monitor.cov)
  Coverpoint: addr_cp - 85%
    bin low_addr: 45 hits
    bin mid_addr: 32 hits  
    bin high_addr: 8 hits
  Coverpoint: write_cp - 90%
    bin read: 156 hits
    bin write: 142 hits
  Coverpoint: burst_cp - 45%
    bin burst_1: 89 hits
    bin burst_4: 12 hits
    bin burst_8: 0 hits  [UNCOVERED]
    bin burst_16: 0 hits [UNCOVERED]
  Coverpoint: error_cp - 20%
    bin no_error: 298 hits
    bin slverr: 3 hits
    bin timeout: 0 hits [UNCOVERED]

Cross Coverage:
  addr_write_cross: 67%
'''

with tabs[2]:
    col1, col2 = st.columns([1, 1], gap="medium")
    
    with col1:
        st.markdown('<div class="card-title">Coverage Report Input</div>', unsafe_allow_html=True)
        
        st.markdown("Paste your coverage report to identify gaps and get suggestions for improving coverage.")
        
        # Load sample button
        if st.button("📋 Load Sample Report", key="load_sample_cov", use_container_width=True):
            st.session_state['cov_input'] = SAMPLE_COVERAGE_REPORT
        
        cov_text = st.text_area(
            "Coverage",
            value=st.session_state.get('cov_input', ''),
            height=350,
            placeholder="Paste your coverage report here...\n\nSupported formats:\n- VCS URG reports\n- Questa coverage reports\n- Simple text summaries\n- JSON coverage data",
            label_visibility="collapsed"
        )
        
        if st.button("Analyze Coverage", type="primary", use_container_width=True, key="analyze"):
            if cov_text.strip():
                with st.spinner("Analyzing coverage report..."):
                    try:
                        # First try our simple regex parsing which works better
                        import re
                        
                        # Parse overall/total coverage - multiple patterns
                        total = 0.0
                        patterns = [
                            r'[Oo]verall\s*[Cc]overage[:\s]+([\d.]+)\s*%',
                            r'[Tt]otal\s*[Cc]overage[:\s]+([\d.]+)\s*%',
                            r'[Oo]verall[:\s]+([\d.]+)\s*%',
                            r'[Tt]otal[:\s]+([\d.]+)\s*%',
                            r'[Cc]overage[:\s]+([\d.]+)\s*%',
                        ]
                        for pattern in patterns:
                            match = re.search(pattern, cov_text)
                            if match:
                                total = float(match.group(1))
                                break
                        
                        # Parse coverpoint percentages
                        cp_matches = re.findall(r'([\w_]+)(?:_cp)?[:\s-]+\s*([\d.]+)\s*%', cov_text)
                        gaps = []
                        for name, pct in cp_matches:
                            pct_val = float(pct)
                            if pct_val < 90:
                                gaps.append(f"{name}: {pct_val:.0f}% (needs {90-pct_val:.0f}% more)")
                        
                        # Parse uncovered bins
                        uncovered = re.findall(r'bin\s+([\w_]+)[^\n]*(?:0\s*hits|UNCOVERED)', cov_text, re.IGNORECASE)
                        suggestions = [f"Add test to hit bin '{u}'" for u in uncovered[:10]]
                        
                        # Also look for general uncovered items
                        uncovered2 = re.findall(r'([\w_]+)[:\s]*0\s*hits', cov_text)
                        for u in uncovered2[:5]:
                            if u not in uncovered:
                                suggestions.append(f"Create sequence to cover '{u}'")
                        
                        st.session_state['cov_result'] = {
                            'total_coverage': total,
                            'gaps': gaps,
                            'suggestions': suggestions
                        }
                    except Exception as e:
                        st.error(f"Error analyzing: {str(e)}")
            else:
                st.warning("Please paste your coverage report first")
    
    with col2:
        st.markdown('<div class="card-title">Analysis Results</div>', unsafe_allow_html=True)
        
        if st.session_state.get('cov_result'):
            analysis = st.session_state['cov_result']
            
            # Overall metric
            total_cov = analysis.get('total_coverage', 0)
            st.metric("Overall Coverage", f"{total_cov:.1f}%", 
                      delta=f"{total_cov-95:.1f}% from 95% goal" if total_cov < 95 else "✓ Goal met!")
            
            # Progress bar
            st.progress(min(total_cov / 100, 1.0))
            
            # Gaps
            gaps = analysis.get('gaps', [])
            if gaps:
                st.markdown("**📉 Coverage Gaps Identified:**")
                for gap in gaps[:10]:
                    if isinstance(gap, str):
                        st.warning(gap)
                    else:
                        st.warning(str(gap))
            
            # Suggestions
            suggestions = analysis.get('suggestions', [])
            if suggestions:
                st.markdown("**💡 Recommended Actions:**")
                for i, s in enumerate(suggestions[:5], 1):
                    st.info(f"{i}. {s}")
            
            # Generate sequence code for gaps
            if gaps or suggestions:
                st.markdown("**🔧 Generated Test Sequence:**")
                seq_code = '''class coverage_closure_seq extends uvm_sequence #(apb_seq_item);
    `uvm_object_utils(coverage_closure_seq)
    
    function new(string name = "coverage_closure_seq");
        super.new(name);
    endfunction
    
    task body();
        apb_seq_item req;
        
        // Target uncovered bins
        repeat(20) begin
            req = apb_seq_item::type_id::create("req");
            start_item(req);
            
            // Randomize to hit gaps
            assert(req.randomize() with {
                // Force burst lengths to hit uncovered bins
                len inside {7, 15};  // burst_8, burst_16
                // Force error conditions
                if ($urandom_range(0,10) == 0) inject_error == 1;
            });
            
            finish_item(req);
        end
    endtask
endclass'''
                st.code(seq_code, language="systemverilog")
        else:
            st.info("👆 Paste a coverage report and click **Analyze Coverage** to see results.\n\nOr click **Load Sample Report** to try with example data.")

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
                            # SVAGenerator expects ParsedRTL, SimpleParsedRTL has _parsed attribute
                            if hasattr(parsed, '_parsed'):
                                sva_gen = SVAGenerator(parsed._parsed)
                            else:
                                sva_gen = SVAGenerator(parsed)
                            sva_module = sva_gen.generate_all()
                            result = sva_module.to_sv()
                            st.session_state['sva_result'] = result
                            st.session_state['sva_module'] = parsed.module_name
                            st.session_state['sva_count'] = result.count('assert property') + result.count('property ')
                        else:
                            # Generate assertions from natural language description
                            lines = sva_input.strip().split('\n')
                            assertions = []
                            for i, line in enumerate(lines):
                                line = line.strip()
                                if line.startswith('-'):
                                    line = line[1:].strip()
                                if not line:
                                    continue
                                prop_name = f"prop_{i+1}"
                                assertions.append(f'''// Assertion {i+1}: {line}
property {prop_name};
    @(posedge clk) disable iff (!rst_n)
    // TODO: Implement based on: {line}
    1; // Placeholder - customize this assertion
endproperty
assert property ({prop_name}) else $error("Assertion {prop_name} failed");
cover property ({prop_name});''')
                            result = f"// Generated SVA Assertions\n// Based on natural language requirements\n\nmodule assertions_bind;\n\n" + "\n\n".join(assertions) + "\n\nendmodule"
                            st.session_state['sva_result'] = result
                            st.session_state['sva_module'] = "custom"
                            st.session_state['sva_count'] = len(assertions)
                    except Exception as e:
                        # Fallback: generate basic assertions from port analysis
                        try:
                            parsed = parse_rtl(sva_input)
                            clk = parsed.clocks[0] if parsed.clocks else 'clk'
                            rst = parsed.resets[0] if parsed.resets else 'rst_n'
                            assertions = [f'''// Auto-generated SVA for {parsed.module_name}
// Clock: {clk}, Reset: {rst}

module {parsed.module_name}_sva_bind;

// Reset assertion
property p_reset_behavior;
    @(posedge {clk})
    !{rst} |-> ##1 1'b1; // Outputs stable after reset
endproperty
assert property (p_reset_behavior);
''']
                            # Add input/output stability assertions
                            for inp in parsed.inputs[:5]:
                                if inp not in [clk, rst]:
                                    assertions.append(f'''// Input stability check for {inp}
property p_{inp}_stable;
    @(posedge {clk}) disable iff (!{rst})
    $stable({inp}) || 1'b1; // Placeholder
endproperty''')
                            assertions.append('\nendmodule')
                            result = '\n'.join(assertions)
                            st.session_state['sva_result'] = result
                            st.session_state['sva_module'] = parsed.module_name
                            st.session_state['sva_count'] = result.count('property ')
                        except:
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
                        # Parse registers based on format
                        registers = []
                        if spec_format == "CSV (Simple)":
                            lines = reg_spec.strip().split('\n')
                            for line in lines[1:]:  # Skip header
                                parts = line.split(',')
                                if len(parts) >= 4:
                                    name = parts[0].strip()
                                    addr = parts[1].strip()
                                    width = int(parts[2].strip()) if len(parts) > 2 else 32
                                    access = parts[3].strip() if len(parts) > 3 else 'RW'
                                    reset = parts[4].strip() if len(parts) > 4 else '0x0'
                                    desc = parts[5].strip() if len(parts) > 5 else ''
                                    registers.append({
                                        'name': name,
                                        'address': addr,
                                        'width': width,
                                        'access': access,
                                        'reset_value': reset,
                                        'description': desc
                                    })
                        elif spec_format == "JSON":
                            import json as json_lib
                            data = json_lib.loads(reg_spec)
                            registers = data.get('registers', [])
                        else:
                            # Basic parsing for other formats
                            registers = [{'name': 'REG0', 'address': '0x00', 'width': 32, 'access': 'RW', 'reset_value': '0x0'}]
                        
                        st.session_state['reg_spec'] = {'registers': registers}
                        
                        # Generate UVM register model
                        reg_model = generate_uvm_reg_model(registers)
                        st.session_state['reg_result'] = reg_model
                    except Exception as e:
                        st.error(f"Error parsing: {str(e)}")
            else:
                st.warning("Please provide register specification")
    
    with col2:
        st.markdown('<div class="card-title">Register Map & Tests</div>', unsafe_allow_html=True)
        
        if st.session_state.get('reg_spec'):
            spec = st.session_state['reg_spec']
            registers = spec.get('registers', []) if isinstance(spec, dict) else []
            
            st.success(f"Parsed {len(registers)} registers")
            
            # Display register table
            st.markdown("**Register Map:**")
            reg_data = []
            for reg in registers[:10]:
                if isinstance(reg, dict):
                    reg_data.append({
                        "Name": reg.get('name', ''),
                        "Address": reg.get('address', '0x00'),
                        "Width": reg.get('width', 32),
                        "Access": reg.get('access', 'RW'),
                        "Reset": reg.get('reset_value', '0x0')
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
        <a href="https://github.com/tusharpathaknyu/UVMForge" target="_blank">GitHub</a>
        <span style="color: {theme['text_muted']}; margin: 0 0.5rem;">|</span>
        <a href="#" onclick="alert('Keyboard Shortcuts:\\n\\nCtrl+Enter: Generate\\nCtrl+S: Download\\nCtrl+H: Toggle History')">⌨️ Shortcuts</a>
    </div>
</div>
""", unsafe_allow_html=True)
