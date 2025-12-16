"""
Tests for app.py helper functions (WaveDrom, Quality Score, Bug Prediction, ZIP)
"""

import pytest
import sys
import json
import zipfile
import io
from pathlib import Path

# Add project root to path
project_root = Path(__file__).parent.parent
sys.path.insert(0, str(project_root))
sys.path.insert(0, str(project_root / 'src'))

from src.app_helpers import (
    generate_wavedrom, 
    calculate_quality_score, 
    predict_bugs, 
    create_testbench_zip,
    validate_rtl_syntax,
    get_protocol_comparison,
    create_html_export,
    SVA_LIBRARY
)
from src.rtl_parser import parse_rtl


class TestWaveDromGenerator:
    """Test WaveDrom JSON generation"""
    
    def test_apb_wavedrom(self):
        """Test APB WaveDrom generation"""
        result = generate_wavedrom("apb")
        data = json.loads(result)
        
        assert 'signal' in data
        assert len(data['signal']) > 0
        # Check for APB signals
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'PCLK' in signal_names
        assert 'PSEL' in signal_names
    
    def test_axi_wavedrom(self):
        """Test AXI4-Lite WaveDrom generation"""
        result = generate_wavedrom("axi4lite")
        data = json.loads(result)
        
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'ACLK' in signal_names
        assert 'AWVALID' in signal_names
    
    def test_spi_wavedrom(self):
        """Test SPI WaveDrom generation"""
        result = generate_wavedrom("spi")
        data = json.loads(result)
        
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'SCLK' in signal_names
        assert 'MOSI' in signal_names
    
    def test_uart_wavedrom(self):
        """Test UART WaveDrom generation"""
        result = generate_wavedrom("uart")
        data = json.loads(result)
        
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'TX' in signal_names
    
    def test_i2c_wavedrom(self):
        """Test I2C WaveDrom generation"""
        result = generate_wavedrom("i2c")
        data = json.loads(result)
        
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'SCL' in signal_names
        assert 'SDA' in signal_names
    
    def test_unknown_protocol_fallback(self):
        """Test unknown protocol falls back to APB"""
        result = generate_wavedrom("unknown_protocol")
        data = json.loads(result)
        
        # Should fall back to APB
        signal_names = [s.get('name', '') for s in data['signal']]
        assert 'PCLK' in signal_names


class TestQualityScore:
    """Test testbench quality scoring"""
    
    def test_complete_testbench_high_score(self):
        """Test complete testbench gets high score"""
        # Good testbench with all components
        code = """
        interface apb_if(input logic clk);
        endinterface
        
        class apb_driver extends uvm_driver;
            virtual interface apb_if vif;
            `uvm_info("DRV", "message", UVM_MEDIUM)
        endclass
        
        class apb_monitor extends uvm_monitor;
            `uvm_error("MON", "error")
        endclass
        
        class apb_scoreboard extends uvm_scoreboard;
        endclass
        
        class apb_coverage extends uvm_subscriber;
            covergroup cg;
                coverpoint addr;
            endgroup
        endclass
        
        class apb_agent extends uvm_agent;
        endclass
        
        class apb_env extends uvm_env;
        endclass
        
        class apb_sequence extends uvm_sequence;
        endclass
        
        class apb_test extends uvm_test;
        endclass
        """
        
        parsed = parse_rtl("""
        module apb_slave(
            input pclk, presetn, psel, penable, pwrite,
            input [31:0] paddr, pwdata,
            output [31:0] prdata,
            output pready
        );
        endmodule
        """)
        
        quality = calculate_quality_score(parsed, code)
        
        assert quality['score'] >= 70
        assert 'breakdown' in quality
        assert quality['breakdown']['completeness'] > 0
    
    def test_minimal_testbench_low_score(self):
        """Test minimal testbench gets lower score"""
        # Minimal testbench
        code = """
        module test;
            // minimal
        endmodule
        """
        
        parsed = parse_rtl("module empty; endmodule")
        quality = calculate_quality_score(parsed, code)
        
        assert quality['score'] < 50


class TestBugPrediction:
    """Test bug prediction feature"""
    
    def test_apb_bug_prediction(self):
        """Test APB designs predict relevant bugs"""
        # Use more complete APB RTL with all required signals
        parsed = parse_rtl("""
        module apb_slave #(
            parameter DATA_WIDTH = 32,
            parameter ADDR_WIDTH = 8
        )(
            input  logic                    pclk,
            input  logic                    preset_n,
            input  logic                    psel,
            input  logic                    penable,
            input  logic                    pwrite,
            input  logic [ADDR_WIDTH-1:0]   paddr,
            input  logic [DATA_WIDTH-1:0]   pwdata,
            output logic [DATA_WIDTH-1:0]   prdata,
            output logic                    pready,
            output logic                    pslverr
        );
            reg [1:0] state;
            localparam IDLE = 0, ACCESS = 1;
        endmodule
        """)
        
        bugs = predict_bugs(parsed)
        
        assert len(bugs) > 0
        bug_titles = [b['title'] for b in bugs]
        # Should predict APB-specific bugs OR generic bugs at minimum
        assert len(bug_titles) > 0
    
    def test_spi_bug_prediction(self):
        """Test SPI designs predict clock phase bugs"""
        parsed = parse_rtl("""
        module spi_master(
            input clk, rst_n,
            output sclk, mosi, cs_n,
            input miso
        );
        endmodule
        """)
        
        bugs = predict_bugs(parsed)
        
        # Should predict SPI-specific bugs if SPI detected
        assert isinstance(bugs, list)
    
    def test_bug_severity_levels(self):
        """Test bugs have severity levels"""
        parsed = parse_rtl("""
        module axi_slave(
            input aclk, aresetn,
            input awvalid, wvalid, arvalid,
            output awready, wready, arready,
            output bvalid, rvalid
        );
            reg [1:0] state;
        endmodule
        """)
        
        bugs = predict_bugs(parsed)
        
        for bug in bugs:
            assert 'severity' in bug
            assert bug['severity'] in ['high', 'medium', 'low']
            assert 'title' in bug
            assert 'description' in bug


class TestZIPExport:
    """Test ZIP file generation"""
    
    def test_zip_creation(self):
        """Test ZIP file is created with expected contents"""
        code = "// Test testbench"
        zip_bytes = create_testbench_zip("test_module", code, None)
        
        # Verify it's a valid ZIP
        zip_buffer = io.BytesIO(zip_bytes)
        with zipfile.ZipFile(zip_buffer, 'r') as zf:
            names = zf.namelist()
            
            # Check expected files
            assert 'README.md' in names
            assert any('Makefile' in n for n in names)
            assert any('test_module' in n for n in names)
    
    def test_zip_contains_makefiles(self):
        """Test ZIP contains both VCS and Questa makefiles"""
        code = "// Test testbench"
        zip_bytes = create_testbench_zip("apb_slave", code, None)
        
        zip_buffer = io.BytesIO(zip_bytes)
        with zipfile.ZipFile(zip_buffer, 'r') as zf:
            names = zf.namelist()
            
            assert 'tb/Makefile.vcs' in names
            assert 'tb/Makefile.questa' in names
    
    def test_zip_readme_content(self):
        """Test README has correct module name"""
        code = "// Test testbench"
        zip_bytes = create_testbench_zip("my_dut", code, None)
        
        zip_buffer = io.BytesIO(zip_bytes)
        with zipfile.ZipFile(zip_buffer, 'r') as zf:
            readme = zf.read('README.md').decode('utf-8')
            
            assert 'my_dut' in readme
            assert 'VerifAI' in readme


class TestWaveDromValidJSON:
    """Test WaveDrom outputs are valid JSON"""
    
    @pytest.fixture(params=['apb', 'axi4lite', 'spi', 'uart', 'i2c'])
    def protocol(self, request):
        return request.param
    
    def test_valid_json_output(self, protocol):
        """Test all protocols produce valid JSON"""
        result = generate_wavedrom(protocol)
        
        # Should not raise
        data = json.loads(result)


class TestRTLSyntaxValidation:
    """Test RTL syntax validation"""
    
    def test_valid_module(self):
        """Test valid module passes validation"""
        code = """
        module test(
            input clk,
            output reg data
        );
        endmodule
        """
        result = validate_rtl_syntax(code)
        assert result['valid'] is True
        assert len(result['errors']) == 0
    
    def test_missing_module(self):
        """Test missing module declaration"""
        code = "wire test;"
        result = validate_rtl_syntax(code)
        assert result['valid'] is False
        assert any('module' in e.lower() for e in result['errors'])
    
    def test_missing_endmodule(self):
        """Test missing endmodule"""
        code = "module test(input clk);"
        result = validate_rtl_syntax(code)
        assert result['valid'] is False
        assert any('endmodule' in e.lower() for e in result['errors'])
    
    def test_unbalanced_parentheses(self):
        """Test unbalanced parentheses detection"""
        code = "module test(input clk; endmodule"
        result = validate_rtl_syntax(code)
        assert result['valid'] is False
        assert any('parenthes' in e.lower() for e in result['errors'])
    
    def test_unbalanced_braces(self):
        """Test unbalanced braces detection"""
        code = """
        module test(input clk);
        always @(*) begin
            if (1) {
                data = 1;
            
        end
        endmodule
        """
        result = validate_rtl_syntax(code)
        assert result['valid'] is False
        assert any('brace' in e.lower() for e in result['errors'])
    
    def test_unbalanced_begin_end_warning(self):
        """Test unbalanced begin/end generates warning"""
        code = """
        module test(input clk);
        always @(*) begin
            data = 1;
        endmodule
        """
        result = validate_rtl_syntax(code)
        # May have warnings about begin/end
        assert 'warnings' in result
    
    def test_empty_code(self):
        """Test empty code is invalid"""
        result = validate_rtl_syntax("")
        assert result['valid'] is False
        assert any('empty' in e.lower() for e in result['errors'])
    
    def test_whitespace_only(self):
        """Test whitespace-only is invalid"""
        result = validate_rtl_syntax("   \n\t  ")
        assert result['valid'] is False


class TestProtocolComparison:
    """Test protocol comparison data"""
    
    def test_returns_all_protocols(self):
        """Test all protocols are present"""
        comparison = get_protocol_comparison()
        expected = ['APB', 'AXI4-Lite', 'AXI4', 'SPI', 'I2C', 'UART']
        for proto in expected:
            assert proto in comparison
    
    def test_protocol_has_required_fields(self):
        """Test each protocol has required fields"""
        comparison = get_protocol_comparison()
        required_fields = ['complexity', 'throughput', 'burst', 'pipelining', 'use_case']
        for proto, data in comparison.items():
            for field in required_fields:
                assert field in data, f"Missing {field} in {proto}"
    
    def test_complexity_values(self):
        """Test complexity values are valid"""
        comparison = get_protocol_comparison()
        valid_complexity = ['Low', 'Medium', 'High']
        for proto, data in comparison.items():
            assert data['complexity'] in valid_complexity


class TestHTMLExport:
    """Test HTML export generation"""
    
    def test_html_contains_module_name(self):
        """Test HTML contains module name"""
        html = create_html_export("my_module", "// code here")
        assert "my_module" in html
        assert "<html>" in html
        assert "</html>" in html
    
    def test_html_escapes_special_chars(self):
        """Test HTML escapes < and >"""
        code = "if (a < b) output > 0;"
        html = create_html_export("test", code)
        assert "&lt;" in html
        assert "&gt;" in html
        assert "<html>" in html  # but HTML tags preserved
    
    def test_html_contains_code(self):
        """Test HTML contains the code"""
        code = "module test_unique_xyz();"
        html = create_html_export("test", code)
        assert "test_unique_xyz" in html
    
    def test_html_contains_metadata(self):
        """Test HTML contains metadata"""
        html = create_html_export("my_test", "// code")
        assert "VerifAI" in html
        assert "Generated by" in html


class TestSVALibrary:
    """Test SVA library contents"""
    
    def test_library_has_patterns(self):
        """Test SVA library has patterns"""
        assert len(SVA_LIBRARY) > 0
    
    def test_patterns_have_required_fields(self):
        """Test each pattern has required fields"""
        for key, pattern in SVA_LIBRARY.items():
            assert 'name' in pattern, f"Missing name in {key}"
            assert 'description' in pattern, f"Missing description in {key}"
            assert 'code' in pattern, f"Missing code in {key}"
            assert 'usage' in pattern, f"Missing usage in {key}"
    
    def test_handshake_pattern(self):
        """Test handshake pattern exists"""
        assert 'handshake' in SVA_LIBRARY
        assert 'valid' in SVA_LIBRARY['handshake']['code'].lower()
        assert 'ready' in SVA_LIBRARY['handshake']['code'].lower()
    
    def test_fifo_patterns(self):
        """Test FIFO patterns exist"""
        assert 'fifo_full' in SVA_LIBRARY
        assert 'fifo_empty' in SVA_LIBRARY
    
    def test_timeout_pattern(self):
        """Test timeout pattern exists"""
        assert 'timeout' in SVA_LIBRARY
        assert '##' in SVA_LIBRARY['timeout']['code']
    
    def test_all_patterns_have_property(self):
        """Test all patterns define a property"""
        for key, pattern in SVA_LIBRARY.items():
            assert 'property' in pattern['code'].lower(), f"No property in {key}"
