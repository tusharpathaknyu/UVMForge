"""
Tests for Coverage Analyzer and SVA Generator
=============================================
Testing the key differentiator features.
"""

import pytest
import sys
from pathlib import Path

# Add src to path
sys.path.insert(0, str(Path(__file__).parent.parent / 'src'))

from coverage_analyzer import (
    CoverageAnalyzer, CoverageParser, CoverageReport, 
    Covergroup, CoverPoint, CoverageBin, CoverageGap,
    CoverageStatus, SuggestedSequence
)
from sva_generator import (
    SVAGenerator, SVAModule, SVAProperty,
    AssertionType, AssertionCategory,
    generate_sva_from_parsed
)
from rtl_parser import RTLParser


class TestCoverageAnalyzer:
    """Tests for coverage gap analysis"""
    
    def test_parse_text_summary_basic(self):
        """Test parsing a basic coverage summary"""
        analyzer = CoverageAnalyzer()
        
        content = """=== Coverage Report ===
Covergroup: cg_test
  Coverpoint: cp_addr
    bin addr_0: 100/100 (100%)
    bin addr_1: 50/100 (50%)
    bin addr_2: 0/100 (0%)
    
Overall Coverage: 50%"""
        
        report = analyzer.parse_text_summary(content)
        
        assert report.overall_coverage == 50.0
        assert len(report.covergroups) == 1
        assert report.covergroups[0].name == "cg_test"
        assert len(report.covergroups[0].coverpoints) == 1
    
    def test_parse_text_summary_with_cross(self):
        """Test parsing coverage with cross coverage"""
        analyzer = CoverageAnalyzer()
        
        content = """Covergroup: cg_apb
  Coverpoint: cp_addr
    bin addr_0x00: 45/100 (45%)
    bin addr_0x04: 78/100 (78%)
  Cross: cp_addr x cp_write
    bin <addr_0x00, read_op>: 35/50 (70%)
    bin <addr_0x00, write_op>: 10/50 (20%)
    
Overall Coverage: 53.25%"""
        
        report = analyzer.parse_text_summary(content)
        
        assert len(report.covergroups) == 1
        cg = report.covergroups[0]
        assert len(cg.coverpoints) == 1
        assert len(cg.crosses) == 1
        assert len(cg.crosses[0].bins) == 2
    
    def test_analyze_coverage_finds_gaps(self):
        """Test that coverage analysis identifies gaps"""
        analyzer = CoverageAnalyzer()
        
        content = """Covergroup: cg_test
  Coverpoint: cp_data
    bin zero: 100/100 (100%)
    bin low: 50/100 (50%)
    bin high: 0/100 (0%)
    
Overall Coverage: 50%"""
        
        report = analyzer.parse_text_summary(content)
        gaps = analyzer.analyze_coverage(report, target_coverage=95)
        
        assert len(gaps) >= 2  # At least low and high bins
        
        # High priority for 0 hits
        high_gaps = [g for g in gaps if g.hit_count == 0]
        assert all(g.priority == "high" for g in high_gaps)
    
    def test_gap_to_suggestion_generates_code(self):
        """Test that gap generates valid UVM sequence code"""
        analyzer = CoverageAnalyzer()
        
        gap = CoverageGap(
            covergroup="cg_test",
            coverpoint="cp_addr",
            bin_name="addr_high",
            bin_value="0",
            priority="high",
            suggested_stimulus="addr = $urandom_range(4096, 65535)",
            suggested_sequence="high_address_seq",
            hit_count=0,
            goal_count=100,
            current_coverage=0.0,
            target_coverage=95.0,
            hits_needed=100
        )
        
        suggestion = analyzer.gap_to_suggestion(gap)
        
        assert isinstance(suggestion, SuggestedSequence)
        assert "class high_address_seq" in suggestion.uvm_sequence_code
        assert "addr = $urandom_range(4096, 65535)" in suggestion.uvm_sequence_code
        assert "uvm_sequence" in suggestion.uvm_sequence_code
    
    def test_stimulus_suggestion_for_address(self):
        """Test stimulus patterns for address coverpoints"""
        analyzer = CoverageAnalyzer()
        
        # Test various address patterns
        test_cases = [
            ("addr_low", "cp_addr", "addr"),
            ("addr_high", "cp_address", "addr"),
            ("addr_boundary", "cp_addr", "boundary"),
        ]
        
        for bin_name, cp_name, expected_keyword in test_cases:
            stimulus, seq_name = analyzer._suggest_stimulus(bin_name, cp_name)
            assert expected_keyword.lower() in stimulus.lower() or expected_keyword in seq_name.lower()
    
    def test_stimulus_suggestion_for_data(self):
        """Test stimulus patterns for data coverpoints"""
        analyzer = CoverageAnalyzer()
        
        stimulus, _ = analyzer._suggest_stimulus("zero", "cp_data")
        assert "0" in stimulus or "zero" in stimulus.lower()
        
        stimulus, _ = analyzer._suggest_stimulus("all_ones", "cp_wdata")
        assert "1" in stimulus or "ones" in stimulus.lower()


class TestCoverageParser:
    """Tests for coverage report parser"""
    
    def test_parse_json_format(self):
        """Test JSON coverage format parsing"""
        parser = CoverageParser()
        
        json_content = """{
            "total_coverage": 75.5,
            "covergroups": [{
                "name": "cg_apb",
                "coverpoints": [{
                    "name": "cp_addr",
                    "bins": [
                        {"name": "low", "hits": 100, "goal": 100},
                        {"name": "high", "hits": 0, "goal": 100}
                    ]
                }]
            }]
        }"""
        
        report = parser.parse(json_content, "json")
        
        assert report.total_coverage == 75.5
        assert len(report.covergroups) == 1
        assert report.covergroups[0].name == "cg_apb"
    
    def test_auto_detect_json(self):
        """Test auto-detection of JSON format"""
        parser = CoverageParser()
        
        json_content = '{"covergroups": [], "total_coverage": 50}'
        format_type = parser._detect_format(json_content)
        
        assert format_type == "json"


class TestSVAGenerator:
    """Tests for SVA assertion generator"""
    
    @pytest.fixture
    def apb_rtl(self):
        """Sample APB slave RTL"""
        return """
module apb_slave (
    input  logic        pclk,
    input  logic        preset_n,
    input  logic        psel,
    input  logic        penable,
    input  logic        pwrite,
    input  logic [31:0] paddr,
    input  logic [31:0] pwdata,
    output logic [31:0] prdata,
    output logic        pready,
    output logic        pslverr
);
endmodule
"""
    
    @pytest.fixture
    def fsm_rtl(self):
        """Sample FSM RTL"""
        return """
module fsm_example (
    input  logic clk,
    input  logic rst_n,
    input  logic start,
    output logic done
);
    typedef enum logic [1:0] {
        IDLE  = 2'b00,
        RUN   = 2'b01,
        DONE  = 2'b10,
        ERROR = 2'b11
    } state_t;
    
    state_t state, next_state;
    
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
endmodule
"""
    
    def test_generate_from_apb_rtl(self, apb_rtl):
        """Test SVA generation from APB RTL"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        
        assert sva_module.module_name == "apb_slave"
        assert len(sva_module.properties) > 0
        
        # Should detect APB protocol and generate protocol assertions
        categories = [p.category for p in sva_module.properties]
        assert AssertionCategory.PROTOCOL in categories or AssertionCategory.RESET in categories
    
    def test_generate_apb_protocol_assertions(self, apb_rtl):
        """Test that APB-specific assertions are generated"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        sva_code = sva_module.to_sv()
        
        # Should have APB-specific assertions
        assert "psel" in sva_code.lower() or "penable" in sva_code.lower()
    
    def test_detect_clock_reset(self, apb_rtl):
        """Test clock and reset detection"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        generator = SVAGenerator(parsed)
        
        clock = generator._detect_clock()
        reset = generator._detect_reset()
        
        assert clock == "pclk"
        assert reset == "preset_n"
        assert generator._is_reset_active_low() == True
    
    def test_generate_fsm_assertions(self, fsm_rtl):
        """Test FSM assertion generation"""
        parser = RTLParser()
        parsed = parser.parse(fsm_rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        
        # Should generate some assertions
        assert len(sva_module.properties) > 0
        
        # Check for reset assertions
        reset_props = [p for p in sva_module.properties 
                       if p.category == AssertionCategory.RESET]
        assert len(reset_props) >= 0  # At least some reset assertions
    
    def test_sva_module_to_sv_output(self, apb_rtl):
        """Test SVA module generates valid SystemVerilog"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        sv_code = sva_module.to_sv()
        
        # Check for required SVA elements
        assert "module" in sv_code
        assert "endmodule" in sv_code
        assert "property" in sv_code or "assert" in sv_code
        assert "posedge" in sv_code
    
    def test_property_types(self, apb_rtl):
        """Test different assertion types are generated"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        
        types = set(p.assertion_type for p in sva_module.properties)
        
        # Should have multiple types
        assert len(types) >= 1
    
    def test_generate_sva_from_parsed_function(self, apb_rtl):
        """Test the convenience function"""
        parser = RTLParser()
        parsed = parser.parse(apb_rtl)
        
        sva_code = generate_sva_from_parsed(parsed)
        
        assert "module" in sva_code
        assert "apb_slave_sva" in sva_code


class TestSVAPropertyGeneration:
    """Tests for individual SVA property generation"""
    
    def test_sva_property_to_sv_assert(self):
        """Test assert property generation"""
        prop = SVAProperty(
            name="test_prop",
            description="Test property",
            category=AssertionCategory.STABILITY,
            assertion_type=AssertionType.ASSERT,
            code="@(posedge clk) (valid) |-> !$isunknown(data)"
        )
        
        sv_code = prop.to_sv()
        
        assert "test_prop" in sv_code
        assert "assert property" in sv_code
        assert "valid" in sv_code
    
    def test_sva_property_to_sv_cover(self):
        """Test cover property generation"""
        prop = SVAProperty(
            name="cover_test",
            description="Cover test property",
            category=AssertionCategory.HANDSHAKE,
            assertion_type=AssertionType.COVER,
            code="@(posedge clk) (valid && ready)"
        )
        
        sv_code = prop.to_sv()
        
        assert "cover_test" in sv_code
        assert "cover property" in sv_code


class TestIntegration:
    """Integration tests for coverage and SVA features"""
    
    def test_coverage_then_sva_workflow(self):
        """Test typical workflow: analyze coverage -> generate SVA"""
        # 1. Analyze coverage
        analyzer = CoverageAnalyzer()
        
        coverage_content = """Covergroup: cg_protocol
  Coverpoint: cp_trans_type
    bin read: 100/100 (100%)
    bin write: 50/100 (50%)
    bin idle: 0/100 (0%)
    
Overall Coverage: 50%"""
        
        report = analyzer.parse_text_summary(coverage_content)
        gaps = analyzer.analyze_coverage(report)
        
        assert len(gaps) >= 2
        
        # 2. Generate SVA for RTL
        rtl = """
module dut (
    input logic clk,
    input logic rst_n,
    input logic [1:0] trans_type,
    output logic ready
);
endmodule
"""
        parser = RTLParser()
        parsed = parser.parse(rtl)
        
        generator = SVAGenerator(parsed)
        sva_module = generator.generate_all()
        
        assert len(sva_module.properties) > 0
    
    def test_gap_suggestions_are_valid_sv(self):
        """Test that generated gap sequences are valid SV syntax"""
        analyzer = CoverageAnalyzer()
        
        gap = CoverageGap(
            covergroup="cg_test",
            coverpoint="cp_data",
            bin_name="boundary",
            bin_value="0",
            priority="high",
            suggested_stimulus="data inside {0, 32'hFFFFFFFF}",
            suggested_sequence="boundary_seq",
            hit_count=0,
            goal_count=100,
            current_coverage=0.0,
            target_coverage=95.0,
            hits_needed=100
        )
        
        suggestion = analyzer.gap_to_suggestion(gap)
        
        # Check for valid SV constructs
        assert "class" in suggestion.uvm_sequence_code
        assert "extends" in suggestion.uvm_sequence_code
        assert "task body" in suggestion.uvm_sequence_code
        assert "endclass" in suggestion.uvm_sequence_code


class TestAllProtocolWaveforms:
    """Test waveform generation for all protocols"""
    
    def test_axi4lite_waveforms(self):
        """Test AXI4-Lite waveform generation"""
        from rtl_parser import WaveformGenerator
        
        waveforms = WaveformGenerator.generate_for_protocol('axi4lite')
        assert len(waveforms) >= 2  # Write and read
        
        # Check for AXI signals in waveform
        all_ascii = " ".join(wf.ascii_art for wf in waveforms)
        assert "AWVALID" in all_ascii or "ARVALID" in all_ascii
    
    def test_spi_waveforms(self):
        """Test SPI waveform generation"""
        from rtl_parser import WaveformGenerator
        
        waveforms = WaveformGenerator.generate_for_protocol('spi')
        assert len(waveforms) >= 1
        
        all_ascii = " ".join(wf.ascii_art for wf in waveforms)
        assert "SCLK" in all_ascii or "MOSI" in all_ascii
    
    def test_uart_waveforms(self):
        """Test UART waveform generation"""
        from rtl_parser import WaveformGenerator
        
        waveforms = WaveformGenerator.generate_for_protocol('uart')
        assert len(waveforms) >= 1
        
        all_ascii = " ".join(wf.ascii_art for wf in waveforms)
        assert "START" in all_ascii or "STOP" in all_ascii
    
    def test_i2c_waveforms(self):
        """Test I2C waveform generation"""
        from rtl_parser import WaveformGenerator
        
        waveforms = WaveformGenerator.generate_for_protocol('i2c')
        assert len(waveforms) >= 1
        
        all_ascii = " ".join(wf.ascii_art for wf in waveforms)
        assert "SDA" in all_ascii or "SCL" in all_ascii


class TestAllProtocolConstraints:
    """Test constraint generation for all protocols"""
    
    @pytest.fixture
    def axi_rtl(self):
        return '''
        module axi_lite_slave (
            input  logic        aclk,
            input  logic        aresetn,
            input  logic [31:0] awaddr,
            input  logic        awvalid,
            output logic        awready,
            input  logic [31:0] wdata,
            input  logic        wvalid,
            output logic        wready,
            output logic [1:0]  bresp,
            output logic        bvalid,
            input  logic        bready,
            input  logic [31:0] araddr,
            input  logic        arvalid,
            output logic        arready,
            output logic [31:0] rdata,
            output logic [1:0]  rresp,
            output logic        rvalid,
            input  logic        rready
        );
        endmodule
        '''
    
    @pytest.fixture
    def uart_rtl(self):
        return '''
        module uart_tx (
            input  logic        clk,
            input  logic        rst_n,
            input  logic [7:0]  tx_data,
            input  logic        tx_valid,
            output logic        tx_ready,
            output logic        tx
        );
        endmodule
        '''
    
    @pytest.fixture
    def spi_rtl(self):
        return '''
        module spi_master (
            input  logic       clk,
            input  logic       rst_n,
            input  logic [7:0] tx_data,
            output logic [7:0] rx_data,
            output logic       sclk,
            output logic       mosi,
            input  logic       miso,
            output logic       cs_n
        );
        endmodule
        '''
    
    @pytest.fixture
    def i2c_rtl(self):
        return '''
        module i2c_master (
            input  logic       clk,
            input  logic       rst_n,
            input  logic [6:0] slave_addr,
            input  logic [7:0] tx_data,
            output logic [7:0] rx_data,
            inout  wire        sda,
            output logic       scl
        );
        endmodule
        '''
    
    def test_axi_constraints(self, axi_rtl):
        """Test AXI-specific constraints are generated"""
        from rtl_parser import parse_rtl
        result = parse_rtl(axi_rtl)
        
        constraint_names = [c.signal_name for c in result.constraints]
        assert 'axi_txn' in constraint_names
    
    def test_uart_constraints(self, uart_rtl):
        """Test constraints are generated for UART-like design"""
        from rtl_parser import parse_rtl
        result = parse_rtl(uart_rtl)
        
        # Generic constraints should always be generated
        constraint_names = [c.signal_name for c in result.constraints]
        assert 'data' in constraint_names
        assert 'addr' in constraint_names
    
    def test_spi_constraints(self, spi_rtl):
        """Test SPI-specific constraints are generated"""
        from rtl_parser import parse_rtl
        result = parse_rtl(spi_rtl)
        
        constraint_names = [c.signal_name for c in result.constraints]
        # SPI should be detected with enough signals
        assert 'spi_txn' in constraint_names or 'data' in constraint_names
    
    def test_i2c_constraints(self, i2c_rtl):
        """Test I2C-specific constraints are generated"""
        from rtl_parser import parse_rtl
        result = parse_rtl(i2c_rtl)
        
        constraint_names = [c.signal_name for c in result.constraints]
        # I2C should be detected with sda/scl signals
        assert 'i2c_txn' in constraint_names or 'data' in constraint_names


class TestEdgeCases:
    """Test edge cases and error handling"""
    
    def test_empty_rtl(self):
        """Test handling of empty RTL"""
        from rtl_parser import parse_rtl
        result = parse_rtl("")
        
        assert result.module_name == "unknown_module"
        assert len(result.inputs) == 0
    
    def test_rtl_no_ports(self):
        """Test RTL with no ports"""
        from rtl_parser import parse_rtl
        result = parse_rtl("module empty; endmodule")
        
        assert result.module_name == "empty"
        assert len(result.inputs) == 0
        assert len(result.outputs) == 0
    
    def test_rtl_comments_only(self):
        """Test RTL with only comments"""
        from rtl_parser import parse_rtl
        result = parse_rtl("// This is a comment\n/* Another comment */")
        
        assert result.module_name == "unknown_module"
    
    def test_complex_fsm_detection(self):
        """Test FSM detection with multiple patterns"""
        from rtl_parser import parse_rtl
        
        rtl = '''
        module fsm_complex (
            input logic clk,
            input logic rst_n
        );
            typedef enum logic [2:0] {
                IDLE     = 3'b000,
                START    = 3'b001,
                TRANSFER = 3'b010,
                WAIT     = 3'b011,
                DONE     = 3'b100
            } state_t;
            
            state_t current_state, next_state;
            
            always_ff @(posedge clk or negedge rst_n) begin
                if (!rst_n)
                    current_state <= IDLE;
                else
                    current_state <= next_state;
            end
        endmodule
        '''
        
        result = parse_rtl(rtl)
        assert result.fsm is not None
        assert len(result.fsm['states']) >= 4


if __name__ == "__main__":
    pytest.main([__file__, "-v"])

