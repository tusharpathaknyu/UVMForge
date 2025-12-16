"""
Coverage Gap Analyzer
=====================
Analyzes coverage reports and suggests sequences to close coverage gaps.

This is a MAJOR differentiator - no chatbot can do this!
It actually reads your coverage data and suggests targeted tests.
"""

import re
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Tuple, Any
from enum import Enum
from pathlib import Path
import json


class CoverageType(Enum):
    CODE = "code"
    FUNCTIONAL = "functional"
    TOGGLE = "toggle"
    FSM = "fsm"
    ASSERTION = "assertion"


class CoverageStatus(Enum):
    COVERED = "covered"
    UNCOVERED = "uncovered"
    PARTIAL = "partial"


@dataclass
class CoverageBin:
    """Represents a single coverage bin"""
    name: str
    hits: int
    goal: int = 1
    status: CoverageStatus = CoverageStatus.UNCOVERED
    
    @property
    def is_covered(self) -> bool:
        return self.hits >= self.goal
    
    @property
    def coverage_pct(self) -> float:
        if self.goal == 0:
            return 100.0
        return min(100.0, (self.hits / self.goal) * 100)


@dataclass
class CoverPoint:
    """Represents a coverpoint with bins"""
    name: str
    bins: List[CoverageBin] = field(default_factory=list)
    expression: str = ""
    
    @property
    def coverage_pct(self) -> float:
        if not self.bins:
            return 0.0
        covered = sum(1 for b in self.bins if b.is_covered)
        return (covered / len(self.bins)) * 100
    
    @property
    def uncovered_bins(self) -> List[CoverageBin]:
        return [b for b in self.bins if not b.is_covered]


@dataclass
class CrossCoverage:
    """Represents cross coverage"""
    name: str
    coverpoints: List[str]
    bins: List[CoverageBin] = field(default_factory=list)
    
    @property
    def coverage_pct(self) -> float:
        if not self.bins:
            return 0.0
        covered = sum(1 for b in self.bins if b.is_covered)
        return (covered / len(self.bins)) * 100


@dataclass
class Covergroup:
    """Represents a covergroup"""
    name: str
    coverpoints: List[CoverPoint] = field(default_factory=list)
    crosses: List[CrossCoverage] = field(default_factory=list)
    
    @property
    def coverage_pct(self) -> float:
        total_bins = sum(len(cp.bins) for cp in self.coverpoints)
        total_bins += sum(len(cr.bins) for cr in self.crosses)
        if total_bins == 0:
            return 0.0
        covered = sum(sum(1 for b in cp.bins if b.is_covered) for cp in self.coverpoints)
        covered += sum(sum(1 for b in cr.bins if b.is_covered) for cr in self.crosses)
        return (covered / total_bins) * 100


@dataclass 
class CoverageGap:
    """Represents a coverage gap that needs to be closed"""
    covergroup: str
    coverpoint: str
    bin_name: str
    bin_value: str
    priority: str  # high, medium, low
    suggested_stimulus: str
    suggested_sequence: str
    hit_count: int = 0
    goal_count: int = 1
    current_coverage: float = 0.0
    target_coverage: float = 100.0
    hits_needed: int = 1


@dataclass
class SuggestedSequence:
    """A suggested UVM sequence to close a coverage gap"""
    name: str
    description: str
    uvm_sequence_code: str
    stimulus_values: str = ""
    expected_coverage_gain: float = 0.0
    

@dataclass
class CoverageReport:
    """Complete coverage report"""
    source_file: str
    total_coverage: float
    covergroups: List[Covergroup] = field(default_factory=list)
    gaps: List[CoverageGap] = field(default_factory=list)
    
    @property
    def overall_coverage(self) -> float:
        return self.total_coverage


class CoverageParser:
    """
    Parses coverage reports from various EDA tools.
    Supports: VCS, Questa, Xcelium, Verilator formats
    """
    
    def parse(self, content: str, format_type: str = "auto") -> CoverageReport:
        """Parse coverage report content"""
        if format_type == "auto":
            format_type = self._detect_format(content)
        
        if format_type == "vcs":
            return self._parse_vcs(content)
        elif format_type == "questa":
            return self._parse_questa(content)
        elif format_type == "json":
            return self._parse_json(content)
        elif format_type == "simple":
            return self._parse_simple(content)
        else:
            return self._parse_simple(content)
    
    def _detect_format(self, content: str) -> str:
        """Detect coverage report format"""
        if '"covergroups"' in content or '"coverage"' in content:
            return "json"
        elif "URG" in content or "vcs" in content.lower():
            return "vcs"
        elif "questa" in content.lower() or "modelsim" in content.lower():
            return "questa"
        else:
            return "simple"
    
    def _parse_json(self, content: str) -> CoverageReport:
        """Parse JSON coverage format"""
        data = json.loads(content)
        
        covergroups = []
        for cg_data in data.get('covergroups', []):
            coverpoints = []
            for cp_data in cg_data.get('coverpoints', []):
                bins = []
                for bin_data in cp_data.get('bins', []):
                    bins.append(CoverageBin(
                        name=bin_data.get('name', ''),
                        hits=bin_data.get('hits', 0),
                        goal=bin_data.get('goal', 1),
                        status=CoverageStatus.COVERED if bin_data.get('hits', 0) > 0 else CoverageStatus.UNCOVERED
                    ))
                coverpoints.append(CoverPoint(
                    name=cp_data.get('name', ''),
                    bins=bins,
                    expression=cp_data.get('expression', '')
                ))
            
            covergroups.append(Covergroup(
                name=cg_data.get('name', ''),
                coverpoints=coverpoints
            ))
        
        return CoverageReport(
            source_file="json",
            total_coverage=data.get('total_coverage', 0.0),
            covergroups=covergroups
        )
    
    def _parse_simple(self, content: str) -> CoverageReport:
        """Parse simple text coverage format"""
        covergroups = []
        current_cg = None
        current_cp = None
        
        for line in content.split('\n'):
            line = line.strip()
            
            # Covergroup
            cg_match = re.match(r'(?:covergroup|cg)\s+(\w+).*?(\d+(?:\.\d+)?)\s*%', line, re.IGNORECASE)
            if cg_match:
                if current_cg:
                    covergroups.append(current_cg)
                current_cg = Covergroup(name=cg_match.group(1))
                continue
            
            # Coverpoint
            cp_match = re.match(r'(?:coverpoint|cp)\s+(\w+).*?(\d+(?:\.\d+)?)\s*%', line, re.IGNORECASE)
            if cp_match and current_cg:
                current_cp = CoverPoint(name=cp_match.group(1))
                current_cg.coverpoints.append(current_cp)
                continue
            
            # Bin
            bin_match = re.match(r'(?:bin|bins)\s+(\w+).*?(?:hits?[=:]?\s*)?(\d+)', line, re.IGNORECASE)
            if bin_match and current_cp:
                hits = int(bin_match.group(2))
                current_cp.bins.append(CoverageBin(
                    name=bin_match.group(1),
                    hits=hits,
                    status=CoverageStatus.COVERED if hits > 0 else CoverageStatus.UNCOVERED
                ))
        
        if current_cg:
            covergroups.append(current_cg)
        
        # Calculate total coverage
        total = 0.0
        if covergroups:
            total = sum(cg.coverage_pct for cg in covergroups) / len(covergroups)
        
        return CoverageReport(
            source_file="text",
            total_coverage=total,
            covergroups=covergroups
        )
    
    def _parse_vcs(self, content: str) -> CoverageReport:
        """Parse VCS/URG coverage report"""
        # VCS URG format parsing
        return self._parse_simple(content)  # Fallback to simple for now
    
    def _parse_questa(self, content: str) -> CoverageReport:
        """Parse Questa/ModelSim coverage report"""
        return self._parse_simple(content)  # Fallback to simple for now


class CoverageAnalyzer:
    """
    Analyzes coverage gaps and suggests sequences to close them.
    This is the KILLER feature - AI-powered coverage closure!
    """
    
    # Stimulus patterns for common coverage scenarios
    STIMULUS_PATTERNS = {
        # Address patterns
        'addr_low': {'range': (0, 0xFF), 'sequence': 'low_addr_seq', 'stimulus': 'addr = $urandom_range(0, 255)'},
        'addr_mid': {'range': (0x100, 0xFFF), 'sequence': 'mid_addr_seq', 'stimulus': 'addr = $urandom_range(256, 4095)'},
        'addr_high': {'range': (0x1000, 0xFFFF), 'sequence': 'high_addr_seq', 'stimulus': 'addr = $urandom_range(4096, 65535)'},
        'addr_boundary': {'values': [0, 0xFF, 0x100, 0xFFF, 0xFFFF], 'sequence': 'boundary_addr_seq', 'stimulus': 'addr inside {0, 8\'hFF, 9\'h100, 12\'hFFF, 16\'hFFFF}'},
        
        # Data patterns
        'data_zero': {'value': 0, 'sequence': 'zero_data_seq', 'stimulus': 'data = 0'},
        'data_ones': {'value': 0xFFFFFFFF, 'sequence': 'all_ones_seq', 'stimulus': 'data = \'1'},
        'data_pattern': {'values': [0xAAAAAAAA, 0x55555555], 'sequence': 'pattern_data_seq', 'stimulus': 'data inside {32\'hAAAA_AAAA, 32\'h5555_5555}'},
        
        # Operation patterns
        'read': {'value': 0, 'sequence': 'read_seq', 'stimulus': 'write = 0'},
        'write': {'value': 1, 'sequence': 'write_seq', 'stimulus': 'write = 1'},
        'back2back_read': {'sequence': 'b2b_read_seq', 'stimulus': 'repeat(10) @(posedge clk) write = 0'},
        'back2back_write': {'sequence': 'b2b_write_seq', 'stimulus': 'repeat(10) @(posedge clk) write = 1'},
        
        # Protocol-specific
        'burst_1': {'sequence': 'single_beat_seq', 'stimulus': 'len = 0'},
        'burst_4': {'sequence': 'burst4_seq', 'stimulus': 'len = 3'},
        'burst_8': {'sequence': 'burst8_seq', 'stimulus': 'len = 7'},
        'burst_16': {'sequence': 'burst16_seq', 'stimulus': 'len = 15'},
        
        # Error injection
        'error_inject': {'sequence': 'error_inject_seq', 'stimulus': 'inject_error = 1'},
        'timeout': {'sequence': 'timeout_seq', 'stimulus': 'force_timeout = 1'},
    }
    
    def __init__(self):
        self.parser = CoverageParser()
    
    def parse_text_summary(self, content: str) -> CoverageReport:
        """
        Parse a text-based coverage summary.
        This handles common human-readable formats from coverage tools.
        """
        covergroups = []
        overall_coverage = 0.0
        
        current_cg = None
        current_cp = None
        
        lines = content.split('\n')
        
        for line in lines:
            line_stripped = line.strip()
            
            # Overall coverage
            overall_match = re.search(r'overall\s*(?:coverage)?[:\s]+(\d+(?:\.\d+)?)\s*%', line_stripped, re.IGNORECASE)
            if overall_match:
                overall_coverage = float(overall_match.group(1))
                continue
            
            # Covergroup line
            cg_match = re.match(r'(?:Covergroup|cg)[:\s]+(\w+)', line_stripped, re.IGNORECASE)
            if cg_match:
                if current_cg:
                    covergroups.append(current_cg)
                current_cg = Covergroup(name=cg_match.group(1))
                continue
            
            # Coverpoint line
            cp_match = re.match(r'(?:Coverpoint|cp)[:\s]+(\w+)', line_stripped, re.IGNORECASE)
            if cp_match and current_cg:
                current_cp = CoverPoint(name=cp_match.group(1))
                current_cg.coverpoints.append(current_cp)
                continue
            
            # Bin line: "bin name: hits/goal (pct%)"
            bin_match = re.search(r'bin\s+(\S+)[:\s]+(\d+)/(\d+)\s*\((\d+(?:\.\d+)?)\s*%\)', line_stripped, re.IGNORECASE)
            if bin_match and current_cp:
                hits = int(bin_match.group(2))
                goal = int(bin_match.group(3))
                current_cp.bins.append(CoverageBin(
                    name=bin_match.group(1),
                    hits=hits,
                    goal=goal,
                    status=CoverageStatus.COVERED if hits >= goal else CoverageStatus.UNCOVERED
                ))
                continue
            
            # Cross line
            cross_match = re.search(r'(?:Cross|cross)[:\s]+(\S+)', line_stripped, re.IGNORECASE)
            if cross_match and current_cg:
                cross = CrossCoverage(name=cross_match.group(1), coverpoints=[])
                current_cg.crosses.append(cross)
                continue
            
            # Cross bin line: "bin <val1, val2>: hits/goal (pct%)"
            cross_bin_match = re.search(r'bin\s+<([^>]+)>[:\s]+(\d+)/(\d+)\s*\((\d+(?:\.\d+)?)\s*%\)', line_stripped, re.IGNORECASE)
            if cross_bin_match and current_cg and current_cg.crosses:
                hits = int(cross_bin_match.group(2))
                goal = int(cross_bin_match.group(3))
                current_cg.crosses[-1].bins.append(CoverageBin(
                    name=f"<{cross_bin_match.group(1)}>",
                    hits=hits,
                    goal=goal,
                    status=CoverageStatus.COVERED if hits >= goal else CoverageStatus.UNCOVERED
                ))
                continue
        
        if current_cg:
            covergroups.append(current_cg)
        
        # Calculate overall if not found
        if overall_coverage == 0.0 and covergroups:
            total_bins = 0
            covered_bins = 0
            for cg in covergroups:
                for cp in cg.coverpoints:
                    total_bins += len(cp.bins)
                    covered_bins += len([b for b in cp.bins if b.is_covered])
                for cr in cg.crosses:
                    total_bins += len(cr.bins)
                    covered_bins += len([b for b in cr.bins if b.is_covered])
            if total_bins > 0:
                overall_coverage = (covered_bins / total_bins) * 100
        
        return CoverageReport(
            source_file="text_summary",
            total_coverage=overall_coverage,
            covergroups=covergroups
        )
    
    def analyze_coverage(self, report: CoverageReport, target_coverage: float = 95.0) -> List[CoverageGap]:
        """
        Analyze a coverage report and return a list of gaps to close.
        """
        gaps = []
        
        for cg in report.covergroups:
            # Coverpoint gaps
            for cp in cg.coverpoints:
                for bin in cp.bins:
                    if not bin.is_covered or bin.coverage_pct < target_coverage:
                        # Calculate how many more hits needed
                        current_pct = bin.coverage_pct
                        hits_needed = max(1, bin.goal - bin.hits)
                        
                        # Determine priority
                        priority = "medium"
                        bin_lower = bin.name.lower()
                        if bin.hits == 0:
                            priority = "high"
                        elif any(x in bin_lower for x in ['error', 'boundary', 'edge']):
                            priority = "high"
                        elif current_pct > 50:
                            priority = "low"
                        
                        stimulus, seq_name = self._suggest_stimulus(bin.name, cp.name)
                        
                        gaps.append(CoverageGap(
                            covergroup=cg.name,
                            coverpoint=cp.name,
                            bin_name=bin.name,
                            bin_value=str(bin.hits),
                            priority=priority,
                            suggested_stimulus=stimulus,
                            suggested_sequence=seq_name,
                            hit_count=bin.hits,
                            goal_count=bin.goal,
                            current_coverage=current_pct,
                            target_coverage=target_coverage,
                            hits_needed=hits_needed
                        ))
            
            # Cross coverage gaps
            for cross in cg.crosses:
                for bin in cross.bins:
                    if not bin.is_covered or bin.coverage_pct < target_coverage:
                        hits_needed = max(1, bin.goal - bin.hits)
                        priority = "high" if bin.hits == 0 else "medium"
                        
                        stimulus = f"/* Cross: {bin.name} */"
                        seq_name = f"cross_{cross.name}_{bin.name.replace('<', '').replace('>', '').replace(', ', '_')}_seq"
                        
                        gaps.append(CoverageGap(
                            covergroup=cg.name,
                            coverpoint=cross.name,
                            bin_name=bin.name,
                            bin_value=str(bin.hits),
                            priority=priority,
                            suggested_stimulus=stimulus,
                            suggested_sequence=seq_name,
                            hit_count=bin.hits,
                            goal_count=bin.goal,
                            current_coverage=bin.coverage_pct,
                            target_coverage=target_coverage,
                            hits_needed=hits_needed
                        ))
        
        # Sort by priority then by coverage (lowest first)
        priority_order = {'high': 0, 'medium': 1, 'low': 2}
        gaps.sort(key=lambda g: (priority_order.get(g.priority, 2), g.current_coverage))
        
        return gaps
    
    def gap_to_suggestion(self, gap: CoverageGap) -> SuggestedSequence:
        """Convert a coverage gap to a suggested UVM sequence."""
        stimulus = gap.suggested_stimulus
        
        # Generate UVM sequence code
        seq_code = f'''class {gap.suggested_sequence} extends uvm_sequence;
  `uvm_object_utils({gap.suggested_sequence})
  
  function new(string name = "{gap.suggested_sequence}");
    super.new(name);
  endfunction
  
  task body();
    req = new("req");
    start_item(req);
    
    // Target: {gap.coverpoint}.{gap.bin_name}
    // Current: {gap.current_coverage:.0f}% ({gap.hit_count} hits)
    // Need: {gap.hits_needed} more hits
    
    assert(req.randomize() with {{
      {stimulus};
    }}) else `uvm_error("SEQ", "Randomization failed")
    
    finish_item(req);
  endtask
endclass'''
        
        return SuggestedSequence(
            name=gap.suggested_sequence,
            description=f"Close gap in {gap.coverpoint}.{gap.bin_name}",
            uvm_sequence_code=seq_code,
            stimulus_values=stimulus,
            expected_coverage_gain=min(gap.hits_needed, 10) / gap.goal_count * 100 if gap.goal_count > 0 else 0
        )
    
    def analyze(self, coverage_content: str, format_type: str = "auto") -> CoverageReport:
        """Analyze coverage and identify gaps"""
        report = self.parser.parse(coverage_content, format_type)
        
        # Analyze gaps
        gaps = self._find_gaps(report)
        report.gaps = gaps
        
        return report
    
    def analyze_file(self, file_path: str) -> CoverageReport:
        """Analyze coverage from file"""
        content = Path(file_path).read_text()
        return self.analyze(content)
    
    def _find_gaps(self, report: CoverageReport) -> List[CoverageGap]:
        """Find coverage gaps and suggest fixes"""
        gaps = []
        
        for cg in report.covergroups:
            for cp in cg.coverpoints:
                for bin in cp.uncovered_bins:
                    gap = self._create_gap(cg.name, cp.name, bin)
                    if gap:
                        gaps.append(gap)
        
        # Sort by priority
        priority_order = {'high': 0, 'medium': 1, 'low': 2}
        gaps.sort(key=lambda g: priority_order.get(g.priority, 2))
        
        return gaps
    
    def _create_gap(self, cg_name: str, cp_name: str, bin: CoverageBin) -> Optional[CoverageGap]:
        """Create a coverage gap with suggested stimulus"""
        # Analyze bin name to determine stimulus
        bin_lower = bin.name.lower()
        
        # Determine priority based on coverage type
        priority = "medium"
        if any(x in bin_lower for x in ['error', 'fail', 'timeout', 'illegal']):
            priority = "high"  # Error scenarios are critical
        elif any(x in bin_lower for x in ['boundary', 'edge', 'corner']):
            priority = "high"  # Boundary cases are important
        elif any(x in bin_lower for x in ['default', 'other', 'misc']):
            priority = "low"
        
        # Find matching stimulus pattern
        stimulus, sequence = self._suggest_stimulus(bin.name, cp_name)
        
        return CoverageGap(
            covergroup=cg_name,
            coverpoint=cp_name,
            bin_name=bin.name,
            bin_value=str(bin.hits),
            priority=priority,
            suggested_stimulus=stimulus,
            suggested_sequence=sequence
        )
    
    def _suggest_stimulus(self, bin_name: str, cp_name: str) -> Tuple[str, str]:
        """Suggest stimulus to hit the bin"""
        bin_lower = bin_name.lower()
        cp_lower = cp_name.lower()
        
        # Address-related
        if 'addr' in cp_lower or 'address' in cp_lower:
            if 'low' in bin_lower or 'small' in bin_lower:
                return self.STIMULUS_PATTERNS['addr_low']['stimulus'], 'low_address_seq'
            elif 'high' in bin_lower or 'large' in bin_lower:
                return self.STIMULUS_PATTERNS['addr_high']['stimulus'], 'high_address_seq'
            elif 'bound' in bin_lower or 'edge' in bin_lower:
                return self.STIMULUS_PATTERNS['addr_boundary']['stimulus'], 'boundary_address_seq'
            else:
                return f'addr = /* hit {bin_name} */', f'{bin_name}_seq'
        
        # Data-related
        if 'data' in cp_lower or 'wdata' in cp_lower or 'rdata' in cp_lower:
            if 'zero' in bin_lower:
                return self.STIMULUS_PATTERNS['data_zero']['stimulus'], 'zero_data_seq'
            elif 'one' in bin_lower or 'all_ones' in bin_lower:
                return self.STIMULUS_PATTERNS['data_ones']['stimulus'], 'all_ones_seq'
            elif 'pattern' in bin_lower or 'aa' in bin_lower or '55' in bin_lower:
                return self.STIMULUS_PATTERNS['data_pattern']['stimulus'], 'pattern_data_seq'
            else:
                return f'data = /* hit {bin_name} */', f'{bin_name}_seq'
        
        # Operation type
        if 'op' in cp_lower or 'type' in cp_lower or 'write' in cp_lower:
            if 'read' in bin_lower:
                return self.STIMULUS_PATTERNS['read']['stimulus'], 'read_only_seq'
            elif 'write' in bin_lower:
                return self.STIMULUS_PATTERNS['write']['stimulus'], 'write_only_seq'
        
        # Burst length
        if 'len' in cp_lower or 'burst' in cp_lower or 'size' in cp_lower:
            if '1' in bin_lower or 'single' in bin_lower:
                return self.STIMULUS_PATTERNS['burst_1']['stimulus'], 'single_burst_seq'
            elif '4' in bin_lower:
                return self.STIMULUS_PATTERNS['burst_4']['stimulus'], 'burst4_seq'
            elif '8' in bin_lower:
                return self.STIMULUS_PATTERNS['burst_8']['stimulus'], 'burst8_seq'
            elif '16' in bin_lower:
                return self.STIMULUS_PATTERNS['burst_16']['stimulus'], 'burst16_seq'
        
        # Error scenarios
        if 'error' in cp_lower or 'err' in bin_lower:
            return self.STIMULUS_PATTERNS['error_inject']['stimulus'], 'error_injection_seq'
        
        # Default
        return f'/* Constrain to hit {bin_name} */', f'{bin_name}_targeted_seq'
    
    def generate_closure_sequences(self, report: CoverageReport, module_name: str = "dut") -> str:
        """Generate UVM sequences to close coverage gaps"""
        if not report.gaps:
            return "// No coverage gaps found - 100% coverage achieved!"
        
        sequences = []
        sequences.append(f'''// UVMForge Generated Coverage Closure Sequences
// Target: {module_name}
// Gaps Found: {len(report.gaps)}
// Current Coverage: {report.total_coverage:.1f}%

class {module_name}_coverage_closure_seq extends {module_name}_base_seq;
    `uvm_object_utils({module_name}_coverage_closure_seq)
    
    function new(string name = "{module_name}_coverage_closure_seq");
        super.new(name);
    endfunction
    
    task body();
        `uvm_info("COV_CLOSE", "Starting coverage closure sequence", UVM_LOW)
''')
        
        # Group gaps by coverpoint
        gaps_by_cp: Dict[str, List[CoverageGap]] = {}
        for gap in report.gaps:
            key = f"{gap.covergroup}.{gap.coverpoint}"
            if key not in gaps_by_cp:
                gaps_by_cp[key] = []
            gaps_by_cp[key].append(gap)
        
        for cp_key, gaps in gaps_by_cp.items():
            sequences.append(f'''
        // === Close gaps in {cp_key} ===''')
            for gap in gaps:
                sequences.append(f'''
        // Gap: {gap.bin_name} (Priority: {gap.priority})
        `uvm_do_with(req, {{ {gap.suggested_stimulus}; }})''')
        
        sequences.append('''
        
        `uvm_info("COV_CLOSE", "Coverage closure sequence complete", UVM_LOW)
    endtask
    
endclass
''')
        
        # Generate individual targeted sequences
        for gap in report.gaps[:10]:  # Top 10 gaps
            sequences.append(f'''
// Targeted sequence for: {gap.covergroup}.{gap.coverpoint}.{gap.bin_name}
class {gap.suggested_sequence} extends {module_name}_base_seq;
    `uvm_object_utils({gap.suggested_sequence})
    
    function new(string name = "{gap.suggested_sequence}");
        super.new(name);
    endfunction
    
    task body();
        repeat(100) begin
            `uvm_do_with(req, {{ {gap.suggested_stimulus}; }})
        end
    endtask
    
endclass
''')
        
        return '\n'.join(sequences)
    
    def generate_report(self, report: CoverageReport) -> str:
        """Generate human-readable coverage gap report"""
        lines = []
        lines.append("=" * 60)
        lines.append("UVMForge Coverage Gap Analysis Report")
        lines.append("=" * 60)
        lines.append(f"\nTotal Coverage: {report.total_coverage:.1f}%")
        lines.append(f"Coverage Gaps Found: {len(report.gaps)}")
        
        if report.gaps:
            lines.append("\n" + "-" * 60)
            lines.append("Coverage Gaps by Priority:")
            lines.append("-" * 60)
            
            high_gaps = [g for g in report.gaps if g.priority == 'high']
            med_gaps = [g for g in report.gaps if g.priority == 'medium']
            low_gaps = [g for g in report.gaps if g.priority == 'low']
            
            if high_gaps:
                lines.append(f"\n🔴 HIGH PRIORITY ({len(high_gaps)} gaps):")
                for gap in high_gaps[:5]:
                    lines.append(f"   • {gap.covergroup}.{gap.coverpoint}.{gap.bin_name}")
                    lines.append(f"     Suggested: {gap.suggested_stimulus}")
            
            if med_gaps:
                lines.append(f"\n🟡 MEDIUM PRIORITY ({len(med_gaps)} gaps):")
                for gap in med_gaps[:5]:
                    lines.append(f"   • {gap.covergroup}.{gap.coverpoint}.{gap.bin_name}")
                    lines.append(f"     Suggested: {gap.suggested_stimulus}")
            
            if low_gaps:
                lines.append(f"\n🟢 LOW PRIORITY ({len(low_gaps)} gaps):")
                for gap in low_gaps[:3]:
                    lines.append(f"   • {gap.covergroup}.{gap.coverpoint}.{gap.bin_name}")
        
        lines.append("\n" + "=" * 60)
        lines.append("Run the generated coverage_closure_seq to close these gaps!")
        lines.append("=" * 60)
        
        return '\n'.join(lines)


def analyze_coverage(coverage_content: str, module_name: str = "dut") -> Dict[str, Any]:
    """Convenience function to analyze coverage"""
    analyzer = CoverageAnalyzer()
    report = analyzer.analyze(coverage_content)
    
    return {
        'total_coverage': report.total_coverage,
        'num_gaps': len(report.gaps),
        'gaps': [
            {
                'covergroup': g.covergroup,
                'coverpoint': g.coverpoint,
                'bin': g.bin_name,
                'priority': g.priority,
                'suggested_stimulus': g.suggested_stimulus,
                'suggested_sequence': g.suggested_sequence
            }
            for g in report.gaps
        ],
        'closure_sequences': analyzer.generate_closure_sequences(report, module_name),
        'report': analyzer.generate_report(report)
    }


# Example/test
if __name__ == "__main__":
    sample_coverage = """
    covergroup apb_cg:
        coverpoint addr_cp: 75%
            bin addr_low hits: 100
            bin addr_mid hits: 50
            bin addr_high hits: 0
            bin addr_boundary hits: 0
        
        coverpoint op_cp: 50%
            bin read hits: 200
            bin write hits: 150
            bin back2back_read hits: 0
            bin back2back_write hits: 0
        
        coverpoint data_cp: 60%
            bin data_zero hits: 10
            bin data_ones hits: 0
            bin data_pattern hits: 0
            bin data_random hits: 500
        
        coverpoint error_cp: 0%
            bin timeout_error hits: 0
            bin protocol_error hits: 0
    """
    
    result = analyze_coverage(sample_coverage, "apb_slave")
    print(result['report'])
    print("\n\nGenerated Sequences:")
    print(result['closure_sequences'][:2000])
