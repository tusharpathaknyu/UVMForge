"""
APB Protocol Configuration
"""

from dataclasses import dataclass
from typing import List, Dict, Any


@dataclass
class APBConfig:
    """APB Protocol Configuration"""
    
    # APB Version (3 or 4)
    version: int = 3
    
    # Data width (8, 16, 32)
    data_width: int = 32
    
    # Address width
    addr_width: int = 32
    
    # APB4 specific - PSTRB support
    has_strobe: bool = False
    
    # APB4 specific - PPROT support  
    has_prot: bool = False
    
    # Timeout in clock cycles
    timeout_cycles: int = 1000
    
    @property
    def strb_width(self) -> int:
        return self.data_width // 8
    
    def get_signals(self) -> List[Dict[str, Any]]:
        """Get list of APB signals based on version"""
        signals = [
            # Clock and Reset
            {"name": "PCLK", "width": 1, "direction": "input", "description": "Clock"},
            {"name": "PRESETn", "width": 1, "direction": "input", "description": "Active-low reset"},
            
            # APB3 Signals
            {"name": "PADDR", "width": self.addr_width, "direction": "output", "description": "Address"},
            {"name": "PSEL", "width": 1, "direction": "output", "description": "Select"},
            {"name": "PENABLE", "width": 1, "direction": "output", "description": "Enable"},
            {"name": "PWRITE", "width": 1, "direction": "output", "description": "Write"},
            {"name": "PWDATA", "width": self.data_width, "direction": "output", "description": "Write data"},
            {"name": "PRDATA", "width": self.data_width, "direction": "input", "description": "Read data"},
            {"name": "PREADY", "width": 1, "direction": "input", "description": "Ready"},
            {"name": "PSLVERR", "width": 1, "direction": "input", "description": "Slave error"},
        ]
        
        # APB4 additions
        if self.version >= 4:
            if self.has_strobe:
                signals.append({
                    "name": "PSTRB", 
                    "width": self.strb_width, 
                    "direction": "output", 
                    "description": "Write strobe"
                })
            if self.has_prot:
                signals.append({
                    "name": "PPROT", 
                    "width": 3, 
                    "direction": "output", 
                    "description": "Protection"
                })
        
        return signals
    
    def validate(self) -> List[str]:
        """Validate configuration, return list of errors"""
        errors = []
        
        if self.data_width not in [8, 16, 32]:
            errors.append(f"Invalid data_width: {self.data_width}. Must be 8, 16, or 32.")
        
        if self.version not in [3, 4]:
            errors.append(f"Invalid APB version: {self.version}. Must be 3 or 4.")
        
        if self.version < 4 and (self.has_strobe or self.has_prot):
            errors.append("PSTRB and PPROT are only available in APB4")
        
        return errors
