"""
AXI4-Lite Protocol Configuration
"""

from dataclasses import dataclass
from typing import List, Dict, Any


@dataclass
class AXI4LiteConfig:
    """AXI4-Lite Protocol Configuration"""
    
    # Data width (32 or 64)
    data_width: int = 32
    
    # Address width
    addr_width: int = 32
    
    # Support AWPROT/ARPROT
    has_prot: bool = True
    
    # Timeout in clock cycles
    timeout_cycles: int = 1000
    
    @property
    def strb_width(self) -> int:
        return self.data_width // 8
    
    def get_signals(self) -> Dict[str, List[Dict[str, Any]]]:
        """Get list of AXI4-Lite signals organized by channel"""
        
        signals = {
            "global": [
                {"name": "ACLK", "width": 1, "direction": "input", "description": "Clock"},
                {"name": "ARESETn", "width": 1, "direction": "input", "description": "Active-low reset"},
            ],
            
            "write_address": [
                {"name": "AWADDR", "width": self.addr_width, "direction": "output", "description": "Write address"},
                {"name": "AWVALID", "width": 1, "direction": "output", "description": "Write address valid"},
                {"name": "AWREADY", "width": 1, "direction": "input", "description": "Write address ready"},
            ],
            
            "write_data": [
                {"name": "WDATA", "width": self.data_width, "direction": "output", "description": "Write data"},
                {"name": "WSTRB", "width": self.strb_width, "direction": "output", "description": "Write strobe"},
                {"name": "WVALID", "width": 1, "direction": "output", "description": "Write valid"},
                {"name": "WREADY", "width": 1, "direction": "input", "description": "Write ready"},
            ],
            
            "write_response": [
                {"name": "BRESP", "width": 2, "direction": "input", "description": "Write response"},
                {"name": "BVALID", "width": 1, "direction": "input", "description": "Write response valid"},
                {"name": "BREADY", "width": 1, "direction": "output", "description": "Write response ready"},
            ],
            
            "read_address": [
                {"name": "ARADDR", "width": self.addr_width, "direction": "output", "description": "Read address"},
                {"name": "ARVALID", "width": 1, "direction": "output", "description": "Read address valid"},
                {"name": "ARREADY", "width": 1, "direction": "input", "description": "Read address ready"},
            ],
            
            "read_data": [
                {"name": "RDATA", "width": self.data_width, "direction": "input", "description": "Read data"},
                {"name": "RRESP", "width": 2, "direction": "input", "description": "Read response"},
                {"name": "RVALID", "width": 1, "direction": "input", "description": "Read valid"},
                {"name": "RREADY", "width": 1, "direction": "output", "description": "Read ready"},
            ],
        }
        
        # Add protection signals
        if self.has_prot:
            signals["write_address"].insert(1, {
                "name": "AWPROT", "width": 3, "direction": "output", "description": "Write protection"
            })
            signals["read_address"].insert(1, {
                "name": "ARPROT", "width": 3, "direction": "output", "description": "Read protection"
            })
        
        return signals
    
    def get_response_codes(self) -> Dict[str, int]:
        """Get AXI response codes"""
        return {
            "OKAY": 0b00,
            "EXOKAY": 0b01,  # Not used in AXI4-Lite
            "SLVERR": 0b10,
            "DECERR": 0b11,
        }
    
    def validate(self) -> List[str]:
        """Validate configuration, return list of errors"""
        errors = []
        
        if self.data_width not in [32, 64]:
            errors.append(f"Invalid data_width: {self.data_width}. AXI4-Lite supports 32 or 64.")
        
        if self.addr_width < 1 or self.addr_width > 64:
            errors.append(f"Invalid addr_width: {self.addr_width}. Must be 1-64.")
        
        return errors
