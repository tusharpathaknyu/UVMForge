"""
I2C Protocol Configuration for UVMForge
"""

from dataclasses import dataclass, field
from typing import List


@dataclass
class I2CConfig:
    """I2C (Inter-Integrated Circuit) Protocol Configuration"""
    
    # Speed modes
    # Standard Mode: 100 kHz
    # Fast Mode: 400 kHz
    # Fast Mode Plus: 1 MHz
    # High Speed Mode: 3.4 MHz
    speed_mode: str = "standard"  # standard, fast, fast_plus, high_speed
    clock_frequency: int = 100000  # Hz
    
    # Addressing
    address_bits: int = 7  # 7 or 10 bit addressing
    device_address: int = 0x50  # Default slave address
    
    # Features
    supports_clock_stretching: bool = True
    supports_multi_master: bool = False
    supports_10bit_addr: bool = False
    
    # Timing (in ns) - for standard mode defaults
    t_buf: int = 4700    # Bus free time between STOP and START
    t_hd_sta: int = 4000  # Hold time for START condition
    t_su_sta: int = 4700  # Setup time for repeated START
    t_su_sto: int = 4000  # Setup time for STOP condition
    t_hd_dat: int = 0     # Data hold time
    t_su_dat: int = 250   # Data setup time
    t_low: int = 4700     # SCL low period
    t_high: int = 4000    # SCL high period
    
    # FIFO
    has_tx_fifo: bool = True
    has_rx_fifo: bool = True
    fifo_depth: int = 8
    
    @property
    def clock_period_ns(self) -> int:
        """Get clock period in nanoseconds"""
        return int(1e9 / self.clock_frequency)
    
    def get_speed_description(self) -> str:
        """Get human-readable speed description"""
        speeds = {
            "standard": "Standard Mode (100 kHz)",
            "fast": "Fast Mode (400 kHz)",
            "fast_plus": "Fast Mode Plus (1 MHz)",
            "high_speed": "High Speed Mode (3.4 MHz)"
        }
        return speeds.get(self.speed_mode, "Unknown mode")


# Common I2C configurations
I2C_PRESETS = {
    "standard": I2CConfig(),
    "fast": I2CConfig(
        speed_mode="fast",
        clock_frequency=400000,
        t_buf=1300,
        t_hd_sta=600,
        t_su_sta=600,
        t_su_sto=600,
        t_low=1300,
        t_high=600
    ),
    "fast_plus": I2CConfig(
        speed_mode="fast_plus",
        clock_frequency=1000000,
        t_buf=500,
        t_hd_sta=260,
        t_su_sta=260,
        t_su_sto=260,
        t_low=500,
        t_high=260
    ),
    "eeprom": I2CConfig(
        device_address=0x50,
        speed_mode="standard"
    ),
    "sensor": I2CConfig(
        device_address=0x68,
        speed_mode="fast"
    ),
    "10bit": I2CConfig(
        address_bits=10,
        supports_10bit_addr=True
    ),
    "multi_master": I2CConfig(
        supports_multi_master=True,
        supports_clock_stretching=True
    ),
}
