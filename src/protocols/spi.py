"""
SPI Protocol Configuration for UVMForge
"""

from dataclasses import dataclass, field
from typing import List


@dataclass
class SPIConfig:
    """SPI (Serial Peripheral Interface) Protocol Configuration"""
    
    # Basic parameters
    data_width: int = 8           # Data bits per transfer (typically 8, 16, 32)
    clock_divider: int = 2        # System clock to SPI clock divider
    
    # SPI Modes (CPOL, CPHA combinations)
    # Mode 0: CPOL=0, CPHA=0 - Clock idle low, sample on rising edge
    # Mode 1: CPOL=0, CPHA=1 - Clock idle low, sample on falling edge  
    # Mode 2: CPOL=1, CPHA=0 - Clock idle high, sample on falling edge
    # Mode 3: CPOL=1, CPHA=1 - Clock idle high, sample on rising edge
    spi_mode: int = 0
    
    # Transfer configuration
    msb_first: bool = True        # MSB-first or LSB-first transmission
    full_duplex: bool = True      # Full-duplex or half-duplex mode
    
    # Chip select configuration
    num_slaves: int = 1           # Number of slave devices
    cs_active_low: bool = True    # Chip select polarity
    
    # Timing (in clock cycles)
    cs_setup_time: int = 1        # CS setup time before first clock
    cs_hold_time: int = 1         # CS hold time after last clock
    inter_transfer_gap: int = 2   # Gap between consecutive transfers
    
    # Features
    supports_quad_spi: bool = False    # QSPI support
    supports_dual_spi: bool = False    # Dual SPI support
    
    @property
    def cpol(self) -> int:
        """Clock polarity from SPI mode"""
        return (self.spi_mode >> 1) & 1
    
    @property
    def cpha(self) -> int:
        """Clock phase from SPI mode"""
        return self.spi_mode & 1
    
    def get_mode_description(self) -> str:
        """Get human-readable mode description"""
        modes = {
            0: "Mode 0 (CPOL=0, CPHA=0): Sample on rising edge, idle low",
            1: "Mode 1 (CPOL=0, CPHA=1): Sample on falling edge, idle low",
            2: "Mode 2 (CPOL=1, CPHA=0): Sample on falling edge, idle high",
            3: "Mode 3 (CPOL=1, CPHA=1): Sample on rising edge, idle high"
        }
        return modes.get(self.spi_mode, "Unknown mode")


# Common SPI configurations
SPI_PRESETS = {
    "standard": SPIConfig(),
    "fast": SPIConfig(clock_divider=1, data_width=8),
    "multi_slave": SPIConfig(num_slaves=4),
    "16bit": SPIConfig(data_width=16),
    "32bit": SPIConfig(data_width=32),
    "mode1": SPIConfig(spi_mode=1),
    "mode2": SPIConfig(spi_mode=2),
    "mode3": SPIConfig(spi_mode=3),
    "quad_spi": SPIConfig(supports_quad_spi=True, data_width=8),
    "flash_memory": SPIConfig(spi_mode=0, data_width=8, supports_quad_spi=True),
    "adc_sensor": SPIConfig(spi_mode=0, data_width=16, clock_divider=4),
}
