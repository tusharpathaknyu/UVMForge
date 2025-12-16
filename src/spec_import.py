"""
Specification Parsers - Import from industry-standard formats
Supports: IP-XACT, SystemRDL, CSV/Excel register maps

This is a KEY differentiator - no chatbot can do this!
"""

import re
import xml.etree.ElementTree as ET
from dataclasses import dataclass, field
from typing import List, Dict, Optional, Any
from pathlib import Path
from enum import Enum
import json


class AccessType(Enum):
    READ_WRITE = "rw"
    READ_ONLY = "ro"
    WRITE_ONLY = "wo"
    WRITE_1_CLEAR = "w1c"
    WRITE_1_SET = "w1s"
    READ_CLEAR = "rc"
    READ_SET = "rs"


@dataclass
class BitField:
    """Represents a bit field within a register"""
    name: str
    description: str
    bit_offset: int
    bit_width: int
    access: AccessType = AccessType.READ_WRITE
    reset_value: int = 0
    enum_values: Dict[str, int] = field(default_factory=dict)
    
    @property
    def msb(self) -> int:
        return self.bit_offset + self.bit_width - 1
    
    @property
    def lsb(self) -> int:
        return self.bit_offset
    
    @property
    def mask(self) -> int:
        return ((1 << self.bit_width) - 1) << self.bit_offset


@dataclass
class Register:
    """Represents a hardware register"""
    name: str
    address: int
    description: str = ""
    width: int = 32
    access: AccessType = AccessType.READ_WRITE
    reset_value: int = 0
    fields: List[BitField] = field(default_factory=list)
    
    @property
    def address_hex(self) -> str:
        return f"0x{self.address:08X}"


@dataclass
class RegisterBlock:
    """A block/group of registers"""
    name: str
    base_address: int
    description: str = ""
    registers: List[Register] = field(default_factory=list)
    
    @property
    def address_range(self) -> int:
        if not self.registers:
            return 0
        max_addr = max(r.address for r in self.registers)
        return max_addr + 4  # Assuming 32-bit registers
    
    def get_register_by_name(self, name: str) -> Optional[Register]:
        for reg in self.registers:
            if reg.name.lower() == name.lower():
                return reg
        return None
    
    def get_register_by_address(self, address: int) -> Optional[Register]:
        for reg in self.registers:
            if reg.address == address:
                return reg
        return None


@dataclass
class ParsedSpec:
    """Complete parsed specification"""
    name: str
    version: str = "1.0"
    description: str = ""
    data_width: int = 32
    addr_width: int = 32
    register_blocks: List[RegisterBlock] = field(default_factory=list)
    source_format: str = ""
    source_file: str = ""
    
    @property
    def all_registers(self) -> List[Register]:
        regs = []
        for block in self.register_blocks:
            regs.extend(block.registers)
        return regs
    
    @property
    def total_registers(self) -> int:
        return sum(len(b.registers) for b in self.register_blocks)


class IPXACTParser:
    """
    Parser for IP-XACT (IEEE 1685) XML files.
    IP-XACT is the industry standard for IP documentation.
    """
    
    # IP-XACT namespaces
    NAMESPACES = {
        'spirit': 'http://www.spiritconsortium.org/XMLSchema/SPIRIT/1.5',
        'ipxact': 'http://www.accellera.org/XMLSchema/IPXACT/1685-2014',
        'ipxact2022': 'http://www.accellera.org/XMLSchema/IPXACT/1685-2022',
    }
    
    def __init__(self):
        self.ns = None
    
    def parse(self, content: str, source_file: str = "") -> ParsedSpec:
        """Parse IP-XACT XML content"""
        root = ET.fromstring(content)
        
        # Detect namespace
        self.ns = self._detect_namespace(root)
        
        # Extract component info
        name = self._get_text(root, './/name') or "unknown"
        version = self._get_text(root, './/version') or "1.0"
        description = self._get_text(root, './/description') or ""
        
        # Parse memory maps -> address blocks -> registers
        register_blocks = self._parse_memory_maps(root)
        
        return ParsedSpec(
            name=name,
            version=version,
            description=description,
            register_blocks=register_blocks,
            source_format="IP-XACT",
            source_file=source_file
        )
    
    def parse_file(self, file_path: str) -> ParsedSpec:
        """Parse IP-XACT from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"IP-XACT file not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))
    
    def _detect_namespace(self, root: ET.Element) -> str:
        """Detect which IP-XACT namespace is used"""
        tag = root.tag
        if '{' in tag:
            ns = tag.split('}')[0].strip('{')
            return ns
        return ""
    
    def _ns_tag(self, tag: str) -> str:
        """Add namespace to tag"""
        if self.ns:
            return f'{{{self.ns}}}{tag}'
        return tag
    
    def _get_text(self, element: ET.Element, path: str) -> Optional[str]:
        """Get text content from element"""
        # Try with different namespaces
        for prefix, ns in self.NAMESPACES.items():
            try:
                elem = element.find(path.replace('//', f'.//{{{ns}}}').replace('/', f'/{{{ns}}}'))
                if elem is not None and elem.text:
                    return elem.text.strip()
            except:
                pass
        
        # Try without namespace
        elem = element.find(path)
        if elem is not None and elem.text:
            return elem.text.strip()
        return None
    
    def _parse_memory_maps(self, root: ET.Element) -> List[RegisterBlock]:
        """Parse memory maps from IP-XACT"""
        blocks = []
        
        # Find all addressBlock elements
        for ns_uri in self.NAMESPACES.values():
            address_blocks = root.findall(f'.//{{{ns_uri}}}addressBlock')
            if address_blocks:
                for ab in address_blocks:
                    block = self._parse_address_block(ab, ns_uri)
                    if block:
                        blocks.append(block)
                break
        
        return blocks
    
    def _parse_address_block(self, ab: ET.Element, ns: str) -> Optional[RegisterBlock]:
        """Parse a single address block"""
        name = ab.findtext(f'{{{ns}}}name', 'unknown')
        base_addr_text = ab.findtext(f'{{{ns}}}baseAddress', '0')
        description = ab.findtext(f'{{{ns}}}description', '')
        
        try:
            base_address = int(base_addr_text, 0)  # Handle hex or decimal
        except:
            base_address = 0
        
        registers = []
        for reg_elem in ab.findall(f'.//{{{ns}}}register'):
            reg = self._parse_register(reg_elem, ns)
            if reg:
                registers.append(reg)
        
        return RegisterBlock(
            name=name,
            base_address=base_address,
            description=description,
            registers=registers
        )
    
    def _parse_register(self, reg: ET.Element, ns: str) -> Optional[Register]:
        """Parse a single register"""
        name = reg.findtext(f'{{{ns}}}name', 'unknown')
        offset_text = reg.findtext(f'{{{ns}}}addressOffset', '0')
        description = reg.findtext(f'{{{ns}}}description', '')
        size_text = reg.findtext(f'{{{ns}}}size', '32')
        reset_text = reg.findtext(f'{{{ns}}}reset/{{{ns}}}value', '0')
        
        try:
            offset = int(offset_text, 0)
            size = int(size_text, 0)
            reset = int(reset_text, 0)
        except:
            offset = 0
            size = 32
            reset = 0
        
        # Parse fields
        fields = []
        for field_elem in reg.findall(f'.//{{{ns}}}field'):
            fld = self._parse_field(field_elem, ns)
            if fld:
                fields.append(fld)
        
        return Register(
            name=name,
            address=offset,
            description=description,
            width=size,
            reset_value=reset,
            fields=fields
        )
    
    def _parse_field(self, field: ET.Element, ns: str) -> Optional[BitField]:
        """Parse a bit field"""
        name = field.findtext(f'{{{ns}}}name', 'unknown')
        description = field.findtext(f'{{{ns}}}description', '')
        offset_text = field.findtext(f'{{{ns}}}bitOffset', '0')
        width_text = field.findtext(f'{{{ns}}}bitWidth', '1')
        access_text = field.findtext(f'{{{ns}}}access', 'read-write')
        reset_text = field.findtext(f'{{{ns}}}resets/{{{ns}}}reset/{{{ns}}}value', '0')
        
        try:
            offset = int(offset_text, 0)
            width = int(width_text, 0)
            reset = int(reset_text, 0)
        except:
            offset = 0
            width = 1
            reset = 0
        
        # Map access type
        access_map = {
            'read-write': AccessType.READ_WRITE,
            'read-only': AccessType.READ_ONLY,
            'write-only': AccessType.WRITE_ONLY,
            'read-writeOnce': AccessType.READ_WRITE,
            'writeOnce': AccessType.WRITE_ONLY,
        }
        access = access_map.get(access_text.lower(), AccessType.READ_WRITE)
        
        return BitField(
            name=name,
            description=description,
            bit_offset=offset,
            bit_width=width,
            access=access,
            reset_value=reset
        )


class SystemRDLParser:
    """
    Parser for SystemRDL register descriptions.
    SystemRDL is popular in many semiconductor companies.
    """
    
    def __init__(self):
        self.content = ""
    
    def parse(self, content: str, source_file: str = "") -> ParsedSpec:
        """Parse SystemRDL content"""
        self.content = content
        
        # Extract addrmap name
        name_match = re.search(r'addrmap\s+(\w+)\s*{', content)
        name = name_match.group(1) if name_match else "unknown"
        
        # Parse registers
        registers = self._parse_registers()
        
        block = RegisterBlock(
            name=name,
            base_address=0,
            registers=registers
        )
        
        return ParsedSpec(
            name=name,
            register_blocks=[block],
            source_format="SystemRDL",
            source_file=source_file
        )
    
    def parse_file(self, file_path: str) -> ParsedSpec:
        """Parse SystemRDL from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"SystemRDL file not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))
    
    def _parse_registers(self) -> List[Register]:
        """Parse all registers from SystemRDL"""
        registers = []
        
        # Match reg definitions: reg name @ address { ... }
        reg_pattern = r'reg\s*{([^}]*)}\s*(\w+)\s*(?:@\s*(0x[0-9a-fA-F]+|\d+))?'
        
        for match in re.finditer(reg_pattern, self.content, re.DOTALL):
            reg_body = match.group(1)
            reg_name = match.group(2)
            reg_addr = match.group(3)
            
            address = int(reg_addr, 0) if reg_addr else len(registers) * 4
            fields = self._parse_fields(reg_body)
            
            registers.append(Register(
                name=reg_name,
                address=address,
                fields=fields
            ))
        
        return registers
    
    def _parse_fields(self, reg_body: str) -> List[BitField]:
        """Parse fields from register body"""
        fields = []
        
        # Match field definitions: field {} name[msb:lsb]
        field_pattern = r'field\s*{([^}]*)}\s*(\w+)\s*\[\s*(\d+)(?:\s*:\s*(\d+))?\s*\]'
        
        for match in re.finditer(field_pattern, reg_body, re.DOTALL):
            field_body = match.group(1)
            field_name = match.group(2)
            msb = int(match.group(3))
            lsb = int(match.group(4)) if match.group(4) else msb
            
            # Parse access type from field body
            access = AccessType.READ_WRITE
            if 'sw=r' in field_body.lower() and 'sw=rw' not in field_body.lower():
                access = AccessType.READ_ONLY
            elif 'sw=w' in field_body.lower():
                access = AccessType.WRITE_ONLY
            
            # Parse description
            desc_match = re.search(r'desc\s*=\s*"([^"]*)"', field_body)
            description = desc_match.group(1) if desc_match else ""
            
            fields.append(BitField(
                name=field_name,
                description=description,
                bit_offset=lsb,
                bit_width=msb - lsb + 1,
                access=access
            ))
        
        return fields


class CSVRegisterParser:
    """
    Parser for CSV register maps.
    This is a common format in many companies for quick register definitions.
    
    Expected CSV format:
    Register Name, Address, Field Name, Bit Range, Access, Reset Value, Description
    
    Or simplified:
    Name, Address, Width, Access, Reset, Description
    """
    
    def parse(self, content: str, source_file: str = "") -> ParsedSpec:
        """Parse CSV content"""
        import csv
        from io import StringIO
        
        reader = csv.DictReader(StringIO(content))
        
        # Normalize headers
        fieldnames = [f.lower().strip() for f in reader.fieldnames] if reader.fieldnames else []
        
        registers = []
        current_reg = None
        
        for row in reader:
            # Normalize row keys
            row = {k.lower().strip(): v.strip() for k, v in row.items()}
            
            # Detect format
            if 'register name' in row or 'register' in row or 'name' in row:
                reg_name = row.get('register name') or row.get('register') or row.get('name', '')
                address = row.get('address', row.get('offset', '0'))
                
                if reg_name:
                    # Parse address
                    try:
                        addr = int(address, 0) if address else len(registers) * 4
                    except:
                        addr = len(registers) * 4
                    
                    # Check if this is a new register or a field of existing
                    field_name = row.get('field name', row.get('field', ''))
                    
                    if field_name and current_reg and current_reg.name == reg_name:
                        # Add field to current register
                        field = self._parse_field_row(row)
                        if field:
                            current_reg.fields.append(field)
                    else:
                        # New register
                        if current_reg:
                            registers.append(current_reg)
                        
                        current_reg = Register(
                            name=reg_name,
                            address=addr,
                            description=row.get('description', ''),
                            width=int(row.get('width', '32')),
                            access=self._parse_access(row.get('access', 'rw'))
                        )
                        
                        # If this row also has field info, add it
                        if field_name:
                            field = self._parse_field_row(row)
                            if field:
                                current_reg.fields.append(field)
        
        if current_reg:
            registers.append(current_reg)
        
        block = RegisterBlock(
            name="registers",
            base_address=0,
            registers=registers
        )
        
        return ParsedSpec(
            name=Path(source_file).stem if source_file else "csv_import",
            register_blocks=[block],
            source_format="CSV",
            source_file=source_file
        )
    
    def parse_file(self, file_path: str) -> ParsedSpec:
        """Parse CSV from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"CSV file not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))
    
    def _parse_field_row(self, row: Dict) -> Optional[BitField]:
        """Parse a field from a CSV row"""
        field_name = row.get('field name', row.get('field', ''))
        if not field_name:
            return None
        
        # Parse bit range
        bit_range = row.get('bit range', row.get('bits', row.get('bit', '')))
        if ':' in str(bit_range):
            msb, lsb = bit_range.split(':')
            msb = int(msb.strip().strip('['))
            lsb = int(lsb.strip().strip(']'))
        elif bit_range:
            msb = lsb = int(str(bit_range).strip('[]'))
        else:
            return None
        
        return BitField(
            name=field_name,
            description=row.get('description', ''),
            bit_offset=lsb,
            bit_width=msb - lsb + 1,
            access=self._parse_access(row.get('access', 'rw')),
            reset_value=int(row.get('reset', row.get('reset value', '0')), 0) if row.get('reset') else 0
        )
    
    def _parse_access(self, access_str: str) -> AccessType:
        """Parse access type string"""
        access_map = {
            'rw': AccessType.READ_WRITE,
            'r/w': AccessType.READ_WRITE,
            'read-write': AccessType.READ_WRITE,
            'ro': AccessType.READ_ONLY,
            'r': AccessType.READ_ONLY,
            'read-only': AccessType.READ_ONLY,
            'wo': AccessType.WRITE_ONLY,
            'w': AccessType.WRITE_ONLY,
            'write-only': AccessType.WRITE_ONLY,
            'w1c': AccessType.WRITE_1_CLEAR,
            'w1s': AccessType.WRITE_1_SET,
        }
        return access_map.get(access_str.lower().strip(), AccessType.READ_WRITE)


class JSONRegisterParser:
    """
    Parser for JSON register definitions.
    Flexible format that many teams use.
    """
    
    def parse(self, content: str, source_file: str = "") -> ParsedSpec:
        """Parse JSON content"""
        data = json.loads(content)
        
        name = data.get('name', data.get('module', 'json_import'))
        description = data.get('description', '')
        data_width = data.get('data_width', 32)
        addr_width = data.get('addr_width', 32)
        
        registers = []
        for reg_data in data.get('registers', []):
            reg = Register(
                name=reg_data.get('name', 'unknown'),
                address=int(str(reg_data.get('address', reg_data.get('offset', 0))), 0),
                description=reg_data.get('description', ''),
                width=reg_data.get('width', 32),
                reset_value=int(str(reg_data.get('reset', 0)), 0)
            )
            
            for field_data in reg_data.get('fields', []):
                field = BitField(
                    name=field_data.get('name', 'unknown'),
                    description=field_data.get('description', ''),
                    bit_offset=field_data.get('offset', field_data.get('lsb', 0)),
                    bit_width=field_data.get('width', field_data.get('bits', 1)),
                    access=AccessType(field_data.get('access', 'rw')),
                    reset_value=int(str(field_data.get('reset', 0)), 0)
                )
                reg.fields.append(field)
            
            registers.append(reg)
        
        block = RegisterBlock(
            name=name,
            base_address=data.get('base_address', 0),
            registers=registers
        )
        
        return ParsedSpec(
            name=name,
            description=description,
            data_width=data_width,
            addr_width=addr_width,
            register_blocks=[block],
            source_format="JSON",
            source_file=source_file
        )
    
    def parse_file(self, file_path: str) -> ParsedSpec:
        """Parse JSON from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"JSON file not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))


class UnifiedSpecParser:
    """
    Unified parser that auto-detects format and parses accordingly.
    """
    
    def __init__(self):
        self.ipxact_parser = IPXACTParser()
        self.rdl_parser = SystemRDLParser()
        self.csv_parser = CSVRegisterParser()
        self.json_parser = JSONRegisterParser()
    
    def parse(self, content: str, source_file: str = "") -> ParsedSpec:
        """Auto-detect format and parse"""
        format_type = self._detect_format(content, source_file)
        
        if format_type == "IP-XACT":
            return self.ipxact_parser.parse(content, source_file)
        elif format_type == "SystemRDL":
            return self.rdl_parser.parse(content, source_file)
        elif format_type == "CSV":
            return self.csv_parser.parse(content, source_file)
        elif format_type == "JSON":
            return self.json_parser.parse(content, source_file)
        else:
            raise ValueError(f"Unknown specification format")
    
    def parse_file(self, file_path: str) -> ParsedSpec:
        """Parse from file"""
        path = Path(file_path)
        if not path.exists():
            raise FileNotFoundError(f"File not found: {file_path}")
        
        content = path.read_text()
        return self.parse(content, str(path))
    
    def _detect_format(self, content: str, file_path: str = "") -> str:
        """Detect the specification format"""
        ext = Path(file_path).suffix.lower() if file_path else ""
        
        # Check by extension
        if ext == '.xml':
            if 'ipxact' in content.lower() or 'spirit' in content.lower():
                return "IP-XACT"
        elif ext == '.rdl':
            return "SystemRDL"
        elif ext == '.csv':
            return "CSV"
        elif ext == '.json':
            return "JSON"
        
        # Check by content
        content_lower = content.lower()
        if '<?xml' in content_lower and ('ipxact' in content_lower or 'spirit' in content_lower):
            return "IP-XACT"
        elif 'addrmap' in content_lower and 'reg' in content_lower:
            return "SystemRDL"
        elif content.strip().startswith('{'):
            return "JSON"
        elif ',' in content and ('register' in content_lower or 'address' in content_lower):
            return "CSV"
        
        return "unknown"


def spec_to_dict(spec: ParsedSpec) -> Dict[str, Any]:
    """Convert ParsedSpec to dictionary for JSON serialization"""
    return {
        'name': spec.name,
        'version': spec.version,
        'description': spec.description,
        'data_width': spec.data_width,
        'addr_width': spec.addr_width,
        'source_format': spec.source_format,
        'total_registers': spec.total_registers,
        'register_blocks': [
            {
                'name': block.name,
                'base_address': block.base_address,
                'description': block.description,
                'registers': [
                    {
                        'name': reg.name,
                        'address': reg.address,
                        'address_hex': reg.address_hex,
                        'description': reg.description,
                        'width': reg.width,
                        'access': reg.access.value,
                        'reset_value': reg.reset_value,
                        'fields': [
                            {
                                'name': f.name,
                                'description': f.description,
                                'bits': f'{f.msb}:{f.lsb}' if f.bit_width > 1 else str(f.bit_offset),
                                'width': f.bit_width,
                                'access': f.access.value,
                                'reset': f.reset_value
                            }
                            for f in reg.fields
                        ]
                    }
                    for reg in block.registers
                ]
            }
            for block in spec.register_blocks
        ]
    }


# Example usage
if __name__ == "__main__":
    # Test CSV parser
    sample_csv = """Register Name,Address,Field Name,Bit Range,Access,Reset Value,Description
STATUS,0x00,BUSY,0,RO,0,Device busy flag
STATUS,0x00,ERROR,1,RO,0,Error flag
STATUS,0x00,DONE,2,RO,0,Operation complete
CONTROL,0x04,START,0,RW,0,Start operation
CONTROL,0x04,RESET,1,W1C,0,Reset device
CONTROL,0x04,MODE,7:4,RW,0,Operation mode
DATA,0x08,VALUE,31:0,RW,0,Data register
CONFIG,0x0C,ENABLE,0,RW,0,Enable device
CONFIG,0x0C,INT_EN,1,RW,0,Interrupt enable
"""
    
    parser = UnifiedSpecParser()
    spec = parser.parse(sample_csv, "test.csv")
    
    import json
    print(json.dumps(spec_to_dict(spec), indent=2))
