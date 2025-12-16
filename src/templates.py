"""
Protocol template snippets for LLM context
"""

PROTOCOL_TEMPLATES = {
    "apb": """
// APB UVM Testbench Structure
interface apb_if(input logic pclk, input logic presetn);
    logic        psel;
    logic        penable;
    logic        pwrite;
    logic [31:0] paddr;
    logic [31:0] pwdata;
    logic [31:0] prdata;
    logic        pready;
    logic        pslverr;
    
    modport master(output psel, penable, pwrite, paddr, pwdata,
                   input prdata, pready, pslverr);
    modport slave(input psel, penable, pwrite, paddr, pwdata,
                  output prdata, pready, pslverr);
endinterface

class apb_seq_item extends uvm_sequence_item;
    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand bit write;
    logic [31:0] rdata;
    logic slverr;
    
    `uvm_object_utils_begin(apb_seq_item)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(write, UVM_ALL_ON)
    `uvm_object_utils_end
endclass
""",

    "axi4_lite": """
// AXI4-Lite UVM Testbench Structure
interface axi4lite_if(input logic aclk, input logic aresetn);
    // Write address channel
    logic        awvalid;
    logic        awready;
    logic [31:0] awaddr;
    logic [2:0]  awprot;
    
    // Write data channel
    logic        wvalid;
    logic        wready;
    logic [31:0] wdata;
    logic [3:0]  wstrb;
    
    // Write response channel
    logic        bvalid;
    logic        bready;
    logic [1:0]  bresp;
    
    // Read address channel
    logic        arvalid;
    logic        arready;
    logic [31:0] araddr;
    logic [2:0]  arprot;
    
    // Read data channel
    logic        rvalid;
    logic        rready;
    logic [31:0] rdata;
    logic [1:0]  rresp;
endinterface

class axi4lite_seq_item extends uvm_sequence_item;
    rand logic [31:0] addr;
    rand logic [31:0] data;
    rand bit write;
    rand logic [3:0] strb;
    logic [1:0] resp;
    
    `uvm_object_utils_begin(axi4lite_seq_item)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(write, UVM_ALL_ON)
        `uvm_field_int(strb, UVM_ALL_ON)
    `uvm_object_utils_end
endclass
""",

    "uart": """
// UART UVM Testbench Structure
interface uart_if(input logic clk, input logic rstn);
    logic tx;
    logic rx;
    logic cts;
    logic rts;
    
    modport transmitter(output tx, rts, input rx, cts);
    modport receiver(input tx, rts, output rx, cts);
endinterface

class uart_seq_item extends uvm_sequence_item;
    rand logic [7:0] data;
    rand bit parity_en;
    rand bit parity_type; // 0=even, 1=odd
    rand int baud_rate;
    logic parity_error;
    logic frame_error;
    
    `uvm_object_utils_begin(uart_seq_item)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(parity_en, UVM_ALL_ON)
        `uvm_field_int(baud_rate, UVM_ALL_ON)
    `uvm_object_utils_end
    
    constraint valid_baud {
        baud_rate inside {9600, 19200, 38400, 57600, 115200};
    }
endclass
""",

    "spi": """
// SPI UVM Testbench Structure
interface spi_if(input logic clk, input logic rstn);
    logic sclk;
    logic mosi;
    logic miso;
    logic ss_n;
    
    modport master(output sclk, mosi, ss_n, input miso);
    modport slave(input sclk, mosi, ss_n, output miso);
endinterface

class spi_seq_item extends uvm_sequence_item;
    rand logic [7:0] data;
    rand bit cpol;
    rand bit cpha;
    logic [7:0] rdata;
    
    `uvm_object_utils_begin(spi_seq_item)
        `uvm_field_int(data, UVM_ALL_ON)
        `uvm_field_int(cpol, UVM_ALL_ON)
        `uvm_field_int(cpha, UVM_ALL_ON)
    `uvm_object_utils_end
    
    constraint valid_mode {
        cpol inside {0, 1};
        cpha inside {0, 1};
    }
endclass
""",

    "i2c": """
// I2C UVM Testbench Structure
interface i2c_if(input logic clk, input logic rstn);
    wire sda;
    wire scl;
    
    logic sda_out;
    logic sda_oe;
    logic scl_out;
    logic scl_oe;
    
    assign sda = sda_oe ? sda_out : 1'bz;
    assign scl = scl_oe ? scl_out : 1'bz;
endinterface

class i2c_seq_item extends uvm_sequence_item;
    rand logic [6:0] addr;
    rand logic [7:0] data[];
    rand bit read;
    rand bit use_10bit_addr;
    logic ack;
    logic nack;
    
    `uvm_object_utils_begin(i2c_seq_item)
        `uvm_field_int(addr, UVM_ALL_ON)
        `uvm_field_array_int(data, UVM_ALL_ON)
        `uvm_field_int(read, UVM_ALL_ON)
    `uvm_object_utils_end
    
    constraint valid_addr {
        addr inside {[7'h08:7'h77]}; // Valid I2C addresses
    }
    
    constraint data_size {
        data.size() inside {[1:256]};
    }
endclass
"""
}
