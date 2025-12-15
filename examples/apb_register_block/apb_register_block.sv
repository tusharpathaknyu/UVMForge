//------------------------------------------------------------------------------
// APB Register Block - Example DUT
// This is a simple APB slave with configurable registers
//------------------------------------------------------------------------------

module apb_register_block #(
    parameter ADDR_WIDTH = 8,
    parameter DATA_WIDTH = 32
)(
    // Clock and Reset
    input  logic                    clk,
    input  logic                    rst_n,
    
    // APB Interface
    input  logic [ADDR_WIDTH-1:0]   paddr,
    input  logic                    psel,
    input  logic                    penable,
    input  logic                    pwrite,
    input  logic [DATA_WIDTH-1:0]   pwdata,
    output logic [DATA_WIDTH-1:0]   prdata,
    output logic                    pready,
    output logic                    pslverr
);

    //--------------------------------------------------------------------------
    // Register Addresses
    //--------------------------------------------------------------------------
    localparam ADDR_STATUS  = 8'h00;
    localparam ADDR_CONTROL = 8'h04;
    localparam ADDR_DATA    = 8'h08;
    localparam ADDR_CONFIG  = 8'h0C;
    
    //--------------------------------------------------------------------------
    // Registers
    //--------------------------------------------------------------------------
    logic [DATA_WIDTH-1:0] reg_status;   // Read-only
    logic [DATA_WIDTH-1:0] reg_control;  // Read-write
    logic [DATA_WIDTH-1:0] reg_data;     // Read-write
    logic [DATA_WIDTH-1:0] reg_config;   // Read-write
    
    //--------------------------------------------------------------------------
    // APB State Machine
    //--------------------------------------------------------------------------
    typedef enum logic [1:0] {
        IDLE   = 2'b00,
        SETUP  = 2'b01,
        ACCESS = 2'b10
    } apb_state_e;
    
    apb_state_e state, next_state;
    
    // State register
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    // Next state logic
    always_comb begin
        next_state = state;
        case (state)
            IDLE: begin
                if (psel && !penable)
                    next_state = SETUP;
            end
            SETUP: begin
                if (psel && penable)
                    next_state = ACCESS;
                else
                    next_state = IDLE;
            end
            ACCESS: begin
                next_state = IDLE;
            end
            default: next_state = IDLE;
        endcase
    end
    
    //--------------------------------------------------------------------------
    // Write Logic
    //--------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n) begin
            reg_control <= '0;
            reg_data    <= '0;
            reg_config  <= '0;
        end
        else if (psel && penable && pwrite) begin
            case (paddr)
                ADDR_CONTROL: reg_control <= pwdata;
                ADDR_DATA:    reg_data    <= pwdata;
                ADDR_CONFIG:  reg_config  <= pwdata;
                // STATUS is read-only, ignore writes
            endcase
        end
    end
    
    //--------------------------------------------------------------------------
    // Read Logic
    //--------------------------------------------------------------------------
    always_comb begin
        prdata = '0;
        if (psel && !pwrite) begin
            case (paddr)
                ADDR_STATUS:  prdata = reg_status;
                ADDR_CONTROL: prdata = reg_control;
                ADDR_DATA:    prdata = reg_data;
                ADDR_CONFIG:  prdata = reg_config;
                default:      prdata = '0;
            endcase
        end
    end
    
    //--------------------------------------------------------------------------
    // Status Register (Example: reflects some internal state)
    //--------------------------------------------------------------------------
    always_ff @(posedge clk or negedge rst_n) begin
        if (!rst_n)
            reg_status <= 32'h0000_0001;  // Reset value: ready bit set
        else begin
            // Example status logic
            reg_status[0] <= 1'b1;                    // Always ready
            reg_status[1] <= (reg_data != '0);        // Data valid
            reg_status[7:2] <= '0;
            reg_status[31:8] <= reg_config[31:8];     // Mirror config
        end
    end
    
    //--------------------------------------------------------------------------
    // Response Signals
    //--------------------------------------------------------------------------
    assign pready  = 1'b1;  // Always ready (no wait states)
    assign pslverr = 1'b0;  // No errors
    
endmodule : apb_register_block
