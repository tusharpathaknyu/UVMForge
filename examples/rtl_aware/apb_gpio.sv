// Sample APB Slave for VerifAI RTL-Aware Demo
// This file demonstrates what VerifAI can parse and generate testbenches for

module apb_gpio #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 8,
    parameter NUM_GPIOS  = 16
) (
    // APB Interface
    input  logic                    pclk,
    input  logic                    preset_n,
    input  logic                    psel,
    input  logic                    penable,
    input  logic                    pwrite,
    input  logic [ADDR_WIDTH-1:0]   paddr,
    input  logic [DATA_WIDTH-1:0]   pwdata,
    output logic [DATA_WIDTH-1:0]   prdata,
    output logic                    pready,
    output logic                    pslverr,
    
    // GPIO Interface
    input  logic [NUM_GPIOS-1:0]    gpio_in,
    output logic [NUM_GPIOS-1:0]    gpio_out,
    output logic [NUM_GPIOS-1:0]    gpio_oe,
    
    // Interrupt
    output logic                    gpio_irq
);

    // =========================================================================
    // Register Map
    // =========================================================================
    // 0x00 - GPIO_DATA     : GPIO data register (RW)
    // 0x04 - GPIO_DIR      : GPIO direction (1=output, 0=input) (RW)
    // 0x08 - GPIO_INT_EN   : Interrupt enable per GPIO (RW)
    // 0x0C - GPIO_INT_STAT : Interrupt status (W1C)
    // 0x10 - GPIO_INT_TYPE : Interrupt type (0=level, 1=edge) (RW)
    // 0x14 - GPIO_INT_POL  : Interrupt polarity (0=low/fall, 1=high/rise) (RW)
    
    localparam ADDR_GPIO_DATA     = 8'h00;
    localparam ADDR_GPIO_DIR      = 8'h04;
    localparam ADDR_GPIO_INT_EN   = 8'h08;
    localparam ADDR_GPIO_INT_STAT = 8'h0C;
    localparam ADDR_GPIO_INT_TYPE = 8'h10;
    localparam ADDR_GPIO_INT_POL  = 8'h14;
    
    // Registers
    logic [NUM_GPIOS-1:0] reg_data;
    logic [NUM_GPIOS-1:0] reg_dir;
    logic [NUM_GPIOS-1:0] reg_int_en;
    logic [NUM_GPIOS-1:0] reg_int_stat;
    logic [NUM_GPIOS-1:0] reg_int_type;
    logic [NUM_GPIOS-1:0] reg_int_pol;
    
    // APB State Machine
    typedef enum logic [1:0] {
        IDLE   = 2'b00,
        SETUP  = 2'b01,
        ACCESS = 2'b10
    } apb_state_t;
    
    apb_state_t state, next_state;
    
    // =========================================================================
    // APB State Machine
    // =========================================================================
    always_ff @(posedge pclk or negedge preset_n) begin
        if (!preset_n)
            state <= IDLE;
        else
            state <= next_state;
    end
    
    always_comb begin
        next_state = state;
        case (state)
            IDLE:   if (psel) next_state = SETUP;
            SETUP:  if (penable) next_state = ACCESS;
            ACCESS: next_state = IDLE;
        endcase
    end
    
    // Ready always asserted (no wait states)
    assign pready = (state == ACCESS);
    assign pslverr = 1'b0;
    
    // =========================================================================
    // Register Write
    // =========================================================================
    always_ff @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            reg_data     <= '0;
            reg_dir      <= '0;
            reg_int_en   <= '0;
            reg_int_stat <= '0;
            reg_int_type <= '0;
            reg_int_pol  <= '0;
        end else if (state == ACCESS && pwrite) begin
            case (paddr)
                ADDR_GPIO_DATA:     reg_data     <= pwdata[NUM_GPIOS-1:0];
                ADDR_GPIO_DIR:      reg_dir      <= pwdata[NUM_GPIOS-1:0];
                ADDR_GPIO_INT_EN:   reg_int_en   <= pwdata[NUM_GPIOS-1:0];
                ADDR_GPIO_INT_STAT: reg_int_stat <= reg_int_stat & ~pwdata[NUM_GPIOS-1:0]; // W1C
                ADDR_GPIO_INT_TYPE: reg_int_type <= pwdata[NUM_GPIOS-1:0];
                ADDR_GPIO_INT_POL:  reg_int_pol  <= pwdata[NUM_GPIOS-1:0];
            endcase
        end
    end
    
    // =========================================================================
    // Register Read
    // =========================================================================
    always_comb begin
        prdata = '0;
        case (paddr)
            ADDR_GPIO_DATA:     prdata[NUM_GPIOS-1:0] = gpio_in;  // Read actual input
            ADDR_GPIO_DIR:      prdata[NUM_GPIOS-1:0] = reg_dir;
            ADDR_GPIO_INT_EN:   prdata[NUM_GPIOS-1:0] = reg_int_en;
            ADDR_GPIO_INT_STAT: prdata[NUM_GPIOS-1:0] = reg_int_stat;
            ADDR_GPIO_INT_TYPE: prdata[NUM_GPIOS-1:0] = reg_int_type;
            ADDR_GPIO_INT_POL:  prdata[NUM_GPIOS-1:0] = reg_int_pol;
        endcase
    end
    
    // =========================================================================
    // GPIO Output
    // =========================================================================
    assign gpio_out = reg_data;
    assign gpio_oe  = reg_dir;
    
    // =========================================================================
    // Interrupt Logic
    // =========================================================================
    logic [NUM_GPIOS-1:0] gpio_in_sync, gpio_in_d;
    
    // Synchronizer
    always_ff @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            gpio_in_sync <= '0;
            gpio_in_d    <= '0;
        end else begin
            gpio_in_sync <= gpio_in;
            gpio_in_d    <= gpio_in_sync;
        end
    end
    
    // Interrupt detection
    always_ff @(posedge pclk or negedge preset_n) begin
        if (!preset_n) begin
            reg_int_stat <= '0;
        end else begin
            for (int i = 0; i < NUM_GPIOS; i++) begin
                if (reg_int_en[i]) begin
                    if (reg_int_type[i]) begin
                        // Edge triggered
                        if (reg_int_pol[i]) begin
                            // Rising edge
                            if (gpio_in_sync[i] && !gpio_in_d[i])
                                reg_int_stat[i] <= 1'b1;
                        end else begin
                            // Falling edge
                            if (!gpio_in_sync[i] && gpio_in_d[i])
                                reg_int_stat[i] <= 1'b1;
                        end
                    end else begin
                        // Level triggered
                        if (gpio_in_sync[i] == reg_int_pol[i])
                            reg_int_stat[i] <= 1'b1;
                    end
                end
            end
        end
    end
    
    assign gpio_irq = |(reg_int_stat & reg_int_en);

endmodule
