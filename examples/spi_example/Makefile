# UVMForge Generated Makefile
# Protocol: SPI
# Module: spi_controller

# Simulator selection (override with: make SIM=questa)
SIM ?= verilator

# Source files
SV_FILES = \
    spi_pkg.sv \\
    spi_if.sv \\
    spi_seq_item.sv \\
    spi_driver.sv \\
    spi_monitor.sv \\
    spi_sequencer.sv \\
    spi_agent.sv \\
    spi_seq_lib.sv \\
    spi_scoreboard.sv \\
    spi_coverage.sv \\
    spi_env.sv \\
    spi_base_test.sv \\
    top_tb.sv

# UVM settings
UVM_HOME ?= $(shell which vcs > /dev/null && echo "builtin" || echo "$(HOME)/uvm-1.2")
UVM_FLAGS = +UVM_VERBOSITY=UVM_MEDIUM +UVM_TESTNAME=spi_base_test

# Verilator flags
VERILATOR_FLAGS = --binary --timing -Wall -Wno-fatal

# VCS flags  
VCS_FLAGS = -full64 -sverilog +v2k -timescale=1ns/1ps -ntb_opts uvm-1.2

# Questa flags
QUESTA_FLAGS = -sv -timescale 1ns/1ps +acc -coverage

.PHONY: all sim clean compile run

all: sim

# Verilator (free, open-source)
verilator: $(SV_FILES)
	verilator $(VERILATOR_FLAGS) --top-module top_tb $(SV_FILES)
	./obj_dir/Vtop_tb

# VCS
vcs: $(SV_FILES)
	vcs $(VCS_FLAGS) -o simv $(SV_FILES)
	./simv $(UVM_FLAGS)

# Questa/ModelSim
questa: $(SV_FILES)
	vlib work
	vlog $(QUESTA_FLAGS) $(SV_FILES)
	vsim -c -do "run -all; quit" top_tb $(UVM_FLAGS)

# Generic sim target
sim:
ifeq ($(SIM),verilator)
	$(MAKE) verilator
else ifeq ($(SIM),vcs)
	$(MAKE) vcs
else ifeq ($(SIM),questa)
	$(MAKE) questa
else
	@echo "Unknown simulator: $(SIM)"
	@echo "Supported: verilator, vcs, questa"
endif

clean:
	rm -rf obj_dir simv* work *.log *.vcd csrc DVEfiles
