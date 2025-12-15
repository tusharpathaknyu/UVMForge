#!/usr/bin/env python3
"""
VerifAI - AI-Powered UVM Testbench Generator
Main CLI Entry Point
"""

import os
import sys
from pathlib import Path

import click
from rich.console import Console
from rich.panel import Panel
from rich.progress import Progress, SpinnerColumn, TextColumn
from rich.syntax import Syntax
from rich.table import Table

from src.llm_client import get_llm_client
from src.parser import SpecParser
from src.generator import UVMGenerator

console = Console()


def print_banner():
    """Print the VerifAI banner"""
    banner = """
╔═══════════════════════════════════════════════════════════╗
║                    🚀 VerifAI v1.0                        ║
║          AI-Powered UVM Testbench Generator               ║
╚═══════════════════════════════════════════════════════════╝
    """
    console.print(banner, style="bold cyan")


def print_examples():
    """Print example specifications"""
    examples = """
[bold]Example Specifications:[/bold]

[cyan]1. Simple APB register block:[/cyan]
   "Create APB testbench for a register block with STATUS (0x00, RO), 
    CONTROL (0x04, RW), DATA (0x08, RW)"

[cyan]2. AXI4-Lite peripheral:[/cyan]
   "Create AXI4-Lite testbench for a GPIO controller with 
    DATA register at 0x00 and DIRECTION register at 0x04"

[cyan]3. Detailed specification:[/cyan]
   "Create a UVM testbench for an APB slave with 32-bit data width,
    containing 4 registers: STATUS (0x00, read-only, reset 0x1),
    CONTROL (0x04, read-write), TX_DATA (0x08, write-only),
    RX_DATA (0x0C, read-only)"
    """
    console.print(examples)


@click.command()
@click.option('--spec', '-s', help='Specification string')
@click.option('--spec-file', '-f', type=click.Path(exists=True), help='Specification file')
@click.option('--protocol', '-p', type=click.Choice(['apb', 'axi4lite', 'auto']), 
              default='auto', help='Protocol (default: auto-detect)')
@click.option('--output', '-o', type=click.Path(), default='./output', 
              help='Output directory')
@click.option('--llm', type=click.Choice(['auto', 'openai', 'anthropic', 'ollama', 'gemini', 'mock']),
              default='auto', help='LLM provider')
@click.option('--interactive', '-i', is_flag=True, help='Interactive mode')
def main(spec, spec_file, protocol, output, llm, interactive):
    """
    VerifAI - Generate UVM testbenches from natural language.
    
    Examples:
    
        verifai --spec "APB slave with 4 registers"
        
        verifai --spec-file my_spec.txt --output ./my_tb
        
        verifai --interactive
    """
    print_banner()
    
    # Get specification
    if spec_file:
        spec = Path(spec_file).read_text()
    elif interactive or not spec:
        spec = interactive_mode()
        if not spec:
            return
    
    # Generate testbench
    generate_testbench(spec, output, llm)


def interactive_mode() -> str:
    """Run interactive mode to get specification"""
    console.print("\n[bold]Enter your specification[/bold] (or 'help' for examples, 'quit' to exit):\n")
    
    while True:
        spec = console.input("[bold cyan]> [/bold cyan]")
        
        if spec.lower() == 'quit':
            console.print("Goodbye! 👋")
            return ""
        elif spec.lower() == 'help':
            print_examples()
            continue
        elif spec.strip():
            return spec
        else:
            console.print("[yellow]Please enter a specification.[/yellow]")


def generate_testbench(spec: str, output_dir: str, llm_provider: str):
    """Generate testbench from specification"""
    
    with Progress(
        SpinnerColumn(),
        TextColumn("[progress.description]{task.description}"),
        console=console,
    ) as progress:
        
        # Step 1: Initialize LLM
        task = progress.add_task("[cyan]Initializing LLM...", total=None)
        try:
            llm_client = get_llm_client(llm_provider)
        except Exception as e:
            console.print(f"[red]Error initializing LLM: {e}[/red]")
            console.print("[yellow]Tip: Run 'ollama serve' for free local LLM, or set OPENAI_API_KEY[/yellow]")
            return
        progress.update(task, completed=True)
        
        # Step 2: Parse specification
        task = progress.add_task("[cyan]Parsing specification...", total=None)
        parser = SpecParser(llm_client)
        try:
            parsed = parser.parse(spec)
        except Exception as e:
            console.print(f"[red]Error parsing specification: {e}[/red]")
            # Fallback to quick parse
            console.print("[yellow]Falling back to quick parse...[/yellow]")
            parsed = parser.parse_quick(spec)
        progress.update(task, completed=True)
        
        # Show parsed specification
        console.print("\n[bold]Parsed Specification:[/bold]")
        table = Table(show_header=False, box=None)
        table.add_row("Protocol:", f"[cyan]{parsed.protocol.upper()}[/cyan]")
        table.add_row("Module:", f"[cyan]{parsed.module_name}[/cyan]")
        table.add_row("Data Width:", f"[cyan]{parsed.data_width}[/cyan]")
        table.add_row("Registers:", f"[cyan]{len(parsed.registers)}[/cyan]")
        console.print(table)
        
        if parsed.registers:
            console.print("\n[bold]Registers:[/bold]")
            reg_table = Table()
            reg_table.add_column("Name")
            reg_table.add_column("Address")
            reg_table.add_column("Access")
            for reg in parsed.registers:
                reg_table.add_row(reg.name, f"0x{reg.address:02X}", reg.access.value)
            console.print(reg_table)
        
        # Step 3: Generate files
        task = progress.add_task("[cyan]Generating UVM files...", total=None)
        generator = UVMGenerator()
        
        # Create output directory with module name
        full_output = Path(output_dir) / parsed.module_name
        
        try:
            files = generator.generate(parsed, str(full_output))
        except Exception as e:
            console.print(f"[red]Error generating files: {e}[/red]")
            return
        progress.update(task, completed=True)
    
    # Print results
    console.print(f"\n[bold green]✅ Generated {len(files)} files in {full_output}/[/bold green]\n")
    
    console.print("[bold]Files created:[/bold]")
    for f in files:
        icon = "📦" if f.category == "package" else \
               "🔌" if f.category == "interface" else \
               "🤖" if f.category == "agent" else \
               "📊" if f.category in ["scoreboard", "coverage"] else \
               "🧪" if f.category == "test" else \
               "📁"
        console.print(f"  {icon} {f.filename}")
    
    console.print(f"\n[bold]Next steps:[/bold]")
    console.print(f"  1. Add your DUT to [cyan]{full_output}/[/cyan]")
    console.print(f"  2. Run: [cyan]cd {full_output} && make sim[/cyan]")
    console.print()


if __name__ == "__main__":
    main()
