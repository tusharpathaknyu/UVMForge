"""
LLM Client - Handles communication with various LLM providers
Supports: OpenAI, Anthropic, Ollama (local), Google Gemini
"""

import os
from abc import ABC, abstractmethod
from typing import Optional, Dict, Any
from dataclasses import dataclass
import json

# Load environment variables from .env file
from dotenv import load_dotenv
load_dotenv()


@dataclass
class LLMResponse:
    """Response from LLM"""
    content: str
    model: str
    tokens_used: int = 0
    

class BaseLLMClient(ABC):
    """Abstract base class for LLM clients"""
    
    @abstractmethod
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        """Generate response from LLM"""
        pass
    
    @abstractmethod
    def is_available(self) -> bool:
        """Check if this LLM provider is available"""
        pass


class OpenAIClient(BaseLLMClient):
    """OpenAI GPT Client"""
    
    def __init__(self, model: str = "gpt-4o-mini"):
        self.model = model
        self.api_key = os.getenv("OPENAI_API_KEY")
        self._client = None
        
    def is_available(self) -> bool:
        return self.api_key is not None
    
    def _get_client(self):
        if self._client is None:
            try:
                from openai import OpenAI
                self._client = OpenAI(api_key=self.api_key)
            except ImportError:
                raise ImportError("OpenAI package not installed. Run: pip install openai")
        return self._client
    
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        client = self._get_client()
        
        messages = []
        if system_prompt:
            messages.append({"role": "system", "content": system_prompt})
        messages.append({"role": "user", "content": prompt})
        
        response = client.chat.completions.create(
            model=self.model,
            messages=messages,
            temperature=0.7,
            max_tokens=4096
        )
        
        return LLMResponse(
            content=response.choices[0].message.content,
            model=self.model,
            tokens_used=response.usage.total_tokens if response.usage else 0
        )


class AnthropicClient(BaseLLMClient):
    """Anthropic Claude Client"""
    
    def __init__(self, model: str = "claude-3-haiku-20240307"):
        self.model = model
        self.api_key = os.getenv("ANTHROPIC_API_KEY")
        self._client = None
        
    def is_available(self) -> bool:
        return self.api_key is not None
    
    def _get_client(self):
        if self._client is None:
            try:
                from anthropic import Anthropic
                self._client = Anthropic(api_key=self.api_key)
            except ImportError:
                raise ImportError("Anthropic package not installed. Run: pip install anthropic")
        return self._client
    
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        client = self._get_client()
        
        response = client.messages.create(
            model=self.model,
            max_tokens=4096,
            system=system_prompt if system_prompt else "You are a helpful assistant.",
            messages=[{"role": "user", "content": prompt}]
        )
        
        return LLMResponse(
            content=response.content[0].text,
            model=self.model,
            tokens_used=response.usage.input_tokens + response.usage.output_tokens
        )


class OllamaClient(BaseLLMClient):
    """Ollama Local LLM Client (Free!)"""
    
    def __init__(self, model: str = "llama3.2"):
        self.model = model
        self.base_url = os.getenv("OLLAMA_HOST", "http://localhost:11434")
        
    def is_available(self) -> bool:
        try:
            import requests
            response = requests.get(f"{self.base_url}/api/tags", timeout=2)
            return response.status_code == 200
        except:
            return False
    
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        try:
            import ollama
            
            full_prompt = prompt
            if system_prompt:
                full_prompt = f"{system_prompt}\n\n{prompt}"
            
            response = ollama.generate(
                model=self.model,
                prompt=full_prompt
            )
            
            return LLMResponse(
                content=response['response'],
                model=self.model,
                tokens_used=response.get('eval_count', 0)
            )
        except ImportError:
            # Fallback to requests
            import requests
            
            payload = {
                "model": self.model,
                "prompt": prompt,
                "system": system_prompt,
                "stream": False
            }
            
            response = requests.post(
                f"{self.base_url}/api/generate",
                json=payload
            )
            
            if response.status_code == 200:
                data = response.json()
                return LLMResponse(
                    content=data.get('response', ''),
                    model=self.model
                )
            else:
                raise Exception(f"Ollama error: {response.text}")


class MockLLMClient(BaseLLMClient):
    """Mock client for testing without LLM"""
    
    def __init__(self):
        self.model = "mock"
        
    def is_available(self) -> bool:
        return True
    
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        # Return a mock parsed specification
        return LLMResponse(
            content=json.dumps({
                "protocol": "apb",
                "module_name": "apb_register_block",
                "data_width": 32,
                "addr_width": 8,
                "registers": [
                    {"name": "STATUS", "address": "0x00", "access": "RO", "reset_value": "0x0"},
                    {"name": "CONTROL", "address": "0x04", "access": "RW", "reset_value": "0x0"},
                    {"name": "DATA", "address": "0x08", "access": "RW", "reset_value": "0x0"},
                    {"name": "CONFIG", "address": "0x0C", "access": "RW", "reset_value": "0x0"}
                ],
                "features": ["scoreboard", "coverage", "sequences"]
            }),
            model="mock"
        )


class GeminiClient(BaseLLMClient):
    """Google Gemini Client"""
    
    def __init__(self, model: str = "gemini-2.0-flash"):
        self.model = model
        self.api_key = os.getenv("GOOGLE_API_KEY")
        self._client = None
        
    def is_available(self) -> bool:
        return self.api_key is not None
    
    def _get_client(self):
        if self._client is None:
            try:
                import google.generativeai as genai
                genai.configure(api_key=self.api_key)
                self._client = genai.GenerativeModel(self.model)
            except ImportError:
                raise ImportError("Google Generative AI package not installed. Run: pip install google-generativeai")
        return self._client
    
    def generate(self, prompt: str, system_prompt: str = "") -> LLMResponse:
        client = self._get_client()
        
        full_prompt = prompt
        if system_prompt:
            full_prompt = f"{system_prompt}\n\n{prompt}"
        
        response = client.generate_content(full_prompt)
        
        return LLMResponse(
            content=response.text,
            model=self.model,
            tokens_used=0  # Gemini doesn't return token count in the same way
        )


def get_llm_client(provider: str = "auto") -> BaseLLMClient:
    """
    Get an LLM client based on provider preference.
    
    Args:
        provider: One of "auto", "openai", "anthropic", "ollama", "mock"
        
    Returns:
        An LLM client instance
    """
    if provider == "mock":
        return MockLLMClient()
    
    if provider == "openai":
        client = OpenAIClient()
        if not client.is_available():
            raise ValueError("OpenAI API key not found. Set OPENAI_API_KEY environment variable.")
        return client
    
    if provider == "anthropic":
        client = AnthropicClient()
        if not client.is_available():
            raise ValueError("Anthropic API key not found. Set ANTHROPIC_API_KEY environment variable.")
        return client
    
    if provider == "ollama":
        client = OllamaClient()
        if not client.is_available():
            raise ValueError("Ollama is not running. Start it with: ollama serve")
        return client
    
    if provider == "gemini":
        client = GeminiClient()
        if not client.is_available():
            raise ValueError("Google API key not found. Set GOOGLE_API_KEY environment variable.")
        return client
    
    # Auto mode: try each provider in order
    if provider == "auto":
        # Priority: Gemini (you have key) > Ollama (free) > OpenAI > Anthropic
        clients = [
            ("Google Gemini", GeminiClient()),
            ("Ollama (local)", OllamaClient()),
            ("OpenAI", OpenAIClient()),
            ("Anthropic", AnthropicClient()),
        ]
        
        for name, client in clients:
            if client.is_available():
                print(f"✓ Using {name} as LLM provider")
                return client
        
        # Fall back to mock if nothing available
        print("⚠ No LLM provider available. Using mock mode (limited functionality)")
        return MockLLMClient()
    
    raise ValueError(f"Unknown provider: {provider}")
