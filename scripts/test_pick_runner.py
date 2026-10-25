#!/usr/bin/env python3
"""Shared runner-picker workflow and recovery-identity regressions."""
import sys
from tauceti_tools.templates import run_script

if __name__ == "__main__":
    raise SystemExit(run_script("test_pick_runner.py", sys.argv[1:]))
