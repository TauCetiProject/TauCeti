#!/usr/bin/env python3
"""Shared machine placement, capacity and startup recovery regressions."""
import sys
from tauceti_tools.templates import run_script

if __name__ == "__main__":
    raise SystemExit(run_script("test_fleet_runner.py", sys.argv[1:]))
