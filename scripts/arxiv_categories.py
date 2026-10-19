"""arXiv's mathematics categories, and the one each TauCetiRoadmap roadmap declares.

Every roadmap directory in TauCetiRoadmap carries a `metadata.toml` naming one category by its
code (`topic = "math.NT"`). The site shows the category's name, never the code: "Number Theory".
Shared by the Progress page's generator (`roadmap_progress.py`) and the Statistics charts
(`pr_stats_graphs.py`). Pure stdlib.
"""

from __future__ import annotations

import pathlib
import tomllib

# https://arxiv.org/category_taxonomy
ARXIV_MATH = {
    "math.AC": "Commutative Algebra", "math.AG": "Algebraic Geometry", "math.AP": "Analysis of PDEs",
    "math.AT": "Algebraic Topology", "math.CA": "Classical Analysis and ODEs",
    "math.CO": "Combinatorics", "math.CT": "Category Theory", "math.CV": "Complex Variables",
    "math.DG": "Differential Geometry", "math.DS": "Dynamical Systems",
    "math.FA": "Functional Analysis", "math.GM": "General Mathematics", "math.GN": "General Topology",
    "math.GR": "Group Theory", "math.GT": "Geometric Topology", "math.HO": "History and Overview",
    "math.IT": "Information Theory", "math.KT": "K-Theory and Homology", "math.LO": "Logic",
    "math.MG": "Metric Geometry", "math.MP": "Mathematical Physics", "math.NA": "Numerical Analysis",
    "math.NT": "Number Theory", "math.OA": "Operator Algebras", "math.OC": "Optimization and Control",
    "math.PR": "Probability", "math.QA": "Quantum Algebra", "math.RA": "Rings and Algebras",
    "math.RT": "Representation Theory", "math.SG": "Symplectic Geometry", "math.SP": "Spectral Theory",
    "math.ST": "Statistics Theory",
}


def read_topic(dirpath: pathlib.Path) -> str | None:
    """The category code a roadmap directory declares in its `metadata.toml`, or None when it declares
    none or one that is not an arXiv mathematics category. Never raises: a missing, unreadable or
    malformed file is no category, not a failure."""
    try:
        topic = tomllib.loads((dirpath / "metadata.toml").read_text(encoding="utf-8")).get("topic")
    except (OSError, UnicodeDecodeError, tomllib.TOMLDecodeError):
        return None
    return topic if isinstance(topic, str) and topic in ARXIV_MATH else None
