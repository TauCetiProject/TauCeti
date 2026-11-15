/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.LinearAlgebra.Matrix.Defs

/-!
# The bipartite support graph of a matrix

The nonzero entries of a rectangular matrix define a simple graph on the disjoint union of
its row and column types. `Matrix.supportGraph` joins a row and a column exactly when their
entry is nonzero, and has no edges between two rows or between two columns. The entries need
only have a zero element.
-/

public section

namespace Matrix

variable {ι κ : Type*}

section SupportGraph

variable {R : Type*} [Zero R]

/-- The bipartite support graph of a matrix: a row and a column are adjacent exactly when
their matrix entry is nonzero. Rows and columns are separate vertex types even for a square
matrix. -/
def supportGraph (K : Matrix ι κ R) : SimpleGraph (ι ⊕ κ) where
  Adj
    | .inl i, .inr j => K i j ≠ 0
    | .inr j, .inl i => K i j ≠ 0
    | _, _ => False
  symm := ⟨by rintro (_ | _) (_ | _) <;> simp_all⟩
  loopless := ⟨by rintro (_ | _) <;> simp⟩

@[simp]
theorem supportGraph_adj_inl_inr (K : Matrix ι κ R) (i : ι) (j : κ) :
    K.supportGraph.Adj (.inl i) (.inr j) ↔ K i j ≠ 0 := (Iff.rfl)

@[simp]
theorem supportGraph_adj_inr_inl (K : Matrix ι κ R) (j : κ) (i : ι) :
    K.supportGraph.Adj (.inr j) (.inl i) ↔ K i j ≠ 0 := (Iff.rfl)

@[simp]
theorem supportGraph_not_adj_inl_inl (K : Matrix ι κ R) (i i' : ι) :
    ¬K.supportGraph.Adj (.inl i) (.inl i') := by simp [supportGraph]

@[simp]
theorem supportGraph_not_adj_inr_inr (K : Matrix ι κ R) (j j' : κ) :
    ¬K.supportGraph.Adj (.inr j) (.inr j') := by simp [supportGraph]

end SupportGraph

end Matrix
