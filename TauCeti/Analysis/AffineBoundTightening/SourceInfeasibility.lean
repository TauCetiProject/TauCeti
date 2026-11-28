/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.AffineBoundTightening.Source
public import TauCeti.Analysis.AffineBoundTightening.LinearProgram

/-!
# Scalar infeasibility excludes bounded original feasible points

The initialized affine graph of a bounded original feasible point gives a scalar-feasible
singleton assignment. Consequently infeasibility of the scalar program rules out every
original feasible point in the initial box, including any unchanged extra restrictions and
integer coordinates. No nonempty-iteration or limit hypothesis is required. The implication
is one-way: a feasible scalar program need not give an original feasible point.

This is the bounded application of the joint singleton construction of Belotti, Cafieri,
Lee and Liberti, *Feasibility-Based Bounds Tightening via Fixed Points*, COCOA 2010, §4.
Compare their 2012 Proposition 4.2 for the distinct variable-width formulation. The scalar
display corrections of the qualified joint construction are documented in `LinearProgram`.
-/

public section

open Set

namespace TauCeti.AffineBoundTightening

variable {n m : ℕ}

/-- Scalar-LP infeasibility at the source initialization excludes every original feasible point
in the initial variable box, retaining arbitrary extra and designated-integer restrictions. -/
theorem source_infeasible (A : Matrix (Fin m) (Fin n) ℝ) (r : Fin m → ℝ)
    (l u : Fin n → ℝ) (extra : Set (Fin n → ℝ)) (integers : Finset (Fin n))
    (h : ¬ ∃ p, IsFeasible A (sourceInitial A r l u) p) :
    sourceSet A r extra integers ∩ Icc l u = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hg := (mem_sourceSet_inter_initial_iff.mp hx).2
  exact h ⟨graphAssignment A x, isFeasible_graphAssignment hg⟩

end TauCeti.AffineBoundTightening
