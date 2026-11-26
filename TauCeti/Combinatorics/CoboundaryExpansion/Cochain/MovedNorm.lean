/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.CoboundaryExpansion.Cochain.Basic
public import TauCeti.GroupTheory.Perm.MovedNorm

/-!
# Moved-point counts on the complete complex

For permutation-valued cochains built from increasing pairs, defect and gauge cost for the
moved-point norm can be computed as natural-number sums before casting to the reals.
-/

public section

namespace TauCeti.Cochain

open Finset Equiv Equiv.Perm TwoComplex

variable {V A : Type*} [Fintype V] [LinearOrder V] [Fintype A] [DecidableEq A]

/-- The moved-point defect is the sum of triangle permutation support sizes. -/
theorem defect_ofLt_complete_movedNorm (f : V → V → Perm A) :
    (ofLt (complete V) f).defect (movedNorm A) =
      (↑(∑ p ∈ univ.filter (fun p : V × V × V => p.1 < p.2.1 ∧ p.2.1 < p.2.2),
        (f p.1 p.2.1 * f p.2.1 p.2.2 * (f p.1 p.2.2)⁻¹).support.card) : ℝ) := by
  rw [defect_ofLt_complete]
  simp only [movedNorm_apply, Nat.cast_sum]

/-- The moved-point gauge cost is the sum of gauged edge permutation support sizes. -/
theorem cost_ofLt_complete_movedNorm (f : V → V → Perm A) (β : V → Perm A) :
    (ofLt (complete V) f).cost (movedNorm A) β =
      (↑(∑ p ∈ univ.filter (fun p : V × V => p.1 < p.2),
        ((β p.1)⁻¹ * f p.1 p.2 * β p.2).support.card) : ℝ) := by
  rw [cost_ofLt_complete]
  simp only [movedNorm_apply, Nat.cast_sum]

end TauCeti.Cochain
