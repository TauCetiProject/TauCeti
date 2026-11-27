/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.BruhatTits.AffineRoot
import TauCeti.GroupTheory.BruhatTits.SL2

/-!
# Affine roots of `SL₂`

For a real valuation with value group `ℤ`, the standard `SL₂` apartment has affine roots
`a + n`, with `n ∈ ℤ`, in each of its two gradient directions. The base point lies on
the wall with constant zero. Moving by the coroot raises the affine root value by two.
-/

namespace TauCeti.BruhatTits

open DynkinType

variable {K : Type*} [Field K] (ω : AddValuation K (WithTop ℝ))
  (hω : ∃ x : K, x ≠ 0 ∧ ω x ≠ 0)

example (hℤ : {r : ℝ | ∃ x : K, x ≠ 0 ∧ ω x = r} = Set.range (Int.cast : ℤ → ℝ))
    (i : Fin (1 * (1 + 1))) :
    Set.range (fun α : {α : AffineRoot (Valuation.sl2 ℝ ω hω) // α.gradient = i} ↦
      α.val.constant) = Set.range (Int.cast : ℤ → ℝ) := by
  rw [AffineRoot.range_constant, Valuation.primedValueSet_eq_valueSet, Valuation.valueSet_sl2]
  exact hℤ

example (i : Fin (1 * (1 + 1))) :
    ∃ α : AffineRoot (Valuation.sl2 ℝ ω hω), α.gradient = i ∧
      Apartment.base (Valuation.sl2 ℝ ω hω) ∈ α.wall := by
  have h : (0 : ℝ) ∈ (Valuation.sl2 ℝ ω hω).primedValueSet i := by
    simp only [Valuation.primedValueSet_eq_valueSet, Valuation.valueSet_sl2, Set.mem_ofPred_eq]
    exact ⟨1, one_ne_zero, by simp⟩
  exact ⟨⟨i, 0, h⟩, rfl, by simp⟩

example (α : AffineRoot (Valuation.sl2 ℝ ω hω)) (x : Apartment (Valuation.sl2 ℝ ω hω)) :
    α.eval ((sl2RootPairing ℝ).coroot α.gradient +ᵥ x) = 2 + α.eval x := by
  simp

end TauCeti.BruhatTits
