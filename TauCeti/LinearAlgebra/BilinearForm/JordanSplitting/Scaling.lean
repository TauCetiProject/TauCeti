/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.BilinearForm.JordanSplitting.Basic

/-!
# Scaling a Jordan splitting

Multiplying a bilinear form by its uniformizer shifts every Jordan constituent up one
scale, inserting the zero submodule at scale zero. This gives a splitting of the scaled
form without choosing a new orthogonal decomposition.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §91C.
-/

public section

namespace LinearMap.BilinForm

open LinearMap (BilinForm)

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  {B : BilinForm R M} {π : R} {N : ℕ → Submodule R M}

/-- Multiplication by `π` shifts a Jordan splitting up one scale, with zero constituent
at scale zero. Neither symmetry nor nondegeneracy is needed for this construction. -/
theorem IsJordanSplitting.smul_uniformizer (h : B.IsJordanSplitting π N) :
    (π • B).IsJordanSplitting π (fun | 0 => ⊥ | i + 1 => N i) where
  isInternal := by
    refine (DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top _).mpr ⟨?_, ?_⟩
    · intro i
      cases i with
      | zero => exact disjoint_bot_left
      | succ i =>
        apply (h.isInternal.submodule_iSupIndep i).mono_right
        refine iSup₂_le fun j hj ↦ ?_
        cases j with
        | zero => exact bot_le
        | succ j => exact le_iSup₂_of_le j (by omega) le_rfl
    · apply eq_top_iff.mpr
      rw [← h.isInternal.submodule_iSup_eq_top]
      exact iSup_le fun i ↦ le_iSup (fun | 0 => (⊥ : Submodule R M) | j + 1 => N j) (i + 1)
  apply_eq_zero := by
    intro i j hij x hx y hy
    cases i with
    | zero => simp_all
    | succ i =>
      cases j with
      | zero => simp_all
      | succ j => simp [h.apply_eq_zero i j (by omega) x hx y hy]
  isModular := by
    intro i
    cases i with
    | zero =>
      exact isModular_of_subsingleton
    | succ i =>
      simpa only [smul_restrict, pow_succ'] using
        (h.isModular i).smul π

end LinearMap.BilinForm

end
