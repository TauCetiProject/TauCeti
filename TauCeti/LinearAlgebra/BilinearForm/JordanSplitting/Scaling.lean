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

variable {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M]
  {B : BilinForm R M} {π : R} {N : ℕ → Submodule R M}

/-- Multiplication by `π` shifts a Jordan splitting up one scale, with zero constituent
at scale zero. Neither symmetry nor nondegeneracy is needed for this construction. -/
theorem IsJordanSplitting.uniformizer_smul (h : B.IsJordanSplitting π N) :
    (π • B).IsJordanSplitting π (fun | 0 => ⊥ | i + 1 => N i) where
  isInternal := by
    -- Shift and unshift the direct sum explicitly: the lattice characterization of
    -- internality needs additive inverses, whereas recomposition works over semirings.
    let S : ℕ → Submodule R M := fun | 0 => ⊥ | i + 1 => N i
    let E := DirectSum.toModule (M := fun i ↦ N i) R ℕ (DirectSum ℕ (fun i ↦ S i))
      (fun i ↦ DirectSum.lof R ℕ (fun i ↦ S i) (i + 1))
    let F := DirectSum.toModule (M := fun i ↦ S i) R ℕ (DirectSum ℕ (fun i ↦ N i))
      (fun | 0 => 0 | i + 1 => DirectSum.lof R ℕ (fun i ↦ N i) i)
    have hFE : F.comp E = LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp [E, F]
    have hEF : E.comp F = LinearMap.id := by
      apply DirectSum.linearMap_ext
      intro i
      cases i with
      | zero =>
        ext x
        have hx : x = 0 := Subsingleton.elim _ _
        simp [hx]
      | succ i =>
        ext x
        simp [E, F]
    have hcoe : (DirectSum.coeLinearMap S).comp E = DirectSum.coeLinearMap N := by
      apply DirectSum.linearMap_ext
      intro i
      ext x
      simp [E]
    have hleft : Function.LeftInverse F E := fun x ↦ LinearMap.congr_fun hFE x
    have hright : Function.RightInverse F E := fun x ↦ LinearMap.congr_fun hEF x
    have hE : Function.Bijective E := ⟨hleft.injective, hright.surjective⟩
    -- IsInternal uses additive recomposition; coeLinearMap has the same underlying map.
    have hInternal := h.isInternal
    change Function.Bijective (DirectSum.coeLinearMap N) at hInternal
    change Function.Bijective (DirectSum.coeLinearMap S)
    apply (Function.Bijective.of_comp_iff _ hE).mp
    simpa only [← LinearMap.coe_comp, hcoe] using hInternal
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
      simpa only [restrict_smul, pow_succ'] using
        (h.isModular i).smul π

end LinearMap.BilinForm

end
