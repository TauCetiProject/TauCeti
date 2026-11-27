/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Windows.Bounds
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.RayClass
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz.RayClass
public import TauCeti.NumberTheory.LFunctions.Hecke.FamilyRieszRemainder
import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Rat

/-!
# Upper Riesz windows for cyclic families of Dirichlet characters

The weighted first Riesz remainder of a cyclic Dirichlet family is the remainder of its
rational ray class family. The individual explicit formulas then give bounds on the weighted
sum on arbitrarily distant power windows, if the members with nonzero weight have a
common zero-free right half-plane.
-/

public section

open Filter TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- The real Riesz remainder of the transported weights is the weighted cyclic Dirichlet sum. -/
@[simp] theorem familyRieszRemainder_cyclicFamilyWeights (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) (y : ℝ) :
    familyRieszRemainder ℚ (ψ.cyclicFamilyWeights w) y =
      ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re := by
  simpa only [familyRieszRemainder_apply, smul_eq_mul, rieszRemainder_toPrimitiveRayClassCharacter]
    using ψ.sum_cyclicFamilyWeights w (fun η ↦ (η.rieszRemainder y).re)

/-- If the characters with nonzero weight have no zero in `Re s > σ`, the weighted cyclic
Riesz sum has one-sided bounds on windows of any ratio at every exponent above
`max σ (1 / 2)`. In particular, under GRH for the family, every exponent above `1 / 2`
works, with any real weights. -/
theorem hasWindows_cyclicFamily_riesz_of_zeroFreeRightOf (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) {σ θ : ℝ} (hθ : max σ (1 / 2) < θ)
    (h : ∀ κ ∈ ψ.cyclicFamily, w κ ≠ 0 → ZeroFreeRightOf σ κ.character.LFunction)
    (L : ℝ) :
    HasWindows {y | ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re ≤ y ^ θ} L := by
  obtain ⟨C, hC⟩ := exists_abs_familyRieszRemainder_le_of_zeroFreeRightOf_rat
    (ψ.cyclicFamilyWeights w) fun η hη ↦ by
      obtain ⟨κ, rfl⟩ := toPrimitiveRayClassCharacter.surjective η
      obtain ⟨hm, hw⟩ := mem_support_cyclicFamilyWeights.mp hη
      exact (κ.zeroFreeRightOf_heckeLFunctionC_toPrimitiveRayClassCharacter_iff σ).mpr
        (h κ (toPrimitiveRayClassCharacter_mem_cyclicFamilyRayClass.mp hm)
          (by simpa only [Equiv.symm_apply_apply] using hw))
  have hbound : ∀ᶠ y : ℝ in atTop,
      (∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re) ≤ C * y ^ max σ (1 / 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [← ψ.familyRieszRemainder_cyclicFamilyWeights]
    exact (le_abs_self _).trans (hC y hy)
  exact hasWindows_rpow_bound_of_eventually_le hbound hθ L

end TauCeti.PrimitiveDirichletCharacter
