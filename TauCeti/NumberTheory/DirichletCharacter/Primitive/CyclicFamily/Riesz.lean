/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Pow.Windows.Bounds
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.CyclicFamily.RayClass
public import TauCeti.NumberTheory.DirichletCharacter.Primitive.Riesz
public import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Family
import TauCeti.NumberTheory.LFunctions.Hecke.RieszRemainder.Rat

/-!
# Riesz remainders for cyclic families

The weighted remainder on rational ray class characters becomes a finite sum of Dirichlet
remainders indexed by the primitive characters of the cyclic family. A common zero-free
right half-plane for the nonzero-weight members gives upper bounds on arbitrarily distant
scale windows, for either sign of the weights.
-/

public section

open Filter TauCeti.LFunctions

namespace TauCeti.PrimitiveDirichletCharacter

/-- The Riesz remainder of the transferred weights is the weighted sum of the real parts of
the Dirichlet remainders over the original cyclic family. -/
theorem finsuppRieszRemainder_cyclicFamilyWeights (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) (y : ℝ) :
    LFunctions.finsuppRieszRemainder (ψ.cyclicFamilyWeights w) y =
      ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re := by
  rw [LFunctions.finsuppRieszRemainder_apply]
  simpa only [smul_eq_mul, rieszRemainder_toPrimitiveRayClassCharacter] using
    ψ.sum_cyclicFamilyWeights w (fun η ↦ (η.rieszRemainder y).re)

/-- If the L-functions of the nonzero-weight members are zero-free right of
`max σ (1 / 2)`, the weighted cyclic Riesz sum has one-sided bounds on windows of any
ratio at every exponent above `max σ (1 / 2)`. In particular, under GRH for the family,
every exponent above `1 / 2` works, with any real weights. -/
theorem hasWindows_cyclicFamily_riesz_of_zeroFreeRightOf (ψ : PrimitiveDirichletCharacter)
    (w : PrimitiveDirichletCharacter → ℝ) {σ θ : ℝ} (hθ : max σ (1 / 2) < θ)
    (h : ∀ κ ∈ ψ.cyclicFamily, w κ ≠ 0 → ZeroFreeRightOf (max σ (1 / 2)) κ.character.LFunction)
    (L : ℝ) :
    HasWindows {y | ∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re ≤ y ^ θ} L := by
  obtain ⟨C, hC⟩ := exists_norm_finsuppRieszRemainder_le_of_zeroFreeRightOf_rat
    (ψ.cyclicFamilyWeights w) fun η hη ↦ by
      obtain ⟨κ, rfl⟩ := toPrimitiveRayClassCharacter.surjective η
      obtain ⟨hm, hw⟩ := mem_support_cyclicFamilyWeights.mp hη
      exact (κ.zeroFreeRightOf_heckeLFunctionC_toPrimitiveRayClassCharacter_iff _).mpr
        (h κ (toPrimitiveRayClassCharacter_mem_cyclicFamilyRayClass.mp hm)
          (by simpa only [Equiv.symm_apply_apply] using hw))
  have hbound : ∀ᶠ y : ℝ in atTop,
      (∑ κ ∈ ψ.cyclicFamily, w κ * (κ.rieszRemainder y).re) ≤ C * y ^ max σ (1 / 2) := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with y hy
    rw [← ψ.finsuppRieszRemainder_cyclicFamilyWeights]
    exact (Real.le_norm_self _).trans (hC y hy)
  exact hasWindows_rpow_bound_of_eventually_le hbound hθ L

end TauCeti.PrimitiveDirichletCharacter
