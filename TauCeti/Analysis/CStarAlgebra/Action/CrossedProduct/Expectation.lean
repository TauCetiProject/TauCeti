/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Action.CrossedProduct.Fourier
public import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Positivity and faithfulness of the identity Fourier coefficient

For a discrete group, the identity Fourier coefficient on the concrete regular crossed
product is positive and faithful. Its quadratic form on `x* x` is the squared norm of
`x` applied to a singleton-supported vector. Varying the singleton shows faithfulness,
without a countability assumption on the group or nondegeneracy of the faithful inducing
representation. Coefficients may be nonunital.

We use the existing contractive map `RegularCrossedProduct.fourierCoeff` rather than
introduce a second coefficient map. These results provide the positivity and faithfulness
of the canonical conditional expectation; the coefficient-algebra inclusion and bimodule
identities are not constructed here.

## References

Dana Williams, *Crossed Products of C*-Algebras*, Chapter 7, for the regular representation
and its canonical expectation. The proofs use the matrix-entry formula
`RegularCrossedProduct.inner_single_fourierCoeff`.
-/

public section

noncomputable section

open MeasureTheory
open scoped InnerProductSpace CStarAlgebra

namespace TauCeti.CStarAction.RegularCrossedProduct

variable {G A H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [MeasurableSpace G] [BorelSpace G] [NonUnitalCStarAlgebra A]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (α : CStarAction G A) (ρ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) (hρ : Function.Injective ρ)

/-- Diagonal matrix entries of `x* x` are squared norms of its columns. In coefficient
notation the diagonal at `s` is `ρ (α s⁻¹ (fourierCoeff 1 (x* x)))`. -/
theorem inner_fourierCoeff_one_star_mul_self (x : regularAlgebra α ρ Measure.count)
    (s : G) (v : H) :
    ⟪v, ρ (α s⁻¹ (fourierCoeff α ρ hρ 1 (star x * x))) v⟫_ℂ =
      (‖(x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
        Lp H 2 (Measure.count : Measure G))
        (indicatorConstLp 2 (measurableSet_singleton s) (by simp) v)‖ ^ 2 : ℂ) := by
  have h := inner_single_fourierCoeff α ρ hρ (star x * x) s s v v
  simp only [mul_inv_cancel] at h
  rw [← h]
  simp only [MulMemClass.coe_mul, StarMemClass.coe_star,
    ContinuousLinearMap.star_eq_adjoint, mul_apply_eq_comp,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- The identity coefficient detects vanishing of `x* x`. This is faithfulness in the
usual C⋆-algebraic sense and does not require a chosen order on the coefficient algebra. -/
theorem fourierCoeff_one_star_mul_self_eq_zero_iff
    (x : regularAlgebra α ρ Measure.count) :
    fourierCoeff α ρ hρ 1 (star x * x) = 0 ↔ x = 0 := by
  refine ⟨fun hx => ?_, ?_⟩
  · have hsingle (s : G) (v : H) :
        (x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
          Lp H 2 (Measure.count : Measure G))
          (indicatorConstLp 2 (measurableSet_singleton s) (by simp) v) = 0 := by
      have h := inner_fourierCoeff_one_star_mul_self α ρ hρ x s v
      rw [hx, map_zero, map_zero, zero_apply, inner_zero_right] at h
      exact norm_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp (by exact_mod_cast h.symm))
    apply eq_zero_of_fourierCoeff_eq_zero α ρ hρ
    intro g
    apply hρ
    apply ContinuousLinearMap.ext
    intro v
    apply ext_inner_left ℂ
    intro w
    have h := inner_single_fourierCoeff α ρ hρ x 1 g⁻¹ w v
    simpa only [inv_one, one_apply, one_mul, inv_inv, hsingle, inner_zero_right,
      map_zero, zero_apply] using h.symm
  · rintro rfl
    rw [mul_zero, map_zero]

section Order

variable [PartialOrder A] [StarOrderedRing A]

/-- The identity Fourier coefficient is positive, including for nonunital coefficients
and a possibly degenerate faithful inducing representation. -/
theorem fourierCoeff_one_nonneg (x : regularAlgebra α ρ Measure.count) (hx : 0 ≤ x) :
    0 ≤ fourierCoeff α ρ hρ 1 x := by
  have hsaX : IsSelfAdjoint x :=
    (ContinuousLinearMap.nonneg_iff_isPositive.mp hx).isSelfAdjoint.of_map
      (NonUnitalStarSubalgebraClass.subtype (regularAlgebra α ρ Measure.count))
      Subtype.val_injective
  have hsa : IsSelfAdjoint (fourierCoeff α ρ hρ 1 x) := by
    have h := fourierCoeff_star α ρ hρ 1 x
    simpa only [IsSelfAdjoint, inv_one, one_apply, hsaX.star_eq] using h.symm
  have hpos : (ρ (fourierCoeff α ρ hρ 1 x)).IsPositive := by
    refine ⟨(hsa.map ρ).isSymmetric, fun v => ?_⟩
    have hx' : 0 ≤ (x : Lp H 2 (Measure.count : Measure G) →L[ℂ]
        Lp H 2 (Measure.count : Measure G)) := hx
    rw [ContinuousLinearMap.reApplyInnerSelf_apply, inner_re_symm]
    have h := (ContinuousLinearMap.nonneg_iff_isPositive.mp hx').re_inner_nonneg_right
      (indicatorConstLp 2 (measurableSet_singleton (1 : G)) (by simp) v)
    simpa only [inner_single_fourierCoeff α ρ hρ, one_mul, inv_one, one_apply] using h
  exact (NonUnitalStarAlgHom.map_le_map_iff ρ hρ).mp
    (by simpa only [map_zero] using ContinuousLinearMap.nonneg_iff_isPositive.mpr hpos)

end Order

end TauCeti.CStarAction.RegularCrossedProduct
