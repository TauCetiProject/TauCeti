/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PointSpectrum
public import TauCeti.Analysis.InnerProductSpace.Positive.FunctionalCalculus
import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison

/-!
# Smooth positive and negative spectral projections

For an invertible self-adjoint operator `A` on a finite-dimensional real inner product space,
the orthogonal projections onto its negative and positive spectral subspaces are
`(1 - A * (A * A) ^ (-(1 / 2))) / 2` and
`(1 + A * (A * A) ^ (-(1 / 2))) / 2`, respectively.
Consequently these native spectral projections depend smoothly, even real analytically, on
`A` as long as it remains self-adjoint and invertible. No smoothly varying eigenbasis is needed.

These formulas supply smooth local projections for splitting a nondegenerate symmetric form
into its positive and negative subbundles. They concern the existing
`Module.End.pointSpectralSubspace` and `Submodule.starProjection`, not new choices of subspaces
or projections. The invertibility hypothesis excludes eigenvalues crossing zero; dimension zero
is allowed.

## References

* R. Bhatia, *Matrix Analysis*, Springer, 1997, Chapter V (matrix functions).
* R. Bott, *Nondegenerate critical manifolds*, Annals of Mathematics 60 (1954), 248–261.
-/

public section

noncomputable section

open Set
open scoped ContDiff

namespace ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The negative spectral projection of an invertible self-adjoint operator, expressed using
its inverse absolute value. This formula requires no choice of eigenbasis. -/
theorem starProjection_pointSpectralSubspace_Iio_zero_eq (A : E →L[ℝ] E) (hA : IsSelfAdjoint A)
    (hunit : IsUnit A) :
    (Module.End.pointSpectralSubspace A.toLinearMap (Iio 0)).starProjection =
      (1 / 2 : ℝ) • (1 - A * (A * A) ^ (-(1 / 2) : ℝ)) := by
  have hs := isSelfAdjoint_iff_isSymmetric.mp hA
  apply coe_injective
  rw [hs.coe_starProjection_pointSpectralSubspace]
  symm
  apply (hs.eq_cfc_iff _).mpr
  intro μ v hv
  simp only [coe_coe, RCLike.ofReal_real_eq_id, id_eq] at hv
  by_cases hv0 : v = 0
  · simp [hv0]
  have hμ : μ ≠ 0 := by
    intro hμ
    apply hv0
    exact (isUnit_iff_bijective.mp hunit).injective (by simpa [hμ] using hv)
  -- The inverse square root of `A²` acts by `|μ|⁻¹` on a `μ`-eigenvector.
  have hpos : 0 ≤ A * A := by simpa only [hA.star_eq] using star_mul_self_nonneg A
  have heig : (A * A) v = μ ^ 2 • v := by
    simp only [mul_apply_eq_comp, hv, map_smul, smul_smul, pow_two]
  have hpow : ((A * A) ^ (-(1 / 2) : ℝ)) v = |μ|⁻¹ • v := by
    rw [CFC.rpow_eq_cfc_real hpos,
      cfc_apply_of_apply_eq_smul (fun r : ℝ ↦ r ^ (-(1 / 2) : ℝ)) heig
        (nonneg_iff_isPositive.mp hpos).isSelfAdjoint]
    simp only [RCLike.ofReal_real_eq_id, id_eq]
    congr 1
    exact (Real.rpow_neg (sq_nonneg μ) (1 / 2)).trans
      (congrArg Inv.inv ((Real.sqrt_eq_rpow (μ ^ 2)).symm.trans (Real.sqrt_sq_eq_abs μ)))
  simp only [toLinearMap_smul, toLinearMap_sub, toLinearMap_one, LinearMap.smul_apply,
    LinearMap.sub_apply, one_apply_eq_self, coe_coe, mul_apply_eq_comp, hpow, map_smul, hv,
    smul_smul, RCLike.ofReal_real_eq_id, id_eq]
  by_cases hneg : μ < 0
  · rw [indicator_of_mem hneg, Pi.one_apply, abs_of_neg hneg]
    have hratio : (-μ)⁻¹ * μ = -1 := by simp [hμ]
    rw [hratio]
    module
  · rw [indicator_of_notMem hneg, abs_of_pos (lt_of_le_of_ne (le_of_not_gt hneg) hμ.symm),
      inv_mul_cancel₀ hμ]
    module

/-- The positive spectral projection of an invertible self-adjoint operator, expressed using
its inverse absolute value. -/
theorem starProjection_pointSpectralSubspace_Ioi_zero_eq (A : E →L[ℝ] E) (hA : IsSelfAdjoint A)
    (hunit : IsUnit A) :
    (Module.End.pointSpectralSubspace A.toLinearMap (Ioi 0)).starProjection =
      (1 / 2 : ℝ) • (1 + A * (A * A) ^ (-(1 / 2) : ℝ)) := by
  simpa only [toLinearMap_neg, Module.End.pointSpectralSubspace_neg, neg_Iio, neg_zero,
    neg_mul_neg, neg_mul, mul_neg, neg_neg, sub_neg_eq_add] using
    starProjection_pointSpectralSubspace_Iio_zero_eq (-A) hA.neg hunit.neg

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  {n : ℕ∞ω} {A : P → E →L[ℝ] E} {s : Set P}

/-- The negative spectral projections of a smooth family of invertible self-adjoint operators
form a smooth family, including at real analytic regularity. -/
theorem _root_.ContDiffOn.starProjection_pointSpectralSubspace_Iio_zero (hA : ContDiffOn ℝ n A s)
    (hself : ∀ x ∈ s, IsSelfAdjoint (A x)) (hunit : ∀ x ∈ s, IsUnit (A x)) :
    ContDiffOn ℝ n
      (fun x ↦ (Module.End.pointSpectralSubspace (A x).toLinearMap (Iio 0)).starProjection) s := by
  have hpos (x) (hx : x ∈ s) : IsStrictlyPositive (A x * A x) :=
    ((hunit x hx).mul (hunit x hx)).isStrictlyPositive (by
      simpa only [(hself x hx).star_eq] using star_mul_self_nonneg (A x))
  have hpow := (contDiffOn_rpow (E := E) (n := n) (-(1 / 2))).comp (hA.mul hA) hpos
  exact (((contDiffOn_const (c := (1 : E →L[ℝ] E))).sub (hA.mul hpow)).const_smul
    (1 / 2 : ℝ)).congr
    fun x hx ↦ starProjection_pointSpectralSubspace_Iio_zero_eq (A x) (hself x hx) (hunit x hx)

/-- The positive spectral projections of a smooth family of invertible self-adjoint operators
form a smooth family, including at real analytic regularity. -/
theorem _root_.ContDiffOn.starProjection_pointSpectralSubspace_Ioi_zero (hA : ContDiffOn ℝ n A s)
    (hself : ∀ x ∈ s, IsSelfAdjoint (A x)) (hunit : ∀ x ∈ s, IsUnit (A x)) :
    ContDiffOn ℝ n
      (fun x ↦ (Module.End.pointSpectralSubspace (A x).toLinearMap (Ioi 0)).starProjection) s := by
  simpa only [Pi.neg_apply, toLinearMap_neg, Module.End.pointSpectralSubspace_neg,
    neg_Iio, neg_zero] using hA.neg.starProjection_pointSpectralSubspace_Iio_zero
      (fun x hx ↦ (hself x hx).neg) (fun x hx ↦ (hunit x hx).neg)

end ContinuousLinearMap
