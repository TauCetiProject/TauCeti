/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Interpolation.RealMethod
public import TauCeti.MeasureTheory.Function.LpSeminorm.CompareExp

/-!
# Secondary-exponent embeddings for the real method

The real interpolation spaces increase with their secondary exponent:
`(X₀, X₁)_{θ,p} ⊆ (X₀, X₁)_{θ,q}` when `1 ≤ p ≤ q`, including `q = ∞`.
Unlike the usual finite-measure comparison, this holds for the infinite measure `dt / t`.
The decisive estimate bounds every value of `t ^ (-θ) K(t,u)` by the interpolation norm.

`KMethodSpace.inclusion` is the continuous linear inclusion, with a bound independent of the
couple and the target exponent. It preserves the underlying element of the sum space.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Springer, 1976,
  §3.4, Theorem 3.4.1.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti.CompatibleCouple

variable {𝕜 X₀ X₁ V : Type*} [NormedField 𝕜]
  [NormedAddCommGroup X₀] [NormedSpace 𝕜 X₀] [NormedAddCommGroup X₁] [NormedSpace 𝕜 X₁]
  [AddCommGroup V] [Module 𝕜 V] [TopologicalSpace V] [ContinuousAdd V]
  {C : CompatibleCouple 𝕜 X₀ X₁ V} {θ t : ℝ} {p q : ℝ≥0∞}

/-- Every weighted value of the `K`-functional is bounded by its real-method norm divided by
`c_{θ,p}`. This is the pointwise estimate behind secondary-exponent embeddings. -/
theorem kMethodConst_mul_ofReal_rpow_kFunctional_le (ht : 0 < t) (u : C.SumSpace) :
    kMethodConst θ p * ENNReal.ofReal (t ^ (-θ) * C.kFunctional t u) ≤
      C.kMethodENorm θ p u := by
  have hmp : MeasurePreserving (t * ·) multHaar multHaar :=
    ⟨measurable_const_mul t, map_multHaar_mul_left ht⟩
  have hmeas : AEStronglyMeasurable
      ((t ^ (-θ) * C.kFunctional t u) • fun s : ℝ => s ^ (-θ) * min 1 s) multHaar :=
    (ContinuousOn.aestronglyMeasurable_multHaar <|
      (continuousOn_id.rpow_const fun s hs => Or.inl (ne_of_gt hs)).mul
        (continuous_const.min continuous_id).continuousOn).const_smul _
  calc
    kMethodConst θ p * ENNReal.ofReal (t ^ (-θ) * C.kFunctional t u) =
        eLpNorm ((t ^ (-θ) * C.kFunctional t u) • fun s : ℝ => s ^ (-θ) * min 1 s)
          p multHaar := by
      rw [eLpNorm_const_smul, Real.enorm_of_nonneg
        (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le)),
        mul_comm, kMethodConst_def]
    _ ≤ eLpNorm ((fun s => s ^ (-θ) * C.kFunctional s u) ∘ (t * ·)) p multHaar := by
      refine eLpNorm_mono_ae_real hmeas ?_
      filter_upwards [ae_pos_multHaar] with s hs
      rw [Pi.smul_apply, smul_eq_mul, Real.norm_of_nonneg
        (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))
          (mul_nonneg (Real.rpow_nonneg hs.le _) (le_min zero_le_one hs.le))),
        Function.comp_apply, Real.mul_rpow ht.le hs.le]
      have h := min_mul_kFunctional_le ht (mul_pos ht hs).le u
      rw [mul_div_cancel_left₀ s ht.ne'] at h
      nlinarith [mul_le_mul_of_nonneg_left h
        (mul_nonneg (Real.rpow_nonneg ht.le (-θ)) (Real.rpow_nonneg hs.le (-θ)))]
    _ = C.kMethodENorm θ p u := by
      rw [kMethodENorm_def]
      exact eLpNorm_comp_measurePreserving
        (aestronglyMeasurable_rpow_neg_mul_kFunctional θ u) hmp

namespace KMethodSpace

variable [T1Space V] [Fact (1 ≤ p)]

/-- The weighted `K`-functional of an interpolation-space element is bounded everywhere on
`(0,∞)`, not merely almost everywhere. -/
theorem rpow_mul_kFunctional_le_norm (u : C.KMethodSpace θ p) (ht : 0 < t) :
    t ^ (-θ) * C.kFunctional t (toSumₗ u) ≤ (kMethodConst θ p).toReal⁻¹ * ‖u‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le (Fact.out : 1 ≤ p)).ne'
  have h := kMethodConst_mul_ofReal_rpow_kFunctional_le ht (toSumₗ u) (θ := θ) (p := p)
  rw [← ofReal_norm] at h
  by_cases hc : kMethodConst θ p = ∞
  · have hz : ENNReal.ofReal (t ^ (-θ) * C.kFunctional t (toSumₗ u)) = 0 := by
      by_contra hz
      rw [hc, ENNReal.top_mul hz] at h
      exact ENNReal.ofReal_ne_top (top_le_iff.1 h)
    exact (ENNReal.ofReal_eq_zero.1 hz).trans (by positivity)
  · rw [le_inv_mul_iff₀ (ENNReal.toReal_pos (kMethodConst_ne_zero θ hp) hc)]
    have := ENNReal.toReal_le_of_le_ofReal (norm_nonneg u) h
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))] using this

/-- Increasing the secondary exponent multiplies the real-method norm by at most
`max 1 c_{θ,p}⁻¹`. The constant is independent of the target exponent and the couple. -/
theorem kMethodENorm_toSum_le (hpq : p ≤ q) (u : C.KMethodSpace θ p) :
    C.kMethodENorm θ q (toSumₗ u) ≤
      ENNReal.ofReal (max 1 (kMethodConst θ p).toReal⁻¹ * ‖u‖) := by
  by_cases hu : u = 0
  · simp [hu]
  have hM : 0 < max 1 (kMethodConst θ p).toReal⁻¹ * ‖u‖ :=
    mul_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (norm_pos_iff.2 hu)
  rw [kMethodENorm_def]
  apply MeasureTheory.eLpNorm_le_of_exponent_le
    (aestronglyMeasurable_rpow_neg_mul_kFunctional θ _) (by
      exact zero_lt_one.trans_le (Fact.out : 1 ≤ p)) hpq hM
  · rw [← kMethodENorm_def, ← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    exact le_mul_of_one_le_left (norm_nonneg u) (le_max_left _ _)
  · filter_upwards [ae_pos_multHaar] with t ht
    rw [Real.norm_of_nonneg
      (mul_nonneg (Real.rpow_nonneg ht.le _) (kFunctional_nonneg ht.le))]
    exact (rpow_mul_kFunctional_le_norm u ht).trans (by
      gcongr
      exact le_max_right _ _)

/-- The continuous inclusion of real interpolation spaces when the secondary exponent
increases. Its underlying map on the sum space is the identity. -/
def inclusion [Fact (1 ≤ q)] (hpq : p ≤ q) :
    C.KMethodSpace θ p →L[𝕜] C.KMethodSpace θ q :=
  LinearMap.mkContinuous
    { toFun u := mk (toSumₗ u) (mem_kMethod_iff.2
        ((kMethodENorm_toSum_le hpq u).trans_lt ENNReal.ofReal_lt_top))
      map_add' u v := by ext; simp
      map_smul' c u := by ext; simp }
    (max 1 (kMethodConst θ p).toReal⁻¹) fun u => by
      simpa only [LinearMap.coe_mk, AddHom.coe_mk, norm_mk] using
        ENNReal.toReal_le_of_le_ofReal (by positivity) (kMethodENorm_toSum_le hpq u)

@[simp]
theorem toSumₗ_inclusion [Fact (1 ≤ q)] (hpq : p ≤ q) (u : C.KMethodSpace θ p) :
    toSumₗ (inclusion hpq u) = toSumₗ u := by
  simp [inclusion]

/-- The inclusion does not identify distinct elements. -/
theorem inclusion_injective [Fact (1 ≤ q)] (hpq : p ≤ q) :
    Function.Injective (inclusion (C := C) (θ := θ) hpq) := by
  intro u v h
  apply toSumₗ_injective
  simpa using congrArg toSumₗ h

/-- The secondary-exponent inclusion has the couple-independent norm bound
`max 1 c_{θ,p}⁻¹`. -/
theorem norm_inclusion_le [Fact (1 ≤ q)] (hpq : p ≤ q) (u : C.KMethodSpace θ p) :
    ‖inclusion hpq u‖ ≤ max 1 (kMethodConst θ p).toReal⁻¹ * ‖u‖ := by
  rw [norm_def, toSumₗ_inclusion]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) (kMethodENorm_toSum_le hpq u)

@[simp]
theorem inclusion_refl : inclusion (C := C) (θ := θ) (le_refl p) =
    ContinuousLinearMap.id 𝕜 _ := by
  ext u
  simp

/-- Secondary-exponent inclusions compose without changing the underlying element. -/
@[simp]
theorem inclusion_comp {r : ℝ≥0∞} [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    (hpq : p ≤ q) (hqr : q ≤ r) :
    (inclusion (C := C) (θ := θ) hqr).comp (inclusion hpq) = inclusion (hpq.trans hqr) := by
  ext u
  simp

end KMethodSpace

end TauCeti.CompatibleCouple
