/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
public import TauCeti.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Projection

/-!
# Quantitative perturbation stability via the continuous functional calculus

Using an isometric real continuous functional calculus, elements satisfying a polynomial
`⋆`-relation up to a small norm defect can be perturbed to exact solutions at linear cost:

* `IsSelfAdjoint.exists_isStarProjection_and_norm_sub_le`: for self-adjoint `b` with
  `‖b * b - b‖ < 1 / 9`, there is a star projection `p` with `‖p - b‖ ≤ 2 * ‖b * b - b‖`.
* `IsSelfAdjoint.isUnit_of_norm_sub_one_lt_one` and
  `IsSelfAdjoint.exists_isSelfAdjoint_isUnit_mul_mul_eq_one_and_norm_sub_le`: for self-adjoint `h`,
  `‖h - 1‖ < 1` gives `IsUnit h`, and `‖h - 1‖ < 1 / 2` gives an invertible self-adjoint `k` with
  `k * h * k = 1` and `‖k - 1‖ ≤ ‖h - 1‖`.
* `TauCeti.exists_star_mul_self_eq_one_and_norm_sub_le` and
  `TauCeti.exists_unitary_and_norm_sub_le`: quantitative perturbation of approximate isometries and
  unitaries (`‖v - a‖ ≤ ‖a‖ * ‖star a * a - 1‖`).

## References

* M. Rørdam, F. Larsen, N. Laustsen, *An Introduction to K-Theory for C⋆-Algebras*, Lemma 2.2.4
  and Proposition 2.2.5.
* B. Blackadar, *Operator Algebras*, II.8.3.
-/

public section

section Projection

/-- Continuous piecewise-linear cutoff equal to `0` on `(-∞, 1/3]` and `1` on `[2/3, ∞)`. -/
private def projCut (t : ℝ) : ℝ := max 0 (min 1 (3 * t - 1))

private theorem continuous_projCut : Continuous projCut := by unfold projCut; fun_prop

private theorem projCut_zero : projCut 0 = 0 := by simp [projCut]

private theorem projCut_eq_zero_of_le {t : ℝ} (ht : |t * t - t| < 1 / 9) (hhalf : t ≤ 1 / 2) :
    projCut t = 0 := by
  have hle : 3 * t - 1 ≤ 0 := by nlinarith [abs_lt.mp ht]
  simp [projCut, min_eq_right (hle.trans zero_le_one), max_eq_left hle]

private theorem projCut_eq_one_of_gt {t : ℝ} (ht : |t * t - t| < 1 / 9) (hhalf : ¬ t ≤ 1 / 2) :
    projCut t = 1 := by
  have hge : 1 ≤ 3 * t - 1 := by nlinarith [abs_lt.mp ht]
  simp [projCut, min_eq_left hge]

private theorem isStarProjection_projCut_of_abs_lt {t : ℝ} (ht : |t * t - t| < 1 / 9) :
    IsStarProjection (projCut t) := by
  by_cases hhalf : t ≤ 1 / 2
  · simp [projCut_eq_zero_of_le ht hhalf]
  · simp [projCut_eq_one_of_gt ht hhalf]

private theorem abs_projCut_sub_le_of_abs_lt {t : ℝ} (ht : |t * t - t| < 1 / 9) :
    |projCut t - t| ≤ 2 * |t * t - t| := by
  have hht := abs_lt.mp ht
  by_cases hhalf : t ≤ 1 / 2
  · rw [projCut_eq_zero_of_le ht hhalf, zero_sub, abs_neg, abs_le]
    constructor <;> cases le_or_gt 0 t <;>
      nlinarith [le_abs_self (t * t - t), neg_le_abs (t * t - t)]
  · rw [projCut_eq_one_of_gt ht hhalf, abs_le]
    constructor <;> cases le_or_gt 1 t <;>
      nlinarith [le_abs_self (t * t - t), neg_le_abs (t * t - t)]

variable {A : Type*} [NonUnitalNormedRing A] [StarRing A] [NormedSpace ℝ A]
  [IsScalarTower ℝ A A] [SMulCommClass ℝ A A]
  [NonUnitalIsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- **Quantitative stability of star projections.** If `b` is self-adjoint and
`‖b * b - b‖ < 1 / 9`, then there exists a star projection `p : A` with
`‖p - b‖ ≤ 2 * ‖b * b - b‖`. -/
theorem IsSelfAdjoint.exists_isStarProjection_and_norm_sub_le {b : A} (hb : IsSelfAdjoint b)
    (h : ‖b * b - b‖ < 1 / 9) :
    ∃ p : A, IsStarProjection p ∧ ‖p - b‖ ≤ 2 * ‖b * b - b‖ := by
  have hpoly : cfcₙ (fun s : ℝ ↦ s * s - s) b = b * b - b := by
    rw [cfcₙ_sub .., cfcₙ_mul .., cfcₙ_id' ℝ b]
  have hspec {t : ℝ} (ht : t ∈ quasispectrum ℝ b) : |t * t - t| ≤ ‖b * b - b‖ := by
    simpa [Real.norm_eq_abs, hpoly] using norm_apply_le_norm_cfcₙ (fun s : ℝ ↦ s * s - s) b ht
  refine ⟨cfcₙ projCut b,
    TauCeti.isStarProjection_cfcₙ fun t ht ↦
      isStarProjection_projCut_of_abs_lt ((hspec ht).trans_lt h), ?_⟩
  have hsub : cfcₙ projCut b - b = cfcₙ (fun s : ℝ ↦ projCut s - s) b := by
    conv_lhs => rhs; rw [← cfcₙ_id' ℝ b]
    exact (cfcₙ_sub projCut (fun s : ℝ ↦ s) b continuous_projCut.continuousOn projCut_zero).symm
  rw [hsub]
  exact norm_cfcₙ_le fun t ht ↦ by
    simpa [Real.norm_eq_abs] using
      (abs_projCut_sub_le_of_abs_lt ((hspec ht).trans_lt h)).trans
        (mul_le_mul_of_nonneg_left (hspec ht) zero_le_two)

end Projection

section Polar

/-- Continuous truncated inverse square root `t ↦ (√(max t (1/2)))⁻¹` on `ℝ`. -/
private noncomputable def invSqrtCut (t : ℝ) : ℝ := (√(max t (1 / 2)))⁻¹

private theorem sqrt_max_ne_zero (t : ℝ) : √(max t (1 / 2)) ≠ 0 :=
  (Real.sqrt_pos.mpr (lt_of_lt_of_le (by positivity) (le_max_right t (1 / 2)))).ne'

private theorem invSqrtCut_ne_zero (t : ℝ) : invSqrtCut t ≠ 0 := inv_ne_zero (sqrt_max_ne_zero t)

private theorem continuous_invSqrtCut : Continuous invSqrtCut :=
  Continuous.inv₀ (Real.continuous_sqrt.comp (continuous_id.max continuous_const)) sqrt_max_ne_zero

private theorem invSqrtCut_mul_mul_of_abs_lt {t : ℝ} (ht : |t - 1| < 1 / 2) :
    invSqrtCut t * t * invSqrtCut t = 1 := by
  have ht_gt : 1 / 2 < t := by linarith [(abs_lt.mp ht).left]
  have ht_pos : 0 < t := by linarith
  have hs_pos : 0 < √t := Real.sqrt_pos.mpr ht_pos
  rw [invSqrtCut, max_eq_left ht_gt.le]
  calc (√t)⁻¹ * t * (√t)⁻¹ = (√t)⁻¹ * (√t * √t) * (√t)⁻¹ := by rw [Real.mul_self_sqrt ht_pos.le]
    _ = ((√t)⁻¹ * √t) * (√t * (√t)⁻¹) := by ring
    _ = 1 := by rw [inv_mul_cancel₀ hs_pos.ne', mul_inv_cancel₀ hs_pos.ne', one_mul]

private theorem abs_invSqrtCut_sub_one_le_of_abs_lt {t : ℝ} (ht : |t - 1| < 1 / 2) :
    |invSqrtCut t - 1| ≤ |t - 1| := by
  have ht_gt : 1 / 2 < t := by linarith [(abs_lt.mp ht).left]
  have ht_pos : 0 < t := by linarith
  set s := √t
  have hs_pos : 0 < s := Real.sqrt_pos.mpr ht_pos
  have hs_sq : s * s = t := Real.mul_self_sqrt ht_pos.le
  have hden : 1 ≤ s * (1 + s) := by nlinarith
  have hid : (s⁻¹ - 1) * (s * (1 + s)) = 1 - t := by
    calc (s⁻¹ - 1) * (s * (1 + s)) = (s⁻¹ * s) * (1 + s) - s * (1 + s) := by ring
      _ = 1 * (1 + s) - s - s * s := by rw [inv_mul_cancel₀ hs_pos.ne']; ring
      _ = 1 - t := by linarith [hs_sq]
  rw [invSqrtCut, max_eq_left ht_gt.le]
  calc |s⁻¹ - 1| = |s⁻¹ - 1| * 1 := (mul_one _).symm
    _ ≤ |s⁻¹ - 1| * (s * (1 + s)) := mul_le_mul_of_nonneg_left hden (abs_nonneg _)
    _ = |(s⁻¹ - 1) * (s * (1 + s))| := by
        rw [abs_mul, abs_of_pos (lt_of_lt_of_le zero_lt_one hden)]
    _ = |t - 1| := by rw [hid, abs_sub_comm]

variable {A : Type*} [NormedRing A] [StarRing A] [NormedAlgebra ℝ A]
  [IsometricContinuousFunctionalCalculus ℝ A IsSelfAdjoint]

/-- If `h` is self-adjoint in a normed `⋆`-algebra with an isometric real functional calculus and
`‖h - 1‖ < 1`, then `h` is invertible (without assuming completeness). -/
theorem IsSelfAdjoint.isUnit_of_norm_sub_one_lt_one {h : A} (hh : IsSelfAdjoint h)
    (hd : ‖h - 1‖ < 1) : IsUnit h := by
  refine spectrum.isUnit_of_zero_notMem ℝ fun h0 ↦ ?_
  have hpoly : cfc (fun s : ℝ ↦ s - 1) h = h - 1 := by
    rw [cfc_sub .., cfc_id' ℝ h, cfc_const_one ℝ h]
  have hle := norm_apply_le_norm_cfc (fun s : ℝ ↦ s - 1) h h0
  rw [hpoly, zero_sub, norm_neg, norm_one] at hle
  exact hd.not_ge hle

/-- **Quantitative inverse square root near `1`.** If `h` is self-adjoint and `‖h - 1‖ < 1 / 2`,
then there exists an invertible self-adjoint element `k : A` satisfying `k * h * k = 1` and
`‖k - 1‖ ≤ ‖h - 1‖`. -/
theorem IsSelfAdjoint.exists_isSelfAdjoint_isUnit_mul_mul_eq_one_and_norm_sub_le {h : A}
    (hh : IsSelfAdjoint h) (hd : ‖h - 1‖ < 1 / 2) :
    ∃ k : A, IsSelfAdjoint k ∧ IsUnit k ∧ k * h * k = 1 ∧ ‖k - 1‖ ≤ ‖h - 1‖ := by
  have hpoly : cfc (fun s : ℝ ↦ s - 1) h = h - 1 := by
    rw [cfc_sub .., cfc_id' ℝ h, cfc_const_one ℝ h]
  have hspec {t : ℝ} (ht : t ∈ spectrum ℝ h) : |t - 1| ≤ ‖h - 1‖ := by
    simpa [Real.norm_eq_abs, hpoly] using norm_apply_le_norm_cfc (fun s : ℝ ↦ s - 1) h ht
  have hcont : ContinuousOn invSqrtCut (spectrum ℝ h) := continuous_invSqrtCut.continuousOn
  set k : A := cfc invSqrtCut h
  have hk_eq : k * h * k = 1 := by
    calc cfc invSqrtCut h * h * cfc invSqrtCut h
        = cfc invSqrtCut h * cfc (fun s : ℝ ↦ s) h * cfc invSqrtCut h := by rw [cfc_id' ℝ h]
      _ = cfc (fun s : ℝ ↦ invSqrtCut s * s * invSqrtCut s) h := by
          rw [← cfc_mul invSqrtCut (fun s : ℝ ↦ s) h hcont,
            ← cfc_mul (fun s : ℝ ↦ invSqrtCut s * s) invSqrtCut h (by fun_prop) hcont]
      _ = cfc (fun _ : ℝ ↦ (1 : ℝ)) h :=
          cfc_congr fun t ht ↦ invSqrtCut_mul_mul_of_abs_lt ((hspec ht).trans_lt hd)
      _ = 1 := cfc_const_one ℝ h
  have hk_norm : ‖k - 1‖ ≤ ‖h - 1‖ := by
    have hsub : k - 1 = cfc (fun s : ℝ ↦ invSqrtCut s - 1) h := by
      rw [← cfc_const_one ℝ h, ← cfc_sub _ _ h hcont (by fun_prop)]
    rw [hsub]
    exact norm_cfc_le (norm_nonneg _) fun t ht ↦ by
      simpa [Real.norm_eq_abs] using
        (abs_invSqrtCut_sub_one_le_of_abs_lt ((hspec ht).trans_lt hd)).trans (hspec ht)
  exact ⟨k, IsSelfAdjoint.cfc, isUnit_cfc invSqrtCut h hcont hh fun t _ ↦ invSqrtCut_ne_zero t,
    hk_eq, hk_norm⟩

namespace TauCeti

/-- **Quantitative stability of isometries.** If `‖star a * a - 1‖ < 1 / 2`, then there exists
`v : A` with `star v * v = 1` and `‖v - a‖ ≤ ‖a‖ * ‖star a * a - 1‖`. -/
theorem exists_star_mul_self_eq_one_and_norm_sub_le {a : A}
    (ha : ‖star a * a - 1‖ < 1 / 2) :
    ∃ v : A, star v * v = 1 ∧ ‖v - a‖ ≤ ‖a‖ * ‖star a * a - 1‖ := by
  obtain ⟨k, hk_sa, -, hk_eq, hk_norm⟩ :=
    (IsSelfAdjoint.star_mul_self a).exists_isSelfAdjoint_isUnit_mul_mul_eq_one_and_norm_sub_le ha
  refine ⟨a * k, by rw [star_mul, hk_sa.star_eq]; simpa only [mul_assoc] using hk_eq, ?_⟩
  calc ‖a * k - a‖ = ‖a * (k - 1)‖ := by rw [mul_sub, mul_one]
    _ ≤ ‖a‖ * ‖k - 1‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖star a * a - 1‖ := mul_le_mul_of_nonneg_left hk_norm (norm_nonneg a)

/-- **Quantitative stability of unitaries.** In a normed `⋆`-algebra with an isometric real
functional calculus (such as any unital C⋆-algebra), if `‖star a * a - 1‖ < 1 / 2` and
`‖a * star a - 1‖ < 1`, then there exists `u : unitary A` with
`‖(u : A) - a‖ ≤ ‖a‖ * ‖star a * a - 1‖`. -/
theorem exists_unitary_and_norm_sub_le {a : A}
    (ha₁ : ‖star a * a - 1‖ < 1 / 2) (ha₂ : ‖a * star a - 1‖ < 1) :
    ∃ u : unitary A, ‖(u : A) - a‖ ≤ ‖a‖ * ‖star a * a - 1‖ := by
  obtain ⟨k, hk_sa, hk_unit, hk_eq, hk_norm⟩ :=
    (IsSelfAdjoint.star_mul_self a).exists_isSelfAdjoint_isUnit_mul_mul_eq_one_and_norm_sub_le ha₁
  obtain ⟨u₁, hu₁⟩ :=
    (IsSelfAdjoint.star_mul_self a).isUnit_of_norm_sub_one_lt_one (ha₁.trans (by norm_num))
  obtain ⟨u₂, hu₂⟩ := (IsSelfAdjoint.mul_star_self a).isUnit_of_norm_sub_one_lt_one ha₂
  have ha_unit : IsUnit a := isUnit_iff_exists_and_exists.mpr
    ⟨⟨star a * ↑u₂⁻¹, by rw [← mul_assoc, ← hu₂, Units.mul_inv]⟩,
     ⟨↑u₁⁻¹ * star a, by rw [mul_assoc, ← hu₁, Units.inv_mul]⟩⟩
  have hv_iso : star (a * k) * (a * k) = 1 := by
    rw [star_mul, hk_sa.star_eq]; simpa only [mul_assoc] using hk_eq
  refine ⟨⟨a * k, (ha_unit.mul hk_unit).mem_unitary_of_star_mul_self hv_iso⟩, ?_⟩
  calc ‖a * k - a‖ = ‖a * (k - 1)‖ := by rw [mul_sub, mul_one]
    _ ≤ ‖a‖ * ‖k - 1‖ := norm_mul_le _ _
    _ ≤ ‖a‖ * ‖star a * a - 1‖ := mul_le_mul_of_nonneg_left hk_norm (norm_nonneg a)

end TauCeti

end Polar
