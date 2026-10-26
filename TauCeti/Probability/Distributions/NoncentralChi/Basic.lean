/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import TauCeti.Probability.Distributions.Chi.Basic
public import TauCeti.Probability.Distributions.NoncentralChiSquared.Cdf
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Noncentral chi distributions

The noncentral chi law `noncentralChiMeasure k δ s` is the law of `s * √X` for a noncentral
chi-squared variable `X` with `k` degrees of freedom and noncentrality `δ ^ 2`. It describes
the Euclidean norm of a Gaussian vector in positive natural dimension `k` with covariance
`s ^ 2 • 1` whose mean has norm `s * δ`.
The parameters are a real degree, a nonnegative noncentrality `δ`, and a real scale. Nonnegative
degree and positive scale give probability measures; negative degree or nonpositive scale give
the zero measure. At zero noncentrality the law is the central chi law.

This file supplies the measure, its parameter measurability, the scaling and squaring identities,
almost-sure positivity, the atom at zero, and the cumulative distribution function. Everything is
transported from the noncentral chi-squared law along the scaled square root.

## References

* N. L. Johnson, S. Kotz, N. Balakrishnan, *Continuous Univariate Distributions*, vol. 2,
  second edition, Wiley, 1995, chapter 29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {k s c x : ℝ} {δ : ℝ≥0}

/-- The noncentral chi law of degree `k`, noncentrality `δ`, and scale `s`: the image of the
noncentral chi-squared law of noncentrality `δ ^ 2` by `s * √·` when `s > 0`, and zero
otherwise. -/
def noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s : ℝ) : Measure ℝ :=
  if 0 < s then (noncentralChiSquaredMeasure k (δ ^ 2)).map (fun x ↦ s * √x) else 0

/-- The defining square-root pushforward at positive scale. -/
theorem noncentralChiMeasure_of_scale_pos (hs : 0 < s) :
    noncentralChiMeasure k δ s =
      (noncentralChiSquaredMeasure k (δ ^ 2)).map (fun x ↦ s * √x) := by
  rw [noncentralChiMeasure, ite_eq_left hs]

/-- Nonpositive scale gives the zero measure. -/
@[simp]
theorem noncentralChiMeasure_of_scale_nonpos (hs : s ≤ 0) : noncentralChiMeasure k δ s = 0 := by
  rw [noncentralChiMeasure, ite_eq_right (not_lt.mpr hs)]

/-- Negative degrees give the zero measure at every noncentrality and scale. -/
@[simp]
theorem noncentralChiMeasure_of_neg (hk : k < 0) : noncentralChiMeasure k δ s = 0 := by
  simp [noncentralChiMeasure, noncentralChiSquaredMeasure_of_neg hk]

/-- Nonnegative degree and positive scale give a probability measure, including degree zero. -/
theorem isProbabilityMeasure_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s) :
    IsProbabilityMeasure (noncentralChiMeasure k δ s) := by
  rw [noncentralChiMeasure_of_scale_pos hs]
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk (δ ^ 2)
  infer_instance

/-- At zero noncentrality the noncentral chi law is the central chi law, for all parameters. -/
@[simp]
theorem noncentralChiMeasure_zero_noncentrality (k s : ℝ) :
    noncentralChiMeasure k 0 s = chiMeasure k s := by
  by_cases hs : 0 < s
  · simp [noncentralChiMeasure_of_scale_pos hs, chiMeasure_of_scale_pos hs]
  · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs),
      chiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- The noncentral chi family is jointly Giry measurable in degree, noncentrality, and scale,
including its invalid branches. -/
@[fun_prop]
theorem measurable_noncentralChiMeasure :
    Measurable fun p : ℝ × ℝ≥0 × ℝ ↦ noncentralChiMeasure p.1 p.2.1 p.2.2 := by
  have hfin (k : ℝ) (l : ℝ≥0) : IsFiniteMeasure (noncentralChiSquaredMeasure k l) := by
    rcases lt_or_ge k 0 with hk | hk
    · rw [noncentralChiSquaredMeasure_of_neg hk l]
      infer_instance
    · have := isProbabilityMeasure_noncentralChiSquaredMeasure hk l
      infer_instance
  -- The pushforward branch jointly varies a finite measure and the scaled square root.
  let μ : ℝ × ℝ≥0 × ℝ → FiniteMeasure ℝ × ℝ := fun p ↦
    (⟨noncentralChiSquaredMeasure p.1 (p.2.1 ^ 2), hfin _ _⟩, p.2.2)
  have hμ : Measurable μ :=
    (measurable_noncentralChiSquaredMeasure.comp (measurable_fst.prodMk
      ((measurable_fst.comp measurable_snd).pow_const 2))).subtype_mk.prodMk
        (measurable_snd.comp measurable_snd)
  have hmap := (TauCeti.MeasureTheory.measurable_map_finiteMeasure_of_measurable_uncurry
    (f := fun (s x : ℝ) ↦ s * √x) (by fun_prop)).comp hμ
  have h : (fun p : ℝ × ℝ≥0 × ℝ ↦ noncentralChiMeasure p.1 p.2.1 p.2.2) = fun p ↦
      if 0 < p.2.2 then ((μ p).1 : Measure ℝ).map (fun x ↦ (μ p).2 * √x) else 0 := by
    funext p
    by_cases hs : 0 < p.2.2
    · simp [μ, hs, noncentralChiMeasure_of_scale_pos hs]
    · simp [hs, noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]
  rw [h]
  exact Measurable.ite (measurableSet_lt measurable_const (measurable_snd.comp measurable_snd))
    hmap measurable_const

/-- Positive scaling multiplies the noncentral chi scale in every parameter regime. -/
@[simp]
theorem noncentralChiMeasure_map_const_mul (hc : 0 < c) :
    (noncentralChiMeasure k δ s).map (fun x ↦ c * x) = noncentralChiMeasure k δ (c * s) := by
  by_cases hs : 0 < s
  swap
  · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs),
      noncentralChiMeasure_of_scale_nonpos (mul_nonpos_of_nonneg_of_nonpos hc.le (not_lt.mp hs))]
  rw [noncentralChiMeasure_of_scale_pos hs, noncentralChiMeasure_of_scale_pos (mul_pos hc hs),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  ext x
  exact (mul_assoc c s (√x)).symm

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℝ}

/-- Taking a scaled square root of a noncentral chi-squared variable gives the noncentral chi
law. -/
theorem hasLaw_noncentralChiMeasure_of_hasLaw_noncentralChiSquaredMeasure (hs : 0 < s)
    (hX : HasLaw X (noncentralChiSquaredMeasure k (δ ^ 2)) P) :
    HasLaw (fun ω ↦ s * √(X ω)) (noncentralChiMeasure k δ s) P := by
  rw [noncentralChiMeasure_of_scale_pos hs]
  exact (hasLaw_map (X := fun x : ℝ ↦ s * √x) (by fun_prop)).fun_comp hX

/-- Squaring a noncentral chi variable gives the squared scale times a noncentral chi-squared
variable of noncentrality `δ ^ 2`. -/
theorem noncentralChiMeasure_map_sq (hs : 0 < s) :
    (noncentralChiMeasure k δ s).map (fun x ↦ x ^ 2) =
      (noncentralChiSquaredMeasure k (δ ^ 2)).map (fun x ↦ s ^ 2 * x) := by
  rw [noncentralChiMeasure_of_scale_pos hs, Measure.map_map (by fun_prop) (by fun_prop)]
  apply Measure.map_congr
  filter_upwards [ae_nonneg_noncentralChiSquaredMeasure k (δ ^ 2)] with x hx
  simp [mul_pow, Real.sq_sqrt hx]

/-- A noncentral chi variable is nonnegative almost surely. -/
theorem ae_nonneg_noncentralChiMeasure (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    ∀ᵐ x ∂noncentralChiMeasure k δ s, 0 ≤ x := by
  by_cases hs : 0 < s
  · rw [noncentralChiMeasure_of_scale_pos hs]
    exact (ae_map_iff (by fun_prop) measurableSet_Ici).2
      (ae_of_all _ fun x ↦ mul_nonneg hs.le (sqrt_nonneg x))
  · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Positive degree makes a noncentral chi variable strictly positive almost surely. -/
theorem ae_pos_noncentralChiMeasure (hk : 0 < k) (δ : ℝ≥0) (s : ℝ) :
    ∀ᵐ x ∂noncentralChiMeasure k δ s, 0 < x := by
  by_cases hs : 0 < s
  · rw [noncentralChiMeasure_of_scale_pos hs]
    apply (ae_map_iff (by fun_prop) measurableSet_Ioi).2
    filter_upwards [ae_pos_noncentralChiSquaredMeasure hk (δ ^ 2)] with x hx
    exact mul_pos hs (sqrt_pos.2 hx)
  · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]

/-- Zero is the only possible atom, for every degree, noncentrality, and scale. -/
@[simp]
theorem noncentralChiMeasure_singleton_of_ne_zero (hx : x ≠ 0) (k : ℝ) (δ : ℝ≥0) (s : ℝ) :
    noncentralChiMeasure k δ s {x} = 0 := by
  by_cases hs : 0 < s
  swap
  · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]
  rw [noncentralChiMeasure_of_scale_pos hs, Measure.map_apply (by fun_prop)
    (measurableSet_singleton x)]
  refine measure_mono_null (fun y hy ↦ ?_)
    (noncentralChiSquaredMeasure_singleton_of_ne_zero (x := (x / s) ^ 2)
      (pow_ne_zero 2 (div_ne_zero hx hs.ne')) k (δ ^ 2))
  rw [mem_preimage, mem_singleton_iff] at hy
  -- A negative `y` has `√y = 0`, which would force `x = 0`.
  have hy0 : 0 ≤ y :=
    le_of_not_gt fun hneg ↦ hx (by rw [← hy, sqrt_eq_zero'.2 hneg.le, mul_zero])
  rw [mem_singleton_iff, ← hy, mul_div_cancel_left₀ _ hs.ne', sq_sqrt hy0]

/-- The scaled square root sends exactly the nonpositive half-line to zero, so the noncentral
chi atom at zero is the noncentral chi-squared atom at zero. -/
private theorem noncentralChiMeasure_singleton_zero (hs : 0 < s) :
    noncentralChiMeasure k δ s {0} = noncentralChiSquaredMeasure k (δ ^ 2) {0} := by
  have hpre : (fun y : ℝ ↦ s * √y) ⁻¹' {0} = Iic 0 := by
    ext y
    simp [hs.ne', sqrt_eq_zero']
  rw [noncentralChiMeasure_of_scale_pos hs,
    Measure.map_apply (by fun_prop) (measurableSet_singleton 0), hpre]
  apply measure_congr
  filter_upwards [ae_nonneg_noncentralChiSquaredMeasure k (δ ^ 2)] with y hy
  simp only [mem_Iic, mem_singleton_iff]
  exact propext ⟨fun h ↦ le_antisymm h hy, fun h ↦ h.le⟩

/-- The atom of the degree-zero law at positive scale has mass `exp (-δ ^ 2 / 2)`, including
mass one at zero noncentrality. -/
@[simp]
theorem noncentralChiMeasure_zero_degree_mass (δ : ℝ≥0) (hs : 0 < s) :
    noncentralChiMeasure 0 δ s {0} = ENNReal.ofReal (exp (-(δ : ℝ) ^ 2 / 2)) := by
  rw [noncentralChiMeasure_singleton_zero hs, noncentralChiSquaredMeasure_zero_degree_mass,
    NNReal.coe_pow]

/-- At positive degree the noncentral chi law has no atoms. -/
theorem nullSingletonClass_noncentralChiMeasure (hk : 0 < k) (δ : ℝ≥0) (s : ℝ) :
    NullSingletonClass (noncentralChiMeasure k δ s) := by
  constructor
  intro x
  by_cases hx : x = 0
  · by_cases hs : 0 < s
    · have := nullSingletonClass_noncentralChiSquaredMeasure hk (δ ^ 2)
      rw [hx, noncentralChiMeasure_singleton_zero hs, measure_singleton]
    · simp [noncentralChiMeasure_of_scale_nonpos (not_lt.mp hs)]
  · exact noncentralChiMeasure_singleton_of_ne_zero hx k δ s

/-- The noncentral chi cdf is the noncentral chi-squared cdf at the squared standardized
coordinate on the nonnegative half-line, and zero below it. -/
theorem cdf_noncentralChiMeasure_eq (hk : 0 ≤ k) (hs : 0 < s) (x : ℝ) :
    cdf (noncentralChiMeasure k δ s) x =
      if x < 0 then 0 else cdf (noncentralChiSquaredMeasure k (δ ^ 2)) ((x / s) ^ 2) := by
  have := isProbabilityMeasure_noncentralChiSquaredMeasure hk (δ ^ 2)
  rw [noncentralChiMeasure_of_scale_pos hs, Measure.cdf_map_const_mul_sqrt _ hs]

/-- At positive degree and nonnegative argument, the noncentral chi cdf is the Poisson-weighted
series of regularized incomplete Gamma functions at the squared standardized coordinate. -/
theorem cdf_noncentralChiMeasure_eq_tsum (hk : 0 < k) (hs : 0 < s) (hx : 0 ≤ x) :
    cdf (noncentralChiMeasure k δ s) x = ∑' n : ℕ,
      (exp (-(δ : ℝ) ^ 2 / 2) * ((δ : ℝ) ^ 2 / 2) ^ n / n.factorial) *
        regularizedGamma ((k + 2 * n) / 2) ((x / s) ^ 2 / 2) := by
  rw [cdf_noncentralChiMeasure_eq hk.le hs, ite_eq_right (not_lt.mpr hx),
    cdf_noncentralChiSquaredMeasure_eq hk, NNReal.coe_pow]

/-- The cdf at zero is zero at positive degree and is the atom `exp (-δ ^ 2 / 2)` at degree
zero. -/
@[simp]
theorem cdf_noncentralChiMeasure_zero (hk : 0 ≤ k) (hs : 0 < s) :
    cdf (noncentralChiMeasure k δ s) 0 = if k = 0 then exp (-(δ : ℝ) ^ 2 / 2) else 0 := by
  rw [cdf_noncentralChiMeasure_eq hk hs, ite_eq_right (lt_irrefl 0), zero_div,
    zero_pow two_ne_zero, cdf_noncentralChiSquaredMeasure_zero hk, NNReal.coe_pow]

/-- Away from the double-zero Dirac boundary, the noncentral chi cdf is strictly increasing on
the nonnegative half-line. -/
theorem strictMonoOn_cdf_noncentralChiMeasure (hk : 0 ≤ k) (hs : 0 < s)
    (h : k ≠ 0 ∨ δ ≠ 0) :
    StrictMonoOn (cdf (noncentralChiMeasure k δ s)) (Ici 0) := by
  have hmono := strictMonoOn_cdf_noncentralChiSquaredMeasure hk
    (l := δ ^ 2) (h.imp_right (pow_ne_zero 2))
  intro a ha b hb hab
  rw [cdf_noncentralChiMeasure_eq hk hs, cdf_noncentralChiMeasure_eq hk hs,
    ite_eq_right (not_lt.mpr ha), ite_eq_right (not_lt.mpr hb)]
  have ha' : 0 ≤ a / s := div_nonneg ha hs.le
  exact hmono (sq_nonneg _) (sq_nonneg _)
    (pow_lt_pow_left₀ (div_lt_div_of_pos_right hab hs) ha' two_ne_zero)

end TauCeti.Probability
