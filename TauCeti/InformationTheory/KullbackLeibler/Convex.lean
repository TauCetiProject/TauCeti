/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Analysis.SpecialFunctions.Log.MulLog

/-!
# Convexity of relative entropy in its first measure

For a fixed finite reference measure `ρ`, relative entropy is convex in the measure being
compared to `ρ`. On its finite-value domain it is strictly convex: mixing two distinct
finite measures with positive weights gives strictly less than their weighted entropies.
This is the uniqueness mechanism for entropy minimization over convex sets of measures,
in particular sets with prescribed marginals.

The statements use Mathlib's finite-measure I-divergence `InformationTheory.klDiv`, including
its mass correction. Neither normalization nor a topology on the measurable carrier is needed.
Infinite values are retained in the convexity inequality; strictness requires both endpoint
values to be finite. Equality for an interior mixture holds exactly when the measures agree.

For absolutely continuous measures, relative entropy is the integral of
`InformationTheory.klFun` of the Radon–Nikodym density. Strict convexity of this integrand
on `[0, ∞)` forces those densities to agree almost everywhere in the equality case.

Strict convexity also holds quantitatively. The midpoint convexity defect of `klFun` at two
nonnegative reals bounds the square of their distance relative to their sum, and integrating
this bound shows that the convexity defect of relative entropy at the midpoint of two measures
controls the `L¹(ρ)` distance of their densities, that is, their total variation distance. This
is the estimate that makes a minimizing sequence of an entropy minimization problem over a
convex set of measures a Cauchy sequence.

## References

* Mathlib, `InformationTheory.klDiv_eq_lintegral_klFun_of_ac` and
  `InformationTheory.strictConvexOn_klFun`.
* I. Csiszár, *I-divergence geometry of probability distributions and minimization problems*,
  Ann. Probability 3 (1975), 146–158. The quantitative midpoint estimate plays the role of the
  parallelogram identity in the proof of his Theorem 2.1.
-/

public section

open MeasureTheory InformationTheory Set Real
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ ν ρ : Measure α} {a b : ℝ≥0}

section Densities

variable [SigmaFinite μ] [SigmaFinite ν] [SigmaFinite ρ]

/-- The entropy integrand of a mixture is the entropy integrand of the mixture of densities. -/
private theorem klFun_rnDeriv_smul_add_smul :
    (fun x ↦ klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) =ᵐ[ρ]
      fun x ↦ klFun (a * (μ.rnDeriv ρ x).toReal + b * (ν.rnDeriv ρ x).toReal) := by
  filter_upwards [Measure.rnDeriv_add' (a • μ) (b • ν) ρ,
    Measure.rnDeriv_smul_left' μ ρ a, Measure.rnDeriv_smul_left' ν ρ b,
    Measure.rnDeriv_lt_top μ ρ, Measure.rnDeriv_lt_top ν ρ] with x hadd hμ hν hμfin hνfin
  simp only [Pi.add_apply, Pi.smul_apply, ENNReal.smul_def, smul_eq_mul] at hadd hμ hν
  simp only [Measure.coe_nnreal_smul] at hadd hμ hν
  rw [hadd, hμ, hν, ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.coe_ne_top hμfin.ne)
    (ENNReal.mul_ne_top ENNReal.coe_ne_top hνfin.ne)]
  simp

/-- The pointwise convexity inequality for the entropy density of a mixture. -/
private theorem klFun_rnDeriv_smul_add_smul_le (hab : a + b = 1) :
    (fun x ↦ klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) ≤ᵐ[ρ]
      fun x ↦ a * klFun (μ.rnDeriv ρ x).toReal + b * klFun (ν.rnDeriv ρ x).toReal := by
  filter_upwards [klFun_rnDeriv_smul_add_smul (μ := μ) (ν := ν) (ρ := ρ) (a := a) (b := b)]
    with x hx
  rw [hx]
  exact convexOn_klFun.2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg a.coe_nonneg b.coe_nonneg
    (by exact_mod_cast hab)

end Densities

variable [IsFiniteMeasure μ] [IsFiniteMeasure ν] [IsFiniteMeasure ρ]

/-- Integrating the weighted entropy densities gives the weighted endpoint entropies. -/
private theorem lintegral_weighted_klFun_rnDeriv (hμac : μ ≪ ρ) (hνac : ν ≪ ρ) :
    (∫⁻ x, ENNReal.ofReal
      (a * klFun (μ.rnDeriv ρ x).toReal + b * klFun (ν.rnDeriv ρ x).toReal) ∂ρ) =
        a * klDiv μ ρ + b * klDiv ν ρ := by
  rw [klDiv_eq_lintegral_klFun_of_ac hμac, klDiv_eq_lintegral_klFun_of_ac hνac]
  simp_rw [ENNReal.ofReal_add
    (mul_nonneg a.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg))
    (mul_nonneg b.coe_nonneg (klFun_nonneg ENNReal.toReal_nonneg)),
    ENNReal.ofReal_mul a.coe_nonneg, ENNReal.ofReal_mul b.coe_nonneg,
    ENNReal.ofReal_coe_nnreal]
  rw [lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
    lintegral_const_mul _ (by fun_prop)]

/-- **Convexity of relative entropy.** For finite measures and nonnegative weights summing to
one, the entropy of their mixture against a fixed finite reference is at most the weighted
sum of their entropies. This includes infinite endpoint values and zero weights. -/
theorem klDiv_smul_add_smul_le (hab : a + b = 1) :
    klDiv (a • μ + b • ν) ρ ≤ a * klDiv μ ρ + b * klDiv ν ρ := by
  rcases eq_or_ne a 0 with rfl | ha
  · have hb : b = 1 := by simpa using hab
    simp [hb]
  rcases eq_or_ne b 0 with rfl | hb
  · have ha : a = 1 := by simpa using hab
    simp [ha]
  by_cases hμ : klDiv μ ρ = ∞
  · simp [hμ, ha]
  by_cases hν : klDiv ν ρ = ∞
  · simp [hν, hb]
  have hμac := (klDiv_ne_top_iff.1 hμ).1
  have hνac := (klDiv_ne_top_iff.1 hν).1
  rw [klDiv_eq_lintegral_klFun_of_ac ((hμac.smul_left a).add_left (hνac.smul_left b)),
    ← lintegral_weighted_klFun_rnDeriv hμac hνac]
  exact lintegral_mono_ae ((klFun_rnDeriv_smul_add_smul_le hab).mono fun _ hx ↦
    ENNReal.ofReal_le_ofReal hx)

/-- **Strict convexity of relative entropy on its finite-value domain.** Two distinct finite
measures with finite entropy against a finite reference have a strict convexity inequality
for every mixture with positive weights. The measures need not have equal mass. -/
theorem klDiv_smul_add_smul_lt (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hμ : klDiv μ ρ ≠ ∞) (hν : klDiv ν ρ ≠ ∞) (hne : μ ≠ ν) :
    klDiv (a • μ + b • ν) ρ < a * klDiv μ ρ + b * klDiv ν ρ := by
  have hμac := (klDiv_ne_top_iff.1 hμ).1
  have hνac := (klDiv_ne_top_iff.1 hν).1
  have hac := (hμac.smul_left a).add_left (hνac.smul_left b)
  have hle := klDiv_smul_add_smul_le (μ := μ) (ν := ν) (ρ := ρ) hab
  have hfin : (∫⁻ x, ENNReal.ofReal (klFun ((a • μ + b • ν).rnDeriv ρ x).toReal) ∂ρ) ≠ ∞ := by
    rw [← klDiv_eq_lintegral_klFun_of_ac hac]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩) hle
  refine lt_of_le_of_ne hle fun heq ↦ hne ?_
  rw [klDiv_eq_lintegral_klFun_of_ac hac, ← lintegral_weighted_klFun_rnDeriv hμac hνac] at heq
  have heqae := (lintegral_eq_iff_ae_eq_of_ae_le hfin (by fun_prop)
    ((klFun_rnDeriv_smul_add_smul_le hab).mono fun _ hx ↦ ENNReal.ofReal_le_ofReal hx)).1 heq
  have hdens : μ.rnDeriv ρ =ᵐ[ρ] ν.rnDeriv ρ := by
    filter_upwards [heqae, klFun_rnDeriv_smul_add_smul (μ := μ) (ν := ν) (ρ := ρ)
      (a := a) (b := b), Measure.rnDeriv_lt_top μ ρ, Measure.rnDeriv_lt_top ν ρ]
      with x hx hmixeq hμfin hνfin
    have hreal : (μ.rnDeriv ρ x).toReal = (ν.rnDeriv ρ x).toReal := by
      by_contra hdiff
      have hs := strictConvexOn_klFun.2 ENNReal.toReal_nonneg ENNReal.toReal_nonneg hdiff
        (NNReal.coe_pos.2 ha) (NNReal.coe_pos.2 hb) (by exact_mod_cast hab)
      simp only [smul_eq_mul] at hs
      rw [hmixeq] at hx
      exact ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg
        (klFun_nonneg (add_nonneg (mul_nonneg a.coe_nonneg ENNReal.toReal_nonneg)
          (mul_nonneg b.coe_nonneg ENNReal.toReal_nonneg)))).2 hs).ne hx
    exact (ENNReal.toReal_eq_toReal_iff' hμfin.ne hνfin.ne).1 hreal
  rw [← Measure.withDensity_rnDeriv_eq μ ρ hμac, ← Measure.withDensity_rnDeriv_eq ν ρ hνac,
    withDensity_congr_ae hdens]

/-- For positive mixture weights and finite endpoint entropies, equality in the entropy
convexity inequality holds exactly when the measures are equal. -/
@[simp] theorem klDiv_smul_add_smul_eq_iff (ha : 0 < a) (hb : 0 < b) (hab : a + b = 1)
    (hμ : klDiv μ ρ ≠ ∞) (hν : klDiv ν ρ ≠ ∞) :
    klDiv (a • μ + b • ν) ρ = a * klDiv μ ρ + b * klDiv ν ρ ↔ μ = ν := by
  refine ⟨fun h ↦ by
    by_contra hne
    exact (klDiv_smul_add_smul_lt ha hb hab hμ hν hne).ne h, fun h ↦ ?_⟩
  subst ν
  rw [← add_smul, hab, one_smul, ← add_mul]
  simp [← ENNReal.coe_add, hab]

/-- The finite-entropy domain consists of a convex set of finite measures. -/
theorem convex_setOf_isFiniteMeasure_klDiv_ne_top :
    Convex ℝ≥0 {μ : Measure α | IsFiniteMeasure μ ∧ klDiv μ ρ ≠ ∞} := by
  rintro μ ⟨hμfin, hμ⟩ ν ⟨hνfin, hν⟩ a b _ _ hab
  let := hμfin
  let := hνfin
  exact ⟨inferInstance, ne_top_of_le_ne_top
    (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩) (klDiv_smul_add_smul_le hab)⟩

/-- Relative entropy, read as a real-valued function on its finite-value domain, is strictly
convex. This allows the usual `StrictConvexOn.eq_of_isMinOn` uniqueness theorem to be used. -/
theorem strictConvexOn_toReal_klDiv :
    StrictConvexOn ℝ≥0 {μ : Measure α | IsFiniteMeasure μ ∧ klDiv μ ρ ≠ ∞}
      (fun μ ↦ (klDiv μ ρ).toReal) := by
  refine ⟨convex_setOf_isFiniteMeasure_klDiv_ne_top, ?_⟩
  rintro μ ⟨hμfin, hμ⟩ ν ⟨hνfin, hν⟩ hne a b ha hb hab
  let := hμfin
  let := hνfin
  have h := ENNReal.toReal_strict_mono
    (ENNReal.add_ne_top.2 ⟨by finiteness, by finiteness⟩)
    (klDiv_smul_add_smul_lt ha hb hab hμ hν hne)
  rw [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
    ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.coe_toReal] at h
  simpa only [NNReal.smul_def, smul_eq_mul] using h

/-! ### Quantitative strict convexity -/

/-- **Quantitative strict convexity of the entropy integrand.** The midpoint convexity defect
of `InformationTheory.klFun` at two nonnegative reals bounds the square of their distance,
relative to their sum. -/
theorem sq_sub_le_mul_klFun_add_klFun_sub {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    (x - y) ^ 2 ≤ 4 * (x + y) * (klFun x + klFun y - 2 * klFun (2⁻¹ * x + 2⁻¹ * y)) := by
  set m := 2⁻¹ * x + 2⁻¹ * y with hm
  rcases (show 0 ≤ m by positivity).eq_or_lt with hm0 | hm0
  · obtain rfl : x = 0 := by linarith
    obtain rfl : y = 0 := by linarith
    simp
  -- The defect is the sum of the gaps of `u ↦ u * log u` above its supporting line at `m`,
  -- and each gap dominates a squared difference of square roots.
  have hdef : klFun x + klFun y - 2 * klFun m =
      (x * log x - m * log m - (x - m) * (log m + 1)) +
        (y * log y - m * log m - (y - m) * (log m + 1)) := by
    simp only [klFun, hm]
    ring
  have hJ := add_le_add (sq_sqrt_sub_sqrt_le_mul_log_sub_mul_log_sub hm0 hx)
    (sq_sqrt_sub_sqrt_le_mul_log_sub_mul_log_sub hm0 hy)
  rw [← hdef] at hJ
  have hxy : (x - y) ^ 2 = (√x - √y) ^ 2 * (√x + √y) ^ 2 := by
    rw [← mul_pow, show (√x - √y) * (√x + √y) = √x ^ 2 - √y ^ 2 by ring, sq_sqrt hx,
      sq_sqrt hy]
  have h1 : (√x + √y) ^ 2 ≤ 2 * (x + y) := by
    nlinarith [sq_sqrt hx, sq_sqrt hy, sq_nonneg (√x - √y)]
  have h2 : (√x - √y) ^ 2 ≤ 2 * (klFun x + klFun y - 2 * klFun m) := by
    nlinarith [sq_nonneg (√x + √y - 2 * √m)]
  rw [hxy]
  calc (√x - √y) ^ 2 * (√x + √y) ^ 2 ≤ (2 * (klFun x + klFun y - 2 * klFun m)) * (2 * (x + y)) :=
        mul_le_mul h2 h1 (sq_nonneg _) (by nlinarith [sq_nonneg (√x - √y)])
    _ = _ := by ring

/-- The linear form of `TauCeti.sq_sub_le_mul_klFun_add_klFun_sub`, with a free scale `t`. -/
private theorem mul_abs_sub_add_two_mul_klFun_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) {t : ℝ}
    (ht : 0 ≤ t) :
    t * |x - y| + 2 * klFun (2⁻¹ * x + 2⁻¹ * y) ≤ t ^ 2 * (x + y) + klFun x + klFun y := by
  have h := sq_sub_le_mul_klFun_add_klFun_sub hx hy
  set J := klFun x + klFun y - 2 * klFun (2⁻¹ * x + 2⁻¹ * y) with hJdef
  have hJ : 0 ≤ J := by
    have := convexOn_klFun.2 hx hy (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (0 : ℝ) ≤ 2⁻¹)
      (by norm_num)
    simp only [smul_eq_mul] at this
    linarith
  suffices t * |x - y| ≤ t ^ 2 * (x + y) + J by linarith [hJdef]
  refine (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 ?_
  rw [mul_pow, sq_abs]
  nlinarith [sq_nonneg (t ^ 2 * (x + y) - J), mul_le_mul_of_nonneg_left h (sq_nonneg t)]

/-- The pointwise `ℝ≥0∞` form of `TauCeti.mul_abs_sub_add_two_mul_klFun_le`, with the
entropy integrand and the densities read through `ENNReal.ofReal`. -/
private theorem mul_enorm_sub_add_two_mul_ofReal_klFun_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y)
    (t : ℝ≥0) :
    (t : ℝ≥0∞) * ‖x - y‖ₑ + 2 * ENNReal.ofReal (klFun (2⁻¹ * x + 2⁻¹ * y)) ≤
      t ^ 2 * (ENNReal.ofReal x + ENNReal.ofReal y) + ENNReal.ofReal (klFun x) +
        ENNReal.ofReal (klFun y) := by
  have hm : 0 ≤ klFun (2⁻¹ * x + 2⁻¹ * y) := klFun_nonneg (by positivity)
  calc _ = ENNReal.ofReal (t * |x - y| + 2 * klFun (2⁻¹ * x + 2⁻¹ * y)) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul t.coe_nonneg,
          ENNReal.ofReal_mul zero_le_two, Real.enorm_eq_ofReal_abs]
        simp
    _ ≤ ENNReal.ofReal (t ^ 2 * (x + y) + klFun x + klFun y) :=
        ENNReal.ofReal_le_ofReal (mul_abs_sub_add_two_mul_klFun_le hx hy t.coe_nonneg)
    _ = _ := by
        rw [ENNReal.ofReal_add (add_nonneg (by positivity) (klFun_nonneg hx)) (klFun_nonneg hy),
          ENNReal.ofReal_add (by positivity) (klFun_nonneg hx), ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_add hx hy, ENNReal.ofReal_pow t.coe_nonneg]
        simp

/-- **Quantitative strict convexity of relative entropy.** For finite measures `μ`, `ν` and a
finite reference `ρ`, the convexity defect of relative entropy at the midpoint of `μ` and `ν`
controls the `L¹(ρ)` distance of their densities: for every scale `t ≥ 0`,
`t * ‖dμ/dρ - dν/dρ‖₁ + 2 * klDiv (μ/2 + ν/2) ρ ≤ t² * (μ(univ) + ν(univ)) + klDiv μ ρ +
klDiv ν ρ`. Choosing `t` as the square root of the defect bounds the distance by a multiple of
that square root. The inequality holds trivially when an endpoint entropy is infinite. -/
theorem mul_lintegral_enorm_sub_add_two_mul_klDiv_le (t : ℝ≥0) :
    t * ∫⁻ x, ‖(μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal‖ₑ ∂ρ +
        2 * klDiv ((2⁻¹ : ℝ≥0) • μ + (2⁻¹ : ℝ≥0) • ν) ρ ≤
      t ^ 2 * (μ univ + ν univ) + klDiv μ ρ + klDiv ν ρ := by
  by_cases hμ : klDiv μ ρ = ∞
  · simp [hμ]
  by_cases hν : klDiv ν ρ = ∞
  · simp [hν]
  have hμac := (klDiv_ne_top_iff.1 hμ).1
  have hνac := (klDiv_ne_top_iff.1 hν).1
  have hac := (hμac.smul_left (2⁻¹ : ℝ≥0)).add_left (hνac.smul_left (2⁻¹ : ℝ≥0))
  -- Both sides are integrals against `ρ` of expressions in the densities.
  have hmix : klDiv ((2⁻¹ : ℝ≥0) • μ + (2⁻¹ : ℝ≥0) • ν) ρ =
      ∫⁻ x, ENNReal.ofReal
        (klFun (2⁻¹ * (μ.rnDeriv ρ x).toReal + 2⁻¹ * (ν.rnDeriv ρ x).toReal)) ∂ρ := by
    rw [klDiv_eq_lintegral_klFun_of_ac hac]
    refine lintegral_congr_ae ?_
    filter_upwards [klFun_rnDeriv_smul_add_smul (μ := μ) (ν := ν) (ρ := ρ) (a := 2⁻¹)
      (b := 2⁻¹)] with x hx
    rw [hx, NNReal.coe_inv, NNReal.coe_ofNat]
  have hlhs : t * ∫⁻ x, ‖(μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal‖ₑ ∂ρ +
        2 * klDiv ((2⁻¹ : ℝ≥0) • μ + (2⁻¹ : ℝ≥0) • ν) ρ =
      ∫⁻ x, (t * ‖(μ.rnDeriv ρ x).toReal - (ν.rnDeriv ρ x).toReal‖ₑ +
        2 * ENNReal.ofReal
          (klFun (2⁻¹ * (μ.rnDeriv ρ x).toReal + 2⁻¹ * (ν.rnDeriv ρ x).toReal))) ∂ρ := by
    rw [hmix, lintegral_add_left (by fun_prop), lintegral_const_mul _ (by fun_prop),
      lintegral_const_mul _ (by fun_prop)]
  have hrhs : t ^ 2 * (μ univ + ν univ) + klDiv μ ρ + klDiv ν ρ =
      ∫⁻ x, (t ^ 2 * (μ.rnDeriv ρ x + ν.rnDeriv ρ x) +
        ENNReal.ofReal (klFun (μ.rnDeriv ρ x).toReal) +
          ENNReal.ofReal (klFun (ν.rnDeriv ρ x).toReal)) ∂ρ := by
    rw [lintegral_add_left (by fun_prop), lintegral_add_left (by fun_prop),
      lintegral_const_mul _ (by fun_prop), lintegral_add_left (by fun_prop),
      Measure.lintegral_rnDeriv hμac, Measure.lintegral_rnDeriv hνac,
      klDiv_eq_lintegral_klFun_of_ac hμac, klDiv_eq_lintegral_klFun_of_ac hνac]
  rw [hlhs, hrhs]
  refine lintegral_mono_ae ?_
  -- Pointwise, the densities are finite, so they are the `ENNReal.ofReal` of their real parts.
  filter_upwards [Measure.rnDeriv_lt_top μ ρ, Measure.rnDeriv_lt_top ν ρ] with x hμx hνx
  simpa only [ENNReal.ofReal_toReal hμx.ne, ENNReal.ofReal_toReal hνx.ne] using
    mul_enorm_sub_add_two_mul_ofReal_klFun_le (μ.rnDeriv ρ x).toReal_nonneg
      (ν.rnDeriv ρ x).toReal_nonneg t

end TauCeti
