/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.Data.ENNReal.Inv
import TauCeti.MeasureTheory.Integral.Bochner.Holder
import TauCeti.MeasureTheory.Integral.RieszPotential.Basic
import TauCeti.MeasureTheory.Measure.OpenPos

/-!
# Sobolev inequalities on sets of finite measure

Let `E` be a real normed space of dimension `n ≥ 1` with an additive Haar measure `μ`, and let
`ω = μ(B(0, 1))`. On a set `Ω` of finite measure, `W^{1,p}_0(Ω)` embeds in `L^q(Ω)` whenever
`1 ≤ p ≤ q < ∞` and `δ = 1/p - 1/q < 1/n`, with the explicit bound

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) μ(Ω) ^ (1/n - δ) ‖Du‖_{Lᵖ}`.

Unlike the Gagliardo–Nirenberg–Sobolev inequality `TauCeti.W1p.eLpNorm_value_le_mul_enorm_gradient`,
which holds on every `Ω` with a constant independent of `Ω` but only for `p < n` and at the
critical exponent `1/q = 1/p - 1/n`, this bound covers every dimension and every `p`, at the price
of the factor `μ(Ω) ^ (1/n - δ)`. That factor is what makes it scale correctly: on a ball of
radius `R` it is a multiple of `R ^ (1 - n δ)`, which is exactly how `‖u‖_{L^q} / ‖Du‖_{Lᵖ}`
scales under dilation. In particular `W^{1,2}_0` of a ball embeds in some `L^q` with `q > 2` in
every dimension, including `n = 1` and `n = 2`, where no critical exponent is available. The
borderline case `p = n` is `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient`.

A `C¹` function `u` with compact support in `Ω` is bounded pointwise by the Riesz potential of
`‖Du‖` of order one, `‖u x‖ ≤ (n ω)⁻¹ ∫_Ω ‖Du y‖ ‖x - y‖ ^ (1 - n) dy`
(`TauCeti.enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow`), and that potential maps
`Lᵖ(Ω)` to `L^q(Ω)` with the stated constant (`TauCeti.eLpNorm_setLIntegral_enorm_sub_rpow_mul_le`
with `κ = 1/n`). The estimate then passes from test functions to their closure `W^{1,p}_0(Ω)`
(`TauCeti.W1p.eLpNorm_value_le_of_forall_testFunction`).

## Main declarations

* `TauCeti.eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt`: the bound for compactly
  supported `C¹` functions.
* `TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`: the bound on
  `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`: the scale-invariant form
  on a ball `B(x₀, R)`, with constant a multiple of `R ^ (1 - n δ)`.
* `TauCeti.W1p.exists_forall_eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball`: the same
  bound with one constant `K` for all balls, `‖u‖_{L^q} ≤ K R ^ (1 - n δ) ‖∇u‖_{Lᵖ}`.
* `TauCeti.W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top`: some
  exponent `q > p` and constant `S` with `‖u‖_{L^q} ≤ S ‖∇u‖_{Lᵖ}` on `W^{1,p}_0(Ω)`.
* `TauCeti.W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top`: the Poincaré
  inequality `‖u‖_{W^{1,p}} ≤ C ‖∇u‖_{Lᵖ}` on `W^{1,p}_0(Ω)`, for `p < ∞`.
* `TauCeti.mul_two_sub_lt_two_mul_of_lt_two_mul`: for `r > 1`, the condition `r > n/2` implies
  the condition `n (2 - r) < 2 r`, that is `r > 2n/(n+2)`, of the next two results.
* `TauCeti.W1p0.integrable_mul_value_of_memLp`: for `r > max 1 (2n/(n+2))`, an `Lʳ(Ω)` function
  times a `W^{1,2}_0(Ω)` function is integrable.
* `TauCeti.W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp`: for `r > max 1 (2n/(n+2))`,
  an `Lʳ(Ω)` function acts on `W^{1,2}_0(Ω)` as a continuous linear functional `v ↦ ∫_Ω f v`.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.14, and Theorem 7.10.
-/

public section

noncomputable section

open Function MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal

namespace TauCeti

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω : Set E}

/-- **The Sobolev inequality on sets of finite measure, for compactly supported functions.** Let
`n` be the dimension and `ω = μ(B(0, 1))`, and let `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`
(so `n ≥ 1`). If `u` is `C¹` with compact support inside a set `Ω`, then

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) μ(Ω) ^ (1/n - δ) ‖Du‖_{Lᵖ}`. -/
theorem eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hsupp : tsupport u ⊆ Ω) {p q : ℝ≥0}
    (hp : 1 ≤ p) (hpq : p ≤ q) {δ : ℝ} (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u q μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
        μ Ω ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * eLpNorm (fderiv ℝ u) p μ := by
  -- `Ω` may be replaced by its measurable hull, which has the same measure.
  wlog hΩ : MeasurableSet Ω generalizing Ω
  · rw [← measure_toMeasurable Ω]
    exact this (hsupp.trans (subset_toMeasurable μ Ω)) (measurableSet_toMeasurable μ Ω)
  have hδ0 : 0 ≤ δ := hδ ▸ sub_nonneg.2 (inv_anti₀ (by positivity) (by exact_mod_cast hpq))
  have hfin : 0 < finrank ℝ E := Nat.cast_pos.1 (inv_pos.1 (hδ0.trans_lt hδn))
  have : FiniteDimensional ℝ E := Module.finite_of_finrank_pos hfin
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hfin
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast hfin
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hω : 0 < ω := Metric.measureReal_ball_pos μ 0 one_pos
  have hcont := hu.continuous_fderiv one_ne_zero
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  -- The pointwise potential bound `‖u x‖ ≤ (n ω)⁻¹ V x`.
  have hpt : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal ((n * ω)⁻¹) * ‖V x‖ₑ := fun x => by
    refine (enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow (μ := μ) hu h2u x).trans_eq ?_
    rw [eNorm_eq_self, ← setLIntegral_eq_of_support_subset (s := Ω)]
    · congr 1
      refine lintegral_congr fun y => ?_
      rw [mul_comm, show (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n by field_simp]
    · refine fun y hy ↦ by_contra fun hyΩ ↦ ?_
      rw [mem_support, fderiv_of_notMem_tsupport ℝ fun h => hyΩ (hsupp h)] at hy
      simp [eNorm_eq_nnNorm] at hy
  -- The `Lᵖ`-`L^q` bound for the potential, with `κ = 1/n`.
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := p) (q := q)
    (κ := (n : ℝ)⁻¹) hp hpq hδ hδn (inv_le_one_of_one_le₀ hn) hΩ hcont.eNorm.aemeasurable
  rw [← eLpNorm_restrict_eq_of_support_subset hu.continuous.aestronglyMeasurable
    ((subset_tsupport _).trans hsupp)]
  calc
    eLpNorm u q (μ.restrict Ω) ≤ ENNReal.ofReal ((n * ω)⁻¹) * eLpNorm V q (μ.restrict Ω) :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul'' _ hu.continuous.aestronglyMeasurable.restrict
        (ae_of_all _ hpt)
    _ ≤ _ := by
      rw [mul_assoc]
      refine (mul_le_mul_right hpot _).trans_eq ?_
      have hω' : ω ^ (1 - (n : ℝ)⁻¹) = ω * ω ^ (-(n : ℝ)⁻¹) := by
        rw [sub_eq_add_neg, Real.rpow_add hω, Real.rpow_one]
      rw [hω', eLpNorm_eNorm _ hcont.aestronglyMeasurable,
        eLpNorm_restrict_eq_of_support_subset hcont.aestronglyMeasurable
          ((support_fderiv_subset ℝ).trans hsupp),
        ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
      have hA : (n * ω)⁻¹ * (((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) *
          (ω * ω ^ (-(n : ℝ)⁻¹))) =
          (n : ℝ)⁻¹ * ω ^ (-(n : ℝ)⁻¹) * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) := by
        field_simp
      rw [hA, mul_assoc]

end CompactSupport

section W1p0

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E} {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- **The Sobolev inequality on `W^{1,p}_0(Ω)` for `Ω` of finite measure.** Let `n` be the
dimension and `ω = μ(B(0, 1))`, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n` (so `n ≥ 1`). If
`Ω` has finite measure, then every `u ∈ W^{1,p}_0(Ω)` lies in `L^q(Ω)`, with

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ}`.

No regularity of `Ω` is assumed. -/
theorem W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt
    (hOmega : mu Omega ≠ ∞) {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ}
    (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
        mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * ‖W1p.gradient u‖ₑ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpp : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p :=
    ENNReal.coe_toNNReal (ne_top_of_le_ne_top ENNReal.coe_ne_top hpq)
  set C : ℝ≥0∞ := ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ *
    mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
    mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (sub_nonneg.2 hδn.le) hOmega)
  have h := W1p.eLpNorm_value_le_of_forall_testFunction (q := q) (C := C.toNNReal)
    (fun phi => ?_) hu
  · rwa [ENNReal.coe_toNNReal hC] at h
  · rw [ENNReal.coe_toNNReal hC, ← hpp]
    exact eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt (phi.contDiff.of_le (by simp))
      phi.hasCompactSupport phi.tsupport_subset
      (by exact_mod_cast hpp ▸ hp1) (by exact_mod_cast hpp ▸ hpq)
      (by rwa [ENNReal.coe_toNNReal_eq_toReal]) hδn

/-- **The Sobolev inequality on `W^{1,p}_0` of a ball.** Let `n` be the dimension and
`ω = μ(B(0, 1))`, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. If `Ω = B(x₀, R)`, then every
`u ∈ W^{1,p}_0(Ω)` satisfies

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-δ) ((1 - δ) / (1/n - δ)) ^ (1 - δ) R ^ (1 - n δ) ‖∇u‖_{Lᵖ}`.

The power `R ^ (1 - n δ)` is the one dictated by scaling, so the remaining constant depends only
on `n`, `δ` and the normalization of `μ`. -/
theorem W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball
    {x₀ : E} {R : ℝ} (hOmega : (Omega : Set E) = ball x₀ R)
    {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-δ) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * R ^ (1 - finrank ℝ E * δ)) *
        ‖W1p.gradient u‖ₑ := by
  -- For `R ≤ 0` the ball is empty and the left side is `0`.
  rcases le_or_gt R 0 with hR | hR
  · have h0 : mu.restrict (Omega : Set E) = 0 := by
      rw [hOmega, Metric.ball_eq_empty.2 hR, Measure.restrict_empty]
    refine (eLpNorm_mono_measure _ h0.le).trans ?_
    rw [eLpNorm_measure_zero]
    exact zero_le
  -- `p ≤ q` gives `0 ≤ δ`, so `δ < 1/n` forces `n ≥ 1`.
  have hδ0 : 0 ≤ δ := by
    simpa only [one_div, ENNReal.coe_toReal, hδ] using
      ENNReal.one_div_toReal_sub_one_div_toReal_nonneg
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpq
  have hfin : 0 < finrank ℝ E := Nat.cast_pos.1 (inv_pos.1 (hδ0.trans_lt hδn))
  set n := finrank ℝ E
  set ω := mu.real (ball (0 : E) 1)
  have hω : 0 < ω := Metric.measureReal_ball_pos mu 0 one_pos
  have he : 0 ≤ (n : ℝ)⁻¹ - δ := sub_nonneg.2 hδn.le
  have h1δ : 0 ≤ 1 - δ := by
    have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast hfin)
    linarith
  have hmeas : mu Omega = ENNReal.ofReal (R ^ n * ω) := by
    rw [hOmega, Measure.addHaar_ball_of_pos mu x₀ hR, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity)]
  refine (W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt
    (hmeas ▸ ENNReal.ofReal_ne_top) hpq hδ hδn hu).trans_eq ?_
  rw [hmeas, ENNReal.ofReal_rpow_of_nonneg (by positivity) he,
    ← ENNReal.ofReal_mul (mul_nonneg (by positivity) (Real.rpow_nonneg (div_nonneg h1δ he) _))]
  congr 2
  -- `ω ^ (-1/n) (Rⁿ ω) ^ (1/n - δ) = ω ^ (-δ) R ^ (1 - n δ)`.
  rw [Real.mul_rpow (by positivity) hω.le, ← Real.rpow_natCast, ← Real.rpow_mul hR.le,
    show (n : ℝ) * ((n : ℝ)⁻¹ - δ) = 1 - n * δ by field_simp]
  have hω' : ω ^ (-(n : ℝ)⁻¹) * ω ^ ((n : ℝ)⁻¹ - δ) = ω ^ (-δ) := by
    rw [← Real.rpow_add hω]
    ring_nf
  linear_combination (n : ℝ)⁻¹ * ((1 - δ) / ((n : ℝ)⁻¹ - δ)) ^ (1 - δ) * R ^ (1 - n * δ) * hω'

/-- **The Sobolev inequality on `W^{1,p}_0` of balls, with a uniform constant.** Let `n ≥ 1` be
the dimension, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. There is `K > 0`, depending only on
`n`, `δ` and the normalization of `μ`, such that on every ball `Ω = B(x₀, R)` every
`u ∈ W^{1,p}_0(Ω)` satisfies `‖u‖_{L^q} ≤ K R ^ (1 - n δ) ‖∇u‖_{Lᵖ}`. This is
`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball` with its explicit constant
named once for all balls, the form used by iteration arguments on families of balls. -/
theorem W1p.exists_forall_eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball
    {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Omega : Opens E} {x₀ : E} {R : ℝ},
      (Omega : Set E) = ball x₀ R → ∀ u ∈ w1p0Submodule mu Omega p,
        eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
          ENNReal.ofReal (K * R ^ (1 - finrank ℝ E * δ)) * ‖W1p.gradient u‖ₑ := by
  -- `p ≤ q` gives `0 ≤ δ`, so `δ < 1/n` forces `n ≥ 1`.
  have hδ0 : 0 ≤ δ := by
    simpa only [one_div, ENNReal.coe_toReal, hδ] using
      ENNReal.one_div_toReal_sub_one_div_toReal_nonneg
        (zero_lt_one.trans_le (Fact.out : (1 : ℝ≥0∞) ≤ p)).ne' hpq
  have hfin : 0 < finrank ℝ E := Nat.cast_pos.1 (inv_pos.1 (hδ0.trans_lt hδn))
  have : Nontrivial E := Module.nontrivial_of_finrank_pos hfin
  have hn : (1 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hfin
  have : 0 < (finrank ℝ E : ℝ)⁻¹ - δ := sub_pos.2 hδn
  have : 0 < 1 - δ := by linarith [hδn.trans_le (inv_le_one_of_one_le₀ hn)]
  have := Metric.measureReal_ball_pos mu (0 : E) one_pos
  exact ⟨(finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-δ) *
    ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ), by positivity, fun hOmega u hu =>
    W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball hOmega hpq hδ hδn hu⟩

omit [Fact (1 ≤ p)] in
/-- **The Poincaré inequality on `W^{1,2}_0` of a ball.** If `Ω = B(x₀, R)`, then every
`u ∈ W^{1,2}_0(Ω)` satisfies

`‖u‖_{L²} ≤ R ‖∇u‖_{L²}`,

for every additive Haar measure. This is
`TauCeti.W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball` at `p = q = 2`, where the
constant reduces to `R`. -/
theorem W1p.norm_value_le_mul_norm_gradient_of_eq_ball [Nontrivial E] {x₀ : E} {R : ℝ}
    (hR : 0 < R) (hOmega : (Omega : Set E) = ball x₀ R) {u : W1p mu Omega 2}
    (hu : u ∈ w1p0Submodule mu Omega 2) :
    ‖W1p.value u‖ ≤ R * ‖W1p.gradient u‖ := by
  have hn : (finrank ℝ E : ℝ) ≠ 0 := by exact_mod_cast finrank_pos.ne'
  have h := W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball (mu := mu)
    hOmega (q := 2) (by norm_num) (δ := 0) (by norm_num) (by positivity) hu
  simp only [neg_zero, Real.rpow_zero, sub_zero, mul_zero, Real.rpow_one, mul_one, one_div,
    inv_inv, inv_mul_cancel₀ hn, one_mul, ENNReal.coe_ofNat] at h
  have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top eNorm_ne_top) h
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hR.le, toReal_eNorm, ← Lp.norm_def] at this

/-- **A Sobolev inequality on `W^{1,p}_0(Ω)` with a gain of integrability.** If `Ω` has finite
measure, `n ≥ 1` and `p < ∞`, there are an exponent `q > p` and a constant `S` such that
`‖u‖_{L^q} ≤ S ‖∇u‖_{Lᵖ}` for every `u ∈ W^{1,p}_0(Ω)`. This holds in every dimension; see
`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt` for explicit `q` and
`S`. -/
theorem W1p.exists_forall_eLpNorm_value_le_mul_enorm_gradient_of_measure_ne_top [Nontrivial E]
    (hp : p ≠ ∞) (hOmega : mu Omega ≠ ∞) :
    ∃ q : ℝ≥0∞, p < q ∧ ∃ S : ℝ≥0, ∀ u ∈ w1p0Submodule mu Omega p,
      eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤ S * ‖W1p.gradient u‖ₑ := by
  -- Apply the explicit bound at `1/q = 1/p - δ` with `δ = 1/(2 n p)`.
  set n : ℝ := (finrank ℝ E : ℝ)
  have hn : 1 ≤ n := by
    simp only [n, Nat.one_le_cast]
    exact finrank_pos
  have hp1 : 1 ≤ p.toReal := by
    simpa using (ENNReal.toReal_le_toReal ENNReal.one_ne_top hp).2 (Fact.out : (1 : ℝ≥0∞) ≤ p)
  set r : ℝ := p.toReal⁻¹
  have hr : 0 < r := inv_pos.2 (by linarith)
  have hr1 : r ≤ 1 := inv_le_one_of_one_le₀ hp1
  set δ : ℝ := r / (2 * n)
  have hδ : 0 < δ := by positivity
  have hδn : δ < n⁻¹ := by
    rw [div_lt_iff₀ (by positivity), inv_mul_eq_div, lt_div_iff₀ (by positivity)]
    nlinarith
  have hδr : δ < r := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith
  set q : ℝ≥0 := Real.toNNReal (r - δ)⁻¹
  have hq : (q : ℝ) = (r - δ)⁻¹ := Real.coe_toNNReal _ (inv_nonneg.2 (by linarith))
  have hpq : p < q := by
    refine (ENNReal.toReal_lt_toReal hp ENNReal.coe_ne_top).1 ?_
    rw [ENNReal.coe_toReal, hq, ← inv_inv p.toReal]
    exact inv_strictAnti₀ (by linarith) (by linarith)
  set C : ℝ≥0∞ := ENNReal.ofReal (n⁻¹ * mu.real (ball 0 1) ^ (-n⁻¹) *
    ((1 - δ) / (n⁻¹ - δ)) ^ (1 - δ)) * mu Omega ^ (n⁻¹ - δ)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.rpow_ne_top_of_nonneg (by linarith) hOmega)
  refine ⟨q, hpq, C.toNNReal, fun u hu ↦ ?_⟩
  rw [ENNReal.coe_toNNReal hC]
  exact W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt hOmega hpq.le
    (by rw [hq, inv_inv]; ring) hδn hu

/-- **The Poincaré inequality on `W^{1,p}_0(Ω)` for `Ω` of finite measure.** In dimension
`n ≥ 1` and for `p < ∞`, there is a constant `C` with `‖u‖_{W^{1,p}} ≤ C ‖∇u‖_{Lᵖ}` for every
`u ∈ W^{1,p}_0(Ω)`. This is the case `q = p` of
`TauCeti.W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt`, which bounds the value.
No regularity of `Ω` is assumed. -/
theorem W1p.exists_forall_enorm_le_mul_enorm_gradient_of_measure_ne_top [Nontrivial E]
    (hp : p ≠ ∞) (hOmega : mu Omega ≠ ∞) :
    ∃ C : ℝ≥0, ∀ u ∈ w1p0Submodule mu Omega p, ‖u‖ₑ ≤ C * ‖W1p.gradient u‖ₑ := by
  have hpp : p = (p.toNNReal : ℝ≥0∞) := (ENNReal.coe_toNNReal hp).symm
  -- The Sobolev inequality at `q = p`, that is `δ = 0`, bounds the value.
  obtain ⟨S, hS, hval⟩ : ∃ S : ℝ≥0∞, S ≠ ∞ ∧ ∀ u ∈ w1p0Submodule mu Omega p,
      eLpNorm (W1p.value u : E → ℝ) p (mu.restrict Omega) ≤ S * ‖W1p.gradient u‖ₑ := by
    refine ⟨_, ?_, fun u hu => by
      have h := W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (q := p.toNNReal)
        hOmega hpp.le (sub_self _) (inv_pos.2 (Nat.cast_pos.2 finrank_pos)) hu
      rwa [← hpp] at h⟩
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by simp) hOmega)
  refine ⟨(S + 1).toNNReal, fun u hu => ?_⟩
  rw [ENNReal.coe_toNNReal (ENNReal.add_ne_top.2 ⟨hS, ENNReal.one_ne_top⟩), add_mul, one_mul]
  refine (W1p.enorm_le_enorm_value_add_enorm_gradient _).trans (add_le_add ?_ le_rfl)
  rw [Lp.eNorm_def]
  exact hval u hu

end W1p0

section DualPairing

/-- **`r > n/2` implies `r > 2n/(n+2)`.** For `n ≥ 0` and `r > 1`, the condition `n < 2 r`
gives `n (2 - r) < 2 r`, the range of exponents in which `Lʳ(Ω)` acts on `W^{1,2}_0(Ω)`. -/
theorem mul_two_sub_lt_two_mul_of_lt_two_mul {n r : ℝ} (hn : 0 ≤ n) (hr : 1 < r)
    (hnr : n < 2 * r) : n * (2 - r) < 2 * r := by
  nlinarith [mul_nonneg hn (sub_nonneg.2 hr.le)]

variable {E : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [BorelSpace E] {mu : Measure E} [mu.IsAddHaarMeasure]
  {Omega : Opens E}

/-- The pairing `v ↦ ∫_Ω f v` on `W^{1,2}_0(Ω)` as a linear map, given that each product
`f v` is integrable. -/
private def W1p0.setIntegralMulₗ (f : E → ℝ)
    (hint : ∀ v : W1p0 mu Omega 2,
      Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega)) :
    W1p0 mu Omega 2 →ₗ[ℝ] ℝ where
  toFun v := ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu
  map_add' u v := by
    simp only [Submodule.coe_add]
    rw [← integral_add (hint u) (hint v)]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_add_ae (u : W1p mu Omega 2) (v : W1p mu Omega 2)] with x hx
    rw [hx, Pi.add_apply, mul_add]
  map_smul' c u := by
    simp only [RingHom.id_apply, Submodule.coe_smul, smul_eq_mul]
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [W1p.value_smul_ae c (u : W1p mu Omega 2)] with x hx
    rw [hx, Pi.smul_apply, smul_eq_mul]
    ring

/-- **`Lʳ` functions are integrable against `W^{1,2}_0(Ω)`.** Let `n ≥ 1` be the dimension, let
`Ω` have finite measure, and let `r > 1` with `n (2 - r) < 2 r`. For `f ∈ Lʳ(Ω)` and
`v ∈ W^{1,2}_0(Ω)`, the product `f v` is integrable on `Ω`: by the Sobolev inequality `v` lies in
some `Lᵗ(Ω)` with `1/r + 1/t ≤ 1`. -/
theorem W1p0.integrable_mul_value_of_memLp [Nontrivial E]
    (hOmega : mu Omega ≠ ∞) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (finrank ℝ E : ℝ) * (2 - r) < 2 * r)
    {f : E → ℝ} (hf : MemLp f r (mu.restrict Omega)) (v : W1p0 mu Omega 2) :
    Integrable (fun x => f x * W1p.value (v : W1p mu Omega 2) x) (mu.restrict Omega) := by
  have hn : (1 : ℝ) ≤ (finrank ℝ E : ℝ) := Nat.one_le_cast.2 finrank_pos
  have : IsFiniteMeasure (mu.restrict (Omega : Set E)) := isFiniteMeasure_restrict.2 hOmega
  obtain ⟨t, ht0, h2t, hτn, hrt⟩ :=
    ENNReal.exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one (zero_lt_one.trans_le hn) hr hrn
  have hmemt : MemLp (W1p.value (v : W1p mu Omega 2)) t (mu.restrict Omega) :=
    (W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu)
      hOmega h2t (δ := 2⁻¹ - (t : ℝ)⁻¹) (by rw [ENNReal.toReal_ofNat])
        hτn v.property).trans_lt (ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by linarith) hOmega)) eNorm_lt_top)
  have hq1 : (1 : ℝ≥0∞) ≤ ((r : ℝ≥0∞)⁻¹ + (t : ℝ≥0∞)⁻¹)⁻¹ := by
    have hle : ((r⁻¹ + t⁻¹ : ℝ≥0) : ℝ) ≤ 1 := by push_cast; exact hrt
    rw [ENNReal.one_le_inv, ← ENNReal.coe_inv (zero_lt_one.trans hr).ne', ← ENNReal.coe_inv ht0.ne',
      ← ENNReal.coe_add]
    exact_mod_cast hle
  exact (hf.mul hmemt (hpqr := ENNReal.HolderTriple.of _ _)).integrable hq1

/-- **An `Lʳ` function acts continuously on `W^{1,2}_0(Ω)`.** Let `n ≥ 1` be the dimension, let
`Ω` have finite measure, and let `r > 1` with `n (2 - r) < 2 r`, that is `r > 2n/(n + 2)` (which
is automatic for `n ≤ 2`). For `f ∈ Lʳ(Ω)`, the pairing `v ↦ ∫_Ω f v` is a continuous linear
functional on `W^{1,2}_0(Ω)`. This is the right-hand side of the weak
formulation of an elliptic equation with `Lʳ` data. -/
theorem W1p0.exists_strongDual_apply_eq_setIntegral_of_memLp [Nontrivial E]
    (hOmega : mu Omega ≠ ∞) {r : ℝ≥0} (hr : 1 < r)
    (hrn : (finrank ℝ E : ℝ) * (2 - r) < 2 * r)
    {f : E → ℝ} (hf : MemLp f r (mu.restrict Omega)) :
    ∃ ℓ : StrongDual ℝ (W1p0 mu Omega 2), ∀ v : W1p0 mu Omega 2,
      ℓ v = ∫ x in Omega, f x * W1p.value (v : W1p mu Omega 2) x ∂mu := by
  set n : ℝ := (finrank ℝ E : ℝ)
  have hn : (1 : ℝ) ≤ n := Nat.one_le_cast.2 finrank_pos
  set ν := mu.restrict (Omega : Set E)
  have : IsFiniteMeasure ν := isFiniteMeasure_restrict.2 hOmega
  obtain ⟨t, ht0, h2t, hτn, hrt⟩ :=
    ENNReal.exists_nnreal_two_le_inv_sub_lt_and_inv_add_le_one (zero_lt_one.trans_le hn) hr hrn
  -- The Sobolev inequality `‖v‖_{Lᵗ} ≤ S ‖∇v‖_{L²}` on `W^{1,2}_0(Ω)`.
  obtain ⟨S, hSfin, hS⟩ : ∃ S : ℝ≥0∞, S ≠ ∞ ∧ ∀ v : W1p0 mu Omega 2,
      eLpNorm (W1p.value (v : W1p mu Omega 2)) t ν ≤ S * ‖W1p.gradient (v : W1p mu Omega 2)‖ₑ :=
    ⟨_, ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by linarith) hOmega), fun v =>
      W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt (mu := mu)
        hOmega h2t (δ := 2⁻¹ - (t : ℝ)⁻¹) (by rw [ENNReal.toReal_ofNat])
        hτn v.property⟩
  have hmemt : ∀ v : W1p0 mu Omega 2, MemLp (W1p.value (v : W1p mu Omega 2)) t ν := fun v =>
    (hS v).trans_lt (ENNReal.mul_lt_top hSfin.lt_top eNorm_lt_top)
  -- Hölder's inequality: `|∫_Ω f v| ≤ ‖f‖_{Lʳ} ‖v‖_{Lᵗ} |Ω|^{...}`.
  refine ⟨(W1p0.setIntegralMulₗ f
    (W1p0.integrable_mul_value_of_memLp hOmega hr hrn hf)).mkContinuous
    ((eLpNorm f r ν).toReal * S.toReal * ν.real univ ^ (1 - (r : ℝ)⁻¹ - (t : ℝ)⁻¹))
    fun v => ?_, fun v => rfl⟩
  have hhol := TauCeti.MeasureTheory.norm_integral_smul_le_eLpNorm_mul_eLpNorm_mul_measureReal_rpow
    (by exact_mod_cast zero_lt_one.trans hr) (by exact_mod_cast ht0) hrt hf (hmemt v)
    (measure_ne_top ν univ) (Filter.Eventually.of_forall fun x hx => absurd (mem_univ x) hx)
  have hsob : (eLpNorm (W1p.value (v : W1p mu Omega 2)) t ν).toReal ≤ S.toReal * ‖v‖ := by
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top hSfin eNorm_ne_top) (hS v)
    rw [ENNReal.toReal_mul, toReal_eNorm] at this
    exact this.trans (mul_le_mul_of_nonneg_left (W1p.norm_gradient_le _) ENNReal.toReal_nonneg)
  refine hhol.trans ?_
  calc (eLpNorm f r ν).toReal * (eLpNorm (W1p.value (v : W1p mu Omega 2)) t ν).toReal *
        ν.real univ ^ (1 - (r : ℝ)⁻¹ - (t : ℝ)⁻¹)
      ≤ (eLpNorm f r ν).toReal * (S.toReal * ‖v‖) *
        ν.real univ ^ (1 - (r : ℝ)⁻¹ - (t : ℝ)⁻¹) := by gcongr
    _ = _ := by ring

end DualPairing

end TauCeti
