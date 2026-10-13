/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.Embedding
import TauCeti.Analysis.Sobolev.Poincare.Potential
import TauCeti.MeasureTheory.Integral.RieszPotential

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

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.14, and Theorem 7.10.
-/

public section

noncomputable section

namespace TauCeti

open Function MeasureTheory Metric Set Module TopologicalSpace
open scoped Distributions ENNReal NNReal

section CompactSupport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [Nontrivial E] [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → F} {Ω : Set E}

/-- **The Sobolev inequality on sets of finite measure, for compactly supported functions.** Let
`n` be the dimension and `ω = μ(B(0, 1))`, and let `1 ≤ p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`.
If `u` is `C¹` with compact support inside a measurable set `Ω`, then

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) μ(Ω) ^ (1/n - δ) ‖Du‖_{Lᵖ}`. -/
theorem eLpNorm_le_mul_measure_rpow_mul_eLpNorm_fderiv_of_lt (hu : ContDiff ℝ 1 u)
    (h2u : HasCompactSupport u) (hΩ : MeasurableSet Ω) (hsupp : tsupport u ⊆ Ω) {p q : ℝ≥0}
    (hp : 1 ≤ p) (hpq : p ≤ q) {δ : ℝ} (hδ : (p : ℝ)⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) :
    eLpNorm u q μ ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * μ.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
        μ Ω ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * eLpNorm (fderiv ℝ u) p μ := by
  set n := finrank ℝ E
  set ω := μ.real (ball (0 : E) 1)
  have hn : (1 : ℝ) ≤ n := by exact_mod_cast finrank_pos
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne'
    measure_ball_lt_top.ne
  have hcont := hu.continuous_fderiv one_ne_zero
  -- The Riesz potential of order one of `‖Du‖`, over `Ω`.
  set V : E → ℝ≥0∞ := fun x =>
    ∫⁻ y in Ω, ‖x - y‖ₑ ^ ((n : ℝ) * ((n : ℝ)⁻¹ - 1)) * ‖fderiv ℝ u y‖ₑ ∂μ
  -- The pointwise potential bound `‖u x‖ ≤ (n ω)⁻¹ V x`.
  have hpt : ∀ x, ‖u x‖ₑ ≤ ENNReal.ofReal ((n * ω)⁻¹) * ‖V x‖ₑ := fun x => by
    refine (enorm_le_lintegral_enorm_fderiv_mul_enorm_sub_rpow (μ := μ) hu h2u x).trans_eq ?_
    rw [enorm_eq_self, ← setLIntegral_eq_of_support_subset (s := Ω)]
    · congr 1
      refine lintegral_congr fun y => ?_
      rw [mul_comm, show (n : ℝ) * ((n : ℝ)⁻¹ - 1) = 1 - n by field_simp]
    · intro y hy
      by_contra hyΩ
      rw [mem_support, fderiv_of_notMem_tsupport ℝ fun h => hyΩ (hsupp h)] at hy
      simp [enorm_eq_nnnorm] at hy
  -- The `Lᵖ`-`L^q` bound for the potential, with `κ = 1/n`.
  have hpot := eLpNorm_setLIntegral_enorm_sub_rpow_mul_le (μ := μ) (p := p) (q := q)
    (κ := (n : ℝ)⁻¹) hp hpq hδ hδn (inv_le_one_of_one_le₀ hn) hΩ hcont.enorm.aemeasurable
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
      rw [hω', eLpNorm_enorm _ hcont.aestronglyMeasurable,
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

/-- **The Sobolev inequality on `W^{1,p}_0(Ω)` for `Ω` of finite measure.** Let `n ≥ 1` be the
dimension and `ω = μ(B(0, 1))`, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. If `Ω` has finite
measure, then every `u ∈ W^{1,p}_0(Ω)` lies in `L^q(Ω)`, with

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-1/n) ((1 - δ) / (1/n - δ)) ^ (1 - δ) μ(Ω) ^ (1/n - δ) ‖∇u‖_{Lᵖ}`.

No regularity of `Ω` is assumed. -/
theorem W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt [Nontrivial E]
    (hp : p ≠ ∞) (hOmega : mu Omega ≠ ∞) {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ}
    (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ) (hδn : δ < (finrank ℝ E : ℝ)⁻¹)
    {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-(finrank ℝ E : ℝ)⁻¹) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ)) *
        mu Omega ^ ((finrank ℝ E : ℝ)⁻¹ - δ) * ‖W1p.gradient u‖ₑ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpp : ((p.toNNReal : ℝ≥0) : ℝ≥0∞) = p := ENNReal.coe_toNNReal hp
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
      phi.hasCompactSupport Omega.isOpen.measurableSet phi.tsupport_subset
      (by exact_mod_cast hpp ▸ hp1) (by exact_mod_cast hpp ▸ hpq)
      (by rwa [ENNReal.coe_toNNReal_eq_toReal]) hδn

/-- **The Sobolev inequality on `W^{1,p}_0` of a ball.** Let `n ≥ 1` be the dimension and
`ω = μ(B(0, 1))`, and let `p ≤ q < ∞` with `δ = 1/p - 1/q < 1/n`. If `Ω = B(x₀, R)`, then every
`u ∈ W^{1,p}_0(Ω)` satisfies

`‖u‖_{L^q} ≤ n⁻¹ ω ^ (-δ) ((1 - δ) / (1/n - δ)) ^ (1 - δ) R ^ (1 - n δ) ‖∇u‖_{Lᵖ}`.

The power `R ^ (1 - n δ)` is the one dictated by scaling, so the remaining constant depends only
on `n`, `δ` and the normalization of `μ`. -/
theorem W1p.eLpNorm_value_le_mul_rpow_mul_enorm_gradient_of_eq_ball [Nontrivial E]
    (hp : p ≠ ∞) {x₀ : E} {R : ℝ} (hR : 0 < R) (hOmega : (Omega : Set E) = ball x₀ R)
    {q : ℝ≥0} (hpq : p ≤ q) {δ : ℝ} (hδ : p.toReal⁻¹ - (q : ℝ)⁻¹ = δ)
    (hδn : δ < (finrank ℝ E : ℝ)⁻¹) {u : W1p mu Omega p} (hu : u ∈ w1p0Submodule mu Omega p) :
    eLpNorm (W1p.value u : E → ℝ) q (mu.restrict Omega) ≤
      ENNReal.ofReal ((finrank ℝ E : ℝ)⁻¹ * mu.real (ball 0 1) ^ (-δ) *
        ((1 - δ) / ((finrank ℝ E : ℝ)⁻¹ - δ)) ^ (1 - δ) * R ^ (1 - finrank ℝ E * δ)) *
        ‖W1p.gradient u‖ₑ := by
  set n := finrank ℝ E
  set ω := mu.real (ball (0 : E) 1)
  have hn : (0 : ℝ) < n := by exact_mod_cast finrank_pos
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos mu 0 one_pos).ne'
    measure_ball_lt_top.ne
  have he : 0 ≤ (n : ℝ)⁻¹ - δ := sub_nonneg.2 hδn.le
  have h1δ : 0 ≤ 1 - δ := by
    have : (n : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by exact_mod_cast finrank_pos)
    linarith
  have hmeas : mu Omega = ENNReal.ofReal (R ^ n * ω) := by
    rw [hOmega, Measure.addHaar_ball_of_pos mu x₀ hR, ← ofReal_measureReal measure_ball_lt_top.ne,
      ← ENNReal.ofReal_mul (by positivity)]
  refine (W1p.eLpNorm_value_le_mul_measure_rpow_mul_enorm_gradient_of_lt hp
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

end W1p0

end TauCeti
