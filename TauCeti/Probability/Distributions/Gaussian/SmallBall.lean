/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.Basic
public import Mathlib.Probability.HasLaw

/-!
# Small-ball bounds for real Gaussian laws

Because `gaussianPDFReal μ v` never exceeds its value `(√(2 * π * v))⁻¹` at the mean, every
nondegenerate real Gaussian law `gaussianReal μ v` (`v ≠ 0`) is dominated by `(√(2 * π * v))⁻¹`
times Lebesgue measure. Specializing to intervals and `ℓ^∞` boxes gives small-ball
(anti-concentration) estimates for one-dimensional real Gaussian laws and finite products of
independent Gaussian coordinates.

At the degenerate boundary `v = 0`, `gaussianReal μ 0` is `Measure.dirac μ`, which assigns mass `1`
to `{μ}` while `volume {μ} = 0`; the positive-variance hypothesis `v ≠ 0` is therefore sharp.

## Main statements

* `TauCeti.Probability.gaussianReal_apply_le` — Lebesgue domination
  `gaussianReal μ v s ≤ ENNReal.ofReal (√(2 * π * v))⁻¹ * volume s` for `v ≠ 0`.
* `TauCeti.Probability.measureReal_gaussianReal_le` — real-valued counterpart for sets of finite
  Lebesgue measure.
* `TauCeti.Probability.gaussianReal_Icc_le`, `TauCeti.Probability.gaussianReal_closedBall_le`, and
  `TauCeti.Probability.gaussianReal_Icc_neg_le` — interval and symmetric small-ball bounds
  `gaussianReal μ v [x - r, x + r] ≤ ENNReal.ofReal (√(2 / (π * v)) * r)`.
* `TauCeti.Probability.pi_gaussianReal_forall_abs_sub_le` and
  `TauCeti.Probability.pi_gaussianReal_zero_one_forall_abs_le` — `ℓ^∞` box small-ball bounds for
  product Gaussian measures over a finite index type.
* `ProbabilityTheory.HasLaw.measure_abs_sub_le_of_gaussianReal`,
  `ProbabilityTheory.HasLaw.measure_forall_abs_sub_le_of_pi_gaussianReal`, and
  `ProbabilityTheory.HasLaw.measure_forall_abs_le_of_pi_gaussianReal_zero_one` — random-variable
  small-ball bounds under `HasLaw`.
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal

namespace TauCeti.Probability

/-- Uniform upper bound on the `ℝ≥0∞`-valued Gaussian density `gaussianPDF`, valid at every
variance `v` (including `v = 0`, where both sides vanish). -/
theorem gaussianPDF_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDF μ v x ≤ ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ :=
  ENNReal.ofReal_le_ofReal (gaussianPDFReal_le μ v x)

/-- At nonzero variance, `gaussianReal μ v` is dominated by `(√(2 * π * v))⁻¹` times Lebesgue
measure on every subset of `ℝ` (measurable or not). The hypothesis `v ≠ 0` is required because
`gaussianReal μ 0 = Measure.dirac μ` gives mass `1` to the Lebesgue-null singleton `{μ}`. -/
theorem gaussianReal_apply_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (s : Set ℝ) :
    gaussianReal μ v s ≤ ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ * volume s := by
  rw [gaussianReal_apply μ hv s]
  calc
    ∫⁻ x in s, gaussianPDF μ v x
      ≤ ∫⁻ _ in s, ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ :=
        lintegral_mono fun x ↦ gaussianPDF_le μ v x
    _ = ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ * volume s := by
        rw [lintegral_const, Measure.restrict_apply_univ]

/-- Real-valued Lebesgue domination for `gaussianReal μ v` on sets of finite Lebesgue measure.
Finiteness `volume s ≠ ∞` is required because `volume.real Set.univ = 0` while
`(gaussianReal μ v).real Set.univ = 1`. -/
theorem measureReal_gaussianReal_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) {s : Set ℝ}
    (hs : volume s ≠ ∞) :
    (gaussianReal μ v).real s ≤ (√(2 * π * (v : ℝ)))⁻¹ * volume.real s := by
  have htop : ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ * volume s ≠ ∞ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hs
  have h := ENNReal.toReal_mono htop (gaussianReal_apply_le μ hv s)
  rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at h

/-- Small-ball bound for `gaussianReal μ v` on any closed interval `[a, b]` (when `b < a`, both
sides vanish). -/
theorem gaussianReal_Icc_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (a b : ℝ) :
    gaussianReal μ v (Icc a b) ≤ ENNReal.ofReal ((b - a) / √(2 * π * (v : ℝ))) := by
  calc
    gaussianReal μ v (Icc a b)
      ≤ ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ * volume (Icc a b) :=
        gaussianReal_apply_le μ hv (Icc a b)
    _ = ENNReal.ofReal ((b - a) / √(2 * π * (v : ℝ))) := by
        rw [Real.volume_Icc, ← ENNReal.ofReal_mul (by positivity), inv_mul_eq_div]

/-- Small-ball bound for `gaussianReal μ v` (`v ≠ 0`) on any closed ball `[x - r, x + r]`:
the mass is at most `√(2 / (π * v)) * r` (and `0` when `r ≤ 0`), uniformly in the center `x` and
mean `μ`. -/
theorem gaussianReal_closedBall_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (x r : ℝ) :
    gaussianReal μ v (Metric.closedBall x r) ≤ ENNReal.ofReal (√(2 / (π * (v : ℝ))) * r) := by
  have : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  have hconst : (2 : ℝ) * r / √(2 * π * (v : ℝ)) = √(2 / (π * (v : ℝ))) * r := by
    have hsqrt : √(2 / (π * (v : ℝ))) = 2 / √(2 * π * (v : ℝ)) := by
      have harg : (2 : ℝ) / (π * (v : ℝ)) = (2 : ℝ) ^ 2 / (2 * π * (v : ℝ)) := by
        field_simp
      rw [harg, Real.sqrt_div (by positivity), Real.sqrt_sq zero_le_two]
    rw [hsqrt, div_mul_eq_mul_div]
  rw [Real.closedBall_eq_Icc]
  refine (gaussianReal_Icc_le μ hv (x - r) (x + r)).trans_eq ?_
  rw [← hconst]
  congr 1
  ring

/-- Symmetric small-ball bound for `gaussianReal μ v` (`v ≠ 0`) on `[-r, r]`. -/
theorem gaussianReal_Icc_neg_le (μ : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (r : ℝ) :
    gaussianReal μ v (Icc (-r) r) ≤ ENNReal.ofReal (√(2 / (π * (v : ℝ))) * r) := by
  simpa [Real.closedBall_eq_Icc] using gaussianReal_closedBall_le μ hv 0 r

/-- Symmetric small-ball bound for the standard Gaussian law `gaussianReal 0 1` on `[-r, r]`. -/
theorem gaussianReal_zero_one_Icc_neg_le (r : ℝ) :
    gaussianReal 0 1 (Icc (-r) r) ≤ ENNReal.ofReal (√(2 / π) * r) := by
  simpa using gaussianReal_Icc_neg_le 0 one_ne_zero r

/-- Small-ball bound for an `ℓ^∞` box under a finite product of nondegenerate real Gaussian laws. -/
theorem pi_gaussianReal_forall_abs_sub_le {ι : Type*} [Fintype ι] (μ : ι → ℝ)
    {v : ι → ℝ≥0} (hv : ∀ i, v i ≠ 0) (x r : ι → ℝ) :
    (Measure.pi fun i ↦ gaussianReal (μ i) (v i)) {y | ∀ i, |y i - x i| ≤ r i} ≤
      ∏ i, ENNReal.ofReal (√(2 / (π * (v i : ℝ))) * r i) := by
  have hset : {y : ι → ℝ | ∀ i, |y i - x i| ≤ r i} =
      Set.univ.pi fun i ↦ Metric.closedBall (x i) (r i) := by
    ext y
    simp [Metric.mem_closedBall, Real.dist_eq]
  rw [hset, Measure.pi_pi]
  exact Finset.prod_le_prod fun i _ ↦ gaussianReal_closedBall_le (μ i) (hv i) (x i) (r i)

/-- Cube small-ball bound for a finite product of standard Gaussian laws `gaussianReal 0 1`:
the `ℓ^∞` ball of radius `r` has measure at most `(√(2 / π) * r) ^ |ι|`. -/
theorem pi_gaussianReal_zero_one_forall_abs_le (ι : Type*) [Fintype ι] (r : ℝ) :
    (Measure.pi fun _ : ι ↦ gaussianReal 0 1) {y | ∀ i, |y i| ≤ r} ≤
      ENNReal.ofReal (√(2 / π) * r) ^ Fintype.card ι := by
  simpa using pi_gaussianReal_forall_abs_sub_le (ι := ι) (fun _ ↦ 0) (fun _ ↦ one_ne_zero)
    (fun _ ↦ 0) (fun _ ↦ r)

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Small-ball bound for a real random variable with law `gaussianReal μ v` (`v ≠ 0`), uniformly
in the center `x`. -/
theorem measure_abs_sub_le_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} {v : ℝ≥0}
    (hX : HasLaw X (gaussianReal μ v) P) (hv : v ≠ 0) (x r : ℝ) :
    P {ω | |X ω - x| ≤ r} ≤ ENNReal.ofReal (√(2 / (π * (v : ℝ))) * r) := by
  have hset : {y : ℝ | |y - x| ≤ r} = Metric.closedBall x r := by
    ext y
    simp [Metric.mem_closedBall, Real.dist_eq]
  have hmeas : MeasurableSet {y : ℝ | |y - x| ≤ r} := by
    rw [hset]
    exact Metric.isClosed_closedBall.measurableSet
  rw [hX.measure_eq hmeas, hset]
  exact gaussianReal_closedBall_le μ hv x r

/-- Box small-ball bound for a random vector whose coordinates have independent nondegenerate real
Gaussian laws `gaussianReal (μ i) (v i)`. -/
theorem measure_forall_abs_sub_le_of_pi_gaussianReal {ι : Type*} [Fintype ι]
    {X : Ω → ι → ℝ} {μ : ι → ℝ} {v : ι → ℝ≥0}
    (hX : HasLaw X (Measure.pi fun i ↦ gaussianReal (μ i) (v i)) P)
    (hv : ∀ i, v i ≠ 0) (x r : ι → ℝ) :
    P {ω | ∀ i, |X ω i - x i| ≤ r i} ≤
      ∏ i, ENNReal.ofReal (√(2 / (π * (v i : ℝ))) * r i) := by
  have hmeas : MeasurableSet {y : ι → ℝ | ∀ i, |y i - x i| ≤ r i} := by
    have hset : {y : ι → ℝ | ∀ i, |y i - x i| ≤ r i} =
        ⋂ i : ι, {y : ι → ℝ | |y i - x i| ≤ r i} := by
      ext y
      simp
    rw [hset]
    exact MeasurableSet.iInter fun i ↦ measurableSet_le
      (continuous_abs.comp ((continuous_apply i).sub continuous_const)).measurable measurable_const
  rw [hX.measure_eq hmeas]
  exact pi_gaussianReal_forall_abs_sub_le μ hv x r

/-- Cube small-ball bound for a random vector whose coordinates are independent standard Gaussians:
`P(∀ i, |X ω i| ≤ r) ≤ (√(2 / π) * r) ^ |ι|`. -/
theorem measure_forall_abs_le_of_pi_gaussianReal_zero_one {ι : Type*} [Fintype ι]
    {X : Ω → ι → ℝ} (hX : HasLaw X (Measure.pi fun _ : ι ↦ gaussianReal 0 1) P) (r : ℝ) :
    P {ω | ∀ i, |X ω i| ≤ r} ≤ ENNReal.ofReal (√(2 / π) * r) ^ Fintype.card ι := by
  simpa using hX.measure_forall_abs_sub_le_of_pi_gaussianReal (fun _ ↦ one_ne_zero)
    (fun _ ↦ 0) (fun _ ↦ r)

end ProbabilityTheory.HasLaw
