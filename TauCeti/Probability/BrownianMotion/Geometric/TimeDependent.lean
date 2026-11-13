/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.Geometric.Basic
public import TauCeti.Probability.BrownianMotion.Integral.Wiener
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Independence.Integration

/-!
# Geometric Brownian motion with time-dependent coefficients

For a pre-Brownian motion `B`, an initial value `s`, and deterministic drift `μ` and
volatility `σ` with `σ` square integrable on every finite horizon, the process

`S_t = s * exp (∫₀ᵗ (μ_u - σ_u² / 2) du + ∫₀ᵗ σ_u dB_u)`

(`ProbabilityTheory.IsPreBrownianReal.timeDependentGeometricBrownianMotion`) is the explicit
solution of the linear stochastic differential equation `dS_t = μ_t S_t dt + σ_t S_t dB_t`.
Here `∫₀ᵗ σ dB` is the deterministic Wiener integral, a Gaussian `L²` class; the process uses
its chosen representative at each time. That `S` solves the differential equation requires
Itô calculus and is not proved here. For constant coefficients `S` agrees almost surely with
`TauCeti.Probability.geometricBrownianMotion` at every time.

For `s > 0`, `log S_t` is Gaussian with mean `log s + ∫₀ᵗ (μ - σ² / 2)` and variance
`∫₀ᵗ σ²`, so `S_t` is log-normal. Every real absolute moment is
`E|S_t|^q = |s|^q exp (q ∫₀ᵗ μ + q (q - 1) / 2 ∫₀ᵗ σ²)`, and it factors as
`E|ξ|^q` times the same exponential when the initial value `ξ` is random and known at time
zero. Relative to a filtration for which `B` is Brownian, the conditional expectation of
`S_t` at an earlier time `u` is `exp (∫ᵤᵗ μ) S_u`; with `μ` equal to a deterministic short rate
this is the martingale property of the discounted asset.

No moment of the initial value, positivity of `σ` or regularity of `μ` beyond integrability
is assumed. Since the Wiener integral is defined up to null sets and no completeness of the
filtration is assumed, adaptedness of the chosen representatives is not asserted.

## Main declarations

* `ProbabilityTheory.IsPreBrownianReal.timeDependentGeometricBrownianMotion`: the process.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_log_timeDependentGeometricBrownianMotion`:
  the Gaussian law of `log S_t`.
* `ProbabilityTheory.IsPreBrownianReal.integral_abs_rpow_timeDependentGeometricBrownianMotion`:
  the absolute moments of every real order.
* `ProbabilityTheory.IsPreBrownianReal.timeDependentGeometricBrownianMotion_const`: agreement
  with geometric Brownian motion for constant coefficients.
* `TauCeti.Probability.IsFilteredPreBrownianReal.condExp_timeDependentGeometricBrownianMotion`:
  `E[S_t | ℱ_u] = exp (∫ᵤᵗ μ) S_u`.
* `IsFilteredPreBrownianReal.integral_abs_rpow_timeDependentGeometricBrownianMotion_random_initial`:
  absolute moments for an initial value known at time zero.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §5.6, for linear stochastic differential equations.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §4.4, for generalized geometric Brownian motion and Itô integrals of deterministic
  integrands.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set Filter
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {μ σ : ℝ≥0 → ℝ}

/-- The drift integral `∫₀ᵀ (μ - σ² / 2)` splits as `∫₀ᵀ μ - (∫₀ᵀ σ²) / 2`. -/
private theorem integral_sub_sq_div_two {T : ℝ≥0} (hμ : Integrable μ (timeMeasure T))
    (hσ : MemLp σ 2 (timeMeasure T)) :
    ∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure T =
      (∫ u, μ u ∂timeMeasure T) - (∫ u, σ u ^ 2 ∂timeMeasure T) / 2 := by
  rw [integral_sub hμ (hσ.integrable_sq.div_const 2), integral_div]

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {s : ℝ} {μ σ : ℝ≥0 → ℝ}

/-- **Geometric Brownian motion with time-dependent coefficients.** For deterministic drift
`μ` and volatility `σ`, square integrable on every horizon, this is
`S_t = s * exp (∫₀ᵗ (μ_u - σ_u² / 2) du + ∫₀ᵗ σ_u dB_u)`, where `∫₀ᵗ σ dB` is the
chosen representative of the Wiener integral of `σ` on `(0,t]`. The drift integral is a
Bochner integral; results about its value assume that `μ` is integrable. -/
def timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (s : ℝ) (μ σ : ℝ≥0 → ℝ)
    (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) (ω : Ω) : ℝ :=
  s * exp ((∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t) + hB.wienerIntegral t ((hσ t).toLp σ) ω)

/-- The defining formula of `timeDependentGeometricBrownianMotion`. -/
theorem timeDependentGeometricBrownianMotion_def (hB : IsPreBrownianReal B P) (s : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) (ω : Ω) :
    hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω =
      s * exp ((∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t) +
        hB.wienerIntegral t ((hσ t).toLp σ) ω) := (rfl)

/-- For a positive initial value, the process is positive at every time and sample point. -/
theorem timeDependentGeometricBrownianMotion_pos (hB : IsPreBrownianReal B P) (hs : 0 < s)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) (ω : Ω) :
    0 < hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω :=
  mul_pos hs (exp_pos _)

/-- The process starts almost surely at its initial value. -/
theorem ae_timeDependentGeometricBrownianMotion_zero (hB : IsPreBrownianReal B P) (s : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) :
    ∀ᵐ ω ∂P, hB.timeDependentGeometricBrownianMotion s μ σ hσ 0 ω = s := by
  filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
  rw [timeDependentGeometricBrownianMotion_def, wienerIntegral_zero, hω]
  simp

/-- From time `u` to time `t` the process is multiplied by the exponential of the increments
of the drift integral and of the Wiener integral. -/
theorem timeDependentGeometricBrownianMotion_eq_mul (hB : IsPreBrownianReal B P) (s : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (u t : ℝ≥0) (ω : Ω) :
    hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω =
      hB.timeDependentGeometricBrownianMotion s μ σ hσ u ω *
        exp ((∫ v, (μ v - σ v ^ 2 / 2) ∂timeMeasure t) -
            (∫ v, (μ v - σ v ^ 2 / 2) ∂timeMeasure u) +
          (hB.wienerIntegral t ((hσ t).toLp σ) ω - hB.wienerIntegral u ((hσ u).toLp σ) ω)) := by
  rw [timeDependentGeometricBrownianMotion_def, timeDependentGeometricBrownianMotion_def,
    mul_assoc, ← exp_add]
  ring_nf

/-- An absolute power of the process is `|s| ^ q` times an exponential of an affine function
of the Wiener integral. This holds for every initial value and every real exponent. -/
theorem abs_rpow_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (s q : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) (ω : Ω) :
    |hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω| ^ q =
      |s| ^ q * exp (q * (∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t) +
        q * hB.wienerIntegral t ((hσ t).toLp σ) ω) := by
  rw [timeDependentGeometricBrownianMotion_def, abs_mul, abs_of_pos (exp_pos _),
    mul_rpow (abs_nonneg s) (exp_pos _).le, ← exp_mul, mul_comm _ q, mul_add]

/-- **The Gaussian law of the logarithm.** For `s > 0`, `log S_t` is Gaussian with mean
`log s + ∫₀ᵗ (μ - σ² / 2)` and variance `∫₀ᵗ σ²`. -/
theorem hasLaw_log_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P)
    (hs : 0 < s) (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) :
    HasLaw (fun ω ↦ log (hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω))
      (gaussianReal (log s + ∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t)
        (∫ u, σ u ^ 2 ∂timeMeasure t).toNNReal) P := by
  have hS : (fun ω ↦ log (hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω)) =
      (· + (log s + ∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t)) ∘
        hB.wienerIntegral t ((hσ t).toLp σ) := by
    ext ω
    rw [timeDependentGeometricBrownianMotion_def, log_mul hs.ne' (exp_pos _).ne', log_exp,
      Function.comp_apply]
    ring
  rw [hS]
  refine (HasLaw.comp ⟨by fun_prop, ?_⟩ (hB.hasLaw_wienerIntegral_toLp (hσ t)))
  rw [gaussianReal_map_add_const, zero_add]

/-- **The law of geometric Brownian motion with time-dependent coefficients.** For `s > 0`,
`S_t` is log-normal with log-mean `log s + ∫₀ᵗ (μ - σ² / 2)` and log-variance `∫₀ᵗ σ²`. -/
theorem hasLaw_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (hs : 0 < s)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) :
    HasLaw (hB.timeDependentGeometricBrownianMotion s μ σ hσ t)
      (logNormalMeasure (log s + ∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t)
        (∫ u, σ u ^ 2 ∂timeMeasure t).toNNReal) P := by
  have hS : hB.timeDependentGeometricBrownianMotion s μ σ hσ t =
      exp ∘ fun ω ↦ log (hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω) := by
    ext ω
    rw [Function.comp_apply, exp_log (hB.timeDependentGeometricBrownianMotion_pos hs μ σ hσ t ω)]
  rw [hS, logNormalMeasure_map_exp]
  exact HasLaw.comp ⟨by fun_prop, rfl⟩
    (hB.hasLaw_log_timeDependentGeometricBrownianMotion hs μ σ hσ t)

/-- Exponentials of multiples of Wiener integrals are integrable. -/
private theorem integrable_exp_mul_wienerIntegral (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    {f : ℝ≥0 → ℝ} (hf : MemLp f 2 (timeMeasure T)) (q : ℝ) :
    Integrable (fun ω ↦ exp (q * hB.wienerIntegral T (hf.toLp f) ω)) P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact mgf_pos_iff.mp (mgf_gaussianReal (hB.hasLaw_wienerIntegral_toLp hf) q ▸ exp_pos _)

/-- The exponential moments of a Wiener integral are those of its Gaussian law. -/
private theorem integral_exp_mul_wienerIntegral (hB : IsPreBrownianReal B P) {T : ℝ≥0}
    {f : ℝ≥0 → ℝ} (hf : MemLp f 2 (timeMeasure T)) (q : ℝ) :
    ∫ ω, exp (q * hB.wienerIntegral T (hf.toLp f) ω) ∂P =
      exp (q ^ 2 * (∫ t, f t ^ 2 ∂timeMeasure T) / 2) := by
  rw [← mgf, mgf_gaussianReal (hB.hasLaw_wienerIntegral_toLp hf),
    Real.coe_toNNReal _ (integral_nonneg fun _ ↦ sq_nonneg _)]
  ring_nf

/-- Every real absolute power of the process is integrable. -/
theorem integrable_abs_rpow_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P)
    (s q : ℝ) (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) :
    Integrable (fun ω ↦ |hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω| ^ q) P := by
  simp_rw [abs_rpow_timeDependentGeometricBrownianMotion, exp_add]
  exact ((hB.integrable_exp_mul_wienerIntegral (hσ t) q).const_mul _).const_mul _

/-- **The moments of geometric Brownian motion with time-dependent coefficients.** For every
initial value and real exponent `q`,
`E|S_t|^q = |s|^q exp (q ∫₀ᵗ μ + q (q - 1) / 2 ∫₀ᵗ σ²)`. -/
theorem integral_abs_rpow_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P)
    (s q : ℝ) {μ σ : ℝ≥0 → ℝ} (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) {t : ℝ≥0}
    (hμ : Integrable μ (timeMeasure t)) :
    ∫ ω, |hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω| ^ q ∂P =
      |s| ^ q * exp (q * (∫ u, μ u ∂timeMeasure t) +
        q * (q - 1) * (∫ u, σ u ^ 2 ∂timeMeasure t) / 2) := by
  simp_rw [abs_rpow_timeDependentGeometricBrownianMotion, exp_add, integral_const_mul,
    hB.integral_exp_mul_wienerIntegral, ← exp_add, integral_sub_sq_div_two hμ (hσ t)]
  ring_nf

/-- The process is integrable at every time. -/
theorem integrable_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (s : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) :
    Integrable (hB.timeDependentGeometricBrownianMotion s μ σ hσ t) P := by
  have h := (hB.integrable_exp_mul_wienerIntegral (hσ t) 1).const_mul
    (s * exp (∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t))
  refine h.congr (ae_of_all _ fun ω ↦ ?_)
  simp only [timeDependentGeometricBrownianMotion_def, one_mul, exp_add, mul_assoc]

/-- **The mean of geometric Brownian motion with time-dependent coefficients.**
`E[S_t] = s exp (∫₀ᵗ μ)`. -/
theorem integral_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (s : ℝ)
    {μ σ : ℝ≥0 → ℝ} (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) {t : ℝ≥0}
    (hμ : Integrable μ (timeMeasure t)) :
    ∫ ω, hB.timeDependentGeometricBrownianMotion s μ σ hσ t ω ∂P =
      s * exp (∫ u, μ u ∂timeMeasure t) := by
  have h := hB.integral_exp_mul_wienerIntegral (hσ t) 1
  simp only [one_mul, one_pow] at h
  simp_rw [timeDependentGeometricBrownianMotion_def, exp_add, ← mul_assoc, integral_const_mul,
    h, mul_assoc, ← exp_add, integral_sub_sq_div_two hμ (hσ t)]
  ring_nf

/-- The process has finite moments of every finite order. -/
theorem memLp_timeDependentGeometricBrownianMotion (hB : IsPreBrownianReal B P) (s : ℝ)
    (μ σ : ℝ≥0 → ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) (t : ℝ≥0) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (hB.timeDependentGeometricBrownianMotion s μ σ hσ t) p P := by
  have hm : AEStronglyMeasurable (hB.timeDependentGeometricBrownianMotion s μ σ hσ t) P :=
    (hB.integrable_timeDependentGeometricBrownianMotion s μ σ hσ t).aestronglyMeasurable
  by_cases hp0 : p = 0
  · simpa [hp0] using hm
  · apply (integrable_norm_rpow_iff hm hp0 hp).mp
    simpa only [Real.norm_eq_abs] using
      hB.integrable_abs_rpow_timeDependentGeometricBrownianMotion s p.toReal μ σ hσ t

/-- **Constant coefficients.** With constant drift `μ` and volatility `σ`, the process agrees
almost surely at each time with the geometric Brownian motion
`s * exp ((μ - σ² / 2) t + σ B_t)`. -/
theorem timeDependentGeometricBrownianMotion_const (hB : IsPreBrownianReal B P) (s μ σ : ℝ)
    (hσ : ∀ t, MemLp (fun _ : ℝ≥0 ↦ σ) 2 (timeMeasure t)) (t : ℝ≥0) :
    hB.timeDependentGeometricBrownianMotion s (fun _ ↦ μ) (fun _ ↦ σ) hσ t =ᵐ[P]
      geometricBrownianMotion s μ σ B t := by
  have hc : (hσ t).toLp (fun _ ↦ σ) = Lp.const 2 (timeMeasure t) σ := MemLp.toLp_const _ _ _
  filter_upwards [Lp.coeFn_smul σ (hB.toL2 t), hB.coeFn_toL2 t] with ω h₁ h₂
  rw [timeDependentGeometricBrownianMotion_def, geometricBrownianMotion_def, hc,
    wienerIntegral_const, h₁, Pi.smul_apply, h₂, integral_const, smul_eq_mul, smul_eq_mul]
  simp [measureReal_def, mul_comm]

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ} {μ σ : ℝ≥0 → ℝ}

/-- **Conditional expectation of geometric Brownian motion with time-dependent coefficients.**
For a Brownian motion relative to `ℱ` and `u ≤ t`, `E[S_t | ℱ_u] = exp (∫ᵤᵗ μ) S_u`, with
`∫ᵤᵗ μ = ∫₀ᵗ μ - ∫₀ᵘ μ`. For `μ` a deterministic short rate this says that the asset
discounted by the money-market account is a martingale in conditional-expectation form. -/
theorem condExp_timeDependentGeometricBrownianMotion (hW : IsFilteredPreBrownianReal ℱ W P)
    (s : ℝ) (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) {u t : ℝ≥0} (hut : u ≤ t)
    (hμ : Integrable μ (timeMeasure t)) :
    P[hW.timeDependentGeometricBrownianMotion s μ σ hσ t | ℱ u] =ᵐ[P]
      fun ω ↦ exp ((∫ v, μ v ∂timeMeasure t) - ∫ v, μ v ∂timeMeasure u) *
        hW.timeDependentGeometricBrownianMotion s μ σ hσ u ω := by
  have := (hW.hasLaw_eval 0).isProbabilityMeasure
  set Φ : Ω → ℝ :=
    ⇑(hW.wienerIntegral t ((hσ t).toLp σ)) - ⇑(hW.wienerIntegral u ((hσ u).toLp σ)) with hΦ
  set c := (∫ v, (μ v - σ v ^ 2 / 2) ∂timeMeasure t) - ∫ v, (μ v - σ v ^ 2 / 2) ∂timeMeasure u
  set Y : Ω → ℝ := fun ω ↦ exp (c + Φ ω)
  -- `S_t = S_u Y`, where `S_u` is known at `u` and `Y` is independent of `ℱ u`.
  have hsplit : hW.timeDependentGeometricBrownianMotion s μ σ hσ t =
      hW.timeDependentGeometricBrownianMotion s μ σ hσ u * Y :=
    funext (hW.timeDependentGeometricBrownianMotion_eq_mul s μ σ hσ u t)
  have hind := hW.indep_wienerIntegral_sub hut
    (((hσ t).coeFn_toLp.filter_mono (ae_mono (timeMeasure_mono hut))).trans
      (hσ u).coeFn_toLp.symm)
  have hlaw := hW.hasLaw_wienerIntegral_toLp_sub hut (hσ t) (hσ u)
  have hY : Integrable Y P := by
    refine ((mgf_pos_iff.mp (mgf_gaussianReal hlaw 1 ▸ exp_pos _)).const_mul (exp c)).congr
      (ae_of_all _ fun ω ↦ ?_)
    simp [Y, hΦ, exp_add]
  have hSu : AEStronglyMeasurable[ℱ u] (hW.timeDependentGeometricBrownianMotion s μ σ hσ u) P :=
    (continuous_const.mul (continuous_exp.comp (continuous_const.add continuous_id)))
      |>.comp_aestronglyMeasurable (hW.aestronglyMeasurable_wienerIntegral (ℱ.le u)
        (fun v hv ↦ ((hW.adapted v).mono (ℱ.mono hv) le_rfl).aestronglyMeasurable) _)
  -- The Gaussian increment `Φ` has variance `∫ᵤᵗ σ²`, so `E[Y] = exp (∫ᵤᵗ μ)`.
  have hintY : ∫ ω, Y ω ∂P = exp ((∫ v, μ v ∂timeMeasure t) - ∫ v, μ v ∂timeMeasure u) := by
    have h : ∫ ω, exp (Φ ω) ∂P = exp (((∫ v, σ v ^ 2 ∂timeMeasure t) -
        ∫ v, σ v ^ 2 ∂timeMeasure u).toNNReal / 2) := by
      simpa [mgf, hΦ] using mgf_gaussianReal hlaw 1
    have hle : (∫ v, σ v ^ 2 ∂timeMeasure u) ≤ ∫ v, σ v ^ 2 ∂timeMeasure t :=
      integral_mono_measure (timeMeasure_mono hut) (ae_of_all _ fun _ ↦ sq_nonneg _)
        (hσ t).integrable_sq
    simp_rw [Y, exp_add, integral_const_mul, h, ← exp_add,
      Real.coe_toNNReal _ (sub_nonneg.2 hle), c, integral_sub_sq_div_two hμ (hσ t),
      integral_sub_sq_div_two (hμ.mono_measure (timeMeasure_mono hut)) (hσ u)]
    ring_nf
  have hΦmeas : Measurable Φ :=
    (Lp.stronglyMeasurable _).measurable.sub (Lp.stronglyMeasurable _).measurable
  rw [hsplit]
  filter_upwards [condExp_mul_of_aestronglyMeasurable_left hSu
      (hsplit ▸ hW.integrable_timeDependentGeometricBrownianMotion s μ σ hσ t) hY,
    condExp_indep_eq (f := Y) hΦmeas.comap_le (ℱ.le u)
      (measurable_exp.comp (measurable_const.add (comap_measurable Φ))).stronglyMeasurable
      hind] with ω h₁ h₂
  rw [h₁, Pi.mul_apply, h₂, hintY, mul_comm]

/-- **Moments with a random initial value.** For an initial value `ξ` known at time zero and
every real `q`, `E|S_t|^q = E|ξ|^q exp (q ∫₀ᵗ μ + q (q - 1) / 2 ∫₀ᵗ σ²)`. No moment of `ξ`
is assumed: both sides vanish when `|ξ|^q` is not integrable, by the convention of the
Bochner integral. -/
theorem integral_abs_rpow_timeDependentGeometricBrownianMotion_random_initial
    (hW : IsFilteredPreBrownianReal ℱ W P) {ξ : Ω → ℝ} (hξ : Measurable[ℱ 0] ξ) (q : ℝ)
    (hσ : ∀ t, MemLp σ 2 (timeMeasure t)) {t : ℝ≥0} (hμ : Integrable μ (timeMeasure t)) :
    ∫ ω, |hW.timeDependentGeometricBrownianMotion (ξ ω) μ σ hσ t ω| ^ q ∂P =
      (∫ ω, |ξ ω| ^ q ∂P) * exp (q * (∫ u, μ u ∂timeMeasure t) +
        q * (q - 1) * (∫ u, σ u ^ 2 ∂timeMeasure t) / 2) := by
  set A := ∫ u, (μ u - σ u ^ 2 / 2) ∂timeMeasure t
  set X : Ω → ℝ := ⇑(hW.wienerIntegral t ((hσ t).toLp σ))
  set Φ : Ω → ℝ := X - ⇑(hW.wienerIntegral 0 ((hσ 0).toLp σ)) with hΦ
  have hind : Indep (MeasurableSpace.comap Φ inferInstance) (ℱ 0) P :=
    hW.indep_wienerIntegral_sub (zero_le : (0 : ℝ≥0) ≤ t)
      (ae_iff.2 (by simp))
  have hXΦ : X =ᵐ[P] Φ := by
    filter_upwards [Lp.coeFn_zero ℝ 2 P] with ω hω
    simp only [hΦ, Pi.sub_apply, IsPreBrownianReal.wienerIntegral_zero]
    rw [hω, Pi.zero_apply, sub_zero]
  have hξm : Measurable fun ω ↦ |ξ ω| ^ q :=
    (by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q).comp (hξ.mono (ℱ.le 0) le_rfl)
  have hZm : Measurable[MeasurableSpace.comap Φ inferInstance] fun ω ↦ exp (q * A + q * Φ ω) :=
    measurable_exp.comp (measurable_const.add (measurable_const.mul (comap_measurable Φ)))
  have hindep : IndepFun (fun ω ↦ |ξ ω| ^ q) (fun ω ↦ exp (q * A + q * Φ ω)) P := by
    rw [IndepFun_iff_Indep]
    exact indep_of_indep_of_le_right (indep_of_indep_of_le_left hind.symm
      (((by fun_prop : Measurable fun x : ℝ ↦ |x| ^ q).comp hξ).comap_le)) hZm.comap_le
  have hΦm : Measurable Φ :=
    (Lp.stronglyMeasurable _).measurable.sub (Lp.stronglyMeasurable _).measurable
  have hcongr : (fun ω ↦ |ξ ω| ^ q * exp (q * A + q * X ω)) =ᵐ[P]
      fun ω ↦ |ξ ω| ^ q * exp (q * A + q * Φ ω) := by
    filter_upwards [hXΦ] with ω hω
    rw [hω]
  simp_rw [IsPreBrownianReal.abs_rpow_timeDependentGeometricBrownianMotion]
  rw [integral_congr_ae hcongr, hindep.integral_fun_mul_eq_mul_integral hξm.aestronglyMeasurable
    (measurable_exp.comp (measurable_const.add (measurable_const.mul hΦm))).aestronglyMeasurable]
  congr 1
  have hX : ∫ ω, exp (q * A + q * Φ ω) ∂P = ∫ ω, exp (q * A + q * X ω) ∂P :=
    integral_congr_ae (by filter_upwards [hXΦ] with ω hω; rw [hω])
  simp_rw [hX, exp_add, integral_const_mul, X, hW.integral_exp_mul_wienerIntegral, ← exp_add, A,
    integral_sub_sq_div_two hμ (hσ t)]
  ring_nf

end TauCeti.Probability.IsFilteredPreBrownianReal
