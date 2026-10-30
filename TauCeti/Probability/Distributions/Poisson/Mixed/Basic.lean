/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Poisson.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.GeneratingFunction

import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import TauCeti.Data.Nat.Factorial.Basic
import TauCeti.Probability.Cdf
import TauCeti.Probability.Distributions.Poisson.Basic
import TauCeti.Probability.Distributions.Poisson.Measurability

/-!
# Mixed Poisson distributions

For a measure `ρ` on the rates `ℝ≥0`, the mixed Poisson law `mixedPoissonMeasure ρ` is the count
law obtained by first drawing a rate `Λ ∼ ρ` and then a Poisson count of that rate:
`mixedPoissonMeasure ρ = ρ.bind poissonMeasure`. Gamma mixing, for instance, gives the
negative-binomial laws (`TauCeti.Probability.mixedPoissonMeasure_map_toNNReal_gammaMeasure`).

The masses, the factorial moments `E[(N)ₙ] = E[Λ ^ n]` (with `(k)ₙ = k.descFactorial n`), the mean
and the generating functions are stated for an arbitrary mixing measure and with no integrability
hypothesis: the Bochner integrals on both sides are totalized to zero together when the moment is
infinite, and companion `Integrable` equivalences say when it is finite. The cumulative masses and
the second moment need a finite mixing measure, the second moment and the variance also a finite
second moment of `Λ`, and the variance and the cdf a probability mixing measure.

## Main results

* `TauCeti.Probability.mixedPoissonMeasure_real_singleton`: the mass of `k` is
  `E[exp (-Λ) Λ ^ k / k!]`, and `TauCeti.Probability.mixedPoissonMeasure_real_Iic` gives the
  cumulative masses as the finite sum of these.
* `TauCeti.Probability.mixedPoissonMeasure_dirac`: mixing against a point mass gives back the
  Poisson law.
* `TauCeti.Probability.lintegral_descFactorial_mixedPoissonMeasure` and
  `TauCeti.Probability.integral_descFactorial_mixedPoissonMeasure`: the factorial moments are
  `E[(N)ₙ] = E[Λ ^ n]`, with `TauCeti.Probability.integrable_descFactorial_mixedPoissonMeasure_iff`
  for the equivalence of their finiteness.
* `TauCeti.Probability.integral_natCast_mixedPoissonMeasure` and
  `TauCeti.Probability.variance_mixedPoissonMeasure`: `E[N] = E[Λ]` and
  `Var N = E[Λ] + Var Λ`.
* `TauCeti.Probability.pgf_mixedPoissonMeasure`,
  `TauCeti.Probability.mgf_natCast_mixedPoissonMeasure` and
  `TauCeti.Probability.integrableExpSet_natCast_mixedPoissonMeasure`: the generating functions
  are those of `Λ` evaluated at `z - 1`, respectively `exp t - 1`, and the
  exponential-integrability domain of `N` is the preimage of that of `Λ` under `t ↦ exp t - 1`.

## References

* J. Grandell, *Mixed Poisson Processes*, Chapman & Hall (1997), ch. 2.
* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed., Wiley
  (2005), §8.3.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set
open scoped ENNReal NNReal Nat

namespace TauCeti.Probability

/-- The mixed Poisson law with mixing measure `ρ` on the rates: a Poisson count whose rate is
drawn from `ρ`. -/
def mixedPoissonMeasure (ρ : Measure ℝ≥0) : Measure ℕ :=
  ρ.bind poissonMeasure

theorem mixedPoissonMeasure_def (ρ : Measure ℝ≥0) :
    mixedPoissonMeasure ρ = ρ.bind poissonMeasure := (rfl)

variable {ρ : Measure ℝ≥0}

/-- The mixed Poisson law depends measurably on its mixing measure. -/
@[fun_prop]
theorem measurable_mixedPoissonMeasure : Measurable mixedPoissonMeasure :=
  Measure.measurable_bind' measurable_poissonMeasure

/-- A mixed Poisson law with a probability mixing measure is a probability measure. -/
instance isProbabilityMeasure_mixedPoissonMeasure [IsProbabilityMeasure ρ] :
    IsProbabilityMeasure (mixedPoissonMeasure ρ) :=
  isProbabilityMeasure_bind measurable_poissonMeasure.aemeasurable
    (ae_of_all _ fun _ ↦ inferInstance)

/-- A mixed Poisson law with a finite mixing measure is a finite measure. -/
instance isFiniteMeasure_mixedPoissonMeasure [IsFiniteMeasure ρ] :
    IsFiniteMeasure (mixedPoissonMeasure ρ) :=
  ⟨by simp [mixedPoissonMeasure_def,
    Measure.bind_apply MeasurableSet.univ measurable_poissonMeasure.aemeasurable]⟩

/-- Mixing against a point mass gives back the Poisson law of that rate. -/
@[simp]
theorem mixedPoissonMeasure_dirac (r : ℝ≥0) :
    mixedPoissonMeasure (Measure.dirac r) = poissonMeasure r :=
  Measure.dirac_bind measurable_poissonMeasure r

/-- Integration against a mixed Poisson law is iterated integration: first against the Poisson law
of rate `x`, then against the mixing measure. -/
theorem lintegral_mixedPoissonMeasure (f : ℕ → ℝ≥0∞) :
    ∫⁻ k, f k ∂mixedPoissonMeasure ρ = ∫⁻ x, ∫⁻ k, f k ∂poissonMeasure x ∂ρ :=
  Measure.lintegral_bind measurable_poissonMeasure.aemeasurable (.of_discrete)

/-- The mass of `k` under a mixed Poisson law is the Poisson mass `exp (-x) x ^ k / k!` integrated
against the mixing measure. -/
theorem mixedPoissonMeasure_singleton (ρ : Measure ℝ≥0) (k : ℕ) :
    mixedPoissonMeasure ρ {k} =
      ∫⁻ x, ENNReal.ofReal (exp (-(x : ℝ)) * (x : ℝ) ^ k / k !) ∂ρ := by
  simp only [mixedPoissonMeasure_def,
    Measure.bind_apply (measurableSet_singleton k) measurable_poissonMeasure.aemeasurable,
    poissonMeasure_singleton]

/-! ### Transfer of nonnegative Poisson integrals -/

-- Every observable treated here is a nonnegative function of the count, so each identity is first
-- proved for the lower Lebesgue integral, where `MeasureTheory.Measure.lintegral_bind` applies with
-- no integrability side conditions, and only then passed to the Bochner integral. The Poisson means
-- of the observables used are `TauCeti.Probability.hasSum_descFactorial_poissonMeasure` and
-- `TauCeti.Probability.hasSum_pow_poissonMeasure`.

variable {f : ℕ → ℝ} {g : ℝ≥0 → ℝ}

/-- If a nonnegative observable `f` has Poisson mean `g x` at every rate `x`, its lower integral
against the mixed Poisson law is that of `g` against the mixing measure. -/
private lemma lintegral_ofReal_mixedPoissonMeasure (hf : 0 ≤ f)
    (hfg : ∀ x : ℝ≥0, HasSum (fun k ↦ exp (-(x : ℝ)) * (x : ℝ) ^ k / k ! * f k) (g x)) :
    ∫⁻ k, ENNReal.ofReal (f k) ∂mixedPoissonMeasure ρ = ∫⁻ x, ENNReal.ofReal (g x) ∂ρ := by
  rw [lintegral_mixedPoissonMeasure]
  exact lintegral_congr fun x ↦ lintegral_ofReal_poissonMeasure hf x (hfg x)

private lemma nonneg_of_hasSum (hf : 0 ≤ f)
    (hfg : ∀ x : ℝ≥0, HasSum (fun k ↦ exp (-(x : ℝ)) * (x : ℝ) ^ k / k ! * f k) (g x)) :
    0 ≤ g := fun x ↦ (hfg x).nonneg fun k ↦ mul_nonneg (by positivity) (hf k)

private lemma integrable_mixedPoissonMeasure_iff (hf : 0 ≤ f) (hg : Measurable g)
    (hfg : ∀ x : ℝ≥0, HasSum (fun k ↦ exp (-(x : ℝ)) * (x : ℝ) ^ k / k ! * f k) (g x)) :
    Integrable f (mixedPoissonMeasure ρ) ↔ Integrable g ρ := by
  simp only [Integrable, AEStronglyMeasurable.of_discrete (f := f), hg.aestronglyMeasurable,
    true_and, hasFiniteIntegral_iff_ofReal (ae_of_all _ hf),
    hasFiniteIntegral_iff_ofReal (ae_of_all _ (nonneg_of_hasSum hf hfg)),
    lintegral_ofReal_mixedPoissonMeasure hf hfg]

private lemma integral_mixedPoissonMeasure_eq (hf : 0 ≤ f) (hg : Measurable g)
    (hfg : ∀ x : ℝ≥0, HasSum (fun k ↦ exp (-(x : ℝ)) * (x : ℝ) ^ k / k ! * f k) (g x)) :
    ∫ k, f k ∂mixedPoissonMeasure ρ = ∫ x, g x ∂ρ := by
  rw [integral_eq_lintegral_of_nonneg_ae (ae_of_all _ hf) AEStronglyMeasurable.of_discrete,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ (nonneg_of_hasSum hf hfg))
      hg.aestronglyMeasurable,
    lintegral_ofReal_mixedPoissonMeasure hf hfg]

/-! ### Masses and cumulative masses -/

/-- The mass of `k` under a mixed Poisson law is `E[exp (-Λ) Λ ^ k / k!]`. -/
theorem mixedPoissonMeasure_real_singleton (ρ : Measure ℝ≥0) (k : ℕ) :
    (mixedPoissonMeasure ρ).real {k} = ∫ x, (exp (-(x : ℝ)) * (x : ℝ) ^ k / k !) ∂ρ := by
  rw [measureReal_def, mixedPoissonMeasure_singleton,
    integral_eq_lintegral_of_nonneg_ae (ae_of_all _ fun _ ↦ by positivity) (by fun_prop)]

/-- A mixed Poisson law gives positive probability to a zero count. -/
theorem mixedPoissonMeasure_real_singleton_zero_pos (ρ : Measure ℝ≥0)
    [IsFiniteMeasure ρ] [NeZero ρ] : 0 < (mixedPoissonMeasure ρ).real {0} := by
  rw [mixedPoissonMeasure_real_singleton]
  have hint : Integrable (fun x : ℝ≥0 ↦ exp (-(x : ℝ))) ρ := by
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (exp_pos _).le]
    exact exp_le_one_iff.mpr (neg_nonpos.mpr x.coe_nonneg)
  simpa using integral_exp_pos hint

/-- The cumulative masses of a mixed Poisson law: `P(N ≤ n) = ∑ k ≤ n, E[exp (-Λ) Λ ^ k / k!]`. -/
theorem mixedPoissonMeasure_real_Iic (ρ : Measure ℝ≥0) [IsFiniteMeasure ρ] (n : ℕ) :
    (mixedPoissonMeasure ρ).real (Iic n) =
      ∑ k ∈ Finset.range (n + 1), ∫ x, (exp (-(x : ℝ)) * (x : ℝ) ^ k / k !) ∂ρ := by
  have hrange : ((Finset.range (n + 1) : Finset ℕ) : Set ℕ) = Iic n := by
    ext k
    simp
  simp_rw [← mixedPoissonMeasure_real_singleton, sum_measureReal_singleton, hrange]

/-- The cdf of the real cast of a mixed Poisson law at a nonnegative point. -/
theorem cdf_map_cast_mixedPoissonMeasure (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ] {x : ℝ}
    (hx : 0 ≤ x) :
    cdf ((mixedPoissonMeasure ρ).map (Nat.cast : ℕ → ℝ)) x =
      ∑ k ∈ Finset.range (⌊x⌋₊ + 1), ∫ y, (exp (-(y : ℝ)) * (y : ℝ) ^ k / k !) ∂ρ := by
  rw [Measure.cdf_map_natCast _ hx, mixedPoissonMeasure_real_Iic]

/-! ### Factorial moments, mean and variance -/

/-- The factorial moments of a mixed Poisson law, as lower integrals: `E[(N)ₙ] = E[Λ ^ n]`. This
holds whether or not the moments are finite. -/
theorem lintegral_descFactorial_mixedPoissonMeasure (ρ : Measure ℝ≥0) (n : ℕ) :
    ∫⁻ k, (k.descFactorial n : ℝ≥0∞) ∂mixedPoissonMeasure ρ = ∫⁻ x, (x : ℝ≥0∞) ^ n ∂ρ := by
  have h := lintegral_ofReal_mixedPoissonMeasure (ρ := ρ) (fun k ↦ Nat.cast_nonneg _)
    (fun x ↦ hasSum_descFactorial_poissonMeasure x n)
  simpa only [ENNReal.ofReal_natCast, ENNReal.ofReal_pow NNReal.zero_le_coe,
    ENNReal.ofReal_coe_nnreal] using h

/-- The `n`th factorial moment of a mixed Poisson law is finite exactly when the `n`th moment of
the mixing law is. -/
theorem integrable_descFactorial_mixedPoissonMeasure_iff (n : ℕ) :
    Integrable (fun k : ℕ ↦ (k.descFactorial n : ℝ)) (mixedPoissonMeasure ρ) ↔
      Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ n) ρ :=
  integrable_mixedPoissonMeasure_iff (fun k ↦ Nat.cast_nonneg _) (by fun_prop)
    (fun x ↦ hasSum_descFactorial_poissonMeasure x n)

/-- The factorial moments of a mixed Poisson law: `E[(N)ₙ] = E[Λ ^ n]`. Both sides are totalized
to zero together when the moments are infinite, so no integrability hypothesis is needed. -/
theorem integral_descFactorial_mixedPoissonMeasure (ρ : Measure ℝ≥0) (n : ℕ) :
    ∫ k, (k.descFactorial n : ℝ) ∂mixedPoissonMeasure ρ = ∫ x, (x : ℝ) ^ n ∂ρ :=
  integral_mixedPoissonMeasure_eq (fun k ↦ Nat.cast_nonneg _) (by fun_prop)
    (fun x ↦ hasSum_descFactorial_poissonMeasure x n)

/-- The mean of a mixed Poisson law is the mean of its mixing law: `E[N] = E[Λ]`. -/
theorem integral_natCast_mixedPoissonMeasure (ρ : Measure ℝ≥0) :
    ∫ k, (k : ℝ) ∂mixedPoissonMeasure ρ = ∫ x, (x : ℝ) ∂ρ := by
  simpa only [Nat.descFactorial_one, pow_one] using integral_descFactorial_mixedPoissonMeasure ρ 1

/-- A mixed Poisson count has finite mean exactly when its mixing law does. -/
theorem integrable_natCast_mixedPoissonMeasure_iff :
    Integrable (fun k : ℕ ↦ (k : ℝ)) (mixedPoissonMeasure ρ) ↔
      Integrable (fun x : ℝ≥0 ↦ (x : ℝ)) ρ := by
  simpa only [Nat.descFactorial_one, pow_one] using
    integrable_descFactorial_mixedPoissonMeasure_iff (ρ := ρ) 1

/-- A mixed Poisson count has finite variance exactly when its mixing law does. -/
theorem memLp_two_natCast_mixedPoissonMeasure_iff [IsFiniteMeasure ρ] :
    MemLp (fun k : ℕ ↦ (k : ℝ)) 2 (mixedPoissonMeasure ρ) ↔
      MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ := by
  rw [memLp_two_iff_integrable_sq AEStronglyMeasurable.of_discrete,
    memLp_two_iff_integrable_sq (by fun_prop)]
  simp_rw [← Nat.cast_pow, Nat.sq_eq_descFactorial_two_add, Nat.cast_add]
  constructor
  · intro h
    refine (integrable_descFactorial_mixedPoissonMeasure_iff 2).mp ?_
    refine Integrable.mono' h AEStronglyMeasurable.of_discrete (ae_of_all _ fun k ↦ ?_)
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
    exact le_add_of_nonneg_right (Nat.cast_nonneg k)
  · intro h
    refine ((integrable_descFactorial_mixedPoissonMeasure_iff 2).mpr h).add
      (integrable_natCast_mixedPoissonMeasure_iff.mpr ?_)
    exact ((memLp_two_iff_integrable_sq (by fun_prop)).mpr h).integrable one_le_two

/-- The second moment of a mixed Poisson law: `E[N ^ 2] = E[Λ ^ 2] + E[Λ]`. -/
theorem integral_natCast_sq_mixedPoissonMeasure [IsFiniteMeasure ρ]
    (hρ : MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ) :
    ∫ k, (k : ℝ) ^ 2 ∂mixedPoissonMeasure ρ = ∫ x, (x : ℝ) ^ 2 ∂ρ + ∫ x, (x : ℝ) ∂ρ := by
  have h2 : Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ 2) ρ :=
    (memLp_two_iff_integrable_sq (by fun_prop)).mp hρ
  simp_rw [← Nat.cast_pow, Nat.sq_eq_descFactorial_two_add, Nat.cast_add]
  rw [integral_add ((integrable_descFactorial_mixedPoissonMeasure_iff 2).mpr h2)
      (integrable_natCast_mixedPoissonMeasure_iff.mpr (hρ.integrable one_le_two)),
    integral_descFactorial_mixedPoissonMeasure, integral_natCast_mixedPoissonMeasure]

/-- **Variance of a mixed Poisson law.** A Poisson count with random rate `Λ` has variance
`E[Λ] + Var Λ`: the Poisson variance `E[Λ]` plus the extra dispersion of the rate. -/
theorem variance_mixedPoissonMeasure (ρ : Measure ℝ≥0) [IsProbabilityMeasure ρ]
    (hint : MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ) :
    variance (fun k : ℕ ↦ (k : ℝ)) (mixedPoissonMeasure ρ) =
      (∫ x, (x : ℝ) ∂ρ) + variance (fun x : ℝ≥0 ↦ (x : ℝ)) ρ := by
  rw [variance_eq_sub (memLp_two_natCast_mixedPoissonMeasure_iff.mpr hint), variance_eq_sub hint]
  simp only [Pi.pow_apply]
  rw [integral_natCast_sq_mixedPoissonMeasure hint, integral_natCast_mixedPoissonMeasure]
  ring

/-! ### Generating functions -/

/-- The probability-generating function of a mixed Poisson law at `z ≥ 0` is the
moment-generating function of the mixing law at `z - 1`: `E[z ^ N] = E[exp ((z - 1) Λ)]`. Both
sides are totalized to zero together when infinite. -/
theorem pgf_mixedPoissonMeasure (ρ : Measure ℝ≥0) {z : ℝ} (hz : 0 ≤ z) :
    pgf id (mixedPoissonMeasure ρ) z = mgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (z - 1) := by
  rw [pgf_def, mgf]
  exact integral_mixedPoissonMeasure_eq (fun k ↦ pow_nonneg hz k) (by fun_prop)
    (fun x ↦ hasSum_pow_poissonMeasure x z)

/-- The moment-generating function of the real count of a mixed Poisson law is that of its mixing
law at `exp t - 1`. -/
theorem mgf_natCast_mixedPoissonMeasure (ρ : Measure ℝ≥0) (t : ℝ) :
    mgf (fun k : ℕ ↦ (k : ℝ)) (mixedPoissonMeasure ρ) t =
      mgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (exp t - 1) := by
  simpa only [id_eq] using (pgf_exp id _ t).symm.trans (pgf_mixedPoissonMeasure ρ (exp_pos t).le)

/-- The cumulant-generating function of the real count of a mixed Poisson law is that of its
mixing law at `exp t - 1`. -/
theorem cgf_natCast_mixedPoissonMeasure (ρ : Measure ℝ≥0) (t : ℝ) :
    cgf (fun k : ℕ ↦ (k : ℝ)) (mixedPoissonMeasure ρ) t =
      cgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (exp t - 1) := by
  rw [cgf, cgf, mgf_natCast_mixedPoissonMeasure]

/-- The exponential-integrability domain of the real count of a mixed Poisson law: `exp (t N)` is
integrable exactly when `exp ((exp t - 1) Λ)` is. -/
theorem integrableExpSet_natCast_mixedPoissonMeasure (ρ : Measure ℝ≥0) :
    integrableExpSet (fun k : ℕ ↦ (k : ℝ)) (mixedPoissonMeasure ρ) =
      {t | exp t - 1 ∈ integrableExpSet (fun x : ℝ≥0 ↦ (x : ℝ)) ρ} := by
  ext t
  simp only [integrableExpSet, mem_ofPred_eq, mul_comm t, Real.exp_nat_mul]
  exact integrable_mixedPoissonMeasure_iff (fun k ↦ pow_nonneg (exp_pos t).le k) (by fun_prop)
    (fun x ↦ hasSum_pow_poissonMeasure x (exp t))

end TauCeti.Probability
