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
* `TauCeti.Probability.mixedPoissonMeasure_eq_sum_dirac`: the law is the weighted sum of Dirac
  measures with these masses.
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
* the corresponding results in `ProbabilityTheory.HasLaw` give the factorial moments, mean,
  variance, generating functions, and exact exponential-integrability criterion for a random
  variable with the mixed Poisson law.

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

/-- A mixed Poisson law is the weighted sum of Dirac measures whose coefficients are the
integrated Poisson masses. -/
theorem mixedPoissonMeasure_eq_sum_dirac (ρ : Measure ℝ≥0) :
    mixedPoissonMeasure ρ = Measure.sum fun k : ℕ ↦
      (∫⁻ x, ENNReal.ofReal (exp (-(x : ℝ)) * (x : ℝ) ^ k / k !) ∂ρ) • Measure.dirac k := by
  rw [← Measure.sum_smul_dirac (mixedPoissonMeasure ρ)]
  simp_rw [mixedPoissonMeasure_singleton]

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
  simp only [integrableExpSet, mem_ofPred_eq, mul_comm t, Real.exp_natCast_mul]
  exact integrable_mixedPoissonMeasure_iff (fun k ↦ pow_nonneg (exp_pos t).le k) (by fun_prop)
    (fun x ↦ hasSum_pow_poissonMeasure x (exp t))

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : Ω → ℕ} {ρ : Measure ℝ≥0}

/-- A mixed Poisson random variable has a finite factorial moment exactly when the corresponding
moment of its mixing law is finite. -/
theorem integrable_descFactorial_mixedPoissonMeasure_iff
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (n : ℕ) :
    Integrable (fun ω ↦ ((N ω).descFactorial n : ℝ)) P ↔
      Integrable (fun x : ℝ≥0 ↦ (x : ℝ) ^ n) ρ := by
  rw [← TauCeti.Probability.integrable_descFactorial_mixedPoissonMeasure_iff,
    ← hN.map_eq, integrable_map_measure (by fun_prop) hN.aemeasurable]
  rfl

/-- The factorial moments of a mixed Poisson random variable, as lower integrals, are the
ordinary moments of its mixing law, including when they are infinite. -/
theorem lintegral_descFactorial_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (n : ℕ) :
    ∫⁻ ω, ((N ω).descFactorial n : ℝ≥0∞) ∂P = ∫⁻ x, (x : ℝ≥0∞) ^ n ∂ρ := by
  rw [hN.lintegral_comp (f := fun k ↦ (k.descFactorial n : ℝ≥0∞)) .of_discrete,
    TauCeti.Probability.lintegral_descFactorial_mixedPoissonMeasure]

/-- The factorial moments of a mixed Poisson random variable are the ordinary moments of its
mixing law. Both sides use the totalized Bochner integral. -/
theorem integral_descFactorial_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (n : ℕ) :
    ∫ ω, ((N ω).descFactorial n : ℝ) ∂P = ∫ x, (x : ℝ) ^ n ∂ρ := by
  calc
    _ = ∫ k, (k.descFactorial n : ℝ) ∂mixedPoissonMeasure ρ := by
      simpa only [Function.comp_def] using
        hN.integral_comp (f := fun k ↦ (k.descFactorial n : ℝ)) .of_discrete
    _ = _ := TauCeti.Probability.integral_descFactorial_mixedPoissonMeasure ρ n

/-- A mixed Poisson random variable is integrable after casting to `ℝ` exactly when the identity
is integrable under its mixing law. -/
theorem integrable_natCast_mixedPoissonMeasure_iff
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) :
    Integrable (fun ω ↦ (N ω : ℝ)) P ↔ Integrable (fun x : ℝ≥0 ↦ (x : ℝ)) ρ := by
  simpa only [Nat.descFactorial_one, pow_one] using
    hN.integrable_descFactorial_mixedPoissonMeasure_iff 1

/-- The expectation of a mixed Poisson random variable is the expectation of its mixing law. -/
theorem integral_natCast_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) :
    ∫ ω, (N ω : ℝ) ∂P = ∫ x, (x : ℝ) ∂ρ := by
  simpa only [Nat.descFactorial_one, pow_one] using
    hN.integral_descFactorial_mixedPoissonMeasure 1

/-- The real cast of a mixed Poisson random variable is square-integrable exactly when the
identity is square-integrable under its finite mixing law. -/
theorem memLp_two_natCast_mixedPoissonMeasure_iff [IsFiniteMeasure ρ]
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) :
    MemLp (fun ω ↦ (N ω : ℝ)) 2 P ↔ MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ := by
  rw [← TauCeti.Probability.memLp_two_natCast_mixedPoissonMeasure_iff,
    ← hN.map_eq, memLp_map_measure_iff (by fun_prop) hN.aemeasurable]
  rfl

/-- For a finite mixing measure with square-integrable rate, the second moment of a mixed Poisson
random variable is the second moment plus the mean of its mixing law. -/
theorem integral_natCast_sq_mixedPoissonMeasure [IsFiniteMeasure ρ]
    (hN : HasLaw N (mixedPoissonMeasure ρ) P)
    (hρ : MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ) :
    ∫ ω, (N ω : ℝ) ^ 2 ∂P = ∫ x, (x : ℝ) ^ 2 ∂ρ + ∫ x, (x : ℝ) ∂ρ := by
  calc
    _ = ∫ k, (k : ℝ) ^ 2 ∂mixedPoissonMeasure ρ := by
      simpa only [Function.comp_def] using
        hN.integral_comp (f := fun k ↦ (k : ℝ) ^ 2) .of_discrete
    _ = _ := TauCeti.Probability.integral_natCast_sq_mixedPoissonMeasure hρ

/-- For a probability mixing law with square-integrable rate, the variance of a mixed Poisson
random variable is the mean plus the variance of its mixing law. -/
theorem variance_mixedPoissonMeasure [IsProbabilityMeasure ρ]
    (hN : HasLaw N (mixedPoissonMeasure ρ) P)
    (hρ : MemLp (fun x : ℝ≥0 ↦ (x : ℝ)) 2 ρ) :
    variance (fun ω ↦ (N ω : ℝ)) P =
      (∫ x, (x : ℝ) ∂ρ) + variance (fun x : ℝ≥0 ↦ (x : ℝ)) ρ := by
  rw [← TauCeti.Probability.variance_mixedPoissonMeasure ρ hρ, ← hN.map_eq,
    variance_map (by fun_prop) hN.aemeasurable]
  rfl

/-- At `z ≥ 0`, the probability-generating function of a mixed Poisson random variable is the
moment-generating function of its mixing law at `z - 1`. -/
theorem pgf_mixedPoissonMeasure (hN : HasLaw N (mixedPoissonMeasure ρ) P)
    {z : ℝ} (hz : 0 ≤ z) :
    pgf N P z = mgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (z - 1) :=
  (TauCeti.Probability.HasLaw.pgf_eq hN z).trans
    (TauCeti.Probability.pgf_mixedPoissonMeasure ρ hz)

/-- The moment-generating function of the real cast of a mixed Poisson random variable is that of
its mixing law at `exp t - 1`. -/
theorem mgf_natCast_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (t : ℝ) :
    mgf (fun ω ↦ (N ω : ℝ)) P t =
      mgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (Real.exp t - 1) := by
  rw [← pgf_exp]
  exact hN.pgf_mixedPoissonMeasure (Real.exp_pos t).le

/-- The cumulant-generating function of the real cast of a mixed Poisson random variable is that
of its mixing law at `exp t - 1`. -/
theorem cgf_natCast_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (t : ℝ) :
    cgf (fun ω ↦ (N ω : ℝ)) P t =
      cgf (fun x : ℝ≥0 ↦ (x : ℝ)) ρ (Real.exp t - 1) := by
  rw [cgf, cgf, hN.mgf_natCast_mixedPoissonMeasure]

/-- The exponential-integrability domain of the real cast of a mixed Poisson random variable is
the preimage of the mixing law's domain under `t ↦ exp t - 1`. -/
theorem integrableExpSet_natCast_mixedPoissonMeasure
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) :
    integrableExpSet (fun ω ↦ (N ω : ℝ)) P =
      {t | Real.exp t - 1 ∈ integrableExpSet (fun x : ℝ≥0 ↦ (x : ℝ)) ρ} := by
  rw [← TauCeti.Probability.integrableExpSet_natCast_mixedPoissonMeasure]
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq]
  rw [← hN.map_eq, integrable_map_measure (by fun_prop) hN.aemeasurable]
  rfl

/-- The real cast of a mixed Poisson random variable has a finite exponential moment at `t`
exactly when the mixing law has one at `exp t - 1`. -/
theorem integrable_exp_mul_natCast_mixedPoissonMeasure_iff
    (hN : HasLaw N (mixedPoissonMeasure ρ) P) (t : ℝ) :
    Integrable (fun ω ↦ Real.exp (t * (N ω : ℝ))) P ↔
      Real.exp t - 1 ∈ integrableExpSet (fun x : ℝ≥0 ↦ (x : ℝ)) ρ := by
  have hmem := Set.ext_iff.mp hN.integrableExpSet_natCast_mixedPoissonMeasure t
  simpa only [integrableExpSet, Set.mem_ofPred_eq] using hmem

end ProbabilityTheory.HasLaw
