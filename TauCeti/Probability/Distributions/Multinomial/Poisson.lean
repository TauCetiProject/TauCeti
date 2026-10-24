/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Multinomial.Basic
public import TauCeti.Probability.Distributions.Poisson.Sum
public import TauCeti.Probability.HasLaw
import TauCeti.Geometry.Convex.ConvexSpace.NNReal

/-!
# Poisson allocation and conditioning

Allocating a Poisson total among finitely many categories with fixed multinomial weights
produces independent Poisson counts. Conversely, conditioning independent Poisson counts on
their total gives a multinomial law with weights proportional to their rates.

The measure identity uses `Measure.bind` for allocation and `Measure.pi` for independence.
Zero category weights and zero rates are allowed; conditioning is asserted to be a probability
law only when the conditioning event has positive mass.

## References

* N. L. Johnson, A. W. Kemp, S. Kotz, *Univariate Discrete Distributions*, 3rd ed.,
  Wiley (2005), Chapter 4.
-/

public section

noncomputable section

open Convexity MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace TauCeti.Probability

variable {ι : Type*} [Fintype ι]

private theorem poisson_mul_multinomialWeight (r : ℝ≥0) (p : StdSimplex ℝ≥0 ι)
    (k : ι → ℕ) :
    poissonMeasure r {∑ i, k i} * multinomialWeight p.weights k =
      ∏ i, poissonMeasure (r * p.weights i) {k i} := by
  classical
  have htotal : ∑ i, ((r * p.weights i : ℝ≥0) : ℝ) = r := by
    simpa only [NNReal.coe_mul] using p.sum_mul_coe_weights r
  have hcoeff : (Nat.multinomial Finset.univ k : ℝ) *
      ∏ i, ((k i).factorial : ℝ) = ((∑ i, k i).factorial : ℝ) := by
    rw [mul_comm]
    exact_mod_cast Nat.multinomial_spec Finset.univ k
  have hreal :
      (Real.exp (-(r : ℝ)) * (r : ℝ) ^ (∑ i, k i) / (∑ i, k i).factorial) *
          multinomialWeightReal p.weights k =
        ∏ i, (Real.exp (-((r * p.weights i : ℝ≥0) : ℝ)) *
          ((r * p.weights i : ℝ≥0) : ℝ) ^ k i / (k i).factorial) := by
    rw [multinomialWeightReal_def, Finset.prod_div_distrib,
      Finset.prod_mul_distrib, ← Real.exp_sum, Finset.sum_neg_distrib, htotal]
    simp only [NNReal.coe_mul, mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    have hfac : ((∑ i, k i).factorial : ℝ) ≠ 0 := by positivity
    have hprod : (∏ i, ((k i).factorial : ℝ)) ≠ 0 := by positivity
    apply (eq_div_iff hprod).2
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_eq_iff hfac).2
    rw [← hcoeff]
    ring
  rw [poissonMeasure_singleton, ← ENNReal.ofReal_toReal (multinomialWeight_ne_top _ _),
    multinomialWeight_toReal, ← ENNReal.ofReal_mul (by positivity), hreal]
  simp only [poissonMeasure_singleton]
  exact ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity)

/-- A Poisson total allocated with multinomial weights yields independent Poisson counts,
with category rates equal to the total rate times the weights. This includes rate zero and
zero-weight categories. -/
@[simp]
theorem bind_poissonMeasure_multinomialMeasure (r : ℝ≥0) (p : StdSimplex ℝ≥0 ι) :
    (poissonMeasure r).bind (fun n => multinomialMeasure n p) =
      Measure.pi (fun i => poissonMeasure (r * p.weights i)) := by
  classical
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.bind_apply (measurableSet_singleton k) (.of_discrete),
    lintegral_countable', Measure.pi_singleton]
  simp only [multinomialMeasure_singleton, ite_mul, zero_mul]
  rw [tsum_eq_single (∑ i, k i)]
  · simpa [mul_comm] using poisson_mul_multinomialWeight r p k
  · intro n hn
    simp [Ne.symm hn]

/-- On the event that the total is `n`, the product of Poisson laws with rates `r * pᵢ`
is the multinomial law scaled by the probability of that Poisson total. The identity also
holds at `r = 0`, including the null positive-total events. -/
theorem restrict_pi_poissonMeasure_mul_weights (r : ℝ≥0) (p : StdSimplex ℝ≥0 ι) (n : ℕ) :
    (Measure.pi (fun i => poissonMeasure (r * p.weights i))).restrict {k | ∑ i, k i = n} =
      poissonMeasure r {n} • multinomialMeasure n p := by
  classical
  apply Measure.ext_of_singleton
  intro k
  rw [Measure.restrict_apply (measurableSet_singleton k), Measure.smul_apply,
    smul_eq_mul, multinomialMeasure_singleton]
  by_cases hk : ∑ i, k i = n
  · rw [ite_eq_left hk, Set.singleton_inter_of_mem (s := {l : ι → ℕ | ∑ i, l i = n}) hk]
    rw [Measure.pi_singleton, ← poisson_mul_multinomialWeight, hk]
  · rw [Set.singleton_inter_of_notMem (s := {l : ι → ℕ | ∑ i, l i = n}) hk]
    simp [hk]

/-- Conditioning independent Poisson counts of rates `r * pᵢ` on a total with nonzero
probability gives the multinomial law. At rate zero, this includes conditioning on total zero. -/
theorem cond_pi_poissonMeasure_mul_weights {r : ℝ≥0} (p : StdSimplex ℝ≥0 ι) (n : ℕ)
    (hn : poissonMeasure r {n} ≠ 0) :
    cond (Measure.pi (fun i => poissonMeasure (r * p.weights i))) {k | ∑ i, k i = n} =
      multinomialMeasure n p := by
  have := isProbabilityMeasure_multinomialMeasure n p
  have hmass : (Measure.pi (fun i => poissonMeasure (r * p.weights i)))
      {k | ∑ i, k i = n} = poissonMeasure r {n} := by
    simpa using congrArg (fun μ : Measure (ι → ℕ) => μ Set.univ)
      (restrict_pi_poissonMeasure_mul_weights r p n)
  rw [ProbabilityTheory.cond, hmass,
    restrict_pi_poissonMeasure_mul_weights, smul_smul,
    ENNReal.inv_mul_cancel hn (measure_ne_top _ _), one_smul]

/-- Every total has positive probability at a positive Poisson rate, so conditioning gives
the multinomial law for every natural total. Zero-weight categories remain zero almost surely. -/
theorem cond_pi_poissonMeasure_mul_weights_of_pos {r : ℝ≥0} (hr : 0 < r)
    (p : StdSimplex ℝ≥0 ι) (n : ℕ) :
    cond (Measure.pi (fun i => poissonMeasure (r * p.weights i))) {k | ∑ i, k i = n} =
      multinomialMeasure n p := by
  apply cond_pi_poissonMeasure_mul_weights
  rw [poissonMeasure_singleton, ne_eq, ENNReal.ofReal_eq_zero]
  exact not_le.mpr (by positivity)

/-- Independent Poisson counts, conditioned on their total, are multinomial with normalized
rate weights. The simplex parameter is specified by its coordinates, so no choice of a
normalization or of off-domain weights enters the result. -/
theorem cond_pi_poissonMeasure {r : ι → ℝ≥0} (hr : 0 < ∑ i, r i)
    (p : StdSimplex ℝ≥0 ι) (hp : ∀ i, p.weights i = r i / ∑ j, r j) (n : ℕ) :
    cond (Measure.pi (fun i => poissonMeasure (r i))) {k | ∑ i, k i = n} =
      multinomialMeasure n p := by
  have hrate (i : ι) : (∑ j, r j) * p.weights i = r i := by
    rw [hp i, mul_div_cancel₀ _ hr.ne']
  simpa only [hrate] using cond_pi_poissonMeasure_mul_weights_of_pos hr p n

/-- Conditioning independent Poisson random variables on their total gives the multinomial
law with weights proportional to their rates. -/
theorem _root_.ProbabilityTheory.iIndepFun.hasLaw_cond_sum_poissonMeasure
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : ι → Ω → ℕ} {r : ι → ℝ≥0}
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) (poissonMeasure (r i)) P)
    (hr : 0 < ∑ i, r i) (p : StdSimplex ℝ≥0 ι)
    (hp : ∀ i, p.weights i = r i / ∑ j, r j) (n : ℕ) :
    HasLaw (fun ω i => X i ω) (multinomialMeasure n p)
      (cond P {ω | ∑ i, X i ω = n}) := by
  have h := (hindep.hasLaw_pi hlaw).cond (s := {k | ∑ i, k i = n}) (.of_discrete)
  rw [cond_pi_poissonMeasure hr p hp n] at h
  exact h

/-- If all rates vanish, a positive total is impossible and conditioning on it gives the
zero measure. No normalized category weights are needed. -/
@[simp]
theorem cond_pi_poissonMeasure_zero_of_ne_zero {n : ℕ} (hn : n ≠ 0) :
    cond (Measure.pi (fun _ : ι => Measure.dirac 0)) {k | ∑ i, k i = n} = 0 := by
  apply cond_eq_zero_of_meas_eq_zero
  have hmass := congrArg (fun μ : Measure ℕ => μ {n})
    (map_sum_pi_poissonMeasure (fun _ : ι => 0))
  rw [Measure.map_apply (.of_discrete) (measurableSet_singleton n),
    Set.preimage_singleton] at hmass
  simpa [poissonMeasure_zero, poissonMeasure_singleton, hn] using hmass

-- Simplify before `Finset.sum_eq_zero_iff` rewrites the conditioning event.
/-- At all-zero rates, conditioning on total zero gives the point mass at the zero count
vector, without introducing normalized weights for the zero vector of rates. -/
@[simp↓]
theorem cond_pi_poissonMeasure_zero :
    cond (Measure.pi (fun _ : ι => poissonMeasure 0)) {k | ∑ i, k i = 0} =
      Measure.dirac 0 := by
  classical
  apply Measure.ext_of_singleton
  intro k
  have hzero : (Measure.pi (fun _ : ι => poissonMeasure 0)) {k | ∑ i, k i = 0} = 1 := by
    have hmass := congrArg (fun μ : Measure ℕ => μ {0})
      (map_sum_pi_poissonMeasure (fun _ : ι => 0))
    rw [Measure.map_apply (.of_discrete) (measurableSet_singleton 0),
      Set.preimage_singleton] at hmass
    simpa [poissonMeasure_singleton] using hmass
  rw [cond_apply' (measurableSet_singleton k), hzero, inv_one, one_mul]
  by_cases hk : k = 0
  · subst k
    simp [Measure.pi_singleton]
  · have hsum : ∑ i, k i ≠ 0 := by simpa [funext_iff] using hk
    rw [Set.inter_singleton_of_notMem (s := {l : ι → ℕ | ∑ i, l i = 0}) hsum]
    simp [hk]

/-- A count vector whose law is a Poisson mixture of multinomials has jointly independent
coordinates. -/
theorem _root_.ProbabilityTheory.HasLaw.iIndepFun_of_poisson_multinomial
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → (ι → ℕ)} {r : ℝ≥0} {p : StdSimplex ℝ≥0 ι}
    (hX : HasLaw X ((poissonMeasure r).bind (fun n => multinomialMeasure n p)) P) :
    iIndepFun (fun i ω => X ω i) P := by
  rw [bind_poissonMeasure_multinomialMeasure] at hX
  let _ := hX.isProbabilityMeasure
  exact (iIndepFun_iff_hasLaw_pi_pi
    (fun i => (measurePreserving_eval (fun i => poissonMeasure (r * p.weights i)) i).hasLaw.comp
      hX)).2 hX

end TauCeti.Probability
