/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.Examples.IntegerWalk.Basic
public import TauCeti.Probability.MarkovChain.Occupation
public import TauCeti.Analysis.SpecificLimits.CentralBinomial
public import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# Infinite mean return time of the symmetric integer walk

The symmetric nearest-neighbor walk has infinite extended mean positive return time.
The value at a missing return is infinity, not zero. The result is stated separately
from recurrence, so it can be combined with the return-series criterion to classify
the walk as null recurrent.

Central binomial probabilities tend to zero. Their Cesàro means therefore vanish,
whereas the occupation law identifies their limit with the reciprocal extended mean
return time. A finite mean would give a positive reciprocal, a contradiction.
No invariant-probability characterization is needed.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press (1997), §§1.6 and 1.10.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped ENNReal

namespace TauCeti.Probability

/-- Return probabilities of the symmetric integer walk tend to zero, including along
odd times, when they vanish identically. -/
theorem tendsto_integerWalk_pow_real_self (p : unitInterval) (hp : (p : ℝ) = 1 / 2)
    (x : ℤ) :
    Tendsto (fun n : ℕ => ((integerWalk p ^ n) x).real {x}) atTop (𝓝 0) := by
  have heven (n : ℕ) : ((integerWalk p ^ (2 * n)) x).real {x} =
      (n.centralBinom : ℝ) / 4 ^ n := by
    rw [measureReal_def, integerWalk_pow_even_apply_self]
    have hpow : ((2 * n).choose n : ℝ) * (p : ℝ) ^ n * (1 - (p : ℝ)) ^ n =
        (n.centralBinom : ℝ) / 4 ^ n := by
      rw [hp, mul_assoc, ← mul_pow, show (1 / 2 : ℝ) * (1 - 1 / 2) = 1 / 4 by norm_num,
        div_pow, one_pow, mul_one_div, Nat.centralBinom_eq_two_mul_choose]
    rw [hpow, ENNReal.toReal_ofReal (by positivity)]
  have hbound (n : ℕ) : ((integerWalk p ^ n) x).real {x} ≤
      ((n / 2).centralBinom : ℝ) / 4 ^ (n / 2) := by
    have hm := Nat.mod_lt n (by omega : 0 < 2)
    rcases (by omega : n = 2 * (n / 2) ∨ n = 2 * (n / 2) + 1) with h | h
    · conv_lhs => rw [h]
      rw [heven]
    · conv_lhs => rw [h]
      simp only [measureReal_def, integerWalk_pow_odd_apply_self, ENNReal.toReal_zero]
      positivity
  exact squeeze_zero (fun _ => measureReal_nonneg) hbound
    (TauCeti.tendsto_centralBinom_div_four_pow.comp (Nat.tendsto_div_const_atTop (by omega)))

private theorem tendsto_integerWalk_integral_visitCount_div (p : unitInterval)
    (hp : (p : ℝ) = 1 / 2) (x : ℤ) :
    Tendsto (fun n : ℕ => ∫ ω, (visitCount (fun k => ω (k + 1)) x n : ℝ) / n
      ∂markovChainLaw (Measure.dirac x) (integerWalk p)) atTop (𝓝 0) := by
  classical
  let P := markovChainLaw (Measure.dirac x) (integerWalk p)
  have hint (n : ℕ) :
      ∫ ω, (visitCount (fun k => ω (k + 1)) x n : ℝ) ∂P =
        ∑ i ∈ Finset.range n, ((integerWalk p ^ (i + 1)) x).real {x} := by
    have hsum (ω : ℕ → ℤ) : (visitCount (fun k => ω (k + 1)) x n : ℝ) =
        ∑ i ∈ Finset.range n, {ω | ω (i + 1) = x}.indicator (fun _ => (1 : ℝ)) ω := by
      simp only [visitCount_eq_count, Nat.count_eq_card_filter_range, Finset.card_filter,
        Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Set.indicator_apply,
        Set.mem_ofPred_eq]
    simp_rw [hsum]
    rw [integral_finsetSum _ (fun i _ => (integrable_const (1 : ℝ)).indicator
      (measurableSet_eq_fun (measurable_pi_apply (i + 1)) measurable_const))]
    apply Finset.sum_congr rfl
    intro i hi
    rw [integral_indicator (measurableSet_eq_fun (measurable_pi_apply (i + 1)) measurable_const),
      integral_const, smul_eq_mul, mul_one]
    simp only [measureReal_def, Measure.restrict_apply_univ, P]
    rw [Measure.markovChainLaw_setOf_apply_eq_comp, Measure.dirac_bind (Kernel.measurable _)]
  dsimp only [P] at hint
  simp_rw [integral_div, hint]
  simpa only [div_eq_inv_mul, Function.comp_apply] using
    ((tendsto_integerWalk_pow_real_self p hp x).comp (tendsto_add_atTop_nat 1)).cesaro

/-- The extended mean first positive return of the symmetric integer walk is infinite.
The first return starts at one, and a missing return contributes infinity. -/
theorem integerWalk_meanReturnTime_eq_top (p : unitInterval) (hp : (p : ℝ) = 1 / 2)
    (x : ℤ) : (integerWalk p).meanReturnTime x = ∞ := by
  classical
  let P := markovChainLaw (Measure.dirac x) (integerWalk p)
  by_contra hfinite
  have hpos : 0 < ((integerWalk p).meanReturnTime x)⁻¹.toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.mpr hfinite)
      (ENNReal.inv_ne_top.mpr (ne_zero_of_lt
        (lt_of_lt_of_le zero_lt_one (Kernel.one_le_meanReturnTime (κ := integerWalk p) (x := x)))))
  have hLLN := (HasLaw.id (μ := P)).tendsto_integral_visitCount_div_markovChainLaw_dirac
  exact hpos.ne' (tendsto_nhds_unique hLLN (tendsto_integerWalk_integral_visitCount_div p hp x))

end TauCeti.Probability

namespace ProbabilityTheory.HasLaw

open TauCeti.Probability

/-- Every realization of the symmetric integer walk has infinite extended mean first
positive return. No topology on its probability space is required. -/
theorem lintegral_integerWalk_hittingAfter_eq_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X : Ω → ℕ → ℤ}
    {p : unitInterval} {x : ℤ}
    (hX : HasLaw X (markovChainLaw (Measure.dirac x) (integerWalk p)) P)
    (hp : (p : ℝ) = 1 / 2) :
    (∫⁻ ω, ENat.toENNReal (hittingAfter (fun n ω => X ω n) {x} 1 ω) ∂P) = ∞ := by
  have hτ : Measurable (hittingAfter (fun n (ω : ℕ → ℤ) => ω n) {x} 1) :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (f := Filtration.piLE (X := fun _ : ℕ => ℤ)) (measurableSet_singleton x)).measurable'
  have hm := (measurable_of_countable (fun t : WithTop ℕ => ENat.toENNReal t)).comp hτ
  -- Entrance times depend only on the coordinate path; evaluation after composition
  -- therefore identifies the integrand with the canonical path functional.
  convert (hX.lintegral_comp hm.aemeasurable).trans
    (by simpa only [Kernel.meanReturnTime_def, Function.comp_def] using
      integerWalk_meanReturnTime_eq_top p hp x) using 1
  apply lintegral_congr
  intro ω
  simp only [Function.comp_apply, hittingAfter_def]

end ProbabilityTheory.HasLaw
