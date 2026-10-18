/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Data.Fin.Tuple.OrderStatistic
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Binomial.Basic
import TauCeti.Probability.Distributions.Binomial.Tail

/-!
# Laws of order statistics

The generic finite-tuple order-statistic API is in `TauCeti.Data.Fin.Tuple.OrderStatistic`.
This file uses its counting characterization and measurability to reduce order-statistic laws to
binomial tails. If the entries are independent with common law `μ`, the number of entries at most
`t` is binomial with success probability `F(t) = cdf μ t`, so the `k`-th order statistic has
cumulative distribution function

`∑ j ∈ Finset.Icc (k + 1) n, n.choose j * F(t) ^ j * (1 - F(t)) ^ (n - j)`,

for every law `μ`, atoms included. By the binomial tail identity this sum is the regularized
incomplete beta value `I_{F(t)}(k + 1, n - k)`. For unit uniform entries `F(t) = t` on `[0, 1]`,
so the `k`-th order statistic of `n` independent unit uniforms has the beta law with parameters
`k + 1` and `n - k`.

The laws are stated for the product measure `Measure.pi fun _ => μ`, the law of a tuple of
independent `μ`-distributed entries, with random-variable forms for an independent family
`X : Fin n → Ω → ℝ`.

## Main results

* `TauCeti.Probability.cdf_map_orderStatistic_pi` — the cumulative distribution function of an
  order statistic of independent entries with a common law, as a binomial tail sum, and
  `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta` the same as an
  incomplete beta value, with the random-variable form
  `TauCeti.Probability.measureReal_setOf_orderStatistic_le_iid`;
* `TauCeti.Probability.map_orderStatistic_pi_uniformMeasure` — the `k`-th order statistic of `n`
  independent unit uniforms has the law `betaMeasure (k + 1) (n - k)`, with the random-variable
  form `TauCeti.Probability.hasLaw_orderStatistic_iid_uniformMeasure`.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §2.1, for the
  distribution of a single order statistic and its incomplete beta form.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set Finset

namespace TauCeti.Probability

section Law

variable {n : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {μ : Measure ℝ}
  {X : Fin n → Ω → ℝ}

/-- **The law of an order statistic as an incomplete beta value.** If the `n` coordinates are
independent with common law `μ`, the `k`-th order statistic has cumulative distribution function
`I_{F(t)}(k + 1, n - k)`, where `F = cdf μ`. -/
theorem cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta [IsProbabilityMeasure μ]
    (k : Fin n) (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin n => μ).map (orderStatistic k)) t =
      regularizedIncompleteBeta ((k : ℝ) + 1) ((n : ℝ) - k) (cdf μ t) := by
  have hset : orderStatistic k ⁻¹' Iic t =
      {x : Fin n → ℝ | (k : ℕ) + 1 ≤ #{i | x i ∈ Iic t}} := by
    rw [preimage_orderStatistic_Iic]
    simp_rw [Set.mem_Iic, Nat.lt_iff_add_one_le]
  rw [cdf_eq_real, map_measureReal_apply (measurable_orderStatistic k) measurableSet_Iic, hset,
    (hasLaw_card_filter_mem_pi (s := Iic t) measurableSet_Iic).measureReal_eq
      (p := fun j => (k : ℕ) + 1 ≤ j) .of_discrete, Fintype.card_fin,
    binomial_tail_eq_regularizedIncompleteBeta (by omega), cdf_eq_real]
  congr 1 <;> push_cast <;> ring

/-- **The law of an order statistic.** If the `n` coordinates are independent with common law
`μ`, the `k`-th order statistic (counted from `0`) is at most `t` with probability
`∑ j ∈ Finset.Icc (k + 1) n, n.choose j * F(t) ^ j * (1 - F(t)) ^ (n - j)`, where
`F = cdf μ`: the probability that more than `k` coordinates are at most `t`. Atoms are
allowed. -/
theorem cdf_map_orderStatistic_pi [IsProbabilityMeasure μ] (k : Fin n) (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin n => μ).map (orderStatistic k)) t =
      ∑ j ∈ Finset.Icc ((k : ℕ) + 1) n,
        (n.choose j : ℝ) * cdf μ t ^ j * (1 - cdf μ t) ^ (n - j) := by
  have h := sum_Icc_choose_mul_pow_eq_regularizedIncompleteBeta (m := (k : ℕ) + 1) (n := n)
    (by omega) ⟨cdf μ t, cdf_nonneg μ t, cdf_le_one μ t⟩
  rw [cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta, h]
  congr 1 <;> push_cast <;> ring

/-- The random-variable form of `TauCeti.Probability.cdf_map_orderStatistic_pi`: the `k`-th order
statistic of an independent family of `n` real random variables with common law `μ` is at most
`t` with probability `∑ j ∈ Finset.Icc (k + 1) n, n.choose j * F(t) ^ j * (1 - F(t)) ^ (n - j)`,
where `F = cdf μ`. -/
theorem measureReal_setOf_orderStatistic_le_iid [IsProbabilityMeasure μ]
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (k : Fin n) (t : ℝ) :
    P.real {ω | orderStatistic k (fun i => X i ω) ≤ t} =
      ∑ j ∈ Finset.Icc ((k : ℕ) + 1) n,
        (n.choose j : ℝ) * cdf μ t ^ j * (1 - cdf μ t) ^ (n - j) := by
  have hpi := hindep.hasLaw_pi hlaw
  rw [← cdf_map_orderStatistic_pi, cdf_eq_real,
    map_measureReal_apply (measurable_orderStatistic k) measurableSet_Iic]
  exact hpi.measureReal_eq (p := fun x => orderStatistic k x ≤ t)
    (measurable_orderStatistic k measurableSet_Iic)

/-- **Order statistics of uniform samples are beta distributed.** The `k`-th order statistic
(counted from `0`) of `n` independent uniform variables on the unit interval has the beta law
with parameters `k + 1` and `n - k`. -/
theorem map_orderStatistic_pi_uniformMeasure (k : Fin n) :
    (Measure.pi fun _ : Fin n => uniformMeasure 0 1).map (orderStatistic k) =
      betaMeasure ((k : ℝ) + 1) ((n : ℝ) - k) := by
  have : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have ha : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hb : (0 : ℝ) < (n : ℝ) - k := by
    have := k.isLt
    rw [sub_pos]
    exact_mod_cast this
  have := isProbabilityMeasureBeta ha hb
  refine (Measure.cdf_eq_iff _ _).1 ?_
  ext t
  rw [cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta, cdf_betaMeasure_eq ha hb,
    cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · rw [regularizedIncompleteBeta_eq_zero_of_nonpos ha.ne' _ le_rfl,
      regularizedIncompleteBeta_eq_zero_of_nonpos ha.ne' _ h0]
  · rw [regularizedIncompleteBeta_eq_one_of_one_le ha.le hb le_rfl,
      regularizedIncompleteBeta_eq_one_of_one_le ha.le hb h1]
  · simp

/-- The random-variable form of `TauCeti.Probability.map_orderStatistic_pi_uniformMeasure`: the
`k`-th order statistic of an independent family of `n` uniform variables on the unit interval has
the beta law with parameters `k + 1` and `n - k`. -/
theorem hasLaw_orderStatistic_iid_uniformMeasure (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) (uniformMeasure 0 1) P) (k : Fin n) :
    HasLaw (fun ω => orderStatistic k fun i => X i ω)
      (betaMeasure ((k : ℝ) + 1) ((n : ℝ) - k)) P := by
  rw [← map_orderStatistic_pi_uniformMeasure]
  exact (hasLaw_map (measurable_orderStatistic k).aemeasurable).comp (hindep.hasLaw_pi hlaw)

end Law

end TauCeti.Probability
