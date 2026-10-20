/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.OrderStatistic.Independent
public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Quantile
import Mathlib.Algebra.Order.Interval.Set.SuccPred
import TauCeti.Probability.Distributions.Beta.Cdf
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
  form `TauCeti.Probability.hasLaw_orderStatistic_iid_uniformMeasure`;
* `TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile` — the `k`-th order
  statistic of an iid sample from any real probability law `μ` is obtained by applying
  `μ.quantile` to a beta variable, with random-variable form
  `TauCeti.Probability.hasLaw_orderStatistic_iid_map_betaMeasure_quantile`.

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
  rw [cdf_map_orderStatistic_pi_eq_poissonBinomial, poissonBinomialMeasure_const,
    Fintype.card_fin, ← Set.Ici_add_one_eq_Ioi, Set.Ici,
    binomial_tail_eq_regularizedIncompleteBeta (by omega)]
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

/-! ### Quantile construction -/

/-- **Quantile construction of an order statistic.** The `k`-th order statistic of an iid sample
from a real probability law `μ` has the law obtained by applying `μ.quantile` to a beta variable
with parameters `k + 1` and `n - k`. This allows atoms and discontinuous quantiles. -/
theorem map_orderStatistic_pi_eq_map_betaMeasure_quantile [IsProbabilityMeasure μ] (k : Fin n) :
    (Measure.pi fun _ : Fin n => μ).map (orderStatistic k) =
      (betaMeasure ((k : ℝ) + 1) ((n : ℝ) - k)).map μ.quantile := by
  let U := uniformMeasure 0 1
  have hU : U = volume.restrict (Ioo (0 : ℝ) 1) := by
    dsimp [U]
    rw [uniformMeasure_eq_smul]
    norm_num
    exact MeasureTheory.restrict_Ioo_eq_restrict_Ioc.symm
  have hquantile : U.map μ.quantile = μ := by
    rw [hU]
    exact μ.map_quantile_volume_Ioo
  have hmemU : ∀ᵐ u ∂U, u ∈ Ioo (0 : ℝ) 1 := by
    rw [hU]
    exact ae_restrict_mem measurableSet_Ioo
  have hmem : ∀ᵐ u ∂Measure.pi (fun _ : Fin n => U), ∀ i, u i ∈ Ioo (0 : ℝ) 1 :=
    ae_all_iff.mpr fun i => Measure.tendsto_eval_ae_ae.eventually hmemU
  calc
    (Measure.pi fun _ : Fin n => μ).map (orderStatistic k) =
        ((Measure.pi fun _ : Fin n => U).map fun u i => μ.quantile (u i)).map
          (orderStatistic k) := by
      rw [Measure.pi_map_pi fun _ => μ.measurable_quantile.aemeasurable, hquantile]
    _ = (Measure.pi fun _ : Fin n => U).map
        (fun u => orderStatistic k (fun i => μ.quantile (u i))) := by
      rw [Measure.map_map (measurable_orderStatistic k) (by fun_prop)]
      exact Measure.map_congr (.of_forall fun _ => rfl)
    _ = (Measure.pi fun _ : Fin n => U).map (fun u => μ.quantile (orderStatistic k u)) := by
      apply Measure.map_congr
      filter_upwards [hmem] with u hu
      exact orderStatistic_comp_of_monotoneOn μ.quantile μ.monotoneOn_quantile hu k
    _ = ((Measure.pi fun _ : Fin n => U).map (orderStatistic k)).map μ.quantile := by
      rw [Measure.map_map μ.measurable_quantile (measurable_orderStatistic k)]
      exact Measure.map_congr (.of_forall fun _ => rfl)
    _ = (betaMeasure ((k : ℝ) + 1) ((n : ℝ) - k)).map μ.quantile := by
      dsimp [U]
      rw [map_orderStatistic_pi_uniformMeasure]

/-- The random-variable form of
`TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile`: the `k`-th order
statistic of an iid sample from `μ` has the beta-quantile pushforward law. -/
theorem hasLaw_orderStatistic_iid_map_betaMeasure_quantile [IsProbabilityMeasure μ]
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (k : Fin n) :
    HasLaw (fun ω => orderStatistic k fun i => X i ω)
      ((betaMeasure ((k : ℝ) + 1) ((n : ℝ) - k)).map μ.quantile) P := by
  rw [← map_orderStatistic_pi_eq_map_betaMeasure_quantile]
  exact (hasLaw_map (measurable_orderStatistic k).aemeasurable).comp (hindep.hasLaw_pi hlaw)

end Law

end TauCeti.Probability
