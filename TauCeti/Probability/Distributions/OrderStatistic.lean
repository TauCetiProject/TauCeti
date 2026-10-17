/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Tuple.Sort
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta
public import TauCeti.Probability.Distributions.Uniform.Basic
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Binomial.Basic
import TauCeti.Probability.Distributions.Binomial.Tail

/-!
# Order statistics

The `k`-th order statistic of a tuple `x : Fin n → α` in a linear order is the entry in
position `k` once the entries of `x` are sorted increasingly, keeping repeated values with their
multiplicity. Positions are counted from `0`, so position `0` holds the minimum and position
`Fin.last _` the maximum. The sort is `Tuple.sort`, and the order statistics of `x` are the
entries of the sorted tuple `x ∘ Tuple.sort x`.

The order statistics are characterized by counting: `orderStatistic k x ≤ t` exactly
when more than `k` entries of `x` are at most `t`. This makes the order statistics measurable,
and it reduces their laws to binomial tails. If the entries are independent with common law `μ`,
the number of entries at most `t` is binomial with success probability `F(t) = cdf μ t`, so the
`k`-th order statistic has cumulative distribution function

`∑ j ∈ Finset.Icc (k + 1) n, n.choose j * F(t) ^ j * (1 - F(t)) ^ (n - j)`,

for every law `μ`, atoms included. By the binomial tail identity this sum is the regularized
incomplete beta value `I_{F(t)}(k + 1, n - k)`. For unit uniform entries `F(t) = t` on `[0, 1]`,
so the `k`-th order statistic of `n` independent unit uniforms has the beta law with parameters
`k + 1` and `n - k`.

The laws are stated for the product measure `Measure.pi fun _ => μ`, the law of a tuple of
independent `μ`-distributed entries, with random-variable forms for an independent family
`X : Fin n → Ω → ℝ`.

## Main definitions

* `TauCeti.Probability.orderStatistic` — the `k`-th order statistic of a finite tuple.

## Main results

* `TauCeti.Probability.orderStatistic_le_iff` — the counting characterization, with
  `TauCeti.Probability.orderStatistic_lt_iff` its strict form;
* `TauCeti.Probability.orderStatistic_zero`, `TauCeti.Probability.orderStatistic_last` — the
  extreme order statistics are the minimum and the maximum;
* `TauCeti.Probability.measurable_orderStatistic` — measurability;
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

section Order

variable {α : Type*} [LinearOrder α] {n : ℕ}

/-- The `k`-th **order statistic** of a tuple `x : Fin n → α`: the entry in position `k` once the
entries of `x` are sorted increasingly, repeated values kept with their multiplicity. Positions
are counted from `0`, so `orderStatistic 0 x` is the least entry of `x` and
`orderStatistic (Fin.last _) x` the greatest. -/
def orderStatistic (k : Fin n) (x : Fin n → α) : α :=
  x (Tuple.sort x k)

theorem orderStatistic_def (k : Fin n) (x : Fin n → α) :
    orderStatistic k x = x (Tuple.sort x k) := (rfl)

/-- The order statistics of a tuple increase with their position. -/
theorem monotone_orderStatistic (x : Fin n → α) : Monotone fun k => orderStatistic k x :=
  Tuple.monotone_sort x

/-- The order statistics of a tuple do not depend on the order in which its entries are
listed. -/
@[simp]
theorem orderStatistic_comp_perm (k : Fin n) (x : Fin n → α) (σ : Equiv.Perm (Fin n)) :
    orderStatistic k (x ∘ σ) = orderStatistic k x := by
  simpa only [orderStatistic_def, Function.comp_apply] using
    congrFun (Tuple.comp_perm_comp_sort_eq_comp_sort (f := x) (σ := σ)) k

/-- **The counting characterization of order statistics.** The `k`-th order statistic of `x` is
at most `t` exactly when more than `k` entries of `x` are at most `t`. -/
theorem orderStatistic_le_iff (k : Fin n) (x : Fin n → α) (t : α) :
    orderStatistic k x ≤ t ↔ (k : ℕ) < #{i | x i ≤ t} := by
  have hcard : #{i | x (Tuple.sort x i) ≤ t} = #{i | x i ≤ t} :=
    Finset.card_equiv (Tuple.sort x) (by simp)
  rw [← hcard]
  exact (Tuple.lt_card_le_iff_apply_le_of_monotone (Tuple.monotone_sort x)).symm

/-- The strict form of `TauCeti.Probability.orderStatistic_le_iff`: the `k`-th order statistic of
`x` is below `t` exactly when more than `k` entries of `x` are below `t`. -/
theorem orderStatistic_lt_iff (k : Fin n) (x : Fin n → α) (t : α) :
    orderStatistic k x < t ↔ (k : ℕ) < #{i | x i < t} := by
  have hcard : #{i | x (Tuple.sort x i) < t} = #{i | x i < t} :=
    Finset.card_equiv (Tuple.sort x) (by simp)
  rw [← hcard]
  exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone (Tuple.monotone_sort x)).symm

/-- The least order statistic is the minimum of the entries. -/
@[simp]
theorem orderStatistic_zero (x : Fin (n + 1) → α) :
    orderStatistic 0 x = Finset.univ.inf' Finset.univ_nonempty x := by
  refine eq_of_forall_ge_iff fun t => ?_
  rw [orderStatistic_le_iff, Finset.inf'_le_iff, Fin.val_zero, Finset.card_pos,
    Finset.filter_nonempty_iff]

/-- The greatest order statistic is the maximum of the entries. -/
@[simp]
theorem orderStatistic_last (x : Fin (n + 1) → α) :
    orderStatistic (Fin.last n) x = Finset.univ.sup' Finset.univ_nonempty x := by
  refine eq_of_forall_ge_iff fun t => ?_
  have hcard : n < #{i | x i ≤ t} ↔ #{i | x i ≤ t} = Fintype.card (Fin (n + 1)) := by
    have := Finset.card_le_univ (Finset.univ.filter fun i => x i ≤ t)
    rw [Fintype.card_fin] at this ⊢
    omega
  rw [orderStatistic_le_iff, Fin.val_last, hcard, Finset.card_eq_iff_eq_univ,
    Finset.filter_eq_self, Finset.sup'_le_iff]

variable [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α] [OrderTopology α]
  [SecondCountableTopology α]

/-- Each order statistic is a measurable function of the tuple. -/
@[fun_prop]
theorem measurable_orderStatistic (k : Fin n) :
    Measurable (orderStatistic k : (Fin n → α) → α) := by
  refine measurable_of_Iic fun t => ?_
  have hcount : Measurable fun x : Fin n → α => #{i | x i ≤ t} := by
    simp_rw [Finset.card_filter]
    exact Finset.measurable_sum _ fun i _ =>
      Measurable.ite (measurableSet_le (measurable_pi_apply i) measurable_const) measurable_const
        measurable_const
  have hset : orderStatistic k ⁻¹' Iic t = (fun x : Fin n → α => #{i | x i ≤ t}) ⁻¹' Ioi k := by
    ext x
    simp [orderStatistic_le_iff]
  rw [hset]
  exact hcount (measurableSet_Ioi)

end Order

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
    ext x
    simp [orderStatistic_le_iff]
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
