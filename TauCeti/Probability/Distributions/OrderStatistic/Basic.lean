/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Order.Lattice
public import Mathlib.Probability.Distributions.Beta
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic
public import TauCeti.Probability.Distributions.OrderStatistic.Independent
public import TauCeti.Probability.Distributions.Uniform.Basic
public import TauCeti.Probability.Quantile
import Mathlib.Algebra.Order.Interval.Set.SuccPred
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Binomial.Tail
import TauCeti.Probability.Independence.Lattice

/-!
# Laws of order statistics

The generic finite-tuple order-statistic API is in `TauCeti.Data.Fin.Tuple.OrderStatistic`.
This file uses its counting characterization and measurability to reduce order-statistic laws to
binomial tails, and specializes the extreme positions `0` and `Fin.last n` to finite sample minima
and maxima. If the entries are independent with common law `μ`, the number of entries at most
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

* `TauCeti.Probability.map_orderStatistic_zero`, `TauCeti.Probability.map_orderStatistic_last`,
  `TauCeti.Probability.hasLaw_orderStatistic_zero_iff`,
  `TauCeti.Probability.hasLaw_orderStatistic_last_iff`,
  `TauCeti.Probability.hasLaw_orderStatistic_zero_indep`,
  `TauCeti.Probability.hasLaw_orderStatistic_last_indep` — measure and `HasLaw` bridges between
  `orderStatistic 0` / `orderStatistic (Fin.last n)` and finite sample minima / maxima;
* `TauCeti.Probability.cdf_map_orderStatistic_pi` — the cumulative distribution function of an
  order statistic of independent entries with a common law, as a binomial tail sum, and
  `TauCeti.Probability.cdf_map_orderStatistic_pi_eq_regularizedIncompleteBeta` the same as an
  incomplete beta value, with the random-variable form
  `TauCeti.Probability.measureReal_setOf_orderStatistic_le_iid` and endpoint specializations at
  `0` and `Fin.last n`;
* `TauCeti.Probability.map_orderStatistic_pi_uniformMeasure` — the `k`-th order statistic of `n`
  independent unit uniforms has the law `betaMeasure (k + 1) (n - k)`, with the random-variable
  form `TauCeti.Probability.hasLaw_orderStatistic_iid_uniformMeasure` and endpoint specializations
  `TauCeti.Probability.map_orderStatistic_zero_pi_uniformMeasure` and
  `TauCeti.Probability.map_orderStatistic_last_pi_uniformMeasure`;
* `TauCeti.Probability.map_orderStatistic_pi_eq_map_betaMeasure_quantile` — the `k`-th order
  statistic of an iid sample from any real probability law `μ` is obtained by applying
  `μ.quantile` to a beta variable, with random-variable form
  `TauCeti.Probability.hasLaw_orderStatistic_iid_map_betaMeasure_quantile` and endpoint
  specializations at `0` and `Fin.last n`.

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
    binomial_tail_eq_regularizedIncompleteBeta]
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
    ⟨cdf μ t, cdf_nonneg μ t, cdf_le_one μ t⟩
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
  rw [← cdf_map_orderStatistic_pi, Measure.cdf_map _ _ (measurable_orderStatistic k).aemeasurable]
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

/-! ### Extreme positions: sample minimum and maximum -/

section LinearOrder

variable {α : Type*} [LinearOrder α] [MeasurableSpace α] {n : ℕ}

/-- Pushing any tuple measure forward along `orderStatistic 0` coincides with pushing it forward
along the tuple minimum. No measurability assumption on the order operations is needed because the
two maps are pointwise equal. -/
theorem map_orderStatistic_zero [NeZero n] (ρ : Measure (Fin n → α)) :
    ρ.map (orderStatistic 0) = ρ.map (fun x ↦ Finset.univ.inf' Finset.univ_nonempty x) :=
  congrArg ρ.map (funext orderStatistic_zero)

/-- Pushing any tuple measure forward along `orderStatistic (Fin.last n)` coincides with pushing it
forward along the tuple maximum. -/
theorem map_orderStatistic_last (ρ : Measure (Fin (n + 1) → α)) :
    ρ.map (orderStatistic (Fin.last n)) =
      ρ.map (fun x ↦ Finset.univ.sup' Finset.univ_nonempty x) :=
  congrArg ρ.map (funext orderStatistic_last)

/-- Having a given law for `orderStatistic 0` of a nonempty tuple of random variables is equivalent
to having that law for their sample minimum. -/
theorem hasLaw_orderStatistic_zero_iff {Ω : Type*} {_ : MeasurableSpace Ω} [NeZero n]
    {P : Measure Ω} {ν : Measure α} {X : Fin n → Ω → α} :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) ν P ↔
      HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω) ν P := by
  have hfun : (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) =
      fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω :=
    funext fun ω ↦ orderStatistic_zero (fun i ↦ X i ω)
  rw [hfun]

/-- Having a given law for `orderStatistic (Fin.last n)` of a tuple of random variables is
equivalent to having that law for their sample maximum. -/
theorem hasLaw_orderStatistic_last_iff {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {ν : Measure α} {X : Fin (n + 1) → Ω → α} :
    HasLaw (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω) ν P ↔
      HasLaw (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω) ν P := by
  have hfun : (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω) =
      fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω :=
    funext fun ω ↦ orderStatistic_last (fun i ↦ X i ω)
  rw [hfun]

/-- The least order statistic of independent coordinates has the pushforward of the product measure
along `orderStatistic 0`. Only `MeasurableInf₂ α` is needed because `orderStatistic 0` is the
sample minimum. -/
theorem hasLaw_orderStatistic_zero_indep {Ω : Type*} {_ : MeasurableSpace Ω} [MeasurableInf₂ α]
    [NeZero n] {P : Measure Ω} {μ : Fin n → Measure α} {X : Fin n → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic 0)) P := by
  rw [hasLaw_orderStatistic_zero_iff, map_orderStatistic_zero]
  exact hindep.hasLaw_inf' hX Finset.univ Finset.univ_nonempty

/-- The greatest order statistic of independent coordinates has the pushforward of the product
measure along `orderStatistic (Fin.last n)`. Only `MeasurableSup₂ α` is needed because
`orderStatistic (Fin.last n)` is the sample maximum. -/
theorem hasLaw_orderStatistic_last_indep {Ω : Type*} {_ : MeasurableSpace Ω} [MeasurableSup₂ α]
    {P : Measure Ω} {μ : Fin (n + 1) → Measure α} {X : Fin (n + 1) → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic (Fin.last n))) P := by
  rw [hasLaw_orderStatistic_last_iff, map_orderStatistic_last]
  exact hindep.hasLaw_sup' hX Finset.univ Finset.univ_nonempty

end LinearOrder

section Endpoints

variable {n : ℕ} {μ : Measure ℝ}

/-- For an iid sample of size `n ≠ 0` from `μ`, the least order statistic has cumulative
distribution function `1 - (1 - cdf μ t) ^ n`. -/
theorem cdf_map_orderStatistic_zero_pi_const [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic 0)) t =
      1 - (1 - cdf μ t) ^ n := by
  simp

/-- For an iid sample of size `n + 1` from `μ`, the greatest order statistic has cumulative
distribution function `cdf μ t ^ (n + 1)`. -/
theorem cdf_map_orderStatistic_last_pi_const (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin (n + 1) ↦ μ).map (orderStatistic (Fin.last n))) t =
      cdf μ t ^ (n + 1) := by
  simp

/-- For an iid family of size `n ≠ 0` with law `μ`, the least order statistic is at most `t` with
probability `1 - (1 - cdf μ t) ^ n`. -/
theorem measureReal_setOf_orderStatistic_zero_le_iid {Ω : Type*} {_ : MeasurableSpace Ω}
    [NeZero n] {P : Measure Ω} {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) μ P) (t : ℝ) :
    P.real {ω | orderStatistic 0 (fun i ↦ X i ω) ≤ t} = 1 - (1 - cdf μ t) ^ n := by
  simpa using measureReal_setOf_orderStatistic_zero_le_indep (μ := fun _ ↦ μ) hindep hX t

/-- For an iid family of size `n + 1` with law `μ`, the greatest order statistic is at most `t`
with probability `cdf μ t ^ (n + 1)`. -/
theorem measureReal_setOf_orderStatistic_last_le_iid {Ω : Type*} {_ : MeasurableSpace Ω}
    {P : Measure Ω} {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) μ P) (t : ℝ) :
    P.real {ω | orderStatistic (Fin.last n) (fun i ↦ X i ω) ≤ t} = cdf μ t ^ (n + 1) := by
  simpa using measureReal_setOf_orderStatistic_last_le_indep (μ := fun _ ↦ μ) hindep hX t

/-- The least order statistic of `n ≠ 0` independent unit uniforms has law `betaMeasure 1 n`. -/
theorem map_orderStatistic_zero_pi_uniformMeasure [NeZero n] :
    (Measure.pi fun _ : Fin n ↦ uniformMeasure 0 1).map (orderStatistic 0) =
      betaMeasure 1 n := by
  simpa using map_orderStatistic_pi_uniformMeasure (0 : Fin n)

/-- The greatest order statistic of `n + 1` independent unit uniforms has law
`betaMeasure (n + 1) 1`. -/
theorem map_orderStatistic_last_pi_uniformMeasure :
    (Measure.pi fun _ : Fin (n + 1) ↦ uniformMeasure 0 1).map (orderStatistic (Fin.last n)) =
      betaMeasure ((n : ℝ) + 1) 1 := by
  have h := map_orderStatistic_pi_uniformMeasure (Fin.last n)
  have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
  simpa [Fin.val_last, hsub] using h

/-- The least order statistic of an iid sample of size `n ≠ 0` from `μ` is the pushforward of
`betaMeasure 1 n` under `μ.quantile`, atoms included. -/
theorem map_orderStatistic_zero_pi_eq_map_betaMeasure_quantile [NeZero n] [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic 0) =
      (betaMeasure 1 n).map μ.quantile := by
  simpa using map_orderStatistic_pi_eq_map_betaMeasure_quantile (μ := μ) (0 : Fin n)

/-- The greatest order statistic of an iid sample of size `n + 1` from `μ` is the pushforward of
`betaMeasure (n + 1) 1` under `μ.quantile`, atoms included. -/
theorem map_orderStatistic_last_pi_eq_map_betaMeasure_quantile [IsProbabilityMeasure μ] :
    (Measure.pi fun _ : Fin (n + 1) ↦ μ).map (orderStatistic (Fin.last n)) =
      (betaMeasure ((n : ℝ) + 1) 1).map μ.quantile := by
  have h := map_orderStatistic_pi_eq_map_betaMeasure_quantile (μ := μ) (Fin.last n)
  have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
  simpa [Fin.val_last, hsub] using h

end Endpoints

end TauCeti.Probability
