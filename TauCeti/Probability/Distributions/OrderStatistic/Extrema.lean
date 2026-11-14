/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Bernoulli
public import Mathlib.Probability.Distributions.Exponential
public import TauCeti.Probability.Distributions.OrderStatistic.Basic
import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Inverse
import TauCeti.MeasureTheory.Order.Lattice
import TauCeti.Probability.Distributions.Bernoulli.Basic
import TauCeti.Probability.Distributions.Bernoulli.Quantile
import TauCeti.Probability.Distributions.Beta.Cdf
import TauCeti.Probability.Distributions.Exponential.Basic
import TauCeti.Probability.Distributions.OrderStatistic.Quantile
import TauCeti.Probability.Distributions.PoissonBinomial.Cdf
import TauCeti.Probability.Distributions.Relations

/-!
# Extreme order statistics and sample extrema

For a finite tuple `x : Fin n → α` in a linear order, the zero-based order statistics recover the
sample minimum at index `0` (`TauCeti.orderStatistic_zero`, for `n ≠ 0`) and the sample maximum at
index `Fin.last n` (`TauCeti.orderStatistic_last`, on `Fin (n + 1)`). This file lifts that
pointwise identification to pushforward laws, cumulative distribution functions, quantiles,
Beta-quantile representations, and concrete distribution families, with no continuity or
atomlessness assumption on the source laws.

In particular, two independent routes to the extreme laws meet at every threshold and every
interior probability level, even when ties have positive probability:

* For independent non-identically distributed coordinates, the Poisson-binomial tail formula for
  `orderStatistic k` (`TauCeti.Probability.cdf_map_orderStatistic_pi_eq_poissonBinomial`) collapses
  at `k = 0` (`Ioi 0`) to `1 - ∏ i, (1 - cdf (μ i) t)` and at `k = Fin.last n` (`Ioi n`) to
  `∏ i, cdf (μ i) t`, matching the direct intersection formulas for finite minima and maxima.
* For independent identically distributed coordinates from an arbitrary probability law `μ` on `ℝ`,
  the general inverse-Beta order-statistic quantile
  `μ.quantile (inverseRegularizedIncompleteBeta (k + 1) (n - k) u)` collapses via
  `TauCeti.inverseRegularizedIncompleteBeta_one_left` and
  `TauCeti.inverseRegularizedIncompleteBeta_one_right` to the elementary power levels
  `1 - (1 - u) ^ (n : ℝ)⁻¹` and `u ^ ((n + 1 : ℕ) : ℝ)⁻¹`, matching the quantiles computed
  directly from the product-measure minimum and maximum cumulative distribution functions.

## Main results

* `ProbabilityTheory.iIndepFun.hasLaw_inf'`, `ProbabilityTheory.iIndepFun.hasLaw_sup'` — pushforward
  laws of nonempty finite infima and suprema of independent coordinates in measurable semilattices;
* `TauCeti.Probability.map_orderStatistic_zero`, `TauCeti.Probability.map_orderStatistic_last`,
  `TauCeti.Probability.hasLaw_orderStatistic_zero_iff`,
  `TauCeti.Probability.hasLaw_orderStatistic_last_iff` — measure and `HasLaw` identifications
  between extreme order statistics and finite extrema;
* `TauCeti.Probability.cdf_map_max_pi`, `TauCeti.Probability.cdf_map_min_pi`,
  `TauCeti.Probability.cdf_map_orderStatistic_zero_pi_indep`,
  `TauCeti.Probability.cdf_map_orderStatistic_last_pi_indep` — product-measure cumulative
  distribution functions of finite extrema and extreme order statistics, atoms included;
* `TauCeti.Probability.quantile_map_max_pi`, `TauCeti.Probability.quantile_map_min_pi`,
  `TauCeti.Probability.quantile_map_orderStatistic_zero_pi`,
  `TauCeti.Probability.quantile_map_orderStatistic_last_pi` — lower quantiles of sample extrema and
  extreme order statistics at interior levels `u ∈ (0, 1)`, atoms included;
* `TauCeti.Probability.map_min_pi_uniformMeasure`, `TauCeti.Probability.map_max_pi_uniformMeasure`,
  `TauCeti.Probability.map_min_pi_expMeasure`,
  `TauCeti.Probability.map_min_pi_bernoulliMeasure_real`,
  `TauCeti.Probability.map_max_pi_bernoulliMeasure_real`,
  `TauCeti.Probability.map_min_pi_bernoulliMeasure_nat`,
  `TauCeti.Probability.map_max_pi_bernoulliMeasure_nat` — closed-form extreme laws for uniform,
  heterogeneous exponential, and atomic heterogeneous Bernoulli families.

## References

* H. A. David and H. N. Nagaraja, *Order Statistics*, 3rd ed., Wiley, 2003, §§2.1, 2.3, and 5.2.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal NNReal ProbabilityTheory Topology unitInterval

namespace ProbabilityTheory

/-- A nonempty finite infimum of independent random variables in a measurable inf-semilattice has
the pushforward of the product law along the coordinatewise infimum. -/
theorem iIndepFun.hasLaw_inf' {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace α] [SemilatticeInf α] [MeasurableInf₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P)
    (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω ↦ s.inf' hs fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ s.inf' hs fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_inf'' hs fun i _ ↦ measurable_pi_apply i).aemeasurable).comp
    (hindep.hasLaw_pi hX)

/-- A nonempty finite supremum of independent random variables in a measurable sup-semilattice has
the pushforward of the product law along the coordinatewise supremum. -/
theorem iIndepFun.hasLaw_sup' {Ω ι α : Type*} [MeasurableSpace Ω] [Fintype ι]
    [MeasurableSpace α] [SemilatticeSup α] [MeasurableSup₂ α]
    {P : Measure Ω} {μ : ι → Measure α} {X : ι → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P)
    (s : Finset ι) (hs : s.Nonempty) :
    HasLaw (fun ω ↦ s.sup' hs fun i ↦ X i ω)
      ((Measure.pi μ).map fun x ↦ s.sup' hs fun i ↦ x i) P :=
  (hasLaw_map (Finset.measurable_sup'' hs fun i _ ↦ measurable_pi_apply i).aemeasurable).comp
    (hindep.hasLaw_pi hX)

end ProbabilityTheory

namespace TauCeti.Probability

/-! ### Measure-level and `HasLaw` bridges in a linear order -/

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
theorem hasLaw_orderStatistic_zero_iff {Ω : Type*} [MeasurableSpace Ω] [NeZero n]
    {P : Measure Ω} {ν : Measure α} {X : Fin n → Ω → α} :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) ν P ↔
      HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω) ν P := by
  have hfun : (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) =
      fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω :=
    funext fun ω ↦ orderStatistic_zero (fun i ↦ X i ω)
  rw [hfun]

/-- Having a given law for `orderStatistic (Fin.last n)` of a tuple of random variables is
equivalent to having that law for their sample maximum. -/
theorem hasLaw_orderStatistic_last_iff {Ω : Type*} [MeasurableSpace Ω]
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
theorem hasLaw_orderStatistic_zero_indep {Ω : Type*} [MeasurableSpace Ω] [MeasurableInf₂ α]
    [NeZero n] {P : Measure Ω} {μ : Fin n → Measure α} {X : Fin n → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic 0)) P := by
  rw [hasLaw_orderStatistic_zero_iff, map_orderStatistic_zero]
  exact hindep.hasLaw_inf' hX Finset.univ Finset.univ_nonempty

/-- The greatest order statistic of independent coordinates has the pushforward of the product
measure along `orderStatistic (Fin.last n)`. Only `MeasurableSup₂ α` is needed because
`orderStatistic (Fin.last n)` is the sample maximum. -/
theorem hasLaw_orderStatistic_last_indep {Ω : Type*} [MeasurableSpace Ω] [MeasurableSup₂ α]
    {P : Measure Ω} {μ : Fin (n + 1) → Measure α} {X : Fin (n + 1) → Ω → α}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) :
    HasLaw (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω)
      ((Measure.pi μ).map (orderStatistic (Fin.last n))) P := by
  rw [hasLaw_orderStatistic_last_iff, map_orderStatistic_last]
  exact hindep.hasLaw_sup' hX Finset.univ Finset.univ_nonempty

end LinearOrder

/-! ### Cumulative distribution functions of product-measure extrema and extreme order statistics -/

section Cdf

variable {ι : Type*} {n : ℕ}

/-- The cumulative distribution function of the coordinatewise maximum under a nonempty finite
product of real probability measures is the product of the marginal cumulative distribution
functions. Atoms are allowed. -/
@[simp]
theorem cdf_map_max_pi [Fintype ι] [Nonempty ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (x : ℝ) :
    cdf ((Measure.pi μ).map fun z ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ z i) x =
      ∏ i, cdf (μ i) x :=
  cdf_max_indep (iIndepFun_pi fun _ ↦ measurable_id.aemeasurable)
    (fun i ↦ (measurePreserving_eval μ i).hasLaw) x

/-- The cumulative distribution function of the coordinatewise minimum under a nonempty finite
product of real probability measures is one minus the product of the marginal survival
probabilities. Atoms are allowed. -/
@[simp]
theorem cdf_map_min_pi [Fintype ι] [Nonempty ι] (μ : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (x : ℝ) :
    cdf ((Measure.pi μ).map fun z ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ z i) x =
      1 - ∏ i, (1 - cdf (μ i) x) :=
  cdf_min_indep (iIndepFun_pi fun _ ↦ measurable_id.aemeasurable)
    (fun i ↦ (measurePreserving_eval μ i).hasLaw) x

/-- For a constant product measure, the coordinatewise maximum has cumulative distribution function
`(cdf μ x) ^ Fintype.card ι`. -/
theorem cdf_map_max_pi_const [Fintype ι] [Nonempty ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    cdf ((Measure.pi fun _ : ι ↦ μ).map
      fun z ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ z i) x =
      cdf μ x ^ Fintype.card ι := by
  simp

/-- For a constant product measure, the coordinatewise minimum has cumulative distribution function
`1 - (1 - cdf μ x) ^ Fintype.card ι`. -/
theorem cdf_map_min_pi_const [Fintype ι] [Nonempty ι] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (x : ℝ) :
    cdf ((Measure.pi fun _ : ι ↦ μ).map
      fun z ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ z i) x =
      1 - (1 - cdf μ x) ^ Fintype.card ι := by
  simp

/-- At index `0`, the Poisson-binomial order-statistic cumulative distribution function of
independent (not necessarily identically distributed) real coordinates collapses to
`1 - ∏ i, (1 - cdf (μ i) t)`, recovering the sample minimum formula even for atomic laws. -/
@[simp]
theorem cdf_map_orderStatistic_zero_pi_indep [NeZero n] (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic 0)) t = 1 - ∏ i, (1 - cdf (μ i) t) := by
  rw [cdf_map_orderStatistic_pi_eq_poissonBinomial, Fin.val_zero,
    poissonBinomialMeasure_real_Ioi_zero]

/-- At index `Fin.last n`, the Poisson-binomial order-statistic cumulative distribution function of
independent (not necessarily identically distributed) real coordinates collapses to
`∏ i, cdf (μ i) t`, recovering the sample maximum formula even for atomic laws. -/
@[simp]
theorem cdf_map_orderStatistic_last_pi_indep (μ : Fin (n + 1) → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (t : ℝ) :
    cdf ((Measure.pi μ).map (orderStatistic (Fin.last n))) t = ∏ i, cdf (μ i) t := by
  simpa [cdf_map_orderStatistic_pi_eq_poissonBinomial] using
    poissonBinomialMeasure_real_Ioi_pred_card
      (fun i : Fin (n + 1) ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩)

/-- For an independent family of real random variables with laws `μ i`, the least order statistic is
at most `t` with probability `1 - ∏ i, (1 - cdf (μ i) t)`. -/
theorem measureReal_setOf_orderStatistic_zero_le_indep {Ω : Type*} [MeasurableSpace Ω]
    [NeZero n] {P : Measure Ω} {μ : Fin n → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (t : ℝ) :
    P.real {ω | orderStatistic 0 (fun i ↦ X i ω) ≤ t} = 1 - ∏ i, (1 - cdf (μ i) t) := by
  rw [measureReal_setOf_orderStatistic_le_indep μ hindep hX 0 t, Fin.val_zero,
    poissonBinomialMeasure_real_Ioi_zero]

/-- For an independent family of real random variables with laws `μ i`, the greatest order statistic
is at most `t` with probability `∏ i, cdf (μ i) t`. -/
theorem measureReal_setOf_orderStatistic_last_le_indep {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Fin (n + 1) → Measure ℝ} [∀ i, IsProbabilityMeasure (μ i)]
    {X : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) (μ i) P) (t : ℝ) :
    P.real {ω | orderStatistic (Fin.last n) (fun i ↦ X i ω) ≤ t} = ∏ i, cdf (μ i) t := by
  rw [measureReal_setOf_orderStatistic_le_indep μ hindep hX (Fin.last n) t]
  simpa using poissonBinomialMeasure_real_Ioi_pred_card
    (fun i : Fin (n + 1) ↦ ⟨cdf (μ i) t, cdf_nonneg _ _, cdf_le_one _ _⟩)

/-- For an iid sample of size `n ≠ 0` from `μ`, the least order statistic has cumulative
distribution function `1 - (1 - cdf μ t) ^ n`. -/
theorem cdf_map_orderStatistic_zero_pi [NeZero n] (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic 0)) t =
      1 - (1 - cdf μ t) ^ n := by
  simp

/-- For an iid sample of size `n + 1` from `μ`, the greatest order statistic has cumulative
distribution function `cdf μ t ^ (n + 1)`. -/
theorem cdf_map_orderStatistic_last_pi (μ : Measure ℝ) [IsProbabilityMeasure μ] (t : ℝ) :
    cdf ((Measure.pi fun _ : Fin (n + 1) ↦ μ).map (orderStatistic (Fin.last n))) t =
      cdf μ t ^ (n + 1) := by
  simp

/-- For an iid family of size `n ≠ 0` with law `μ`, the least order statistic is at most `t` with
probability `1 - (1 - cdf μ t) ^ n`. -/
theorem measureReal_setOf_orderStatistic_zero_le_iid {Ω : Type*} [MeasurableSpace Ω]
    [NeZero n] {P : Measure Ω} {μ : Measure ℝ} [IsProbabilityMeasure μ] {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) μ P) (t : ℝ) :
    P.real {ω | orderStatistic 0 (fun i ↦ X i ω) ≤ t} = 1 - (1 - cdf μ t) ^ n := by
  simpa using measureReal_setOf_orderStatistic_zero_le_indep (μ := fun _ ↦ μ) hindep hX t

/-- For an iid family of size `n + 1` with law `μ`, the greatest order statistic is at most `t`
with probability `cdf μ t ^ (n + 1)`. -/
theorem measureReal_setOf_orderStatistic_last_le_iid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {μ : Measure ℝ} [IsProbabilityMeasure μ] {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) μ P) (t : ℝ) :
    P.real {ω | orderStatistic (Fin.last n) (fun i ↦ X i ω) ≤ t} = cdf μ t ^ (n + 1) := by
  simpa using measureReal_setOf_orderStatistic_last_le_indep (μ := fun _ ↦ μ) hindep hX t

end Cdf

/-! ### Quantiles and Beta-quantile constructions of sample extrema -/

section Quantile

variable {ι : Type*} {n : ℕ} {μ : Measure ℝ} [IsProbabilityMeasure μ] {u : ℝ}

/-- **Lower quantile of the iid sample maximum.** For any real probability measure `μ` (atoms and
flat stretches included) and any interior level `u ∈ (0, 1)`, the quantile of the coordinatewise
maximum of a nonempty finite iid product is `μ.quantile (u ^ (Fintype.card ι : ℝ)⁻¹)`. -/
@[simp]
theorem quantile_map_max_pi [Fintype ι] [Nonempty ι] (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : ι ↦ μ).map
      fun z ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ z i).quantile u =
      μ.quantile (u ^ (Fintype.card ι : ℝ)⁻¹) := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  refine Measure.quantile_eq_of_le_cdf_iff _ _ fun x ↦ ?_
  rw [cdf_map_max_pi_const, ← Real.rpow_natCast (cdf μ x) (Fintype.card ι),
    ← Real.rpow_le_rpow_iff (Real.rpow_nonneg hu.1.le _) (cdf_nonneg μ x) hd,
    ← Real.rpow_mul hu.1.le, inv_mul_cancel₀ hd.ne', Real.rpow_one]

/-- **Lower quantile of the iid sample minimum.** For any real probability measure `μ` (atoms and
flat stretches included) and any interior level `u ∈ (0, 1)`, the quantile of the coordinatewise
minimum of a nonempty finite iid product is `μ.quantile (1 - (1 - u) ^ (Fintype.card ι : ℝ)⁻¹)`. -/
@[simp]
theorem quantile_map_min_pi [Fintype ι] [Nonempty ι] (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : ι ↦ μ).map
      fun z ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ z i).quantile u =
      μ.quantile (1 - (1 - u) ^ (Fintype.card ι : ℝ)⁻¹) := by
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have hu1 : 0 ≤ 1 - u := sub_nonneg.mpr hu.2.le
  refine Measure.quantile_eq_of_le_cdf_iff _ _ fun x ↦ ?_
  have hcdf1 : 0 ≤ 1 - cdf μ x := sub_nonneg.mpr (cdf_le_one μ x)
  rw [cdf_map_min_pi_const, le_sub_comm, ← Real.rpow_natCast (1 - cdf μ x) (Fintype.card ι),
    sub_le_comm, ← Real.rpow_le_rpow_iff hcdf1 (Real.rpow_nonneg hu1 _) hd,
    ← Real.rpow_mul hu1, inv_mul_cancel₀ hd.ne', Real.rpow_one]

/-- Random-variable form of `TauCeti.Probability.quantile_map_max_pi` for a nonempty finite iid
family, with no continuity or atomlessness hypothesis. -/
theorem quantile_max_iid {Ω : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (hu : u ∈ Ioo 0 1) :
    (P.map fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω).quantile u =
      μ.quantile (u ^ (Fintype.card ι : ℝ)⁻¹) := by
  rw [(hindep.hasLaw_sup' hlaw Finset.univ Finset.univ_nonempty).map_eq,
    quantile_map_max_pi hu]

/-- Random-variable form of `TauCeti.Probability.quantile_map_min_pi` for a nonempty finite iid
family, with no continuity or atomlessness hypothesis. -/
theorem quantile_min_iid {Ω : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) (hlaw : ∀ i, HasLaw (X i) μ P) (hu : u ∈ Ioo 0 1) :
    (P.map fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω).quantile u =
      μ.quantile (1 - (1 - u) ^ (Fintype.card ι : ℝ)⁻¹) := by
  rw [(hindep.hasLaw_inf' hlaw Finset.univ Finset.univ_nonempty).map_eq,
    quantile_map_min_pi hu]

/-- At `k = 0`, the inverse-Beta order-statistic quantile formula specializes to
`μ.quantile (1 - (1 - u) ^ (n : ℝ)⁻¹)`, matching `TauCeti.Probability.quantile_map_min_pi` even for
atomic laws. -/
theorem quantile_map_orderStatistic_zero_pi [NeZero n] (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic 0)).quantile u =
      μ.quantile (1 - (1 - u) ^ (n : ℝ)⁻¹) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr (NeZero.pos n)
  rw [quantile_map_orderStatistic_pi 0 hu]
  simp [hn, hu.1, hu.2]

/-- At `k = Fin.last n`, the inverse-Beta order-statistic quantile formula specializes to
`μ.quantile (u ^ ((n + 1 : ℕ) : ℝ)⁻¹)`, matching `TauCeti.Probability.quantile_map_max_pi` even for
atomic laws. -/
theorem quantile_map_orderStatistic_last_pi (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : Fin (n + 1) ↦ μ).map (orderStatistic (Fin.last n))).quantile u =
      μ.quantile (u ^ ((n + 1 : ℕ) : ℝ)⁻¹) := by
  have hn : (0 : ℝ) < (n + 1 : ℕ) := by positivity
  rw [quantile_map_orderStatistic_pi (Fin.last n) hu]
  have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
  have hadd : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; ring
  simp only [Fin.val_last, hsub, hadd]
  rw [inverseRegularizedIncompleteBeta_one_right hn hu.1 hu.2]

/-- Random-variable form of `TauCeti.Probability.quantile_map_orderStatistic_zero_pi`. -/
theorem quantile_of_hasLaw_orderStatistic_zero_iid {Ω : Type*} [MeasurableSpace Ω] [NeZero n]
    {P : Measure Ω} {X : Fin n → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (hu : u ∈ Ioo 0 1) :
    (P.map fun ω ↦ orderStatistic 0 fun i ↦ X i ω).quantile u =
      μ.quantile (1 - (1 - u) ^ (n : ℝ)⁻¹) := by
  rw [(hasLaw_orderStatistic_zero_indep hindep hlaw).map_eq,
    quantile_map_orderStatistic_zero_pi hu]

/-- Random-variable form of `TauCeti.Probability.quantile_map_orderStatistic_last_pi`. -/
theorem quantile_of_hasLaw_orderStatistic_last_iid {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Fin (n + 1) → Ω → ℝ} (hindep : iIndepFun X P)
    (hlaw : ∀ i, HasLaw (X i) μ P) (hu : u ∈ Ioo 0 1) :
    (P.map fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω).quantile u =
      μ.quantile (u ^ ((n + 1 : ℕ) : ℝ)⁻¹) := by
  rw [(hasLaw_orderStatistic_last_indep hindep hlaw).map_eq,
    quantile_map_orderStatistic_last_pi hu]

/-- The least order statistic of an iid sample of size `n ≠ 0` from `μ` is the pushforward of
`betaMeasure 1 n` under `μ.quantile`, atoms included. -/
theorem map_orderStatistic_zero_pi_eq_map_betaMeasure_quantile [NeZero n] :
    (Measure.pi fun _ : Fin n ↦ μ).map (orderStatistic 0) =
      (betaMeasure 1 n).map μ.quantile := by
  simpa using map_orderStatistic_pi_eq_map_betaMeasure_quantile (μ := μ) (0 : Fin n)

/-- The greatest order statistic of an iid sample of size `n + 1` from `μ` is the pushforward of
`betaMeasure (n + 1) 1` under `μ.quantile`, atoms included. -/
theorem map_orderStatistic_last_pi_eq_map_betaMeasure_quantile (n : ℕ) :
    (Measure.pi fun _ : Fin (n + 1) ↦ μ).map (orderStatistic (Fin.last n)) =
      (betaMeasure ((n : ℝ) + 1) 1).map μ.quantile := by
  have h := map_orderStatistic_pi_eq_map_betaMeasure_quantile (μ := μ) (Fin.last n)
  have hsub : ((n + 1 : ℕ) : ℝ) - (n : ℝ) = 1 := by push_cast; ring
  simpa [Fin.val_last, hsub] using h

end Quantile

/-! ### Closed-form specializations: uniform, exponential, and atomic Bernoulli laws -/

section Specializations

variable {ι : Type*} {n : ℕ}

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

/-- The coordinatewise minimum of a nonempty finite product of unit uniform laws has law
`betaMeasure 1 (Fintype.card ι)`. -/
theorem map_min_pi_uniformMeasure [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
      (fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      betaMeasure 1 (Fintype.card ι) := by
  have _ : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have _ : IsProbabilityMeasure (betaMeasure 1 (Fintype.card ι)) :=
    isProbabilityMeasureBeta one_pos hd
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_min_pi_const, cdf_betaMeasure_eq one_pos hd, cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · rw [regularizedIncompleteBeta_eq_zero_of_nonpos one_pos.ne' _ h0]
    simp
  · rw [regularizedIncompleteBeta_eq_one_of_one_le zero_le_one hd h1, sub_self,
      zero_pow Fintype.card_ne_zero, sub_zero]
  · push Not at h0 h1
    simp only [sub_zero, div_one]
    rw [regularizedIncompleteBeta_one_left hd h0.le h1.le, Real.rpow_natCast]

/-- The coordinatewise maximum of a nonempty finite product of unit uniform laws has law
`betaMeasure (Fintype.card ι) 1`. -/
theorem map_max_pi_uniformMeasure [Fintype ι] [Nonempty ι] :
    (Measure.pi fun _ : ι ↦ uniformMeasure 0 1).map
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      betaMeasure (Fintype.card ι) 1 := by
  have _ : IsProbabilityMeasure (uniformMeasure 0 1) :=
    isProbabilityMeasure_uniformMeasure zero_lt_one
  have hd : (0 : ℝ) < Fintype.card ι := Nat.cast_pos.mpr Fintype.card_pos
  have _ : IsProbabilityMeasure (betaMeasure (Fintype.card ι) 1) :=
    isProbabilityMeasureBeta hd one_pos
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_max_pi_const, cdf_betaMeasure_eq hd one_pos, cdf_uniformMeasure zero_lt_one]
  split_ifs with h0 h1
  · rw [regularizedIncompleteBeta_eq_zero_of_nonpos hd.ne' _ h0, zero_pow Fintype.card_ne_zero]
  · rw [regularizedIncompleteBeta_eq_one_of_one_le hd.le one_pos h1, one_pow]
  · push Not at h0 h1
    simp only [sub_zero, div_one]
    rw [regularizedIncompleteBeta_one_right hd h0.le h1.le, Real.rpow_natCast]

/-- **Minimum of independent heterogeneous exponentials.** Under a nonempty finite product of
exponential laws with positive rates `r i`, the coordinatewise minimum is exponential of rate
`∑ i, r i`. -/
theorem map_min_pi_expMeasure [Fintype ι] [Nonempty ι] {r : ι → ℝ} (hr : ∀ i, 0 < r i) :
    (Measure.pi fun i ↦ expMeasure (r i)).map
      (fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      expMeasure (∑ i, r i) := by
  have hsum : 0 < ∑ i, r i := Finset.sum_pos (fun i _ ↦ hr i) Finset.univ_nonempty
  have _ (i : ι) : IsProbabilityMeasure (expMeasure (r i)) :=
    isProbabilityMeasure_expMeasure (hr i)
  have _ : IsProbabilityMeasure (expMeasure (∑ i, r i)) := isProbabilityMeasure_expMeasure hsum
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_min_pi, cdf_expMeasure_eq hsum x]
  by_cases hx : 0 ≤ x
  · rw [ite_eq_left hx]
    have hterm : (∏ i, (1 - cdf (expMeasure (r i)) x)) = Real.exp (-((∑ i, r i) * x)) := by
      calc
        (∏ i, (1 - cdf (expMeasure (r i)) x)) = ∏ i, Real.exp (-(r i * x)) := by
          refine Finset.prod_congr rfl fun i _ ↦ ?_
          rw [cdf_expMeasure_eq (hr i) x, ite_eq_left hx, sub_sub_cancel]
        _ = Real.exp (∑ i, -(r i * x)) := (Real.exp_sum Finset.univ _).symm
        _ = Real.exp (-((∑ i, r i) * x)) := by
          congr 1
          rw [Finset.sum_neg_distrib, Finset.sum_mul]
    rw [hterm]
  · rw [ite_eq_right hx]
    have hterm : (∏ i, (1 - cdf (expMeasure (r i)) x)) = 1 := by
      refine Finset.prod_eq_one fun i _ ↦ ?_
      rw [cdf_expMeasure_eq (hr i) x, ite_eq_right hx, sub_zero]
    rw [hterm, sub_self]

/-- Random-variable form of `TauCeti.Probability.map_min_pi_expMeasure` for independent
heterogeneous exponential random variables. -/
theorem hasLaw_min_indep_expMeasure {Ω : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    {P : Measure Ω} {r : ι → ℝ} {X : ι → Ω → ℝ} (hr : ∀ i, 0 < r i) (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (expMeasure (r i)) P) :
    HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω)
      (expMeasure (∑ i, r i)) P := by
  rw [← map_min_pi_expMeasure hr]
  exact hindep.hasLaw_inf' hX Finset.univ Finset.univ_nonempty

/-- The least order statistic of `n ≠ 0` independent exponential coordinates with positive rates
`r i` has law `expMeasure (∑ i, r i)`. -/
theorem map_orderStatistic_zero_pi_expMeasure [NeZero n] {r : Fin n → ℝ} (hr : ∀ i, 0 < r i) :
    (Measure.pi fun i ↦ expMeasure (r i)).map (orderStatistic 0) =
      expMeasure (∑ i, r i) := by
  rw [map_orderStatistic_zero, map_min_pi_expMeasure hr]

/-- Random-variable form of `TauCeti.Probability.map_orderStatistic_zero_pi_expMeasure`, specialized
to a common rate `r`: the least order statistic of `n ≠ 0` iid exponentials of rate `r` is
exponential of rate `n * r`. -/
theorem hasLaw_orderStatistic_zero_iid_expMeasure {Ω : Type*} [MeasurableSpace Ω] [NeZero n]
    {P : Measure Ω} {r : ℝ} {X : Fin n → Ω → ℝ} (hr : 0 < r) (hindep : iIndepFun X P)
    (hX : ∀ i, HasLaw (X i) (expMeasure r) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) (expMeasure ((n : ℝ) * r)) P := by
  rw [hasLaw_orderStatistic_zero_iff]
  simpa using hasLaw_min_iid_expMeasure hr hindep hX

/-- Two measures on `ℕ` agree when their pushforwards under `Nat.cast : ℕ → ℝ` agree. -/
private lemma eq_of_map_natCast_eq {μ ν : Measure ℕ}
    (h : μ.map (Nat.cast : ℕ → ℝ) = ν.map (Nat.cast : ℕ → ℝ)) : μ = ν := by
  refine Measure.ext_of_singleton fun k ↦ ?_
  have hpre : (Nat.cast : ℕ → ℝ) ⁻¹' {(k : ℝ)} = {k} := by
    ext m
    simp
  have hmk := congrArg (fun ρ : Measure ℝ ↦ ρ {(k : ℝ)}) h
  simpa only [Measure.map_apply Measurable.of_discrete (measurableSet_singleton _), hpre] using hmk

/-- **Minimum of independent atomic real Bernoulli variables.** For a nonempty finite family of
real Bernoulli laws with arbitrary success probabilities `p i ∈ [0, 1]` (including `0` and `1`, so
ties occur with positive probability), the coordinatewise minimum has law
`Ber((1 : ℝ), 0, ∏ i, p i)`. -/
theorem map_min_pi_bernoulliMeasure_real [Fintype ι] [Nonempty ι] (p : ι → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i)).map
      (fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      Ber((1 : ℝ), 0, ∏ i, p i) := by
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_min_pi, cdf_bernoulliMeasure]
  by_cases h1 : (1 : ℝ) ≤ x
  · have h0 : (0 : ℝ) ≤ x := zero_le_one.trans h1
    have hprod : (∏ i, (1 - cdf Ber((1 : ℝ), 0, p i) x)) = 0 := by
      have hzero : ∀ i, 1 - cdf Ber((1 : ℝ), 0, p i) x = 0 := fun i ↦ by
        rw [cdf_bernoulliMeasure, ite_eq_left h1, ite_eq_left h0]
        ring
      simp_rw [hzero]
      simp [zero_pow Fintype.card_ne_zero]
    rw [hprod, ite_eq_left h1, ite_eq_left h0]
    ring
  · by_cases h0 : (0 : ℝ) ≤ x
    · have hprod : (∏ i, (1 - cdf Ber((1 : ℝ), 0, p i) x)) = ∏ i, (p i : ℝ) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [cdf_bernoulliMeasure, ite_eq_right h1, ite_eq_left h0]
        ring
      have hcoe : ((∏ i, p i : unitInterval) : ℝ) = ∏ i, (p i : ℝ) :=
        map_prod unitInterval.submonoid.subtype p Finset.univ
      rw [hprod, ite_eq_right h1, ite_eq_left h0, zero_add, hcoe]
    · have hprod : (∏ i, (1 - cdf Ber((1 : ℝ), 0, p i) x)) = 1 := by
        refine Finset.prod_eq_one fun i _ ↦ ?_
        rw [cdf_bernoulliMeasure, ite_eq_right h1, ite_eq_right h0]
        ring
      rw [hprod, ite_eq_right h1, ite_eq_right h0]
      ring

/-- **Maximum of independent atomic real Bernoulli variables.** For a nonempty finite family of
real Bernoulli laws with arbitrary success probabilities `p i ∈ [0, 1]`, the coordinatewise maximum
has law `Ber((1 : ℝ), 0, σ (∏ i, σ (p i)))`. -/
theorem map_max_pi_bernoulliMeasure_real [Fintype ι] [Nonempty ι] (p : ι → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i)).map
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      Ber((1 : ℝ), 0, σ (∏ i, σ (p i))) := by
  refine Measure.eq_of_cdf _ _ ?_
  ext x
  rw [cdf_map_max_pi, cdf_bernoulliMeasure]
  by_cases h1 : (1 : ℝ) ≤ x
  · have h0 : (0 : ℝ) ≤ x := zero_le_one.trans h1
    have hprod : (∏ i, cdf Ber((1 : ℝ), 0, p i) x) = 1 := by
      refine Finset.prod_eq_one fun i _ ↦ ?_
      rw [cdf_bernoulliMeasure, ite_eq_left h1, ite_eq_left h0]
      ring
    rw [hprod, ite_eq_left h1, ite_eq_left h0]
    ring
  · by_cases h0 : (0 : ℝ) ≤ x
    · have hprod : (∏ i, cdf Ber((1 : ℝ), 0, p i) x) = ∏ i, (σ (p i) : ℝ) := by
        refine Finset.prod_congr rfl fun i _ ↦ ?_
        rw [cdf_bernoulliMeasure, ite_eq_right h1, ite_eq_left h0, zero_add,
          unitInterval.coe_symm_eq]
      have hcoe : ((∏ i, σ (p i) : unitInterval) : ℝ) = ∏ i, (σ (p i) : ℝ) :=
        map_prod unitInterval.submonoid.subtype (fun i ↦ σ (p i)) Finset.univ
      rw [hprod, ite_eq_right h1, ite_eq_left h0, zero_add, unitInterval.coe_symm_eq,
        sub_sub_cancel, hcoe]
    · have hprod : (∏ i, cdf Ber((1 : ℝ), 0, p i) x) = 0 := by
        have hzero : ∀ i, cdf Ber((1 : ℝ), 0, p i) x = 0 := fun i ↦ by
          rw [cdf_bernoulliMeasure, ite_eq_right h1, ite_eq_right h0, add_zero]
        simp_rw [hzero]
        simp [zero_pow Fintype.card_ne_zero]
      rw [hprod, ite_eq_right h1, ite_eq_right h0, add_zero]

/-- **Minimum of independent native `ℕ`-valued Bernoulli variables.** -/
theorem map_min_pi_bernoulliMeasure_nat [Fintype ι] [Nonempty ι] (p : ι → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map
      (fun x ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      Ber((1 : ℕ), 0, ∏ i, p i) := by
  refine eq_of_map_natCast_eq ?_
  have hcast : ((Nat.cast : ℕ → ℝ) ∘ fun x : ι → ℕ ↦
      Finset.univ.inf' Finset.univ_nonempty fun i ↦ x i) =
      (fun y : ι → ℝ ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ y i) ∘
        fun x i ↦ (x i : ℝ) := by
    funext x
    exact Finset.apply_inf'_eq_inf'_comp Finset.univ_nonempty (Nat.cast : ℕ → ℝ) Nat.cast_min
  have hpi : (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map (fun x i ↦ (x i : ℝ)) =
      Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i) := by
    rw [Measure.pi_map_pi fun _ ↦ Measurable.of_discrete.aemeasurable]
    congr 1
    funext i
    exact (hasLaw_natCast_bernoulliMeasure (p i)).map_eq
  rw [Measure.map_map (by fun_prop) (by fun_prop), hcast,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, map_min_pi_bernoulliMeasure_real,
    (hasLaw_natCast_bernoulliMeasure (∏ i, p i)).map_eq]

/-- **Maximum of independent native `ℕ`-valued Bernoulli variables.** -/
theorem map_max_pi_bernoulliMeasure_nat [Fintype ι] [Nonempty ι] (p : ι → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map
      (fun x ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      Ber((1 : ℕ), 0, σ (∏ i, σ (p i))) := by
  refine eq_of_map_natCast_eq ?_
  have hcast : ((Nat.cast : ℕ → ℝ) ∘ fun x : ι → ℕ ↦
      Finset.univ.sup' Finset.univ_nonempty fun i ↦ x i) =
      (fun y : ι → ℝ ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ y i) ∘
        fun x i ↦ (x i : ℝ) := by
    funext x
    exact Finset.apply_sup'_eq_sup'_comp Finset.univ_nonempty (Nat.cast : ℕ → ℝ) Nat.cast_max
  have hpi : (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map (fun x i ↦ (x i : ℝ)) =
      Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i) := by
    rw [Measure.pi_map_pi fun _ ↦ Measurable.of_discrete.aemeasurable]
    congr 1
    funext i
    exact (hasLaw_natCast_bernoulliMeasure (p i)).map_eq
  rw [Measure.map_map (by fun_prop) (by fun_prop), hcast,
    ← Measure.map_map (by fun_prop) (by fun_prop), hpi, map_max_pi_bernoulliMeasure_real,
    (hasLaw_natCast_bernoulliMeasure (σ (∏ i, σ (p i)))).map_eq]

/-- Random-variable form of `TauCeti.Probability.map_min_pi_bernoulliMeasure_real`. -/
theorem hasLaw_min_indep_bernoulliMeasure_real {Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {p : ι → unitInterval} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p i) P) :
    HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω)
      Ber((1 : ℝ), 0, ∏ i, p i) P := by
  rw [← map_min_pi_bernoulliMeasure_real]
  exact hindep.hasLaw_inf' hX Finset.univ Finset.univ_nonempty

/-- Random-variable form of `TauCeti.Probability.map_max_pi_bernoulliMeasure_real`. -/
theorem hasLaw_max_indep_bernoulliMeasure_real {Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {p : ι → unitInterval} {X : ι → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p i) P) :
    HasLaw (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω)
      Ber((1 : ℝ), 0, σ (∏ i, σ (p i))) P := by
  rw [← map_max_pi_bernoulliMeasure_real]
  exact hindep.hasLaw_sup' hX Finset.univ Finset.univ_nonempty

/-- Random-variable form of `TauCeti.Probability.map_min_pi_bernoulliMeasure_nat`. -/
theorem hasLaw_min_indep_bernoulliMeasure_nat {Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {p : ι → unitInterval} {X : ι → Ω → ℕ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℕ), 0, p i) P) :
    HasLaw (fun ω ↦ Finset.univ.inf' Finset.univ_nonempty fun i ↦ X i ω)
      Ber((1 : ℕ), 0, ∏ i, p i) P := by
  rw [← map_min_pi_bernoulliMeasure_nat]
  exact hindep.hasLaw_inf' hX Finset.univ Finset.univ_nonempty

/-- Random-variable form of `TauCeti.Probability.map_max_pi_bernoulliMeasure_nat`. -/
theorem hasLaw_max_indep_bernoulliMeasure_nat {Ω : Type*} [MeasurableSpace Ω]
    [Fintype ι] [Nonempty ι] {P : Measure Ω} {p : ι → unitInterval} {X : ι → Ω → ℕ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℕ), 0, p i) P) :
    HasLaw (fun ω ↦ Finset.univ.sup' Finset.univ_nonempty fun i ↦ X i ω)
      Ber((1 : ℕ), 0, σ (∏ i, σ (p i))) P := by
  rw [← map_max_pi_bernoulliMeasure_nat]
  exact hindep.hasLaw_sup' hX Finset.univ Finset.univ_nonempty

/-- The least order statistic of `n ≠ 0` independent atomic real Bernoulli variables with success
probabilities `p i` has law `Ber((1 : ℝ), 0, ∏ i, p i)`. -/
theorem map_orderStatistic_zero_pi_bernoulliMeasure_real [NeZero n] (p : Fin n → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i)).map (orderStatistic 0) =
      Ber((1 : ℝ), 0, ∏ i, p i) := by
  rw [map_orderStatistic_zero, map_min_pi_bernoulliMeasure_real]

/-- The greatest order statistic of `n + 1` independent atomic real Bernoulli variables with
success probabilities `p i` has law `Ber((1 : ℝ), 0, σ (∏ i, σ (p i)))`. -/
theorem map_orderStatistic_last_pi_bernoulliMeasure_real (p : Fin (n + 1) → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℝ), 0, p i)).map (orderStatistic (Fin.last n)) =
      Ber((1 : ℝ), 0, σ (∏ i, σ (p i))) := by
  rw [map_orderStatistic_last, map_max_pi_bernoulliMeasure_real]

/-- The least order statistic of `n ≠ 0` independent native `ℕ`-valued Bernoulli variables with
success probabilities `p i` has law `Ber((1 : ℕ), 0, ∏ i, p i)`. -/
theorem map_orderStatistic_zero_pi_bernoulliMeasure_nat [NeZero n] (p : Fin n → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map (orderStatistic 0) =
      Ber((1 : ℕ), 0, ∏ i, p i) := by
  rw [map_orderStatistic_zero, map_min_pi_bernoulliMeasure_nat]

/-- The greatest order statistic of `n + 1` independent native `ℕ`-valued Bernoulli variables with
success probabilities `p i` has law `Ber((1 : ℕ), 0, σ (∏ i, σ (p i)))`. -/
theorem map_orderStatistic_last_pi_bernoulliMeasure_nat (p : Fin (n + 1) → unitInterval) :
    (Measure.pi fun i ↦ Ber((1 : ℕ), 0, p i)).map (orderStatistic (Fin.last n)) =
      Ber((1 : ℕ), 0, σ (∏ i, σ (p i))) := by
  rw [map_orderStatistic_last, map_max_pi_bernoulliMeasure_nat]

/-- Random-variable form of `TauCeti.Probability.map_orderStatistic_zero_pi_bernoulliMeasure_real`
for independent heterogeneous real Bernoulli variables. -/
theorem hasLaw_orderStatistic_zero_indep_bernoulliMeasure_real {Ω : Type*} [MeasurableSpace Ω]
    [NeZero n] {P : Measure Ω} {p : Fin n → unitInterval} {X : Fin n → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p i) P) :
    HasLaw (fun ω ↦ orderStatistic 0 fun i ↦ X i ω) Ber((1 : ℝ), 0, ∏ i, p i) P := by
  rw [← map_orderStatistic_zero_pi_bernoulliMeasure_real]
  exact hasLaw_orderStatistic_zero_indep hindep hX

/-- Random-variable form of `TauCeti.Probability.map_orderStatistic_last_pi_bernoulliMeasure_real`
for independent heterogeneous real Bernoulli variables. -/
theorem hasLaw_orderStatistic_last_indep_bernoulliMeasure_real {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {p : Fin (n + 1) → unitInterval} {X : Fin (n + 1) → Ω → ℝ}
    (hindep : iIndepFun X P) (hX : ∀ i, HasLaw (X i) Ber((1 : ℝ), 0, p i) P) :
    HasLaw (fun ω ↦ orderStatistic (Fin.last n) fun i ↦ X i ω)
      Ber((1 : ℝ), 0, σ (∏ i, σ (p i))) P := by
  rw [← map_orderStatistic_last_pi_bernoulliMeasure_real]
  exact hasLaw_orderStatistic_last_indep hindep hX

/-- At an interior level `u ∈ (0, 1)`, the lower quantile of the least order statistic of `n ≠ 0`
iid atomic `Ber((1 : ℝ), 0, p)` variables jumps from `0` to `1` at `1 - (p : ℝ) ^ n`, including the
degenerate boundaries `p = 0` and `p = 1`. -/
theorem quantile_map_orderStatistic_zero_pi_bernoulliMeasure [NeZero n] (p : unitInterval)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : Fin n ↦ Ber((1 : ℝ), 0, p)).map (orderStatistic 0)).quantile u =
      if u ≤ 1 - (p : ℝ) ^ n then 0 else 1 := by
  have hlaw := map_orderStatistic_zero_pi_bernoulliMeasure_real (fun _ : Fin n ↦ p)
  rw [hlaw, quantile_bernoulliMeasure hu]
  simp

/-- At an interior level `u ∈ (0, 1)`, the lower quantile of the greatest order statistic of
`n + 1` iid atomic `Ber((1 : ℝ), 0, p)` variables jumps from `0` to `1` at
`(1 - (p : ℝ)) ^ (n + 1)`, including the degenerate boundaries `p = 0` and `p = 1`. -/
theorem quantile_map_orderStatistic_last_pi_bernoulliMeasure (p : unitInterval)
    {u : ℝ} (hu : u ∈ Ioo 0 1) :
    ((Measure.pi fun _ : Fin (n + 1) ↦ Ber((1 : ℝ), 0, p)).map
      (orderStatistic (Fin.last n))).quantile u =
      if u ≤ (1 - (p : ℝ)) ^ (n + 1) then 0 else 1 := by
  have hlaw := map_orderStatistic_last_pi_bernoulliMeasure_real (fun _ : Fin (n + 1) ↦ p)
  rw [hlaw, quantile_bernoulliMeasure hu]
  simp [unitInterval.coe_symm_eq]

end Specializations

end TauCeti.Probability
