/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Alexander Richard Towell
-/
module

public import TauCeti.Probability.Exchangeability.SamplingWithoutReplacement
public import TauCeti.Probability.PopulationSampling.Discrepancy
public import TauCeti.Probability.PopulationSampling.Ties

/-!
# Quantitative finite de Finetti approximation

Let `x : κ → α` be a nonempty finite population. Its empirical distribution is the pushforward
of the uniform law on `κ` by `x`. Sampling `ι` entries from that distribution independently is
therefore the same as choosing a uniform map `ι → κ` and reading the selected entries of `x`.

The general sampling laws, their empirical-product characterization, and their collision and
total-variation bounds live in `TauCeti.Probability.PopulationSampling.Finite` and
`TauCeti.Probability.PopulationSampling.Discrepancy`.

For a random population with law `ρ`, `sampleWithReplacement ρ` draws the population and,
independently, a uniform map `ι → κ`, and reads the selected entries. It is the same
`samplePopulation` construction as `sampleWithoutReplacement ρ`, which instead draws a uniform
injective map; when `κ` is nonempty, by the previous paragraph it is the mixture over `ρ` of the
finite product laws of the empirical distributions. The law `sampleWithoutReplacement ρ` already
represents every shorter marginal of a finite exchangeable process. The collision coupling between
uniform maps and uniform injective maps consequently gives, for every event `A`,

```text
prefixLaw μ X m A ≤ sampleWithReplacement (prefixLaw μ X n) A + choose(m, 2) / n
sampleWithReplacement (prefixLaw μ X n) A ≤ prefixLaw μ X m A + choose(m, 2) / n.
```

Thus, for `n > 0`, every `m`-coordinate marginal of an `n`-exchangeable process is quantitatively
approximated by a mixture of `m`-fold product measures of empirical distributions; for `m ≤ 1`
(including `n = m = 0`) the two laws coincide (`sampleWithReplacement_eq_prefixLaw_of_le_one`).
The bound is stated eventwise, which fixes its normalization; in terms of Mathlib's total variation
distances `etvDist` and `tvDist`, the signed-measure norm `‖P - Q‖` (twice `sup_A |P A - Q A|`), it
gives `etvDist P Q ≤ 2 * choose(m, 2) / n`, while for each individual event `A` the real
probability difference satisfies `|P.real A - Q.real A| ≤ choose(m, 2) / n`.

Counting injective selections instead of using the union bound gives the sharper eventwise
error `1 - n.descFactorial m / n^m`, and twice that error for the signed-measure norm.
This includes `m = n = 0`, whose error is zero. For a nonempty population the error is the
exact index-collision probability.

For `2 ≤ m ≤ n`, if the first `n` coordinates repeat a value with positive probability, the error
improves further: for a measurable set `S` of populations with a repeated value, it is
`1 - p - t * min p (1 - p) * P((X₀, …, Xₙ₋₁) ∈ S)`, where `p = n.descFactorial m / n^m` and
`t = m.descFactorial 2 / n.descFactorial 2`.

## Main declarations

* `TauCeti.Probability.ExchangeableAt.sampleWithReplacement_eq_prefixLaw_of_le_one`: exact
  equality of the `m`-prefix law and the with-replacement sample when `m ≤ 1`;
* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti`: the paired eventwise finite de Finetti
  bound;
* `TauCeti.Probability.ExchangeableAt.prefixLaw_le_sampleWithReplacement_add` and
  `TauCeti.Probability.ExchangeableAt.sampleWithReplacement_le_prefixLaw_add`: the two sides of
  the finite de Finetti bound;
* `TauCeti.Probability.ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le`,
  `TauCeti.Probability.ExchangeableAt.tvDist_prefixLaw_sampleWithReplacement_le`, and
  `TauCeti.Probability.ExchangeableAt.abs_prefixLaw_real_sub_sampleWithReplacement_real_le`:
  the total-variation and real eventwise forms;
* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti_exact_collision`: the sharper eventwise
  bound using the exact collision probability, with corresponding `etvDist`, `tvDist`, and
  `Measure.real` theorems;
* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti_ties` and
  `TauCeti.Probability.ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_ties`: the
  eventwise and `etvDist` bounds whose error decreases with the probability of a repeated value
  among the first `n` coordinates.

## References

* P. Diaconis and D. Freedman, “Finite exchangeable sequences”, *Annals of Probability* 8
  (1980), 745–764.

No material is adapted from `cameronfreer/exchangeability`; that development concerns infinite
exchangeable sequences rather than quantitative finite approximation.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

section FiniteExchangeability

/-- For a prefix of length `m ≤ 1` (`m = 0` or `m = 1`), sampling with replacement from the
`n`-prefix law of an `n`-exchangeable process reproduces the `m`-prefix law exactly. Only
finiteness of `μ` is needed. -/
theorem ExchangeableAt.sampleWithReplacement_eq_prefixLaw_of_le_one
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hm : m ≤ 1) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) = prefixLaw μ X m := by
  have : Subsingleton (Fin m) := Fintype.card_le_one_iff_subsingleton.1 (by simpa using hm)
  rw [← sampleWithoutReplacement_eq_sampleWithReplacement_of_subsingleton,
    h.sampleWithoutReplacement_eq_prefixLaw hmn hX]

/-- **Finite de Finetti theorem.** If the first `n` coordinates of a process are exchangeable and
`m ≤ n`, then its `m`-prefix law and the with-replacement sample of its `n`-prefix law differ by
at most `choose m 2 / n` on every event, in both directions. For `n > 0` that sample is
the empirical-product mixture (`sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`). -/
theorem ExchangeableAt.finiteDeFinetti
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        m.choose 2 / n ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        m.choose 2 / n := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  constructor
  · simpa using sampleWithoutReplacement_le_sampleWithReplacement_add
      (ρ := prefixLaw μ X n) A
  · simpa using sampleWithReplacement_le_sampleWithoutReplacement_add
      (ρ := prefixLaw μ X n) A

/-- **Finite de Finetti with the exact collision error.** The discrepancy on any
event between an exchangeable prefix and its with-replacement sample (the empirical-product
mixture when `n > 0`) is bounded by `1 - (n)_m / n^m`, where `(n)_m` counts ordered injections.
This retains the overlap between pairwise collisions lost in the union bound.
The empty-sample case `m = n = 0` has error zero. -/
theorem ExchangeableAt.finiteDeFinetti_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  constructor
  · simpa using
      sampleWithoutReplacement_le_sampleWithReplacement_add_exact_collision
        (ρ := prefixLaw μ X n) A
  · simpa using
      sampleWithReplacement_le_sampleWithoutReplacement_add_exact_collision
        (ρ := prefixLaw μ X n) A

/-- **Exact finite de Finetti bound, exchangeable law to empirical mixture.** Under finite
exchangeability and `m ≤ n`, the prefix law exceeds its with-replacement sample on an
event by at most the exact index-collision error. -/
theorem ExchangeableAt.prefixLaw_le_sampleWithReplacement_add_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
      (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) :=
  (h.finiteDeFinetti_exact_collision hmn hX A).1

/-- **Exact finite de Finetti bound, empirical mixture to exchangeable law.** Under finite
exchangeability and `m ≤ n`, the with-replacement sample exceeds the prefix law on an
event by at most the exact index-collision error. -/
theorem ExchangeableAt.sampleWithReplacement_le_prefixLaw_add_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
      (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) :=
  (h.finiteDeFinetti_exact_collision hmn hX A).2

/-- **Quantitative finite de Finetti bound, exchangeable law to empirical mixture.** If the first
`n` coordinates of a process are exchangeable and `m ≤ n`, then every event under the
`m`-prefix law has mass at most its mass under sampling `m` entries with replacement from the first
`n` coordinates, plus `choose m 2 / n`. For `n > 0` that sample is the mixture of `m`-fold products
of the empirical distribution of the first `n` coordinates. -/
theorem ExchangeableAt.prefixLaw_le_sampleWithReplacement_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
      m.choose 2 / n :=
  (h.finiteDeFinetti hmn hX A).1

/-- **Quantitative finite de Finetti bound, empirical mixture to exchangeable law.** Under the
same hypotheses, every event under the with-replacement sample (for `n > 0`, the
empirical-product mixture) has mass at most its mass under the `m`-prefix law plus
`choose m 2 / n`. -/
theorem ExchangeableAt.sampleWithReplacement_le_prefixLaw_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
      m.choose 2 / n :=
  (h.finiteDeFinetti hmn hX A).2

/-- **Finite de Finetti theorem, total-variation form.** If the first `n` coordinates of a
process are exchangeable and `m ≤ n`, then the total variation distance between the `m`-prefix
law and the with-replacement sample of the `n`-prefix law (for `n > 0`, the empirical-product
mixture) is at most `2 * choose m 2 / n`.

The normalization is Mathlib's: `etvDist P Q` is the signed-measure norm `‖P - Q‖`, twice the
distance `sup_A |P A - Q A|`, so in terms of that distance the bound is `choose m 2 / n`
(`etvDist_le_two_mul_iff`). -/
theorem ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    etvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * (m.choose 2 / n) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using etvDist_sampleWithoutReplacement_sampleWithReplacement_le
    (ι := Fin m) (prefixLaw μ X n)

/-- The finite de Finetti approximation with exact collision error, for Mathlib's total
variation distance `etvDist`. Its signed-measure normalization is twice the probability-distance
convention `sup_A |P(A) - Q(A)|`; no optimality for each individual population law is asserted. -/
theorem ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    etvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using etvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision
    (ι := Fin m) (prefixLaw μ X n)

/-- Real total-variation (`tvDist`) form of `etvDist_prefixLaw_sampleWithReplacement_le`. -/
theorem ExchangeableAt.tvDist_prefixLaw_sampleWithReplacement_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    tvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * (m.choose 2 / (n : ℝ)) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using tvDist_sampleWithoutReplacement_sampleWithReplacement_le
    (ι := Fin m) (prefixLaw μ X n)

/-- Real total-variation (`tvDist`) form of
`etvDist_prefixLaw_sampleWithReplacement_le_exact_collision`. -/
theorem ExchangeableAt.tvDist_prefixLaw_sampleWithReplacement_le_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    tvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * (1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using tvDist_sampleWithoutReplacement_sampleWithReplacement_le_exact_collision
    (ι := Fin m) (prefixLaw μ X n)

/-- Real eventwise finite de Finetti bound (factor `1`, for arbitrary subsets `A`). -/
theorem ExchangeableAt.abs_prefixLaw_real_sub_sampleWithReplacement_real_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    |(prefixLaw μ X m).real A -
        (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)).real A| ≤
      m.choose 2 / (n : ℝ) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le
    (ι := Fin m) (prefixLaw μ X n) A

/-- Real eventwise exact-collision finite de Finetti bound (factor `1`, for arbitrary subsets
`A`). -/
theorem ExchangeableAt.abs_prefixLaw_real_sub_sampleWithReplacement_real_le_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) (A : Set (Fin m → α)) :
    |(prefixLaw μ X m).real A -
        (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)).real A| ≤
      1 - (n.descFactorial m : ℝ) / (n : ℝ) ^ m := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using
    abs_sampleWithoutReplacement_real_sub_sampleWithReplacement_real_le_exact_collision
      (ι := Fin m) (prefixLaw μ X n) A

/-- **Finite de Finetti with ties.** Let the first `n` coordinates of a process be exchangeable,
`m ≤ n`, and let `S` be a measurable set of populations `Fin n → α` with a repeated value. Then the
`m`-prefix law and the with-replacement sample of the `n`-prefix law differ on every event, in
both directions, by at most `1 - p - t * min p (1 - p) * P((X₀, …, Xₙ₋₁) ∈ S)`, where
`p = n.descFactorial m / n ^ m` and `t = m.descFactorial 2 / n.descFactorial 2`. For `S = ∅` this
is `finiteDeFinetti_exact_collision`. -/
theorem ExchangeableAt.finiteDeFinetti_ties
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {S : Set (Fin n → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Function.Injective x) (A : Set (Fin m → α)) :
    let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
    let t : ℝ := m.descFactorial 2 / n.descFactorial 2
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        ENNReal.ofReal (1 - p - t * min p (1 - p) * (prefixLaw μ X n S).toReal) ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        ENNReal.ofReal (1 - p - t * min p (1 - p) * (prefixLaw μ X n S).toReal) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  constructor
  · simpa using sampleWithoutReplacement_le_sampleWithReplacement_add_ties
      (prefixLaw μ X n) hS hSx A
  · simpa using sampleWithReplacement_le_sampleWithoutReplacement_add_ties
      (prefixLaw μ X n) hS hSx A

/-- **Finite de Finetti with ties, total-variation form.** Under the hypotheses of
`finiteDeFinetti_ties`, Mathlib's extended total variation distance between the `m`-prefix law
and the with-replacement sample of the `n`-prefix law is at most
`2 * ENNReal.ofReal (1 - p - t * min p (1 - p) * P((X₀, …, Xₙ₋₁) ∈ S))`. -/
theorem ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_ties
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {S : Set (Fin n → α)} (hS : MeasurableSet S)
    (hSx : ∀ x ∈ S, ¬ Function.Injective x) :
    let p : ℝ := n.descFactorial m / (n : ℝ) ^ m
    let t : ℝ := m.descFactorial 2 / n.descFactorial 2
    etvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * ENNReal.ofReal (1 - p - t * min p (1 - p) * (prefixLaw μ X n S).toReal) := by
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  simpa using etvDist_sampleWithoutReplacement_sampleWithReplacement_le_ties
    (ι := Fin m) (prefixLaw μ X n) hS hSx

end FiniteExchangeability

end Probability

end TauCeti
