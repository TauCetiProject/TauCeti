/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Alexander Richard Towell
-/
module

public import TauCeti.MeasureTheory.Measure.TotalVariation
public import TauCeti.Probability.Exchangeability.SamplingWithoutReplacement

/-!
# Quantitative finite de Finetti approximation

Let `x : κ → α` be a nonempty finite population. Its empirical distribution is the pushforward
of the uniform law on `κ` by `x`. Sampling `ι` entries from that distribution independently is
therefore the same as choosing a uniform map `ι → κ` and reading the selected entries of `x`.

The general sampling laws, their empirical-product characterization, and their collision bounds
live in `TauCeti.Probability.PopulationSampling.Finite`.

For a random population with law `ρ`, `sampleWithReplacement ρ` draws the population and,
independently, a uniform map `ι → κ`, and reads the selected entries. It is the same
`samplePopulation` construction as `sampleWithoutReplacement ρ`, which instead draws a uniform
injective map; when `κ` is nonempty, by the previous paragraph it is the mixture over `ρ` of the
finite product laws of the empirical distributions. The law `sampleWithoutReplacement ρ` already
represents every shorter marginal of a finite exchangeable process. The collision coupling between
uniform maps and uniform injective maps consequently gives, for every measurable event `A`,

```text
prefixLaw μ X m A ≤ sampleWithReplacement (prefixLaw μ X n) A + choose(m, 2) / n
sampleWithReplacement (prefixLaw μ X n) A ≤ prefixLaw μ X m A + choose(m, 2) / n.
```

Thus, for `n > 0`, every `m`-coordinate marginal of an `n`-exchangeable process is quantitatively
approximated by a mixture of `m`-fold product measures of empirical distributions; for
`n = m = 0` both sides are the shared sampling construction on the empty index type. The bound is
stated eventwise, which fixes its normalization; in terms of Mathlib's total variation distance
`etvDist`, the signed-measure norm `‖P - Q‖` (twice `sup_A |P A - Q A|`), it gives
`etvDist P Q ≤ 2 * choose(m, 2) / n`.

Counting injective selections instead of using the union bound gives the sharper eventwise
error `1 - n.descFactorial m / n^m`, and twice that error for the signed-measure norm.
This includes `m = n = 0`, whose error is zero. For a nonempty population the error is the
exact index-collision probability; it need not equal the discrepancy of the sampled values,
since distinct indices can hold the same value.

## Main declarations

* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti`: the paired eventwise finite de Finetti
  bound;
* `TauCeti.Probability.ExchangeableAt.prefixLaw_le_sampleWithReplacement_add` and
  `TauCeti.Probability.ExchangeableAt.sampleWithReplacement_le_prefixLaw_add`: the two sides of
  the finite de Finetti bound;
* `TauCeti.Probability.ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le`: the same
  bound for Mathlib's total variation distance `etvDist`, with the signed-measure normalization.
* `TauCeti.Probability.ExchangeableAt.finiteDeFinetti_exact_collision`: the sharper eventwise
  bound using the exact collision probability, with a corresponding total-variation theorem.
  The two named one-sided corollaries have the suffix `add_exact_collision`.

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

/-- **Finite de Finetti theorem.** If the first `n` coordinates of a process are exchangeable and
`m ≤ n`, then its `m`-prefix law and the with-replacement sample of its `n`-prefix law differ by
at most `choose m 2 / n` on every measurable event, in both directions. For `n > 0` that sample is
the empirical-product mixture (`sampleWithReplacement_eq_bind_pi_empiricalMeasureOfFintype`). -/
theorem ExchangeableAt.finiteDeFinetti
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        m.choose 2 / n ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        m.choose 2 / n := by
  let _ : IsProbabilityMeasure (prefixLaw μ X n) := by
    rw [prefixLaw_def, blockLaw_def]
    infer_instance
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  constructor
  · simpa using sampleWithoutReplacement_le_sampleWithReplacement_add
      (ρ := prefixLaw μ X n) hA
  · simpa using sampleWithReplacement_le_sampleWithoutReplacement_add
      (ρ := prefixLaw μ X n) hA

/-- **Finite de Finetti with the exact collision error.** The discrepancy on any measurable
event between an exchangeable prefix and its with-replacement sample (the empirical-product
mixture when `n > 0`) is bounded by `1 - (n)_m / n^m`, where `(n)_m` counts ordered injections.
This retains the overlap between pairwise collisions lost in the union bound.
The empty-sample case `m = n = 0` has error zero. -/
theorem ExchangeableAt.finiteDeFinetti_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) ∧
      sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
        (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) := by
  let _ : Nonempty (Fin m → Fin n) := ⟨fun i => i.castLE hmn⟩
  let _ : IsProbabilityMeasure (prefixLaw μ X n) := by
    rw [prefixLaw_def, blockLaw_def]
    infer_instance
  rw [← h.sampleWithoutReplacement_eq_prefixLaw hmn hX]
  constructor
  · simpa using
      sampleWithoutReplacement_le_sampleWithReplacement_add_collision
        (ρ := prefixLaw μ X n) hA
  · simpa using
      sampleWithReplacement_le_sampleWithoutReplacement_add_collision
        (ρ := prefixLaw μ X n) hA

/-- **Exact finite de Finetti bound, exchangeable law to empirical mixture.** Under finite
exchangeability and `m ≤ n`, the prefix law exceeds its with-replacement sample on a measurable
event by at most the exact index-collision error. -/
theorem ExchangeableAt.prefixLaw_le_sampleWithReplacement_add_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
      (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) :=
  (h.finiteDeFinetti_exact_collision hmn hX hA).1

/-- **Exact finite de Finetti bound, empirical mixture to exchangeable law.** Under finite
exchangeability and `m ≤ n`, the with-replacement sample exceeds the prefix law on a measurable
event by at most the exact index-collision error. -/
theorem ExchangeableAt.sampleWithReplacement_le_prefixLaw_add_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
      (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) :=
  (h.finiteDeFinetti_exact_collision hmn hX hA).2

/-- **Quantitative finite de Finetti bound, exchangeable law to empirical mixture.** If the first
`n` coordinates of a process are exchangeable and `m ≤ n`, then every measurable event under the
`m`-prefix law has mass at most its mass under sampling `m` entries with replacement from the first
`n` coordinates, plus `choose m 2 / n`. For `n > 0` that sample is the mixture of `m`-fold products
of the empirical distribution of the first `n` coordinates. -/
theorem ExchangeableAt.prefixLaw_le_sampleWithReplacement_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    prefixLaw μ X m A ≤ sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A +
      m.choose 2 / n :=
  (h.finiteDeFinetti hmn hX hA).1

/-- **Quantitative finite de Finetti bound, empirical mixture to exchangeable law.** Under the
same hypotheses, every measurable event under the with-replacement sample (for `n > 0`, the
empirical-product mixture) has mass at most its mass under the `m`-prefix law plus
`choose m 2 / n`. -/
theorem ExchangeableAt.sampleWithReplacement_le_prefixLaw_add
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) {A : Set (Fin m → α)}
    (hA : MeasurableSet A) :
    sampleWithReplacement (ι := Fin m) (prefixLaw μ X n) A ≤ prefixLaw μ X m A +
      m.choose 2 / n :=
  (h.finiteDeFinetti hmn hX hA).2

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
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun _ hA => h.prefixLaw_le_sampleWithReplacement_add hmn hX hA)
    (fun _ hA => h.sampleWithReplacement_le_prefixLaw_add hmn hX hA)

/-- The finite de Finetti approximation with exact collision error, for Mathlib's total
variation distance `etvDist`. Its signed-measure normalization is twice the probability-distance
convention `sup_A |P(A) - Q(A)|`; no optimality for each individual population law is asserted. -/
theorem ExchangeableAt.etvDist_prefixLaw_sampleWithReplacement_le_exact_collision
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : ℕ → Ω → α} {m n : ℕ} (h : ExchangeableAt μ X n) (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    etvDist (prefixLaw μ X m) (sampleWithReplacement (ι := Fin m) (prefixLaw μ X n)) ≤
      2 * (1 - (n.descFactorial m : ℝ≥0∞) / (n : ℝ≥0∞) ^ m) := by
  rw [two_mul]
  exact etvDist_le_of_forall_le_add
    (fun _ hA => h.prefixLaw_le_sampleWithReplacement_add_exact_collision hmn hX hA)
    (fun _ hA => h.sampleWithReplacement_le_prefixLaw_add_exact_collision hmn hX hA)

end FiniteExchangeability

end Probability

end TauCeti
