/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the directing-measure equivariance is transported to the canonical coding law.
public import TauCeti.Probability.Exchangeability.Arrays.JointLaw
-- Public: the canonical coupled coding law appears in the statements.
public import TauCeti.Probability.Process.Array.RowCoding
-- Non-public: the path coding identity is used to identify the coupled row law.
import TauCeti.Probability.DeFinetti.Coding
-- Non-public: measurability of pushforward on probability measures is used in the symmetry proof.
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Coupled row coding for separately exchangeable arrays

The first functional representation of a separately exchangeable array writes each row as a
sample from one random path law, using independent uniform noise for the rows.  For the second
level of the Aldous--Hoover argument, it is essential to retain that random path law as a
coordinate: column permutations act on it by pushforward, rather than leaving it fixed.

The general construction in `Probability.Process.Array.RowCoding` provides the canonical joint
law. If `π` is a law on probability measures on path space, `arrayRowCodingLaw π` is the law of

```text
(P, (i, j) ↦ unitIntervalCoding (ℕ → α) P (Uᵢ) j),
```

where `P` has law `π` and the `Uᵢ` are independent uniform variables.  A directing measure for
the row process of an array identifies its joint law with this canonical law.  For a separately
exchangeable array, the canonical law retains the full two-axis symmetry: row permutations act
on the coded array alone, while column permutations act simultaneously on the array and by
pushforward on `P`.

This file stops short of the final Aldous--Hoover representation, which further resolves the
random path law into column and cell noise.

## Main definitions and results

* `TauCeti.Probability.ConditionallyIIDWith.jointLaw_arrayRow_eq_arrayRowCodingLaw` -- a row
  directing measure identifies the original coupled law with the canonical coding law;
* `TauCeti.Probability.SeparatelyExchangeable.map_pairReindex_arrayRowCodingLaw_eq` -- the coupled
  coding law inherits the two-axis equivariance of the directing measure and the array.

Conversely, the canonical coupled law has the same equivariance whenever its mixing law is
invariant under column permutations, whether or not it comes from an exchangeable array
(`TauCeti.Probability.map_pairReindex_arrayRowCodingLaw_eq_of_col_invariant`, in
`Probability.Process.Array.RowCoding`).

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.
* O. Kallenberg, *Foundations of Modern Probability*, 3rd ed., Lemma 4.22, for randomization by a
  uniform variable.

No material is adapted from `cameronfreer/exchangeability`, which treats sequences rather than
arrays.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

section CodingLaw

variable [StandardBorelSpace α] [Nonempty α]

/-- A directing measure for the row process identifies its joint law with the canonical coupled
row-coding law.  Unlike the array-law-only coding theorem, this keeps the directing measure as a
coordinate, so its transformation under column permutations remains visible. -/
theorem ConditionallyIIDWith.jointLaw_arrayRow_eq_arrayRowCodingLaw
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (h : ConditionallyIIDWith μ (arrayRow X) ν) :
    (μ.map fun ω ↦ (ν ω, fun p : ℕ × ℕ ↦ X p ω)) =
      arrayRowCodingLaw (μ.map ν) := by
  have hX : ∀ p, AEMeasurable (X p) μ :=
    aemeasurable_entry_of_aemeasurable_arrayRow h.aemeasurable
  rw [← map_uncurry_jointPathLaw_arrayRow hX h.measurable_directing.aemeasurable,
    h.jointPathLaw_eq_map_unitIntervalCoding, arrayRowCodingLaw_def]
  have hinner : Measurable fun q : ProbabilityMeasure (ℕ → α) × (ℕ → unitInterval) ↦
      (q.1, fun i ↦ unitIntervalCoding (ℕ → α) q.1 (q.2 i)) :=
    measurable_fst.prodMk measurable_unitIntervalCodingPath
  rw [Measure.map_map (measurable_id.prodMap measurable_uncurry) hinner]
  refine congrArg (Measure.map · _) ?_
  funext q
  apply Prod.ext rfl
  funext p
  rfl

/-- The coupled row-coding law of a separately exchangeable array retains both symmetries.  A row
permutation reindexes only the coded array.  A column permutation also pushes the random path law
forward by the same coordinate permutation. -/
theorem SeparatelyExchangeable.map_pairReindex_arrayRowCodingLaw_eq
    {μ : Measure Ω} [IsFiniteMeasure μ] {X : ℕ × ℕ → Ω → α}
    {ν : Ω → ProbabilityMeasure (ℕ → α)}
    (h : SeparatelyExchangeable μ X)
    (hν : ConditionallyIIDWith μ (arrayRow X) ν) (σ τ : Equiv.Perm ℕ) :
    (arrayRowCodingLaw (μ.map ν)).map
        (fun q ↦
          (q.1.map (fun x : ℕ → α ↦ fun k ↦ x (τ k)), pairReindex σ τ q.2)) =
      arrayRowCodingLaw (μ.map ν) := by
  have hX : ∀ p, AEMeasurable (X p) μ :=
    aemeasurable_entry_of_aemeasurable_arrayRow hν.aemeasurable
  rw [← hν.jointLaw_arrayRow_eq_arrayRowCodingLaw,
    AEMeasurable.map_map_of_aemeasurable]
  · have hfun :
        ((fun q : ProbabilityMeasure (ℕ → α) × (ℕ × ℕ → α) ↦
            (q.1.map (fun x : ℕ → α ↦ fun k ↦ x (τ k)), pairReindex σ τ q.2)) ∘
          fun ω ↦ (ν ω, fun p : ℕ × ℕ ↦ X p ω)) =
            fun ω ↦ ((ν ω).map (fun x : ℕ → α ↦ fun k ↦ x (τ k)),
              fun p : ℕ × ℕ ↦ X (σ p.1, τ p.2) ω) := by
          funext ω
          rw [Function.comp_apply]
          refine Prod.ext rfl ?_
          funext p
          simp only [pairReindex_apply]
    rw [hfun]
    exact h.jointLaw_arrayRow_pairReindex_eq hν σ τ
  · exact ((TauCeti.MeasureTheory.measurable_probabilityMeasure_map
      (measurable_reindex τ)).comp measurable_fst).prodMk
        ((measurable_pairReindex σ τ).comp measurable_snd) |>.aemeasurable
  · exact hν.measurable_directing.aemeasurable.prodMk
      (AEMeasurable.of_eval hX)

end CodingLaw

end Probability

end TauCeti

end

end
