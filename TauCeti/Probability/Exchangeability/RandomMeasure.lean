/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

-- Public: the coding theorem is the endpoint for the exchangeable sequence of coordinate
-- marginals, and re-exports the exchangeability predicates used below.
public import TauCeti.Probability.DeFinetti.Coding
-- Public: the measurable injective code occurs in the standard-Borel factorization.
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding
-- Non-public: measurability of pushforward on probability measures is used in the proofs.
import TauCeti.MeasureTheory.Measure.Measurability
-- Non-public: full exchangeability is used only to prove the finitary process predicate.
import TauCeti.Probability.Exchangeability.FullyExchangeable
import TauCeti.Probability.Exchangeability.Map

/-!
# Coordinate marginals of an invariant random path measure

A random probability measure `P` on path space need not be exchangeable almost surely even when
its law is invariant under coordinate permutations.  The distinction is essential for separately
exchangeable arrays: their row-directing measure transforms equivariantly under column
permutations, while its distribution is invariant.

This file extracts the first exchangeable sequence carried by such a random measure.  The path
`coordinateMarginals P` records the one-coordinate pushforwards

```text
j ↦ P.map (x ↦ x j).
```

It is equivariant under reindexing of `P`.  Consequently, if a law `π` on random path measures is
invariant under pushforward by every coordinate permutation, then `coordinateMarginals`, viewed as
a process on the probability space `π`, is exchangeable.  De Finetti therefore resolves these
random marginals, after applying a measurable injective code, into a directing law and, in the
probability case, into a measurable function of one global parameter and independent uniform
variables indexed by the coordinates. The code is necessary because Mathlib does not equip the
Giry measurable space on `ProbabilityMeasure α` with a standard-Borel instance.

The coordinate marginals do not in general determine `P`; this API records only its
one-coordinate pushforwards, not its higher finite-dimensional marginals.

## Main definitions and results

* `TauCeti.Probability.coordinateMarginals` -- the path of one-coordinate marginals of a
  path law;
* `TauCeti.Probability.coordinateMarginals_map_permReindex` -- equivariance under coordinate
  permutations;
* `TauCeti.Probability.exchangeable_coordinateMarginals_of_invariant` -- an invariant law of
  random path measures gives an exchangeable measure-valued sequence;
* `TauCeti.Probability.codedCoordinateMarginals` -- the same marginals in a standard Borel
  code;
* `TauCeti.Probability.conditionallyIID_codedCoordinateMarginals_of_invariant` -- the
  corresponding conditional de Finetti factorization;
* `TauCeti.Probability.exists_pathLaw_codedCoordinateMarginals_eq_map_unitIntervalCoding` -- the
  functional representation by a global parameter and independent coordinate noise.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats ordinary exchangeable
sequences rather than invariant random measures.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory unitInterval

open scoped ENNReal

namespace TauCeti

namespace Probability

open TauCeti.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The path of one-coordinate marginals of a probability measure on path space. -/
def coordinateMarginals (P : ProbabilityMeasure (ℕ → α)) : ℕ → ProbabilityMeasure α :=
  fun i => P.map (fun x => x i)

/-- Evaluation of the path of coordinate marginals. -/
@[simp]
theorem coordinateMarginals_apply (P : ProbabilityMeasure (ℕ → α)) (i : ℕ) :
    coordinateMarginals P i = P.map (fun x => x i) :=
  (rfl)

/-- The coordinate-marginal path depends measurably on the probability measure on path space. -/
theorem measurable_coordinateMarginals :
    Measurable (coordinateMarginals : ProbabilityMeasure (ℕ → α) →
      ℕ → ProbabilityMeasure α) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasure_map (measurable_pi_apply i)

/-- Coordinate marginals are equivariant under a permutation of path coordinates. -/
@[simp]
theorem coordinateMarginals_map_permReindex (P : ProbabilityMeasure (ℕ → α))
    (τ : Equiv.Perm ℕ) :
    coordinateMarginals (P.map (permReindex τ)) = permReindex τ (coordinateMarginals P) := by
  funext i
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coordinateMarginals_apply, ProbabilityMeasure.toMeasure_map, permReindex_apply]
  have hperm : permReindex (α := α) τ = fun x : ℕ → α => fun k => x (τ k) := by
    funext x k
    rw [permReindex_apply]
  rw [hperm]
  rw [Measure.map_map (measurable_pi_apply i) (measurable_reindex τ)]
  rfl

/-- The coordinate marginals of a random path measure, represented in the canonical measurable
injective code for probability measures on a countably generated space. -/
def codedCoordinateMarginals [MeasurableSpace.CountablyGenerated α]
    (P : ProbabilityMeasure (ℕ → α)) :
    ℕ → (ProbabilityMeasureCodeIndex α → ℝ≥0∞) :=
  fun i => probabilityMeasureCode (coordinateMarginals P i)

/-- Evaluation of a coded coordinate marginal. -/
@[simp]
theorem codedCoordinateMarginals_apply [MeasurableSpace.CountablyGenerated α]
    (P : ProbabilityMeasure (ℕ → α)) (i : ℕ) :
    codedCoordinateMarginals P i =
      probabilityMeasureCode (coordinateMarginals P i) :=
  (rfl)

/-- The path of coded coordinate marginals is measurable. -/
theorem measurable_codedCoordinateMarginals [MeasurableSpace.CountablyGenerated α] :
    Measurable (codedCoordinateMarginals (α := α)) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasureCode.comp
      ((measurable_pi_apply i).comp measurable_coordinateMarginals)

/-- Coding commutes with reindexing the coordinate marginals. -/
@[simp]
theorem codedCoordinateMarginals_map_permReindex [MeasurableSpace.CountablyGenerated α]
    (P : ProbabilityMeasure (ℕ → α)) (τ : Equiv.Perm ℕ) :
    codedCoordinateMarginals (P.map (permReindex τ)) =
      permReindex τ (codedCoordinateMarginals P) := by
  funext i
  simp only [codedCoordinateMarginals_apply, permReindex_apply]
  exact congrArg probabilityMeasureCode
    (congrFun (coordinateMarginals_map_permReindex P τ) i)

/-- **The coordinate marginals of an invariant random path measure are fully exchangeable.**

The hypothesis is invariance of the *law* `π` under pushing a sampled path measure forward by a
coordinate permutation; it does not assert that the sampled measure itself is exchangeable. -/
theorem fullyExchangeable_coordinateMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α)))
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    FullyExchangeable π fun i P => coordinateMarginals P i := by
  intro τ
  have hmap : Measurable fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ) :=
    measurable_probabilityMeasure_map (measurable_reindex τ)
  have hfun : (fun P : ProbabilityMeasure (ℕ → α) =>
      fun i => coordinateMarginals P (τ i)) =
      coordinateMarginals ∘ fun P => P.map (permReindex τ) := by
    funext P
    exact (coordinateMarginals_map_permReindex P τ).symm
  calc
    π.map (fun P => fun i => coordinateMarginals P (τ i)) =
        π.map (coordinateMarginals ∘
          fun P => P.map (permReindex τ)) := by rw [hfun]
    _ = (π.map fun P => P.map (permReindex τ)).map coordinateMarginals :=
      (Measure.map_map measurable_coordinateMarginals hmap).symm
    _ = π.map coordinateMarginals := by rw [hπ τ]
    _ = pathLaw π (fun i P => coordinateMarginals P i) := (rfl)

/-- **The coordinate marginals of an invariant random path measure are exchangeable.** -/
theorem exchangeable_coordinateMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α)))
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    Exchangeable π fun i P => coordinateMarginals P i :=
  (fullyExchangeable_coordinateMarginals_of_invariant π hπ).exchangeable
    fun _ => ((measurable_pi_apply _).comp
      measurable_coordinateMarginals).aemeasurable

/-- **The coded coordinate marginals of an invariant random path measure are exchangeable.**
The code loses no information about any coordinate marginal. -/
theorem exchangeable_codedCoordinateMarginals_of_invariant
    [MeasurableSpace.CountablyGenerated α]
    (π : Measure (ProbabilityMeasure (ℕ → α)))
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    Exchangeable π fun i P => codedCoordinateMarginals P i :=
  by
    simpa only [codedCoordinateMarginals_apply] using
      (exchangeable_coordinateMarginals_of_invariant π hπ).map_values
        measurable_probabilityMeasureCode
        fun _ => ((measurable_pi_apply _).comp
          measurable_coordinateMarginals).aemeasurable

/-- **Conditional de Finetti factorization of the coded coordinate marginals of an invariant
random path measure.** Because the evaluation code is injective, this retains every
one-coordinate marginal even though `ProbabilityMeasure α` itself is not available as a standard
Borel value space. -/
theorem conditionallyIID_codedCoordinateMarginals_of_invariant
    [MeasurableSpace.CountablyGenerated α]
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsFiniteMeasure π]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    ConditionallyIID π fun i P => codedCoordinateMarginals P i :=
  conditionallyIID_of_exchangeable
    (exchangeable_codedCoordinateMarginals_of_invariant π hπ)
    fun _ => ((measurable_pi_apply _).comp
      measurable_codedCoordinateMarginals).aemeasurable

/-- **Uniform-noise representation of the coded coordinate marginals of an invariant random path
measure.** Under a probability law `π`, their whole path has the law obtained by drawing one
global law on the code space and applying its canonical randomization to independent
coordinate-indexed uniform variables. -/
theorem exists_pathLaw_codedCoordinateMarginals_eq_map_unitIntervalCoding
    [MeasurableSpace.CountablyGenerated α]
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsProbabilityMeasure π]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    ∃ Λ : ProbabilityMeasure
        (ProbabilityMeasure (ProbabilityMeasureCodeIndex α → ℝ≥0∞)),
      pathLaw π (fun i P => codedCoordinateMarginals P i) =
        ((Λ : Measure (ProbabilityMeasure
            (ProbabilityMeasureCodeIndex α → ℝ≥0∞))).prod
          (Measure.infinitePi fun _ : ℕ => (volume : Measure I))).map
            fun q i => unitIntervalCoding
              (ProbabilityMeasureCodeIndex α → ℝ≥0∞) q.1 (q.2 i) :=
  exists_pathLaw_eq_map_unitIntervalCoding
    (fun _ => ((measurable_pi_apply _).comp
      measurable_codedCoordinateMarginals).aemeasurable)
    (exchangeable_codedCoordinateMarginals_of_invariant π hπ)

end Probability

end TauCeti

end
