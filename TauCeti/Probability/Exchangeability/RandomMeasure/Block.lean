/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.RandomMeasure.Basic
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Exchangeability.FullyExchangeable
import TauCeti.Probability.Exchangeability.Map

/-!
# Finite block marginals of an invariant random path measure

A law on random probability measures on path space may be invariant under coordinate
permutations even though a sampled measure is not itself exchangeable. `RandomMeasure.Basic`
extracts the resulting exchangeable sequence of one-coordinate marginals. Here the same argument
is carried out for every positive finite block width.

For `m > 0`, `P.blockMarginals m i` is the pushforward of `P` to the `i`-th consecutive block of
`m` coordinates, from `TauCeti.Probability.Process.PathLaw.Marginals`. Permuting those blocks by
`τ` is the permutation `blockPerm m τ` of all path coordinates, which keeps the within-block
position fixed. Thus an invariant law on random path measures makes the block marginals fully
exchangeable. Applying the measurable injective code for probability measures and de Finetti
gives a conditional-i.i.d. factorization for every fixed width. Unlike the one-coordinate
marginals, the block marginals at all positive widths determine the random path measure.

## Main results

* `TauCeti.Probability.fullyExchangeable_blockMarginals_of_invariant` -- invariance of the random
  path-measure law makes the block marginals fully exchangeable;
* `TauCeti.Probability.exchangeable_codedBlockMarginals_of_invariant` -- so are the coded block
  marginals, as an exchangeable process;
* `TauCeti.Probability.conditionallyIID_codedBlockMarginals_of_invariant` -- their conditional
  de Finetti factorization.

## References

* D. Aldous, "Representations for partially exchangeable arrays of random variables", *Journal of
  Multivariate Analysis* 11 (1981), 581--598.
* O. Kallenberg, *Probabilistic Symmetries and Invariance Principles*, Springer, 2005, Chapter 7.

No material is adapted from `cameronfreer/exchangeability`, which treats ordinary exchangeable
sequences rather than invariant random measures.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

open TauCeti.MeasureTheory MeasureTheory.ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- **The finite block marginals of an invariant random path measure are fully exchangeable.**

The hypothesis is invariance of the law `π` under every coordinate permutation. A permutation of
the consecutive blocks is extended to the underlying path coordinates while preserving positions
inside the blocks. -/
theorem fullyExchangeable_blockMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α))) (m : ℕ) [NeZero m]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    FullyExchangeable π fun i P => blockMarginals P m i := by
  intro τ
  have hmap : Measurable fun P : ProbabilityMeasure (ℕ → α) =>
      P.map (permReindex (blockPerm m τ)) :=
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map
      (measurable_reindex (blockPerm m τ))
  have hfun : (fun P : ProbabilityMeasure (ℕ → α) =>
      fun i => blockMarginals P m (τ i)) =
      blockMarginals (m := m) ∘ fun P => P.map (permReindex (blockPerm m τ)) := by
    funext P
    exact (P.blockMarginals_map_permReindex_blockPerm m τ).symm
  calc
    π.map (fun P => fun i => blockMarginals P m (τ i)) =
        π.map (blockMarginals (m := m) ∘
          fun P => P.map (permReindex (blockPerm m τ))) := by rw [hfun]
    _ = (π.map fun P => P.map (permReindex (blockPerm m τ))).map
          (blockMarginals (m := m)) :=
      (Measure.map_map (measurable_blockMarginals m) hmap).symm
    _ = π.map (blockMarginals (m := m)) := by rw [hπ (blockPerm m τ)]
    _ = pathLaw π (fun i P => blockMarginals P m i) := (rfl)

/-- **The coded finite block marginals of an invariant random path measure are exchangeable.**
The code loses no information about any fixed-width marginal. -/
theorem exchangeable_codedBlockMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α))) (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    Exchangeable π fun i P => codedBlockMarginals P m i := by
  have h := (fullyExchangeable_blockMarginals_of_invariant π m hπ).exchangeable
    (fun _ => ((measurable_pi_apply _).comp
      (measurable_blockMarginals m)).aemeasurable)
  simpa only [codedBlockMarginals_apply] using
    h.map_values measurable_probabilityMeasureCode
      (fun _ => ((measurable_pi_apply _).comp
        (measurable_blockMarginals m)).aemeasurable)

/-- **Conditional de Finetti factorization of the coded finite block marginals of an invariant
random path measure.** The evaluation code is injective, so this retains every marginal on a
consecutive block of the chosen positive width. -/
theorem conditionallyIID_codedBlockMarginals_of_invariant
    (π : Measure (ProbabilityMeasure (ℕ → α))) [IsFiniteMeasure π]
    (m : ℕ) [NeZero m] [MeasurableSpace.CountablyGenerated (Fin m → α)]
    (hπ : ∀ τ : Equiv.Perm ℕ,
      π.map (fun P => P.map (permReindex τ)) = π) :
    ConditionallyIID π fun i P => codedBlockMarginals P m i :=
  conditionallyIID_of_exchangeable
    (exchangeable_codedBlockMarginals_of_invariant π m hπ)
    fun _ => ((measurable_pi_apply _).comp
      (measurable_codedBlockMarginals m)).aemeasurable

end Probability

end TauCeti

end

end
