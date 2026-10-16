/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.RandomMeasure.Basic
public import TauCeti.Probability.Process.PathLaw.BlockMarginals
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Exchangeability.FullyExchangeable
import TauCeti.Probability.Exchangeability.Map

/-!
# Block marginals of an invariant random path measure

A law on random probability measures on path space may be invariant under coordinate
permutations even though a sampled measure is not itself exchangeable. For every positive width,
this file shows that the consecutive block marginals of such a random measure form a fully
exchangeable sequence. Applying the measurable injective code for probability measures and
de Finetti gives a conditional-i.i.d. factorization at each fixed width.

The symmetry-free definition, width-compatibility, coding, and reconstruction API for block
marginals lives in `TauCeti.Probability.Process.PathLaw.BlockMarginals`. Here a permutation of
the block indices is extended to a permutation of all path coordinates while preserving the
position inside each block, so invariance of the random path-measure law applies directly.

## Main results

* `TauCeti.Probability.fullyExchangeable_blockMarginals_of_invariant` -- invariance of the random
  path-measure law makes its consecutive block marginals fully exchangeable;
* `TauCeti.Probability.exchangeable_codedBlockMarginals_of_invariant` -- their canonical codes
  are exchangeable;
* `TauCeti.Probability.conditionallyIID_codedBlockMarginals_of_invariant` -- the coded block
  marginals admit a conditional de Finetti factorization.

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

open TauCeti.MeasureTheory
open MeasureTheory.ProbabilityMeasure

variable {α : Type*} [MeasurableSpace α]

/-- The permutation of path coordinates induced by permuting blocks and preserving the position
inside each block. -/
private def blockPerm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (Nat.divModEquiv m).trans
    ((Equiv.prodCongr τ (Equiv.refl (Fin m))).trans (Nat.divModEquiv m).symm)

@[simp]
private theorem blockPerm_divModEquiv_symm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ)
    (i : ℕ) (j : Fin m) :
    blockPerm m τ (i * m + j) = τ i * m + j := by
  -- Keep `divModEquiv` opaque so its inverse law applies before arithmetic simplification.
  change (Nat.divModEquiv m).symm
      ((Equiv.prodCongr τ (Equiv.refl (Fin m)))
        ((Nat.divModEquiv m) ((Nat.divModEquiv m).symm (i, j)))) =
    (Nat.divModEquiv m).symm (τ i, j)
  rw [Equiv.apply_symm_apply]
  rfl

/-- Block marginals are equivariant when a block permutation is extended to all path
coordinates. -/
private theorem blockMarginals_map_blockPerm (P : ProbabilityMeasure (ℕ → α))
    (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) :
    blockMarginals (P.map (permReindex (blockPerm m τ))) m =
      permReindex τ (blockMarginals P m) := by
  funext i
  apply ProbabilityMeasure.toMeasure_injective
  simp only [blockMarginals_apply, ProbabilityMeasure.toMeasure_map, permReindex_apply]
  rw [Measure.map_map]
  · congr 1
    funext x j
    simpa only [Function.comp_apply, permReindex_apply, Nat.divModEquiv_symm_apply] using
      congrArg x (blockPerm_divModEquiv_symm m τ i j)
  · exact Measurable.of_eval fun j =>
      measurable_pi_apply ((Nat.divModEquiv m).symm (i, j))
  · exact measurable_reindex (blockPerm m τ)

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
    exact (blockMarginals_map_blockPerm P m τ).symm
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
