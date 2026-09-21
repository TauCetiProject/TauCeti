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

For `m > 0`, `blockMarginals P m i` is the pushforward of `P` to the `i`-th consecutive block of
`m` coordinates. Permuting those blocks extends canonically to a permutation of all path
coordinates by keeping the within-block position fixed. Thus an invariant law on random path
measures makes the block marginals fully exchangeable. Applying the measurable injective code for
probability measures and de Finetti gives a conditional-i.i.d. factorization for every fixed
width.

These block marginals retain each finite-dimensional marginal of the random path law, rather than
only its one-coordinate marginals. A block of width `n * m` canonically splits into `n` consecutive
blocks of width `m`; the restriction identities below make the finite-dimensional systems at
different widths compatible. They are the input for comparing the conditional directing laws
obtained at those widths.

## Main definitions and results

* `MeasureTheory.ProbabilityMeasure.blockMarginals` -- the sequence of consecutive
  `m`-coordinate marginals;
* `MeasureTheory.ProbabilityMeasure.codedBlockMarginals` -- those marginals in the canonical
  measurable code;
* `TauCeti.Probability.blockSplitEquiv` -- the measurable equivalence splitting a block of width
  `n * m` into `n` blocks of width `m`;
* `MeasureTheory.ProbabilityMeasure.blockMarginals_mul_map_blockSplitEquiv` -- the joint law of
  the split large block is the law of the corresponding consecutive small blocks;
* `MeasureTheory.ProbabilityMeasure.blockMarginals_mul_map_blockRestriction` -- each component of
  that joint law is the corresponding small block marginal;
* `MeasureTheory.ProbabilityMeasure.codedBlockMarginals_mul_map_blockRestriction` -- the same
  compatibility after applying the canonical probability-measure code;
* `TauCeti.Probability.fullyExchangeable_blockMarginals_of_invariant` -- invariance of the random
  path-measure law makes the block marginals fully exchangeable;
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

open TauCeti.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- The index in the `i`-th consecutive block of width `m` at within-block position `j`. -/
private def blockIndex (m : ℕ) [NeZero m] (i : ℕ) (j : Fin m) : ℕ :=
  (Nat.divModEquiv m).symm (i, j)

/-- The path of consecutive `m`-coordinate marginals of a probability measure on path space.
The positive-width hypothesis is exactly what identifies `ℕ` with `ℕ × Fin m`. -/
def _root_.MeasureTheory.ProbabilityMeasure.blockMarginals
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m] :
    ℕ → ProbabilityMeasure (Fin m → α) :=
  fun i => P.map fun x j => x (blockIndex m i j)

/-- Evaluation of the path of finite block marginals. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_apply
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m] (i : ℕ) :
    P.blockMarginals m i =
      P.map (fun x j => x ((Nat.divModEquiv m).symm (i, j))) :=
  (rfl)

open MeasureTheory.ProbabilityMeasure

/-- The path of finite block marginals depends measurably on the probability measure on path
space. -/
theorem measurable_blockMarginals (m : ℕ) [NeZero m] :
    Measurable (blockMarginals (α := α) · m) :=
  Measurable.of_eval fun i =>
    TauCeti.MeasureTheory.measurable_probabilityMeasure_map
      (Measurable.of_eval fun j => measurable_pi_apply (blockIndex m i j))

/-! ### Compatibility between block widths -/

/-- The measurable equivalence that splits a block of width `n * m` into `n` consecutive blocks
of width `m`. The outer coordinate chooses the small block and the inner coordinate chooses a
position within it. -/
def blockSplitEquiv (α : Type*) [MeasurableSpace α] (m n : ℕ) :
    (Fin (n * m) → α) ≃ᵐ (Fin n → Fin m → α) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin (n * m) => α)
    (finProdFinEquiv : Fin n × Fin m ≃ Fin (n * m))).symm.trans
      (MeasurableEquiv.curry (Fin n) (Fin m) α)

/-- Splitting a finite block reads its `(r, j)` coordinate at the flattened index
`j + m * r`. -/
@[simp]
theorem blockSplitEquiv_apply (m n : ℕ) (x : Fin (n * m) → α) (r : Fin n) (j : Fin m) :
    blockSplitEquiv α m n x r j = x (finProdFinEquiv (r, j)) :=
  (rfl)

/-- Joining split blocks reads a flattened coordinate from its quotient and remainder. -/
@[simp]
theorem blockSplitEquiv_symm_apply (m n : ℕ) (x : Fin n → Fin m → α) (k : Fin (n * m)) :
    (blockSplitEquiv α m n).symm x k =
      x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 :=
  by
    have h := blockSplitEquiv_apply m n ((blockSplitEquiv α m n).symm x)
      (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    have hfun := congrFun (congrFun (Equiv.apply_symm_apply (blockSplitEquiv α m n).toEquiv x)
      (finProdFinEquiv.symm k).1) (finProdFinEquiv.symm k).2
    have hk : finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2) = k :=
      Equiv.apply_symm_apply finProdFinEquiv k
    calc
      (blockSplitEquiv α m n).symm x k =
          (blockSplitEquiv α m n).symm x
            (finProdFinEquiv ((finProdFinEquiv.symm k).1, (finProdFinEquiv.symm k).2)) :=
        congrArg ((blockSplitEquiv α m n).symm x) hk.symm
      _ = x (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2 := h.symm.trans hfun

/-- Restriction of a block of width `n * m` to its `r`-th consecutive subblock of width `m`. -/
def blockRestriction (m n : ℕ) (r : Fin n) : (Fin (n * m) → α) → (Fin m → α) :=
  fun x => blockSplitEquiv α m n x r

/-- Restricting a finite block reads the corresponding flattened coordinate. -/
@[simp]
theorem blockRestriction_apply (m n : ℕ) (r : Fin n) (x : Fin (n * m) → α) (j : Fin m) :
    blockRestriction (α := α) m n r x j = x (finProdFinEquiv (r, j)) :=
  (rfl)

/-- Restriction to a fixed subblock is measurable. -/
theorem measurable_blockRestriction (m n : ℕ) (r : Fin n) :
    Measurable (blockRestriction (α := α) m n r) :=
  (measurable_pi_apply r).comp (blockSplitEquiv α m n).measurable

private theorem blockIndex_mul (m n : ℕ) [NeZero m] [NeZero n]
    (i : ℕ) (r : Fin n) (j : Fin m) :
    blockIndex (n * m) i (finProdFinEquiv (r, j)) =
      blockIndex m (i * n + r) j := by
  -- Unfold both indexing equivalences so the flattened natural-number indices are explicit.
  change i * (n * m) + (j + m * r) = (i * n + r) * m + j
  ring

/-- **A large block is the joint law of its consecutive smaller blocks.** Splitting the `i`-th
block of width `n * m` gives the `n` consecutive width-`m` blocks numbered
`i * n, ..., i * n + n - 1`, with their dependence retained. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_mul_map_blockSplitEquiv
    (P : ProbabilityMeasure (ℕ → α)) (m n : ℕ) [NeZero m] [NeZero n] (i : ℕ) :
    (P.blockMarginals (n * m) i).map (blockSplitEquiv α m n) =
      P.map (fun x (r : Fin n) j => x ((Nat.divModEquiv m).symm (i * n + r, j))) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.blockMarginals_apply]
  rw [Measure.map_map]
  · congr 1
    funext x r j
    exact congrArg x (blockIndex_mul m n i r j)
  · exact (blockSplitEquiv α m n).measurable
  · exact Measurable.of_eval fun j => measurable_pi_apply (blockIndex (n * m) i j)

/-- **Restriction compatibility for block marginals.** The `r`-th width-`m` subblock of the
`i`-th width-`n * m` block is the width-`m` block numbered `i * n + r`. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_mul_map_blockRestriction
    (P : ProbabilityMeasure (ℕ → α)) (m n : ℕ) [NeZero m] [NeZero n]
    (i : ℕ) (r : Fin n) :
    (P.blockMarginals (n * m) i).map (blockRestriction (α := α) m n r) =
      P.blockMarginals m (i * n + r) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.blockMarginals_apply]
  rw [Measure.map_map]
  · congr 1
    funext x j
    exact congrArg x (blockIndex_mul m n i r j)
  · exact measurable_blockRestriction m n r
  · exact Measurable.of_eval fun j => measurable_pi_apply (blockIndex (n * m) i j)

/-- The permutation of path coordinates induced by permuting blocks and preserving the position
inside each block. -/
private def blockPerm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (Nat.divModEquiv m).trans
    ((Equiv.prodCongr τ (Equiv.refl (Fin m))).trans (Nat.divModEquiv m).symm)

@[simp]
private theorem blockPerm_blockIndex (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ)
    (i : ℕ) (j : Fin m) :
    blockPerm m τ (blockIndex m i j) = blockIndex m (τ i) j := by
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
    exact congrArg x (blockPerm_blockIndex m τ i j)
  · exact Measurable.of_eval fun j =>
      measurable_pi_apply (blockIndex m i j)
  · exact measurable_reindex (blockPerm m τ)

/-- The finite block marginals of a random path measure, represented in the canonical measurable
injective code for probability measures on a countably generated space. -/
def _root_.MeasureTheory.ProbabilityMeasure.codedBlockMarginals
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] :
    ℕ → (ProbabilityMeasureCodeIndex (Fin m → α) → ℝ≥0∞) :=
  fun i => probabilityMeasureCode (P.blockMarginals m i)

/-- Evaluation of a coded finite block marginal. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.codedBlockMarginals_apply
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] (i : ℕ) :
    P.codedBlockMarginals m i = probabilityMeasureCode (P.blockMarginals m i) :=
  (rfl)

/-- **Restriction compatibility in the canonical probability-measure code.** Coding the
`r`-th small-block marginal extracted from a large block gives the already-defined code of the
corresponding width-`m` block. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.codedBlockMarginals_mul_map_blockRestriction
    (P : ProbabilityMeasure (ℕ → α)) (m n : ℕ) [NeZero m] [NeZero n]
    [MeasurableSpace.CountablyGenerated (Fin m → α)]
    (i : ℕ) (r : Fin n) :
    probabilityMeasureCode
        ((P.blockMarginals (n * m) i).map (blockRestriction (α := α) m n r)) =
      P.codedBlockMarginals m (i * n + r) := by
  rw [P.blockMarginals_mul_map_blockRestriction]
  rfl

/-- The path of coded finite block marginals is measurable. -/
theorem measurable_codedBlockMarginals (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] :
    Measurable (codedBlockMarginals (α := α) · m) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasureCode.comp
      ((measurable_pi_apply i).comp (measurable_blockMarginals m))

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
