/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Pi
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding
public import TauCeti.Probability.Process.PathLaw.FiniteMarginals
import TauCeti.MeasureTheory.Measure.Measurability

/-!
# Consecutive block marginals of a path law

For a positive width `m`, `ProbabilityMeasure.blockMarginals P m i` is the pushforward of a
probability measure `P` on sequence space to the `i`-th consecutive block of `m` coordinates.
Splitting a block of width `n * m` into `n` blocks of width `m` recovers the corresponding joint
law of consecutive smaller blocks, and restricting that joint law recovers each component.

The zeroth blocks of all positive widths determine the original path measure. This remains true
for random path measures when the block equalities hold almost surely on width-dependent conull
sets. The coded variants use the canonical measurable injective code for probability measures on
countably generated spaces and provide the same reconstruction principle in a standard-Borel
ambient code space.

This API is independent of any symmetry assumption. Exchangeability consequences for block
marginals of invariant random path measures are developed separately in
`TauCeti.Probability.Exchangeability.RandomMeasure.Block`.

## Main definitions and results

* `MeasureTheory.ProbabilityMeasure.blockMarginals` -- the sequence of consecutive
  `m`-coordinate marginals;
* `MeasureTheory.ProbabilityMeasure.map_blockSplitEquiv_blockMarginals_mul` -- splitting a large
  block gives the joint law of the corresponding smaller blocks;
* `MeasureTheory.ProbabilityMeasure.eq_of_blockMarginals_zero_eq` -- the zeroth blocks of every
  positive width determine a path law;
* `MeasureTheory.ProbabilityMeasure.codedBlockMarginals` -- block marginals in the canonical
  probability-measure code;
* `MeasureTheory.ProbabilityMeasure.eq_of_codedBlockMarginals_zero_eq` -- coded zeroth blocks
  determine a path law.
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
theorem _root_.MeasureTheory.ProbabilityMeasure.map_blockSplitEquiv_blockMarginals_mul
    (P : ProbabilityMeasure (ℕ → α)) (m n : ℕ) [NeZero m] [NeZero n] (i : ℕ) :
    (P.blockMarginals (n * m) i).map (blockSplitEquiv α m n) =
      P.map (fun x (r : Fin n) j => x ((Nat.divModEquiv m).symm (i * n + r, j))) := by
  apply ProbabilityMeasure.toMeasure_injective
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.blockMarginals_apply]
  rw [Measure.map_map]
  · congr 1
    funext x r j
    simp only [Function.comp_apply, blockSplitEquiv_apply]
    exact congrArg x (blockIndex_mul m n i r j)
  · exact (blockSplitEquiv α m n).measurable
  · exact Measurable.of_eval fun j => measurable_pi_apply (blockIndex (n * m) i j)

/-- **Restriction compatibility for block marginals.** The `r`-th width-`m` subblock of the
`i`-th width-`n * m` block is the width-`m` block numbered `i * n + r`. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.map_blockRestriction_blockMarginals_mul
    (P : ProbabilityMeasure (ℕ → α)) (m n : ℕ) [NeZero m] (i : ℕ) (r : Fin n) :
    (@ProbabilityMeasure.blockMarginals α _ P (n * m)
      ⟨Nat.mul_ne_zero r.neZero.out (NeZero.ne m)⟩ i).map
        (blockRestriction (α := α) m n r) =
      P.blockMarginals m (i * n + r) := by
  let _ : NeZero n := r.neZero
  have hcomp : blockRestriction (α := α) m n r =
      (fun x : Fin n → Fin m → α => x r) ∘ blockSplitEquiv α m n := by
    funext x j
    simp only [blockRestriction_apply, Function.comp_apply, blockSplitEquiv_apply]
  apply ProbabilityMeasure.toMeasure_injective
  have h := congrArg
    (fun Q : ProbabilityMeasure (Fin n → Fin m → α) =>
      (Q.map fun x => x r).toMeasure)
    (P.map_blockSplitEquiv_blockMarginals_mul m n i)
  simp only [ProbabilityMeasure.toMeasure_map, ProbabilityMeasure.blockMarginals_apply] at h ⊢
  rw [Measure.map_map (measurable_pi_apply r) (blockSplitEquiv α m n).measurable] at h
  rw [Measure.map_map (μ := P.toMeasure) (g := fun x => x r)
    (f := fun x (r : Fin n) j => x ((Nat.divModEquiv m).symm (i * n + r, j)))
    (measurable_pi_apply r) (Measurable.of_eval fun r => Measurable.of_eval fun j =>
      measurable_pi_apply ((Nat.divModEquiv m).symm (i * n + r, j)))] at h
  simpa only [hcomp, Function.comp_def] using h

/-! ### Reconstruction from the block marginals -/

/-- The zeroth block marginal of positive width `m` is the ordinary first-`m` prefix marginal.
This identifies the consecutive-block API with the finite-marginal uniqueness API. -/
-- `blockMarginals_apply` simplifies the left side, so `simpNF` rejects a `@[simp]` tag here.
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_zero_eq_map_prefixProj
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m] :
    P.blockMarginals m 0 = P.map (prefixProj α m) := by
  have hproj :
      (fun x : ℕ → α => fun j : Fin m => x ((Nat.divModEquiv m).symm (0, j))) =
        prefixProj α m := by
    funext x j
    -- Unfold the quotient-remainder inverse to expose the zeroth block coordinate.
    change x (0 * m + j) = x j
    simp
  rw [ProbabilityMeasure.blockMarginals_apply, hproj]

/-- Two path measures are equal if their zeroth block marginals agree at every positive width. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.eq_of_blockMarginals_zero_eq
    {P Q : ProbabilityMeasure (ℕ → α)}
    (h : ∀ m : ℕ, P.blockMarginals (m + 1) 0 = Q.blockMarginals (m + 1) 0) : P = Q := by
  apply ProbabilityMeasure.toMeasure_injective
  apply measure_eq_of_prefixProj_map_eq
  intro m
  let restrictSucc : (Fin (m + 1) → α) → (Fin m → α) :=
    fun x i => x i.castSucc
  have hrestrict : Measurable restrictSucc :=
    Measurable.of_eval fun i => measurable_pi_apply i.castSucc
  have hcomp : prefixProj α m = restrictSucc ∘ prefixProj α (m + 1) := by
    funext x i
    rfl
  have hnext :
      (P : Measure (ℕ → α)).map (prefixProj α (m + 1)) =
        (Q : Measure (ℕ → α)).map (prefixProj α (m + 1)) := by
    simpa only [← ProbabilityMeasure.toMeasure_map,
      ProbabilityMeasure.blockMarginals_zero_eq_map_prefixProj] using
        congrArg ProbabilityMeasure.toMeasure (h m)
  rw [hcomp, ← Measure.map_map hrestrict (measurable_prefixProj (m + 1)), hnext,
    Measure.map_map hrestrict (measurable_prefixProj (m + 1))]

/-- Two random path measures are almost surely equal if their zeroth block marginals agree
almost surely at every positive width. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.ae_eq_of_blockMarginals_zero_ae_eq
    {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {P Q : S → ProbabilityMeasure (ℕ → α)}
    (h : ∀ m : ℕ,
      (fun s => (P s).blockMarginals (m + 1) 0) =ᵐ[μ]
        fun s => (Q s).blockMarginals (m + 1) 0) :
    P =ᵐ[μ] Q := by
  filter_upwards [ae_all_iff.2 h] with s hs
  exact ProbabilityMeasure.eq_of_blockMarginals_zero_eq hs

/-! ### Canonical codes of the block marginals -/

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

/-- The path of coded finite block marginals is measurable. -/
theorem measurable_codedBlockMarginals (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] :
    Measurable (codedBlockMarginals (α := α) · m) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasureCode.comp
      ((measurable_pi_apply i).comp (measurable_blockMarginals m))

/-- Two path measures are equal if their coded zeroth block marginals agree at every positive
width, assuming countable generation of the finite product spaces being coded. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.eq_of_codedBlockMarginals_zero_eq
    [∀ m : ℕ, MeasurableSpace.CountablyGenerated (Fin (m + 1) → α)]
    {P Q : ProbabilityMeasure (ℕ → α)}
    (h : ∀ m : ℕ, P.codedBlockMarginals (m + 1) 0 = Q.codedBlockMarginals (m + 1) 0) :
    P = Q := by
  apply ProbabilityMeasure.eq_of_blockMarginals_zero_eq
  intro m
  exact probabilityMeasureCode_injective (h m)

/-- Two random path measures are almost surely equal if their coded zeroth block marginals agree
almost surely at every positive width, assuming countable generation of the finite product spaces
being coded. -/
theorem _root_.MeasureTheory.ProbabilityMeasure.ae_eq_of_codedBlockMarginals_zero_ae_eq
    [∀ m : ℕ, MeasurableSpace.CountablyGenerated (Fin (m + 1) → α)]
    {S : Type*} [MeasurableSpace S] {μ : Measure S}
    {P Q : S → ProbabilityMeasure (ℕ → α)}
    (h : ∀ m : ℕ,
      (fun s => (P s).codedBlockMarginals (m + 1) 0) =ᵐ[μ]
        fun s => (Q s).codedBlockMarginals (m + 1) 0) :
    P =ᵐ[μ] Q := by
  apply ProbabilityMeasure.ae_eq_of_blockMarginals_zero_ae_eq
  intro m
  filter_upwards [h m] with s hs
  exact probabilityMeasureCode_injective hs

end Probability

end TauCeti

end

end
