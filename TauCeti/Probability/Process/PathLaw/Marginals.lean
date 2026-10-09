/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Pi
public import TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding
public import TauCeti.Probability.Process.PathLaw.Basic
import TauCeti.MeasureTheory.Measure.Measurability
import TauCeti.Probability.Process.PathLaw.FiniteMarginals

/-!
# Coordinate and block marginals of a probability measure on path space

A probability measure `P` on path space `ℕ → α` has a path of one-coordinate marginals
`P.coordinateMarginals : ℕ → ProbabilityMeasure α`, with `i ↦ P.map (x ↦ x i)`, and, for each
positive width `m`, a path of consecutive block marginals `P.blockMarginals m`, whose `i`-th entry
is the law of the coordinates `i * m, …, i * m + m - 1`. Both paths depend measurably on `P`, so a
random path measure induces random measure-valued sequences.

Both paths are equivariant under reindexing. Permuting the path coordinates by `τ` permutes the
coordinate marginals by `τ`. Permuting the blocks of width `m` by `τ` and keeping the position
inside each block fixed is the permutation `Nat.blockPerm m τ` of path coordinates, and it permutes
the block marginals by `τ`. This equivariance is what transfers invariance in law of a random
path measure under coordinate permutations to its sequences of marginals.

The coordinate marginals do not determine `P` in general, since they forget its higher
finite-dimensional marginals. The block marginals do. A block of width `n * m` splits into `n`
consecutive blocks of width `m` along `TauCeti.MeasureTheory.blockSplitEquiv`, which makes the
block marginals at different widths compatible, and the zeroth blocks at all positive widths
determine `P`, also almost surely when the equalities hold on width-dependent null sets.

Measure-valued sequences are represented in the measurable injective code
`TauCeti.MeasureTheory.probabilityMeasureCode` when a standard Borel value space is needed, because
Mathlib does not equip the Giry measurable space on `ProbabilityMeasure α` with a standard-Borel
instance. The coded paths `codedCoordinateMarginals` and `codedBlockMarginals` lose no
information.

## Main definitions and results

* `TauCeti.Probability.map_map_permReindex_eq_of_map_eq` -- invariance in law of a random path
  measure under reindexing is invariance of its law under the induced action;
* `MeasureTheory.ProbabilityMeasure.coordinateMarginals` and its coded form
  `MeasureTheory.ProbabilityMeasure.codedCoordinateMarginals`, with their equivariance under
  `permReindex`;
* `MeasureTheory.ProbabilityMeasure.blockMarginals` and its coded form
  `MeasureTheory.ProbabilityMeasure.codedBlockMarginals`;
* `MeasureTheory.ProbabilityMeasure.blockMarginals_map_permReindex_blockPerm` and its coded form
  `MeasureTheory.ProbabilityMeasure.codedBlockMarginals_map_permReindex_blockPerm` -- equivariance
  of the block marginals under the block permutations `Nat.blockPerm`;
* `MeasureTheory.ProbabilityMeasure.map_blockSplitEquiv_blockMarginals_mul` and
  `MeasureTheory.ProbabilityMeasure.map_blockRestriction_blockMarginals_mul` -- compatibility
  between block widths;
* `MeasureTheory.ProbabilityMeasure.eq_of_blockMarginals_zero_eq` and
  `MeasureTheory.ProbabilityMeasure.eq_of_codedBlockMarginals_zero_eq`, with their almost-sure
  forms -- the zeroth block marginals determine the path measure.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace TauCeti

namespace Probability

open TauCeti.MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-- Invariance in law of an almost-everywhere measurable random path measure under reindexing
implies invariance under the induced action on probability measures. -/
theorem map_map_permReindex_eq_of_map_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {ν : Ω → ProbabilityMeasure (ℕ → α)} (hν : AEMeasurable ν μ)
    (hinv : ∀ τ : Equiv.Perm ℕ,
      μ.map (fun ω => (ν ω).map (fun x : ℕ → α => fun k => x (τ k))) = μ.map ν) :
    ∀ τ : Equiv.Perm ℕ, (μ.map ν).map (fun P => P.map (permReindex τ)) = μ.map ν := by
  intro τ
  have hpush : Measurable fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ) :=
    measurable_probabilityMeasure_map (measurable_reindex τ)
  rw [AEMeasurable.map_map_of_aemeasurable hpush.aemeasurable hν]
  have hcomp : (fun P : ProbabilityMeasure (ℕ → α) => P.map (permReindex τ)) ∘ ν =
      fun ω => (ν ω).map (fun x : ℕ → α => fun k => x (τ k)) := by
    funext ω
    congr 1
  rw [hcomp]
  exact hinv τ

/-! ### Coordinate marginals -/

/-- The path of one-coordinate marginals of a probability measure on path space. -/
def _root_.MeasureTheory.ProbabilityMeasure.coordinateMarginals
    (P : ProbabilityMeasure (ℕ → α)) : ℕ → ProbabilityMeasure α :=
  fun i => P.map (fun x => x i)

/-- Evaluation of the path of coordinate marginals. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.coordinateMarginals_apply
    (P : ProbabilityMeasure (ℕ → α)) (i : ℕ) :
    P.coordinateMarginals i = P.map (fun x => x i) :=
  (rfl)

open MeasureTheory.ProbabilityMeasure

/-- The coordinate-marginal path depends measurably on the probability measure on path space. -/
theorem measurable_coordinateMarginals :
    Measurable (coordinateMarginals : ProbabilityMeasure (ℕ → α) →
      ℕ → ProbabilityMeasure α) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasure_map (measurable_pi_apply i)

/-- Coordinate marginals are equivariant under a permutation of path coordinates. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.coordinateMarginals_map_permReindex
    (P : ProbabilityMeasure (ℕ → α)) (τ : Equiv.Perm ℕ) :
    (P.map (permReindex τ)).coordinateMarginals = permReindex τ P.coordinateMarginals := by
  funext i
  apply ProbabilityMeasure.toMeasure_injective
  simp only [coordinateMarginals_apply, ProbabilityMeasure.toMeasure_map, permReindex_apply]
  have hperm : permReindex (α := α) τ = fun x : ℕ → α => fun k => x (τ k) := by
    funext x k
    rw [permReindex_apply]
  rw [hperm]
  rw [Measure.map_map (measurable_pi_apply i) (measurable_reindex τ)]
  rfl

/-- The coordinate marginals of a path measure, represented in the canonical measurable
injective code for probability measures on a countably generated space. -/
def _root_.MeasureTheory.ProbabilityMeasure.codedCoordinateMarginals
    [MeasurableSpace.CountablyGenerated α] (P : ProbabilityMeasure (ℕ → α)) :
    ℕ → (ProbabilityMeasureCodeIndex α → ℝ≥0∞) :=
  fun i => probabilityMeasureCode (P.coordinateMarginals i)

/-- Evaluation of a coded coordinate marginal. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.codedCoordinateMarginals_apply
    [MeasurableSpace.CountablyGenerated α] (P : ProbabilityMeasure (ℕ → α)) (i : ℕ) :
    P.codedCoordinateMarginals i = probabilityMeasureCode (P.coordinateMarginals i) :=
  (rfl)

/-- The path of coded coordinate marginals is measurable. -/
theorem measurable_codedCoordinateMarginals [MeasurableSpace.CountablyGenerated α] :
    Measurable (codedCoordinateMarginals (α := α)) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasureCode.comp
      ((measurable_pi_apply i).comp measurable_coordinateMarginals)

/-- Coding commutes with reindexing the coordinate marginals. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.codedCoordinateMarginals_map_permReindex
    [MeasurableSpace.CountablyGenerated α] (P : ProbabilityMeasure (ℕ → α)) (τ : Equiv.Perm ℕ) :
    (P.map (permReindex τ)).codedCoordinateMarginals =
      permReindex τ P.codedCoordinateMarginals := by
  funext i
  simp only [codedCoordinateMarginals_apply, permReindex_apply]
  exact congrArg probabilityMeasureCode
    (congrFun (coordinateMarginals_map_permReindex P τ) i)

/-! ### Block marginals -/

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

/-- The path of finite block marginals depends measurably on the probability measure on path
space. -/
theorem measurable_blockMarginals (m : ℕ) [NeZero m] :
    Measurable (blockMarginals (α := α) · m) :=
  Measurable.of_eval fun i =>
    measurable_probabilityMeasure_map
      (Measurable.of_eval fun j => measurable_pi_apply (blockIndex m i j))

/-- The permutation of path coordinates that permutes the consecutive blocks of width `m` by `τ`
and preserves the position inside each block. -/
def _root_.Nat.blockPerm (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) : Equiv.Perm ℕ :=
  (Nat.divModEquiv m).symm.permCongr (Equiv.prodCongr τ (Equiv.refl (Fin m)))

/-- The block permutation moves position `j` of block `i` to position `j` of block `τ i`. -/
@[simp]
theorem _root_.Nat.blockPerm_mul_add (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) (i : ℕ) (j : Fin m) :
    Nat.blockPerm m τ (i * m + j) = τ i * m + j := by
  have h (k : ℕ) : k * m + (j : ℕ) = (Nat.divModEquiv m).symm (k, j) :=
    (Nat.divModEquiv_symm_apply m (k, j)).symm
  -- Keep the indices in `divModEquiv` form so that `simp` cancels the equivalence.
  rw [h, h]
  simp [Nat.blockPerm, -Nat.divModEquiv_symm_apply]

/-- Block marginals are equivariant when a block permutation is extended to all path
coordinates by `Nat.blockPerm`. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.blockMarginals_map_permReindex_blockPerm
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m] (τ : Equiv.Perm ℕ) :
    (P.map (permReindex (Nat.blockPerm m τ))).blockMarginals m =
      permReindex τ (P.blockMarginals m) := by
  funext i
  apply ProbabilityMeasure.toMeasure_injective
  simp only [blockMarginals_apply, ProbabilityMeasure.toMeasure_map, permReindex_apply]
  rw [Measure.map_map]
  · congr 1
    funext x j
    exact congrArg x (Nat.blockPerm_mul_add m τ i j)
  · exact Measurable.of_eval fun j =>
      measurable_pi_apply (blockIndex m i j)
  · exact measurable_reindex (Nat.blockPerm m τ)

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

/-! ### Coded block marginals -/

/-- The finite block marginals of a path measure, represented in the canonical measurable
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

/-- Coding commutes with permuting the block marginals by a block permutation. -/
@[simp]
theorem _root_.MeasureTheory.ProbabilityMeasure.codedBlockMarginals_map_permReindex_blockPerm
    (P : ProbabilityMeasure (ℕ → α)) (m : ℕ) [NeZero m]
    [MeasurableSpace.CountablyGenerated (Fin m → α)] (τ : Equiv.Perm ℕ) :
    (P.map (permReindex (Nat.blockPerm m τ))).codedBlockMarginals m =
      permReindex τ (P.codedBlockMarginals m) := by
  funext i
  simp only [codedBlockMarginals_apply, permReindex_apply]
  exact congrArg probabilityMeasureCode
    (congrFun (blockMarginals_map_permReindex_blockPerm P m τ) i)

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
