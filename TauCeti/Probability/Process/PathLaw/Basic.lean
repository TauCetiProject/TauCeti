/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.MeasureTheory.MeasurableSpace.Embedding
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Tactic.Measurability

/-!
# Finite-dimensional and path laws of a process

For a process `X : ℕ → Ω → α` on a measure space `(Ω, μ)`, this file defines its laws as measures
on finite tuples and on path space `ℕ → α`, together with the elementary path-space maps used to
compare them:

* `blockLaw μ X k` — the law of the finite selection `(X (k 0), …, X (k (m - 1)))`, for an
  arbitrary index type;
* `prefixLaw μ X n` — the law of the first `n` coordinates;
* `pathLaw μ X` — the law of the whole path `ω ↦ (i ↦ X i ω)`;
* `prefixProj α n`, `shift α`, `permReindex π` — the prefix projection, the one-sided left shift,
  and reindexing by a permutation of time;
* `prefixSplitEquiv r` — the measurable equivalence splitting a path into its length-`r` prefix
  and its tail from index `r`.

The definitions are hypothesis-light; measurability hypotheses enter only in the lemmas that
compose `Measure.map`s (`map_prefixProj_pathLaw`, `map_blockLaw`, `map_reindex_pathLaw`, …).
Nothing here mentions a symmetry of the process: the exchangeability predicates built on these
laws live in `TauCeti.Probability.Exchangeability.Basic`.

The laws and path-space maps are adapted from the `cameronfreer/exchangeability` sources pinned
at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses;
`prefixSplitEquiv` is not taken from those sources.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β ι : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The finite-dimensional law of a family along a coordinate selection `k`.

The index type is arbitrary: nothing about a finite selection needs the indices to be natural
numbers, so families over an arbitrary index type can select from it. Sequence-level users get
the `ι = ℕ` case by unification. -/
def blockLaw (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι) :
    Measure (Fin m → α) :=
  μ.map fun ω i => X (k i) ω

/-- The law of the first `n` coordinates of a process. -/
@[expose]
def prefixLaw (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Measure (Fin n → α) :=
  blockLaw μ X fun i : Fin n => i.val

/-- The law of the whole process as a measure on path space. -/
@[expose]
def pathLaw (μ : Measure Ω) (X : ℕ → Ω → α) : Measure (ℕ → α) :=
  μ.map fun ω i => X i ω

/-- Projection from path space to the first `n` coordinates. -/
@[expose]
def prefixProj (α : Type*) (n : ℕ) (x : ℕ → α) : Fin n → α :=
  fun i => x i.val

/-- The left shift on one-sided path space. -/
@[expose]
def shift (α : Type*) (x : ℕ → α) : ℕ → α :=
  fun n => x (n + 1)

/-- Reindex a one-sided path by a permutation of time. -/
@[expose]
def permReindex (π : Equiv.Perm ℕ) (x : ℕ → α) : ℕ → α :=
  fun n => x (π n)

@[simp]
theorem blockLaw_def (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι) :
    blockLaw μ X k = μ.map (fun ω i => X (k i) ω) :=
  (rfl)

-- Annotated `@[grind =>]` rather than `@[simp]`: `blockLaw_def` already simp-normalizes
-- `blockLaw μ X k` to `μ.map …` (so a `@[simp]` here would be shadowed), and the preimage form
-- needs the a.e.-measurability side condition `hXk`, which `simp` cannot discharge.
/-- The block law of `X` along `k`, evaluated on any measurable set `S`, is the measure of its
coordinate-wise preimage. This is the characteristic evaluation of `blockLaw` as a pushforward;
`blockLaw_apply_rectangle` is the rectangle specialization. -/
@[grind =>]
theorem blockLaw_apply_of_measurable (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι)
    (hXk : ∀ i, AEMeasurable (X (k i)) μ) {S : Set (Fin m → α)} (hS : MeasurableSet S) :
    blockLaw μ X k S = μ ((fun ω i => X (k i) ω) ⁻¹' S) := by
  rw [blockLaw_def, Measure.map_apply_of_aemeasurable (AEMeasurable.of_eval hXk) hS]

/-- The block law of `X` along `k`, evaluated on a measurable rectangle `Set.univ.pi B`, is the
measure of the coordinate-wise preimage `{ω | ∀ i, X (k i) ω ∈ B i}` — the rectangle specialization
of `blockLaw_apply_of_measurable`. -/
@[grind =>]
theorem blockLaw_apply_rectangle (μ : Measure Ω) (X : ι → Ω → α) {m : ℕ} (k : Fin m → ι)
    (hXk : ∀ i, AEMeasurable (X (k i)) μ) (B : Fin m → Set α) (hB : ∀ i, MeasurableSet (B i)) :
    blockLaw μ X k (Set.univ.pi B) = μ {ω | ∀ i, X (k i) ω ∈ B i} := by
  rw [blockLaw_apply_of_measurable μ X k hXk (MeasurableSet.univ_pi hB)]
  congr 1
  ext ω
  simp [Set.mem_preimage]

@[simp]
theorem prefixLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) :
    prefixLaw μ X n = blockLaw μ X (fun i : Fin n => i.val) :=
  rfl

/-- A block law of a family under a finite measure is finite. -/
instance isFiniteMeasure_blockLaw (μ : Measure Ω) [IsFiniteMeasure μ] (X : ι → Ω → α) {m : ℕ}
    (k : Fin m → ι) : IsFiniteMeasure (blockLaw μ X k) := by
  rw [blockLaw_def]
  infer_instance

/-- A prefix law of a process under a finite measure is finite. -/
instance isFiniteMeasure_prefixLaw (μ : Measure Ω) [IsFiniteMeasure μ] (X : ℕ → Ω → α)
    (n : ℕ) : IsFiniteMeasure (prefixLaw μ X n) :=
  isFiniteMeasure_blockLaw μ X _

/-- The mass of a finite path, as the measure of the event that the process spells it out:
`prefixLaw μ X n {w} = μ {ω | ∀ i, X i.val ω = w i}`. The singleton specialization of
`blockLaw_apply_of_measurable` along the prefix selection. -/
theorem prefixLaw_singleton_eq_measure [MeasurableSingletonClass α] {μ : Measure Ω}
    {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) {n : ℕ} (w : Fin n → α) :
    prefixLaw μ X n {w} = μ {ω | ∀ i : Fin n, X i.val ω = w i} := by
  rw [prefixLaw_def, blockLaw_apply_of_measurable μ X (fun i : Fin n => i.val)
    (fun i => hX i.val) (measurableSet_singleton w)]
  exact congrArg μ (Set.ext fun ω => by simp [funext_iff, eq_comm])

@[simp]
theorem pathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) :
    pathLaw μ X = μ.map (fun ω i => X i ω) :=
  rfl

/-- The path law of the coordinate process on path space is the law itself. -/
theorem pathLaw_coord (ρ : Measure (ℕ → α)) : pathLaw ρ (fun i (x : ℕ → α) => x i) = ρ := by
  rw [pathLaw_def]; exact Measure.map_id'

omit [MeasurableSpace α] in
@[simp]
theorem prefixProj_apply (n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n x i = x i.val :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem shift_apply (x : ℕ → α) (n : ℕ) : shift α x n = x (n + 1) :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem permReindex_apply (π : Equiv.Perm ℕ) (x : ℕ → α) (n : ℕ) :
    permReindex π x n = x (π n) :=
  rfl

omit [MeasurableSpace α] in
/-- Composing `permReindex π` after `permReindex σ` reindexes by `σ * π`. -/
@[simp]
theorem permReindex_permReindex (π σ : Equiv.Perm ℕ) (x : ℕ → α) :
    permReindex (α := α) π (permReindex (α := α) σ x) =
      permReindex (α := α) (σ * π) x := by
  rfl

/-- The prefix projection is measurable. -/
theorem measurable_prefixProj (n : ℕ) : Measurable (prefixProj α n) := by
  unfold prefixProj
  measurability

/-- The one-sided path-space shift is measurable. -/
theorem measurable_shift : Measurable (shift α) := by
  unfold shift
  measurability

/-- Split a sequence into its length-`r` prefix `Fin r → α` and the tail `ℕ → α` from index `r`, as
a measurable equivalence.  The forward map sends `f` to `(fun i => f i.val, fun j => f (r + j))`;
its inverse glues a prefix/tail pair back into a sequence, taking coordinates below `r` from the
prefix and the rest (reindexed by `· - r`) from the tail. -/
def prefixSplitEquiv (r : ℕ) : (ℕ → α) ≃ᵐ (Fin r → α) × (ℕ → α) :=
  (MeasurableEquiv.arrowCongr' (finSumNatEquiv r).symm (.refl α)).trans
    (MeasurableEquiv.sumPiEquivProdPi fun _ => α)

/-- **Applying `prefixSplitEquiv`**: it reads off the length-`r` prefix and the tail from index
`r`. -/
-- This is the one place that depends on the definitional form of `MeasurableEquiv.arrowCongr'` and
-- `sumPiEquivProdPi`, neither of which exposes an apply lemma. Everything else about the
-- equivalence is derived from here, so the fragile step is isolated rather than repeated.
@[simp]
theorem prefixSplitEquiv_apply (r : ℕ) (f : ℕ → α) :
    prefixSplitEquiv r f = (fun i : Fin r => f (i : ℕ), fun j : ℕ => f (r + j)) := (rfl)

/-- The inverse of `prefixSplitEquiv` glues a prefix/tail pair into a sequence: coordinates below
`r` come from the prefix `p.1`, the rest (reindexed by `· - r`) from the tail `p.2`. -/
@[simp]
theorem prefixSplitEquiv_symm_apply (r : ℕ) (p : (Fin r → α) × (ℕ → α)) (n : ℕ) :
    (prefixSplitEquiv r).symm p n = if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
  have key : (prefixSplitEquiv r).symm p
      = fun n => if h : n < r then p.1 ⟨n, h⟩ else p.2 (n - r) := by
    apply (prefixSplitEquiv r).injective
    rw [MeasurableEquiv.apply_symm_apply, prefixSplitEquiv_apply]
    refine Prod.ext (funext fun i => ?_) (funext fun j => ?_)
    · simp only [dite_eq_left i.isLt, Fin.eta]
    · have h : ¬ (r + j < r) := Nat.not_lt.mpr (Nat.le_add_right r j)
      simp only [dite_eq_right h, Nat.add_sub_cancel_left]
  rw [key]

/-- The prefix law is the pushforward of the path law by `prefixProj`. -/
theorem map_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : AEMeasurable (fun ω => fun i => X i ω) μ) (n : ℕ) :
    (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n := by
  rw [pathLaw_def, prefixLaw_def, blockLaw_def]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable hX,
    Function.comp_def]
  rfl

/-- The prefix laws of a path law are the prefix laws of the process. -/
theorem prefixLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) : prefixLaw (pathLaw μ X) (fun n (x : ℕ → α) => x n) n = prefixLaw μ X n := by
  rw [prefixLaw_def, blockLaw_def,
    ← map_prefixProj_pathLaw μ (AEMeasurable.of_eval hX) n]
  rfl

/-- A coordinatewise measurable map sends block laws to block laws. -/
theorem map_blockLaw (μ : Measure Ω) {X : ι → Ω → α} {m : ℕ} (k : Fin m → ι)
    {f : α → β} [MeasurableSpace β] (hf : Measurable f)
    (hXk : ∀ i : Fin m, AEMeasurable (X (k i)) μ) :
    (blockLaw μ X k).map (fun x : Fin m → α => fun i => f (x i)) =
      blockLaw μ (fun n ω => f (X n ω)) k := by
  rw [blockLaw_def, blockLaw_def]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)).aemeasurable
  · exact AEMeasurable.of_eval hXk

/-- A coordinatewise measurable map sends prefix laws to prefix laws. -/
theorem map_prefixLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    {f : α → β} [MeasurableSpace β] (hf : Measurable f)
    (n : ℕ) (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    (prefixLaw μ X n).map (fun x : Fin n → α => fun i => f (x i)) =
      prefixLaw μ (fun n ω => f (X n ω)) n :=
  map_blockLaw μ (fun i : Fin n => i.val) hf hX

/-- A coordinatewise measurable map sends path laws to path laws. -/
theorem map_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    {f : α → β} [MeasurableSpace β] (hf : Measurable f)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun i => f (x i)) =
      pathLaw μ (fun n ω => f (X n ω)) := by
  rw [pathLaw_def, pathLaw_def]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (Measurable.of_eval fun i => hf.comp (measurable_pi_apply i)).aemeasurable
  · exact AEMeasurable.of_eval hX

/-- Push a block law forward along a coordinate reindexing: selecting the coordinates of
`blockLaw μ X k` through `g : Fin p → Fin n` yields the block law along `k ∘ g`. -/
theorem map_blockLaw_reindex (μ : Measure Ω) {X : ι → Ω → α} {n p : ℕ}
    (k : Fin n → ι) (g : Fin p → Fin n) (hXk : ∀ j : Fin n, AEMeasurable (X (k j)) μ) :
    (blockLaw μ X k).map (fun x : Fin n → α => fun i : Fin p => x (g i)) =
      blockLaw μ X (k ∘ g) := by
  rw [blockLaw_def, blockLaw_def,
    AEMeasurable.map_map_of_aemeasurable
      ((Measurable.of_eval fun i => measurable_pi_apply (g i)).aemeasurable)
      (AEMeasurable.of_eval hXk)]
  rfl

omit [MeasurableSpace Ω] in
/-- Reindexing the coordinates of path space along `φ` is measurable. -/
theorem measurable_reindex (φ : ℕ → ℕ) :
    Measurable (fun x : ℕ → α => fun k => x (φ k)) :=
  Measurable.of_eval fun k => measurable_pi_apply (φ k)

/-- Reindexing a path law gives the path law of the reindexed process. -/
theorem map_reindex_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) =
      pathLaw μ (fun k ω => X (φ k) ω) := by
  rw [pathLaw_def, pathLaw_def]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_reindex φ).aemeasurable
    (AEMeasurable.of_eval hX)]
  rfl

/-- Projecting the `φ`-reindexed path law onto its first `n` coordinates gives the law of the
block `(X (φ 0), …, X (φ (n-1)))`. -/
theorem map_reindex_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) (n : ℕ) :
    ((pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k))).map (prefixProj α n) =
      blockLaw μ X (fun i : Fin n => φ i.val) := by
  rw [map_reindex_pathLaw μ hX φ,
    map_prefixProj_pathLaw μ (AEMeasurable.of_eval fun i => hX (φ i)) n]
  rw [prefixLaw_def, blockLaw_def, blockLaw_def]

/-- Projecting the prefix law on `Fin n` onto its first `m ≤ n` coordinates (via `Fin.castLE`)
gives the prefix law on `Fin m`. -/
theorem map_prefixLaw_castLE (μ : Measure Ω) {X : ℕ → Ω → α} {m n : ℕ} (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    (prefixLaw μ X n).map (fun x : Fin n → α => fun i : Fin m => x (Fin.castLE hmn i)) =
      prefixLaw μ X m := by
  have hidx : (fun i : Fin n => i.val) ∘ Fin.castLE hmn = fun i : Fin m => i.val := by
    funext i; simp
  rw [prefixLaw_def, map_blockLaw_reindex μ _ (Fin.castLE hmn) hX, hidx]
  exact (prefixLaw_def μ X m).symm

end Probability

end TauCeti
