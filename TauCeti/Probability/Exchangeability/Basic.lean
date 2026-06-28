module

public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.AEMeasurable
public import Mathlib.MeasureTheory.MeasurableSpace.Constructions
public import Mathlib.Tactic.Measurability

/-!
# Basic exchangeability definitions

This file starts the Layer 0 exchangeability API: indexed block laws of a process,
prefix laws, path laws, finite exchangeability, full exchangeability, and
contractability. The definitions are intentionally hypothesis-light; measurability
hypotheses enter only in lemmas that compose `Measure.map`s.

These declarations follow the roadmap signatures in
`TauCetiRoadmap/Exchangeability/README.md` and
`TauCetiRoadmap/Exchangeability/Targets.lean`, Layer 0. They are adapted from the
`cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- The finite-dimensional law of a process along a coordinate selection `k`. -/
@[expose]
def blockLaw (μ : Measure Ω) (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) :
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

/-- Finite exchangeability at `n`: the first `n` coordinates have permutation-invariant law. -/
@[expose]
def ExchangeableAt (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) : Prop :=
  ∀ σ : Equiv.Perm (Fin n),
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n

/-- Finite exchangeability at every length. -/
@[expose]
def Exchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ n, ExchangeableAt μ X n

/-- Full exchangeability: the path law is invariant under every permutation of `ℕ`. -/
@[expose]
def FullyExchangeable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ π : Equiv.Perm ℕ, μ.map (fun ω i => X (π i) ω) = pathLaw μ X

/-- Contractability, or spreadability: finite-dimensional laws are invariant under strictly
increasing finite subsequences. -/
@[expose]
def Contractable (μ : Measure Ω) (X : ℕ → Ω → α) : Prop :=
  ∀ (m : ℕ) (k : Fin m → ℕ), StrictMono k → blockLaw μ X k = prefixLaw μ X m

@[simp]
theorem blockLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) {m : ℕ} (k : Fin m → ℕ) :
    blockLaw μ X k = μ.map (fun ω i => X (k i) ω) :=
  rfl

@[simp]
theorem prefixLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) (n : ℕ) :
    prefixLaw μ X n = blockLaw μ X (fun i : Fin n => i.val) :=
  rfl

@[simp]
theorem pathLaw_apply (μ : Measure Ω) (X : ℕ → Ω → α) :
    pathLaw μ X = μ.map (fun ω i => X i ω) :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem prefixProj_apply (n : ℕ) (x : ℕ → α) (i : Fin n) :
    prefixProj α n x i = x i.val :=
  rfl

omit [MeasurableSpace α] in
@[simp]
theorem shift_apply (x : ℕ → α) (n : ℕ) : shift α x n = x (n + 1) :=
  rfl

/-- The prefix projection is measurable. -/
theorem measurable_prefixProj (n : ℕ) : Measurable (prefixProj α n) := by
  unfold prefixProj
  measurability

/-- The one-sided path-space shift is measurable. -/
theorem measurable_shift : Measurable (shift α) := by
  unfold shift
  measurability

/-- Arbitrary coordinate reindexing on one-sided path space is measurable. -/
theorem measurable_reindex (φ : ℕ → ℕ) :
    Measurable fun x : ℕ → α => fun k => x (φ k) :=
  measurable_pi_lambda _ fun k => measurable_pi_apply (φ k)

/-- A prefix projection after arbitrary coordinate reindexing is measurable. -/
theorem measurable_prefixProj_reindex (φ : ℕ → ℕ) (n : ℕ) :
    Measurable fun x : ℕ → α => prefixProj α n (fun k => x (φ k)) :=
  (measurable_prefixProj n).comp (measurable_reindex φ)

/-- The prefix law is the pushforward of the path law by `prefixProj`. -/
theorem map_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : AEMeasurable (fun ω => fun i => X i ω) μ) (n : ℕ) :
    (pathLaw μ X).map (prefixProj α n) = prefixLaw μ X n := by
  rw [pathLaw_apply, prefixLaw_apply, blockLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_prefixProj n).aemeasurable hX,
    Function.comp_def]
  rfl

/-- A coordinatewise measurable map sends block laws to block laws. -/
theorem map_blockLaw (μ : Measure Ω) {X : ℕ → Ω → α} {m : ℕ} (k : Fin m → ℕ)
    {f : α → β} [MeasurableSpace β] (hf : Measurable f)
    (hXk : ∀ i : Fin m, AEMeasurable (X (k i)) μ) :
    (blockLaw μ X k).map (fun x : Fin m → α => fun i => f (x i)) =
      blockLaw μ (fun n ω => f (X n ω)) k := by
  rw [blockLaw_apply, blockLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (measurable_pi_lambda (fun x : Fin m → α => fun i => f (x i)) fun i =>
      hf.comp (measurable_pi_apply i)).aemeasurable
  · exact aemeasurable_pi_lambda (fun ω => fun i => X (k i) ω) hXk

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
  rw [pathLaw_apply, pathLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (measurable_pi_lambda (fun x : ℕ → α => fun i => f (x i)) fun i =>
      hf.comp (measurable_pi_apply i)).aemeasurable
  · exact aemeasurable_pi_lambda (fun ω => fun i => X i ω) hX

/-- Mapping a path law by a coordinate reindexing gives the path law of the reindexed process. -/
theorem map_reindex_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) =
      pathLaw μ (fun k ω => X (φ k) ω) := by
  rw [pathLaw_apply, pathLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable (measurable_reindex φ).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  rfl

/-- Push a block law forward along a coordinate reindexing: selecting the coordinates of
`blockLaw μ X k` through `g : Fin p → Fin n` yields the block law along `k ∘ g`. -/
theorem map_blockLaw_reindex (μ : Measure Ω) {X : ℕ → Ω → α} {n p : ℕ}
    (k : Fin n → ℕ) (g : Fin p → Fin n) (hXk : ∀ j : Fin n, AEMeasurable (X (k j)) μ) :
    (blockLaw μ X k).map (fun x : Fin n → α => fun i : Fin p => x (g i)) =
      blockLaw μ X (k ∘ g) := by
  rw [blockLaw_apply, blockLaw_apply,
    AEMeasurable.map_map_of_aemeasurable
      ((measurable_pi_lambda _ fun i => measurable_pi_apply (g i)).aemeasurable)
      (aemeasurable_pi_lambda _ hXk)]
  rfl

/-- A prefix projection after coordinate reindexing gives the corresponding finite block law. -/
theorem map_reindex_prefixProj_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) (φ : ℕ → ℕ) (n : ℕ) :
    (pathLaw μ X).map (fun x : ℕ → α => prefixProj α n (fun k => x (φ k))) =
      blockLaw μ X (fun i : Fin n => φ i.val) := by
  rw [pathLaw_apply, blockLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable
    (measurable_prefixProj_reindex φ n).aemeasurable
    (aemeasurable_pi_lambda _ hX)]
  rfl

/-- Projecting the prefix law on `Fin n` onto its first `m ≤ n` coordinates (via `Fin.castLE`)
gives the prefix law on `Fin m`. -/
theorem map_prefixLaw_castLE (μ : Measure Ω) {X : ℕ → Ω → α} {m n : ℕ} (hmn : m ≤ n)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    (prefixLaw μ X n).map (fun x : Fin n → α => fun i : Fin m => x (Fin.castLE hmn i)) =
      prefixLaw μ X m := by
  have hidx : (fun i : Fin n => i.val) ∘ Fin.castLE hmn = fun i : Fin m => i.val := by
    funext i; simp
  rw [prefixLaw_apply, map_blockLaw_reindex μ _ (Fin.castLE hmn) hX, hidx]
  exact (prefixLaw_apply μ X m).symm

theorem Exchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Exchangeable μ X) (n : ℕ) : ExchangeableAt μ X n :=
  h n

theorem ExchangeableAt.permute {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) (σ : Equiv.Perm (Fin n)) :
    blockLaw μ X (fun i : Fin n => (σ i).val) = prefixLaw μ X n :=
  h σ

theorem FullyExchangeable.permute {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (π : Equiv.Perm ℕ) :
    μ.map (fun ω i => X (π i) ω) = pathLaw μ X :=
  h π

end Probability

end TauCeti
