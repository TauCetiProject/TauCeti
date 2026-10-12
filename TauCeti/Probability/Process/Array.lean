/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.PathLaw.Basic
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Array processes and coordinate maps

An array process has coordinates indexed by `ℕ × ℕ`. This file provides its row, column and
diagonal processes, reindexing of both axes, and the measurability needed to pass between the
entries and the entire array law. These constructions apply to arbitrary array processes; the
symmetry predicates using them are developed in `Probability.Exchangeability.Arrays.Basic`.

The set `symmetricArraysWithDiag α d` records symmetric arrays with a fixed diagonal and is
stable under simultaneous reindexing of the two axes. It is useful for laws of undirected
random graphs.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α Ω : Type*}

/-! ## Reindexing the two axes -/

/-- Reindex an array-shaped path by a permutation of each axis: the `(i, j)`-entry of
`pairReindex σ τ x` is `x (σ i, τ j)`. This is the two-axis analogue of `permReindex`. -/
def pairReindex (σ τ : Equiv.Perm ℕ) (x : ℕ × ℕ → α) : ℕ × ℕ → α :=
  fun p ↦ x (σ p.1, τ p.2)

@[simp]
theorem pairReindex_apply (σ τ : Equiv.Perm ℕ) (x : ℕ × ℕ → α) (p : ℕ × ℕ) :
    pairReindex σ τ x p = x (σ p.1, τ p.2) :=
  (rfl)

/-- The function form of `pairReindex`. -/
theorem pairReindex_def (σ τ : Equiv.Perm ℕ) :
    pairReindex (α := α) σ τ = fun x p ↦ x (σ p.1, τ p.2) := by
  funext x p
  exact pairReindex_apply σ τ x p

/-- Reindexing both axes twice composes the corresponding permutations on each axis. -/
@[simp]
theorem pairReindex_comp (σ₁ τ₁ σ₂ τ₂ : Equiv.Perm ℕ) :
    pairReindex (α := α) σ₁ τ₁ ∘ pairReindex σ₂ τ₂ =
      pairReindex (σ₂ * σ₁) (τ₂ * τ₁) :=
  (rfl)

/-- Reindexing both axes by the identity permutation leaves an array unchanged. -/
@[simp]
theorem pairReindex_one_one : pairReindex (α := α) 1 1 = id := by
  funext x p
  rfl

/-! ## Rows, columns and the diagonal -/

/-- The `i`-th row of an array, as a random element of path space. -/
def arrayRow (X : ℕ × ℕ → Ω → α) (i : ℕ) : Ω → (ℕ → α) :=
  fun ω j ↦ X (i, j) ω

/-- The `j`-th column of an array, as a random element of path space. -/
def arrayCol (X : ℕ × ℕ → Ω → α) (j : ℕ) : Ω → (ℕ → α) :=
  fun ω i ↦ X (i, j) ω

/-- The diagonal of an array, as a process. -/
def arrayDiag (X : ℕ × ℕ → Ω → α) (i : ℕ) : Ω → α :=
  X (i, i)

@[simp]
theorem arrayRow_apply (X : ℕ × ℕ → Ω → α) (i : ℕ) (ω : Ω) (j : ℕ) :
    arrayRow X i ω j = X (i, j) ω :=
  (rfl)

@[simp]
theorem arrayCol_apply (X : ℕ × ℕ → Ω → α) (j : ℕ) (ω : Ω) (i : ℕ) :
    arrayCol X j ω i = X (i, j) ω :=
  (rfl)

@[simp]
theorem arrayDiag_apply (X : ℕ × ℕ → Ω → α) (i : ℕ) : arrayDiag X i = X (i, i) :=
  (rfl)

/-- The symmetric arrays with constant diagonal value `d`: `x (i, j) = x (j, i)` and
`x (i, i) = d`. For `α = Bool` and `d = false` these are the adjacency arrays of the simple
graphs on `ℕ`. -/
def symmetricArraysWithDiag (α : Type*) (d : α) : Set (ℕ × ℕ → α) :=
  {x | (∀ i j, x (i, j) = x (j, i)) ∧ ∀ i, x (i, i) = d}

/-- Membership in the symmetric arrays with diagonal `d`. -/
@[simp]
theorem mem_symmetricArraysWithDiag_iff {d : α} {x : ℕ × ℕ → α} :
    x ∈ symmetricArraysWithDiag α d ↔ (∀ i j, x (i, j) = x (j, i)) ∧ ∀ i, x (i, i) = d :=
  Iff.rfl

/-- The symmetric arrays with diagonal `d` are stable under diagonal relabelling. -/
@[simp]
theorem preimage_pairReindex_symmetricArraysWithDiag (σ : Equiv.Perm ℕ) (d : α) :
    pairReindex σ σ ⁻¹' symmetricArraysWithDiag α d = symmetricArraysWithDiag α d := by
  ext x
  simp only [Set.mem_preimage, mem_symmetricArraysWithDiag_iff, pairReindex_apply]
  constructor
  · rintro ⟨hs, hd⟩
    exact ⟨fun i j ↦ by simpa using hs (σ.symm i) (σ.symm j),
      fun i ↦ by simpa using hd (σ.symm i)⟩
  · rintro ⟨hs, hd⟩
    exact ⟨fun i j ↦ hs _ _, fun i ↦ hd _⟩

variable [MeasurableSpace α]

/-- The symmetric arrays with diagonal `d` form a measurable set. -/
@[simp, measurability]
theorem measurableSet_symmetricArraysWithDiag [MeasurableEq α] (d : α) :
    MeasurableSet (symmetricArraysWithDiag α d) := by
  have h1 : MeasurableSet {x : ℕ × ℕ → α | ∀ i j, x (i, j) = x (j, i)} := by
    have : {x : ℕ × ℕ → α | ∀ i j, x (i, j) = x (j, i)}
        = ⋂ i, ⋂ j, {x : ℕ × ℕ → α | x (i, j) = x (j, i)} := by
      ext
      simp
    rw [this]
    exact MeasurableSet.iInter fun i ↦ MeasurableSet.iInter fun j ↦
      measurableSet_eq_fun (measurable_pi_apply _) (measurable_pi_apply _)
  have h2 : MeasurableSet {x : ℕ × ℕ → α | ∀ i, x (i, i) = d} := by
    have : {x : ℕ × ℕ → α | ∀ i, x (i, i) = d} = ⋂ i, {x : ℕ × ℕ → α | x (i, i) = d} := by
      ext
      simp
    rw [this]
    exact MeasurableSet.iInter fun i ↦
      measurableSet_eq_fun (measurable_pi_apply _) measurable_const
  exact h1.inter h2

/-- Reindexing the two axes of an array by permutations is a measurable map. -/
@[fun_prop]
theorem measurable_pairReindex (σ τ : Equiv.Perm ℕ) :
    Measurable (pairReindex (α := α) σ τ) :=
  Measurable.of_eval fun _ ↦ measurable_pi_apply _

variable [MeasurableSpace Ω]

/-- If every array entry is almost everywhere measurable, each row is almost everywhere
measurable as a path-valued map. -/
theorem aemeasurable_arrayRow {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) (i : ℕ) : AEMeasurable (arrayRow X i) μ :=
  AEMeasurable.of_eval fun j ↦ hX (i, j)

/-- If every array entry is almost everywhere measurable, each column is almost everywhere
measurable as a path-valued map. -/
theorem aemeasurable_arrayCol {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) (j : ℕ) : AEMeasurable (arrayCol X j) μ :=
  AEMeasurable.of_eval fun i ↦ hX (i, j)

/-- **Entry measurability from row measurability**, the converse of `aemeasurable_arrayRow`.  The
entries are the coordinates of the rows, so this needs no probabilistic structure; a caller holding
a mixed or conditional witness passes its `aemeasurable`. -/
theorem aemeasurable_entry_of_aemeasurable_arrayRow {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : ∀ i, AEMeasurable (arrayRow X i) μ) (p : ℕ × ℕ) : AEMeasurable (X p) μ := by
  simpa [arrayRow_apply] using (h p.1).eval p.2

/-- **Entry measurability from column measurability**, the converse of `aemeasurable_arrayCol`. -/
theorem aemeasurable_entry_of_aemeasurable_arrayCol {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (h : ∀ j, AEMeasurable (arrayCol X j) μ) (p : ℕ × ℕ) : AEMeasurable (X p) μ := by
  simpa [arrayCol_apply] using (h p.2).eval p.1

/-- Reading a measurable function `F` off the sample path of an array turns its law into a
pushforward. This applies, for example, to taking rows, columns, or diagonal entries. -/
theorem map_map_array {β : Type*} [MeasurableSpace β] {μ : Measure Ω} {X : ℕ × ℕ → Ω → α}
    (hX : ∀ p, AEMeasurable (X p) μ) {F : (ℕ × ℕ → α) → β} (hF : Measurable F) :
    (μ.map fun ω p ↦ X p ω).map F = μ.map fun ω ↦ F fun p ↦ X p ω :=
  AEMeasurable.map_map_of_aemeasurable hF.aemeasurable (AEMeasurable.of_eval hX)

end Probability

end TauCeti
