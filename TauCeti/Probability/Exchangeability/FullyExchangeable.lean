/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Exchangeability.Basic
public import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Mathlib.Logic.Equiv.Fintype
import TauCeti.Probability.Process.PathLaw.FiniteMarginals
import TauCeti.Probability.Exchangeability.Contractability

/-!
# Full exchangeability and path-law bridges

The Layer 0 bridges between finite exchangeability, full exchangeability, and path-law
endomorphisms:

* `exchangeable_iff_fullyExchangeable` — finite exchangeability (invariance under permutations of
  each `Fin n`) is equivalent to full exchangeability (invariance under all permutations of `ℕ`)
  for a process with a.e. measurable coordinates under a finite measure.
* `FullyExchangeable.measurePreserving_shift` — a fully exchangeable process has a shift-invariant
  path law, the bridge from symmetry to the Koopman/ergodic lane.
* `fullyExchangeable_iff_forall_map_permReindex_pathLaw` and
  `fullyExchangeable_iff_forall_measurePreserving_permReindex` — full exchangeability is
  equivalently invariance, or measure preservation, of the path law under every time-permutation
  reindexing map.

These bridges live together because they all identify the process-level symmetry
`FullyExchangeable μ X` with corresponding path-law invariance statements. They are thin: they
reuse the Layer 0 API and Mathlib — finite-marginal uniqueness (`FiniteMarginals`), the
contractability bridge (`Contractability`), generic path-law reindexing, and Mathlib's finite
permutation extension theorem — rather than new measure theory.

These declarations are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned at
`e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Full exchangeability implies finite exchangeability at each dimension `n`.** -/
theorem FullyExchangeable.exchangeableAt {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) (n : ℕ) :
    ExchangeableAt μ X n := by
  intro σ
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val)
    (fun i : Fin n => (σ i).val) Fin.val_injective
    (fun _ _ h => σ.injective (Fin.val_injective h))
  have hidx : (fun j : Fin n => π j.val) = fun j : Fin n => (σ j).val := by
    funext j; exact hπ j
  calc blockLaw μ X (fun j : Fin n => (σ j).val)
      = blockLaw μ X (fun j : Fin n => π j.val) := by rw [hidx]
    _ = ((pathLaw μ X).map fun x k => x (π k)).map (prefixProj α n) :=
        (map_reindex_prefixProj_pathLaw μ hX_meas π n).symm
    _ = (pathLaw μ X).map (prefixProj α n) := by
        rw [map_reindex_pathLaw μ hX_meas π, pathLaw_def μ fun k ω => X (π k) ω, hX π]
    _ = prefixLaw μ X n := map_prefixProj_pathLaw μ (AEMeasurable.of_eval hX_meas) n

/-- **Full exchangeability implies finite exchangeability.** -/
theorem FullyExchangeable.exchangeable {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X :=
  fun n => hX.exchangeableAt hX_meas n

/-- **Finite exchangeability implies full exchangeability** for a finite law with a.e. measurable
coordinates: the path law is invariant under every permutation of `ℕ`. -/
theorem Exchangeable.fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) : FullyExchangeable μ X := by
  intro π
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [← pathLaw_def, ← map_reindex_pathLaw μ hX_meas π,
    map_reindex_prefixProj_pathLaw μ hX_meas π n,
    map_prefixProj_pathLaw μ (AEMeasurable.of_eval hX_meas) n]
  exact Exchangeable.blockLaw_eq_prefixLaw_of_injective hX hX_meas _
    (fun _ _ h => Fin.val_injective (π.injective h))

/-- **Finite exchangeability ↔ full exchangeability** for a process with a.e. measurable
coordinates under a finite measure. -/
theorem exchangeable_iff_fullyExchangeable {μ : Measure Ω} {X : ℕ → Ω → α} [IsFiniteMeasure μ]
    (hX_meas : ∀ i, AEMeasurable (X i) μ) : Exchangeable μ X ↔ FullyExchangeable μ X :=
  ⟨fun h => h.fullyExchangeable hX_meas, fun h => h.exchangeable hX_meas⟩

/-- **A fully exchangeable process has a shift-invariant path law** — the Layer 0 shift-preservation
bridge. -/
theorem FullyExchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) := by
  have hc : Contractable μ X := (hX.exchangeable hX_meas).contractable hX_meas
  exact Contractable.measurePreserving_shift hc hX_meas

/-! ## Path-law permutation reindexing -/

/-- Full exchangeability is exactly invariance of the path law under every time permutation. -/
theorem fullyExchangeable_iff_forall_map_permReindex_pathLaw
    (μ : Measure Ω) {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔
      ∀ π : Equiv.Perm ℕ,
        (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X := by
  constructor
  · intro h π
    rw [MeasureTheory.Measure.map_permReindex_pathLaw μ hX π]
    exact h.permute π
  · intro h π
    have hπ := h π
    rwa [MeasureTheory.Measure.map_permReindex_pathLaw μ hX π] at hπ

/-- A fully exchangeable process has path law invariant under any time permutation. -/
theorem FullyExchangeable.map_permReindex_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ)
    (π : Equiv.Perm ℕ) :
    (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X :=
  (fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX).mp h π

/-- Reindexing path space by any time permutation preserves the path law of a fully
exchangeable process. -/
theorem FullyExchangeable.measurePreserving_permReindex {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) (hX : ∀ i, AEMeasurable (X i) μ) (π : Equiv.Perm ℕ) :
    MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X) :=
  ⟨measurable_reindex π, h.map_permReindex_pathLaw hX π⟩

/-- Full exchangeability is exactly preservation of the path law by every time-permutation
reindexing map. -/
theorem fullyExchangeable_iff_forall_measurePreserving_permReindex
    (μ : Measure Ω) {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔
      ∀ π : Equiv.Perm ℕ,
        MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X) := by
  rw [fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX]
  constructor
  · intro h π
    exact ⟨measurable_reindex π, h π⟩
  · intro h π
    exact (h π).map_eq

/-- If every time permutation preserves the path law, then the process is fully exchangeable. -/
theorem fullyExchangeable_of_forall_map_permReindex_pathLaw
    {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : ∀ π : Equiv.Perm ℕ,
      (pathLaw μ X).map (permReindex (α := α) π) = pathLaw μ X) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX).mpr h

/-- A measure-preserving form of the path-law bridge: if every time permutation preserves the
path law, then the process is fully exchangeable. -/
theorem fullyExchangeable_of_forall_measurePreserving_permReindex
    {μ : Measure Ω} {X : ℕ → Ω → α} (hX : ∀ i, AEMeasurable (X i) μ)
    (h : ∀ π : Equiv.Perm ℕ,
      MeasurePreserving (permReindex (α := α) π) (pathLaw μ X) (pathLaw μ X)) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_forall_measurePreserving_permReindex μ hX).mpr h

end Probability

end TauCeti
