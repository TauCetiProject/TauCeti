module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.Shift

/-!
# Contractable laws on path space

This file adds the path-law formulation of contractability, also called spreadability:
a measure on `ℕ → α` is invariant under every strictly increasing reindexing of time.
The process-level predicate `Contractable μ X` remains the main stochastic-process API;
`ContractableLaw` names the equivalent path-space viewpoint needed by the de Finetti
factorization and path-space dynamics.

This is the contractability analogue of `ExchangeableLaw`. It realizes the Exchangeability
roadmap's Layer 0 request for process-level ↔ path-law bridges and for the characterization
of contractability by strictly increasing maps `ℕ → ℕ`. It reuses the existing Tau Ceti
bridge `contractable_iff_forall_map_reindex_pathLaw`; no Mathlib infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A measure on one-sided path space is contractable, or spreadable, if it is invariant under
every strictly increasing reindexing of the time coordinate. -/
def ContractableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ

/-- Constructor for `ContractableLaw` from the defining map invariance. -/
theorem ContractableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ) :
    ContractableLaw ρ :=
  h

/-- Simp normal form for `ContractableLaw`. -/
@[simp]
theorem contractableLaw_iff {ρ : Measure (ℕ → α)} :
    ContractableLaw ρ ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  Iff.rfl

/-- The defining invariance of a contractable path law. -/
@[simp]
theorem ContractableLaw.map_reindex {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  hρ φ hφ

/-- A strictly increasing time reindexing preserves a contractable path law. -/
theorem ContractableLaw.measurePreserving_reindex {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ :=
  ⟨measurable_reindex φ, hρ.map_reindex hφ⟩

/-- Path-law contractability is equivalently measure preservation by every strictly increasing
time reindexing. -/
theorem contractableLaw_iff_forall_measurePreserving_reindex {ρ : Measure (ℕ → α)} :
    ContractableLaw ρ ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ := by
  constructor
  · intro hρ φ hφ
    exact hρ.measurePreserving_reindex hφ
  · intro hρ φ hφ
    exact (hρ φ hφ).map_eq

/-- A contractable path law is preserved by the one-sided shift. -/
theorem ContractableLaw.measurePreserving_shift {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) :
    MeasurePreserving (shift α) ρ ρ :=
  hρ.measurePreserving_reindex (φ := fun k => k + 1) fun _ _ h => Nat.add_lt_add_right h 1

/-- Every iterate of the one-sided shift preserves a contractable path law. -/
theorem ContractableLaw.measurePreserving_shift_iterate {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) ρ ρ :=
  (hρ.measurePreserving_shift).iterate n

/-- The one-sided shift leaves a contractable path law unchanged. -/
@[simp]
theorem ContractableLaw.map_shift {ρ : Measure (ℕ → α)} (hρ : ContractableLaw ρ) :
    ρ.map (shift α) = ρ :=
  hρ.measurePreserving_shift.map_eq

/-- Iterating the one-sided shift leaves a contractable path law unchanged. -/
@[simp]
theorem ContractableLaw.map_shift_iterate {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ) (n : ℕ) :
    ρ.map ((shift α)^[n]) = ρ :=
  (hρ.measurePreserving_shift_iterate n).map_eq

/-- A contractable process has a contractable path law. -/
theorem Contractable.contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Contractable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    ContractableLaw (pathLaw μ X) :=
  ContractableLaw.intro fun _ hφ => (hX.measurePreserving_reindex hX_meas hφ).map_eq

/-- Contractability of a process is equivalent to contractability of its path law. -/
theorem contractable_iff_contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ X ↔ ContractableLaw (pathLaw μ X) := by
  rw [contractable_iff_forall_map_reindex_pathLaw hX_meas, contractableLaw_iff]

/-- If a process has a contractable path law, then the process is contractable. -/
theorem contractable_of_contractableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hρ : ContractableLaw (pathLaw μ X)) :
    Contractable μ X :=
  (contractable_iff_contractableLaw_pathLaw hX_meas).2 hρ

end Probability

end TauCeti
