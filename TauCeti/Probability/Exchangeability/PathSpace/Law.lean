module

public import TauCeti.Probability.Exchangeability.FullyExchangeable
import TauCeti.Probability.Exchangeability.PermutationExtension

/-!
# Exchangeable laws on path space

This file adds the path-law formulation of full exchangeability for measures on `ℕ → α`.
The process-level definitions in `TauCeti.Probability.Exchangeability.Basic` remain the main
user-facing API for stochastic processes; `ExchangeableLaw` names the equivalent path-space
viewpoint needed by π-system, invariant-σ-algebra, and shift arguments.

The bridges here realize the Layer 0 roadmap item asking for process-level ↔ path-law bridges
in both directions. They reuse the existing `FullyExchangeable` path-law bridge from
`FullyExchangeable.lean`; no measure-theoretic infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A measure on one-sided path space is exchangeable if it is invariant under every
permutation of the time coordinate. -/
def ExchangeableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ

/-- Constructor for `ExchangeableLaw` from the defining map invariance. -/
theorem ExchangeableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ) :
    ExchangeableLaw ρ :=
  h

/-- Simp normal form for `ExchangeableLaw`. -/
@[simp]
theorem exchangeableLaw_iff {ρ : Measure (ℕ → α)} :
    ExchangeableLaw ρ ↔ ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ :=
  Iff.rfl

/-- The defining invariance of an exchangeable path law. -/
theorem ExchangeableLaw.map_permReindex {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ)
    (π : Equiv.Perm ℕ) :
    ρ.map (permReindex (α := α) π) = ρ :=
  hρ π

/-- Reindexing by a time permutation preserves an exchangeable path law. -/
theorem ExchangeableLaw.measurePreserving_permReindex {ρ : Measure (ℕ → α)}
    (hρ : ExchangeableLaw ρ) (π : Equiv.Perm ℕ) :
    MeasurePreserving (permReindex (α := α) π) ρ ρ :=
  ⟨measurable_reindex π, hρ.map_permReindex π⟩

/-- Path-law exchangeability is equivalently measure preservation by every time permutation. -/
theorem exchangeableLaw_iff_forall_measurePreserving_permReindex {ρ : Measure (ℕ → α)} :
    ExchangeableLaw ρ ↔
      ∀ π : Equiv.Perm ℕ, MeasurePreserving (permReindex (α := α) π) ρ ρ := by
  constructor
  · intro hρ π
    exact hρ.measurePreserving_permReindex π
  · intro hρ π
    exact (hρ π).map_eq

/-- The prefix marginal after a path-space permutation is the corresponding finite-dimensional
coordinate marginal. -/
theorem map_permReindex_prefixProj (ρ : Measure (ℕ → α)) (π : Equiv.Perm ℕ) (n : ℕ) :
    (ρ.map (permReindex (α := α) π)).map (prefixProj α n) =
      ρ.map (fun x : ℕ → α => fun i : Fin n => x (π i.val)) := by
  have hperm :
      permReindex (α := α) π = (fun x : ℕ → α => fun k => x (π k)) := by
    funext x k
    rw [permReindex_apply]
  rw [hperm, Measure.map_map (measurable_prefixProj n) (measurable_reindex π)]
  rfl

/-- The prefix marginal of an exchangeable path law is invariant under permutations of the
finite prefix. -/
theorem ExchangeableLaw.map_prefixProj_perm {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ)
    (n : ℕ) (σ : Equiv.Perm (Fin n)) :
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (σ i).val) =
      ρ.map (prefixProj α n) := by
  obtain ⟨π, hπ⟩ := Equiv.Perm.exists_extending_pair (fun i : Fin n => i.val)
    (fun i : Fin n => (σ i).val) Fin.val_injective
    (fun _ _ h => σ.injective (Fin.val_injective h))
  have hidx :
      (fun x : ℕ → α => fun i : Fin n => x (π i.val)) =
        fun x : ℕ → α => fun i : Fin n => x (σ i).val := by
    funext x i
    rw [hπ i]
  calc
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (σ i).val)
        = ρ.map (fun x : ℕ → α => fun i : Fin n => x (π i.val)) := by
          rw [← hidx]
    _ = (ρ.map (permReindex (α := α) π)).map (prefixProj α n) := by
          rw [map_permReindex_prefixProj]
    _ = ρ.map (prefixProj α n) := by rw [hρ.map_permReindex π]

/-- A fully exchangeable process has an exchangeable path law. -/
theorem FullyExchangeable.exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : FullyExchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    ExchangeableLaw (pathLaw μ X) := by
  intro π
  exact hX.map_permReindex_pathLaw hX_meas π

/-- A process is fully exchangeable iff its path law is an exchangeable path-space measure. -/
theorem fullyExchangeable_iff_exchangeableLaw_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ X ↔ ExchangeableLaw (pathLaw μ X) := by
  rw [fullyExchangeable_iff_forall_map_permReindex_pathLaw μ hX_meas]
  rfl

/-- For finite laws, finite exchangeability of a process is equivalent to exchangeability of
its path law. -/
theorem exchangeable_iff_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    Exchangeable μ X ↔ ExchangeableLaw (pathLaw μ X) := by
  rw [exchangeable_iff_fullyExchangeable hX_meas,
    fullyExchangeable_iff_exchangeableLaw_pathLaw μ hX_meas]

/-- A process whose path law is exchangeable is fully exchangeable. -/
theorem fullyExchangeable_of_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (hρ : ExchangeableLaw (pathLaw μ X)) :
    FullyExchangeable μ X :=
  (fullyExchangeable_iff_exchangeableLaw_pathLaw μ hX_meas).2 hρ

/-- A process whose path law is exchangeable is finitely exchangeable under a finite base law. -/
theorem exchangeable_of_exchangeableLaw_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (hρ : ExchangeableLaw (pathLaw μ X)) :
    Exchangeable μ X :=
  (exchangeable_iff_exchangeableLaw_pathLaw hX_meas).2 hρ

end Probability

end TauCeti
