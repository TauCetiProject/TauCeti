module

public import TauCeti.Probability.Exchangeability.PathSpace.ContractableLaw

/-!
# Exchangeable path laws are contractable

This file records the path-space form of the Layer 0 bridge from exchangeability to
contractability: an exchangeable finite measure on one-sided path space is invariant under
every strictly increasing reindexing of time. The process-level theorem remains available in
`TauCeti.Probability.Exchangeability.Contractability`; this file is the corresponding
`ExchangeableLaw` to `ContractableLaw` adapter.

The proof uses only the finite-dimensional marginal characterization of `ContractableLaw` and
the existing finite-marginal consequence of `ExchangeableLaw`. No measure-theoretic
infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The finite marginal of an exchangeable path law along a strictly increasing selection is its
prefix marginal. This is the ordered-selection form of
`ExchangeableLaw.map_prefixProj_of_injective`. -/
theorem ExchangeableLaw.map_prefixProj_of_strictMono {ρ : Measure (ℕ → α)}
    (hρ : ExchangeableLaw ρ) {n : ℕ} {k : Fin n → ℕ} (hk : StrictMono k) :
    ρ.map (fun x : ℕ → α => fun i : Fin n => x (k i)) =
      ρ.map (prefixProj α n) :=
  hρ.map_prefixProj_of_injective k hk.injective

/-- An exchangeable finite path law is contractable: invariance under all permutations implies
invariance under every strictly increasing time reindexing. -/
theorem ExchangeableLaw.contractableLaw {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    ContractableLaw ρ := by
  rw [contractableLaw_iff_forall_map_prefixProj_of_strictMono]
  intro n k hk
  exact hρ.map_prefixProj_of_strictMono hk

/-- Every strictly increasing time reindexing preserves an exchangeable finite path law. -/
theorem ExchangeableLaw.map_reindex_of_strictMono {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  hρ.contractableLaw.map_reindex hφ

/-- Every strictly increasing time reindexing is measure-preserving for an exchangeable finite
path law. -/
theorem ExchangeableLaw.measurePreserving_reindex_of_strictMono {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] (hρ : ExchangeableLaw ρ) {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) ρ ρ :=
  hρ.contractableLaw.measurePreserving_reindex hφ

/-- The one-sided shift preserves an exchangeable finite path law. -/
theorem ExchangeableLaw.measurePreserving_shift {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    MeasurePreserving (shift α) ρ ρ :=
  hρ.contractableLaw.measurePreserving_shift

/-- Every iterate of the one-sided shift preserves an exchangeable finite path law. -/
theorem ExchangeableLaw.measurePreserving_shift_iterate {ρ : Measure (ℕ → α)}
    [IsFiniteMeasure ρ] (hρ : ExchangeableLaw ρ) (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) ρ ρ :=
  hρ.contractableLaw.measurePreserving_shift_iterate n

/-- The one-sided shift leaves an exchangeable finite path law unchanged. -/
theorem ExchangeableLaw.map_shift {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) :
    ρ.map (shift α) = ρ :=
  hρ.contractableLaw.map_shift

/-- Iterating the one-sided shift leaves an exchangeable finite path law unchanged. -/
theorem ExchangeableLaw.map_shift_iterate {ρ : Measure (ℕ → α)} [IsFiniteMeasure ρ]
    (hρ : ExchangeableLaw ρ) (n : ℕ) :
    ρ.map ((shift α)^[n]) = ρ :=
  hρ.contractableLaw.map_shift_iterate n

end Probability

end TauCeti
