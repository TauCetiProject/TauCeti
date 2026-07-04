module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift

/-!
# Exchangeable laws are stationary

This file records the Layer 0 stationarity bridge from the Exchangeability roadmap: a finitely
exchangeable process has a shift-invariant path law.  The existing implication
`Exchangeable.contractable` gives the mathematical content; the lemmas here provide the direct
`Exchangeable`-named API that downstream shift, tail, and ergodic arguments can use without
manually detouring through contractability.

The bridge is stated for all strictly monotone time reindexings first, then specialized to the
one-sided shift and its iterates.  The final `processShift` form packages the same invariance at
the process-law level.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Exchangeable laws are invariant under strictly monotone reindexing.**  If `X` is
exchangeable and its coordinates are a.e.-measurable, then the path-law reindexing
`x ↦ x ∘ φ` preserves `pathLaw μ X` for every strictly monotone `φ : ℕ → ℕ`. -/
theorem Exchangeable.measurePreserving_reindex {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (pathLaw μ X) (pathLaw μ X) :=
  (hX.contractable hX_meas).measurePreserving_reindex hX_meas hφ

/-- Reindexing the path law of an exchangeable process by a strictly monotone map leaves it
unchanged. -/
theorem Exchangeable.map_reindex_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) = pathLaw μ X :=
  (hX.measurePreserving_reindex hX_meas hφ).map_eq

/-- **An exchangeable process has a shift-invariant path law.** -/
theorem Exchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) :=
  (hX.contractable hX_meas).measurePreserving_shift hX_meas

/-- Shifting the path law of an exchangeable process leaves it unchanged. -/
theorem Exchangeable.map_shift_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    (pathLaw μ X).map (shift α) = pathLaw μ X :=
  (hX.measurePreserving_shift hX_meas).map_eq

/-- Every iterate of the one-sided shift preserves the path law of an exchangeable process. -/
theorem Exchangeable.measurePreserving_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    MeasurePreserving ((shift α)^[n]) (pathLaw μ X) (pathLaw μ X) :=
  (hX.measurePreserving_shift hX_meas).iterate n

/-- Iterating the one-sided shift leaves the path law of an exchangeable process unchanged. -/
theorem Exchangeable.map_shift_iterate_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    (pathLaw μ X).map ((shift α)^[n]) = pathLaw μ X :=
  (hX.measurePreserving_shift_iterate hX_meas n).map_eq

/-- Setwise stationarity: a shift preimage has the same path-law mass as the original measurable
set. -/
theorem Exchangeable.pathLaw_preimage_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {s : Set (ℕ → α)} (hs : MeasurableSet s) :
    pathLaw μ X (shift α ⁻¹' s) = pathLaw μ X s :=
  (hX.measurePreserving_shift hX_meas).measure_preimage hs.nullMeasurableSet

/-- Setwise stationarity for every shift iterate. -/
theorem Exchangeable.pathLaw_preimage_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) {s : Set (ℕ → α)} (hs : MeasurableSet s) :
    pathLaw μ X (((shift α)^[n]) ⁻¹' s) = pathLaw μ X s :=
  (hX.measurePreserving_shift_iterate hX_meas n).measure_preimage hs.nullMeasurableSet

/-- The law of the `n`-step shifted process of an exchangeable process is the original path law. -/
theorem Exchangeable.map_processShift_eq_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    μ.map (processShift X n) = pathLaw μ X := by
  rw [map_processShift μ hX_meas n, hX.map_shift_iterate_pathLaw hX_meas n]

/-- The one-step shifted process of an exchangeable process has the same law as the original
path. -/
theorem Exchangeable.map_processShift_one_eq_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    μ.map (processShift X 1) = pathLaw μ X :=
  hX.map_processShift_eq_pathLaw hX_meas 1

/-- Prefix laws are unchanged after shifting an exchangeable process by any finite amount. -/
theorem Exchangeable.map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw {μ : Measure Ω}
    {X : ℕ → Ω → α} [IsFiniteMeasure μ] (hX : Exchangeable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) = prefixLaw μ X m := by
  rw [hX.map_shift_iterate_pathLaw hX_meas n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) m]

/-- Setwise prefix-law form of exchangeable stationarity after a finite shift. -/
theorem Exchangeable.map_prefixProj_shift_iterate_pathLaw_apply {μ : Measure Ω}
    {X : ℕ → Ω → α} [IsFiniteMeasure μ] (hX : Exchangeable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) (s : Set (Fin m → α)) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) s = prefixLaw μ X m s := by
  rw [hX.map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw hX_meas n m]

end Probability

end TauCeti
