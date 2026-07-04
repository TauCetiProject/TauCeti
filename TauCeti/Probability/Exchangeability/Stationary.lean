module

public import TauCeti.Probability.Exchangeability.Contractability
public import TauCeti.Probability.Exchangeability.PathSpace.ProcessShift
import TauCeti.Probability.Exchangeability.FiniteMarginals

/-!
# Exchangeable laws are stationary

This file records the Layer 0 stationarity bridge from the Exchangeability roadmap: a finitely
exchangeable process has a shift-invariant path law.  The existing implication
`Exchangeable.contractable` gives the mathematical content; the lemmas here provide the direct
`Exchangeable`-named API that downstream shift, tail, and ergodic arguments can use without
manually detouring through contractability.

The bridge is stated for all injective time reindexings first, then specialized to the one-sided
shift and its iterates.  The final `processShift` form packages the same invariance at
the process-law level.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- **Exchangeable laws are invariant under injective reindexing.**  If `X` is
exchangeable and its coordinates are a.e.-measurable, then the path-law reindexing
`x ↦ x ∘ φ` preserves `pathLaw μ X` for every injective `φ : ℕ → ℕ`. -/
theorem Exchangeable.measurePreserving_reindex {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {φ : ℕ → ℕ} (hφ : Function.Injective φ) :
    MeasurePreserving (fun x : ℕ → α => fun k => x (φ k)) (pathLaw μ X) (pathLaw μ X) := by
  refine ⟨measurable_reindex φ, ?_⟩
  haveI : IsFiniteMeasure (pathLaw μ X) := by rw [pathLaw_def]; infer_instance
  refine measure_eq_of_prefixProj_map_eq ?_
  intro n
  rw [map_reindex_prefixProj_pathLaw μ hX_meas φ n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) n]
  exact hX.blockLaw_eq_prefixLaw_of_injective hX_meas (fun i : Fin n => φ i.val)
    (fun _ _ h => Fin.ext (hφ h))

/-- Reindexing the path law of an exchangeable process by an injective map leaves it
unchanged. -/
theorem Exchangeable.map_reindex_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    {φ : ℕ → ℕ} (hφ : Function.Injective φ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun k => x (φ k)) = pathLaw μ X :=
  (hX.measurePreserving_reindex hX_meas hφ).map_eq

/-- **An exchangeable process has a shift-invariant path law.** -/
theorem Exchangeable.measurePreserving_shift {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ) :
    MeasurePreserving (shift α) (pathLaw μ X) (pathLaw μ X) :=
  (hX.contractable hX_meas).measurePreserving_shift hX_meas

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

/-- Setwise stationarity for every shift iterate. -/
theorem Exchangeable.pathLaw_preimage_shift_iterate {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) {s : Set (ℕ → α)} (hs : NullMeasurableSet s (pathLaw μ X)) :
    pathLaw μ X (((shift α)^[n]) ⁻¹' s) = pathLaw μ X s :=
  (hX.measurePreserving_shift_iterate hX_meas n).measure_preimage hs

/-- The law of the `n`-step shifted process of an exchangeable process is the original path law. -/
theorem Exchangeable.map_processShift_eq_pathLaw {μ : Measure Ω} {X : ℕ → Ω → α}
    [IsFiniteMeasure μ] (hX : Exchangeable μ X) (hX_meas : ∀ i, AEMeasurable (X i) μ)
    (n : ℕ) :
    μ.map (processShift X n) = pathLaw μ X := by
  rw [map_processShift μ hX_meas n, hX.map_shift_iterate_pathLaw hX_meas n]

/-- Prefix laws are unchanged after shifting an exchangeable process by any finite amount. -/
theorem Exchangeable.map_prefixProj_shift_iterate_pathLaw_eq_prefixLaw {μ : Measure Ω}
    {X : ℕ → Ω → α} [IsFiniteMeasure μ] (hX : Exchangeable μ X)
    (hX_meas : ∀ i, AEMeasurable (X i) μ) (n m : ℕ) :
    ((pathLaw μ X).map ((shift α)^[n])).map (prefixProj α m) = prefixLaw μ X m := by
  rw [hX.map_shift_iterate_pathLaw hX_meas n,
    map_prefixProj_pathLaw μ (aemeasurable_pi_lambda _ hX_meas) m]

end Probability

end TauCeti
