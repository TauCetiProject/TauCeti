module

public import TauCeti.Probability.Exchangeability.Contractability

/-!
# Coordinatewise maps of exchangeable processes

This file records the Layer 0 closure API saying that the basic exchangeability
notions are preserved by applying the same measurable map to every coordinate of a
process. This is the process-level form of pushing forward finite-dimensional and
path laws by the coordinatewise map on product spaces.

The target is listed in `TauCetiRoadmap/Exchangeability/README.md`, Layer 0, under
closure of each symmetry class under coordinatewise pushforward `X ↦ (f ∘ Xᵢ)`.
The proofs reuse the `blockLaw`, `prefixLaw`, and `pathLaw` API from
`TauCeti.Probability.Exchangeability.Basic`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α β : Type*} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]

/-- A coordinatewise measurable map sends path laws to path laws. -/
theorem map_pathLaw (μ : Measure Ω) {X : ℕ → Ω → α} {f : α → β} (hf : Measurable f)
    (hX : AEMeasurable (fun ω => fun i => X i ω) μ) :
    (pathLaw μ X).map (fun x : ℕ → α => fun i => f (x i)) =
      pathLaw μ (fun n ω => f (X n ω)) := by
  rw [pathLaw_apply, pathLaw_apply]
  rw [AEMeasurable.map_map_of_aemeasurable]
  · rfl
  · exact (measurable_pi_lambda (fun x : ℕ → α => fun i => f (x i)) fun i =>
      hf.comp (measurable_pi_apply i)).aemeasurable
  · exact hX

/-- Coordinatewise a.e.-measurability of a sequence, bundled as a path-space map. -/
theorem aemeasurable_path_of_forall {μ : Measure Ω} {X : ℕ → Ω → α}
    (hX : ∀ i, AEMeasurable (X i) μ) : AEMeasurable (fun ω => fun i => X i ω) μ :=
  aemeasurable_pi_lambda (fun ω => fun i => X i ω) hX

/-- Coordinatewise measurability of a sequence, bundled as a path-space map. -/
theorem measurable_path_of_forall {X : ℕ → Ω → α} (hX : ∀ i, Measurable (X i)) :
    Measurable (fun ω => fun i => X i ω) :=
  measurable_pi_lambda (fun ω => fun i => X i ω) hX

/-- A coordinatewise measurable map sends path laws to path laws, under coordinatewise
measurability of the process. -/
theorem map_pathLaw_of_forall (μ : Measure Ω) {X : ℕ → Ω → α} {f : α → β}
    (hf : Measurable f) (hX : ∀ i, Measurable (X i)) :
    (pathLaw μ X).map (fun x : ℕ → α => fun i => f (x i)) =
      pathLaw μ (fun n ω => f (X n ω)) :=
  map_pathLaw μ hf (measurable_path_of_forall hX).aemeasurable

/-- Finite exchangeability at a fixed length is preserved by applying a measurable
map to every coordinate. -/
theorem ExchangeableAt.map_values {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) {f : α → β} (hf : Measurable f)
    (hX : ∀ i : Fin n, AEMeasurable (X i.val) μ) :
    ExchangeableAt μ (fun j ω => f (X j ω)) n := by
  intro σ
  calc
    blockLaw μ (fun j ω => f (X j ω)) (fun i : Fin n => (σ i).val) =
        (blockLaw μ X (fun i : Fin n => (σ i).val)).map
          (fun x : Fin n → α => fun i => f (x i)) := by
      exact (map_blockLaw μ (fun i : Fin n => (σ i).val) hf fun i => hX (σ i)).symm
    _ = (prefixLaw μ X n).map (fun x : Fin n → α => fun i => f (x i)) := by
      rw [h σ]
    _ = prefixLaw μ (fun j ω => f (X j ω)) n := by
      exact map_prefixLaw μ hf n hX

/-- Finite exchangeability at a fixed length is preserved by applying a measurable
map to every coordinate of a measurable process. -/
theorem ExchangeableAt.map_values_measurable {μ : Measure Ω} {X : ℕ → Ω → α} {n : ℕ}
    (h : ExchangeableAt μ X n) {f : α → β} (hf : Measurable f)
    (hX : ∀ i : Fin n, Measurable (X i.val)) :
    ExchangeableAt μ (fun j ω => f (X j ω)) n :=
  h.map_values hf fun i => (hX i).aemeasurable

/-- Exchangeability is preserved by applying a measurable map to every coordinate. -/
theorem Exchangeable.map_values {μ : Measure Ω} {X : ℕ → Ω → α} (h : Exchangeable μ X)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    Exchangeable μ (fun j ω => f (X j ω)) := by
  intro n
  exact (h.exchangeableAt n).map_values hf fun i => hX i.val

/-- Exchangeability is preserved by applying a measurable map to every coordinate of a
measurable process. -/
theorem Exchangeable.map_values_measurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Exchangeable μ X) {f : α → β} (hf : Measurable f) (hX : ∀ i, Measurable (X i)) :
    Exchangeable μ (fun j ω => f (X j ω)) :=
  h.map_values hf fun i => (hX i).aemeasurable

/-- Full exchangeability is preserved by applying a measurable map to every coordinate. -/
theorem FullyExchangeable.map_values {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) {f : α → β} (hf : Measurable f)
    (hX : AEMeasurable (fun ω => fun i => X i ω) μ) :
    FullyExchangeable μ (fun j ω => f (X j ω)) := by
  intro π
  let coordinateMap : (ℕ → α) → ℕ → β := fun x i => f (x i)
  have hCoordinateMap : AEMeasurable coordinateMap (μ.map fun ω i => X (π i) ω) := by
    exact (measurable_pi_lambda coordinateMap fun i =>
      hf.comp (measurable_pi_apply i)).aemeasurable
  have hPermuted : AEMeasurable (fun ω => fun i => X (π i) ω) μ := by
    exact (measurable_pi_lambda (fun x : ℕ → α => fun i => x (π i)) fun i =>
      measurable_pi_apply (π i)).aemeasurable.comp_aemeasurable hX
  calc
    μ.map (fun ω i => f (X (π i) ω)) =
        (μ.map (fun ω i => X (π i) ω)).map coordinateMap := by
      rw [AEMeasurable.map_map_of_aemeasurable hCoordinateMap hPermuted]
      rfl
    _ = (pathLaw μ X).map coordinateMap := by
      rw [h π]
    _ = pathLaw μ (fun j ω => f (X j ω)) := by
      exact map_pathLaw μ hf hX

/-- Full exchangeability is preserved by a coordinatewise measurable map when the
process coordinates are a.e.-measurable one at a time. -/
theorem FullyExchangeable.map_values_of_forall {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) {f : α → β} (hf : Measurable f)
    (hX : ∀ i, AEMeasurable (X i) μ) :
    FullyExchangeable μ (fun j ω => f (X j ω)) :=
  h.map_values hf (aemeasurable_path_of_forall hX)

/-- Full exchangeability is preserved by applying a measurable map to every coordinate of a
measurable process. -/
theorem FullyExchangeable.map_values_measurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : FullyExchangeable μ X) {f : α → β} (hf : Measurable f)
    (hX : ∀ i, Measurable (X i)) :
    FullyExchangeable μ (fun j ω => f (X j ω)) :=
  h.map_values hf (measurable_path_of_forall hX).aemeasurable

/-- Contractability is preserved by applying a measurable map to every coordinate. -/
theorem Contractable.map_values {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {f : α → β} (hf : Measurable f) (hX : ∀ i, AEMeasurable (X i) μ) :
    Contractable μ (fun j ω => f (X j ω)) := by
  intro m k hk
  calc
    blockLaw μ (fun j ω => f (X j ω)) k =
        (blockLaw μ X k).map (fun x : Fin m → α => fun i => f (x i)) := by
      exact (map_blockLaw μ k hf fun i => hX (k i)).symm
    _ = (prefixLaw μ X m).map (fun x : Fin m → α => fun i => f (x i)) := by
      rw [h.map hk]
    _ = prefixLaw μ (fun j ω => f (X j ω)) m := by
      exact map_prefixLaw μ hf m fun i => hX i.val

/-- Contractability is preserved by applying a measurable map to every coordinate of a
measurable process. -/
theorem Contractable.map_values_measurable {μ : Measure Ω} {X : ℕ → Ω → α}
    (h : Contractable μ X) {f : α → β} (hf : Measurable f) (hX : ∀ i, Measurable (X i)) :
    Contractable μ (fun j ω => f (X j ω)) :=
  h.map_values hf fun i => (hX i).aemeasurable

end Probability

end TauCeti
