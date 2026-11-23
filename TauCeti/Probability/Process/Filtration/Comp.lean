/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Process.Adapted
public import Mathlib.Probability.Process.Stopping

/-!
# Sampling a filtration

`MeasureTheory.Filtration.comp` composes a filtration with a monotone time map, preserving
sigma-finiteness relative to the filtration. Sampling processes along the same map preserves
adaptedness and strong adaptedness (`MeasureTheory.Adapted.comp` and
`MeasureTheory.StronglyAdapted.comp`).

This restricts filtrations and processes to deterministic grids or shifted indices, allowing
discrete-time martingale results to be applied to the sampled processes. Conversely, a stopping
time of the sampled filtration, read through the time map, is a stopping time of the original
filtration (`MeasureTheory.IsStoppingTime.map`), and stopping the sampled process at it gives the
original process stopped at the mapped time (`MeasureTheory.stoppedValue_comp_of_ne_top`).
-/

public section

namespace MeasureTheory.Filtration

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]

/-- Sample a filtration along a monotone time map. -/
def comp (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) : Filtration κ m where
  seq n := ℱ (τ n)
  mono' _ _ h := ℱ.mono (hτ h)
  le' n := ℱ.le (τ n)

/-- The sampled filtration at an index is the original filtration at its sampling time. -/
@[simp]
theorem comp_apply (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ) (n : κ) :
    ℱ.comp hτ n = ℱ (τ n) := (rfl)

/-- Sampling preserves sigma-finiteness relative to a filtration. -/
instance {μ : Measure Ω} (ℱ : Filtration ι m) [SigmaFiniteFiltration μ ℱ]
    {τ : κ → ι} (hτ : Monotone τ) : SigmaFiniteFiltration μ (ℱ.comp hτ) where
  SigmaFinite n := by
    -- The trim depends on the inclusion proof; unfold sampling here rather than rewriting it.
    change SigmaFinite (μ.trim (ℱ.le (τ n)))
    infer_instance

/-- Measurable events at a sampled index are those at its sampling time. -/
@[simp]
theorem measurableSet_comp_iff (ℱ : Filtration ι m) {τ : κ → ι} (hτ : Monotone τ)
    (n : κ) {s : Set Ω} : MeasurableSet[ℱ.comp hτ n] s ↔ MeasurableSet[ℱ (τ n)] s :=
  (Iff.rfl)

/-- Measurability at a sampled index is measurability at its sampling time. -/
@[simp]
theorem measurable_comp_iff {E : Type*} [MeasurableSpace E] (ℱ : Filtration ι m)
    {τ : κ → ι} (hτ : Monotone τ) (n : κ) {f : Ω → E} :
    Measurable[ℱ.comp hτ n] f ↔ Measurable[ℱ (τ n)] f := (Iff.rfl)

/-- Strong measurability at a sampled index is that at its sampling time. -/
@[simp]
theorem stronglyMeasurable_comp_iff {E : Type*} [TopologicalSpace E] (ℱ : Filtration ι m)
    {τ : κ → ι} (hτ : Monotone τ) (n : κ) {f : Ω → E} :
    StronglyMeasurable[ℱ.comp hτ n] f ↔ StronglyMeasurable[ℱ (τ n)] f := (Iff.rfl)

/-- Sampling at the identity leaves a filtration unchanged. -/
@[simp]
theorem comp_id (ℱ : Filtration ι m) : ℱ.comp (τ := id) monotone_id = ℱ := by
  ext n
  rfl

/-- Successive sampling is sampling along the composite time map. -/
@[simp]
theorem comp_comp {η : Type*} [Preorder η] (ℱ : Filtration ι m)
    {τ : κ → ι} (hτ : Monotone τ) {σ : η → κ} (hσ : Monotone σ) :
    (ℱ.comp hτ).comp hσ = ℱ.comp (hτ.comp hσ) := by
  ext n
  rfl

/-- Sampling preserves the order between filtrations. -/
theorem comp_mono {τ : κ → ι} (hτ : Monotone τ) :
    Monotone (fun ℱ : Filtration ι m ↦ ℱ.comp hτ) :=
  fun _ _ h n ↦ h (τ n)

end MeasureTheory.Filtration

namespace MeasureTheory

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [Preorder κ]
  {ℱ : Filtration ι m} {τ : κ → ι}

/-- Sampling an adapted process along a monotone map preserves adaptation. -/
theorem Adapted.comp {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    {X : (i : ι) → Ω → E i} (hX : Adapted ℱ X) (hτ : Monotone τ) :
    Adapted (ℱ.comp hτ) (fun n ↦ X (τ n)) := by
  intro n
  simpa only [Filtration.measurable_comp_iff] using hX (τ n)

/-- Sampling a strongly adapted process preserves strong adaptation. -/
theorem StronglyAdapted.comp {E : ι → Type*} [∀ i, TopologicalSpace (E i)]
    {X : (i : ι) → Ω → E i} (hX : StronglyAdapted ℱ X) (hτ : Monotone τ) :
    StronglyAdapted (ℱ.comp hτ) (fun n ↦ X (τ n)) := by
  intro n
  simpa only [Filtration.stronglyMeasurable_comp_iff] using hX (τ n)

end MeasureTheory

namespace MeasureTheory

variable {Ω ι κ : Type*} {m : MeasurableSpace Ω} [Preorder ι] [PartialOrder κ] [Countable κ]
  {ℱ : Filtration ι m} {τ : κ → ι}

/-- A stopping time of a filtration sampled along a monotone map `τ` with countable domain,
read through `τ`, is a stopping time of the original filtration. -/
theorem IsStoppingTime.map (hτ : Monotone τ) {σ : Ω → WithTop κ}
    (hσ : IsStoppingTime (ℱ.comp hτ) σ) : IsStoppingTime ℱ (fun ω ↦ (σ ω).map τ) := by
  intro t
  have hset : {ω | (σ ω).map τ ≤ t} = ⋃ k ∈ {k : κ | τ k ≤ t}, {ω | σ ω = k} := by
    ext ω
    cases h : σ ω <;> simp [h]
  rw [hset]
  exact MeasurableSet.biUnion (Set.to_countable _) fun k hk ↦
    ℱ.mono hk _ (hσ.measurableSet_eq_of_countable k)

omit [Preorder ι] [PartialOrder κ] [Countable κ] in
/-- Stopping a sampled process at a finite time is stopping the original process at the
mapped time. -/
theorem stoppedValue_comp_of_ne_top [Nonempty ι] [Nonempty κ] {β : Type*} {X : ι → Ω → β}
    {σ : Ω → WithTop κ} {ω : Ω} (hω : σ ω ≠ ⊤) :
    stoppedValue (fun k ↦ X (τ k)) σ ω = stoppedValue X (fun ω ↦ (σ ω).map τ) ω := by
  obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.1 hω
  simp [stoppedValue, ← hk]

end MeasureTheory
