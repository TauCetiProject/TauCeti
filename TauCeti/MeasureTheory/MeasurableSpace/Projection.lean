/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.MeasurableSpace.Analytic
public import TauCeti.MeasureTheory.MeasurableSpace.CountablyGenerated
public import Mathlib.MeasureTheory.Measure.QuasiMeasurePreserving

/-!
# Measurable projection on an arbitrary measure space

The projection of a product-measurable set along a standard Borel factor is null-measurable
for every s-finite measure on the other factor. The other factor need not have a topology,
be countably generated, or separate points. For a complete s-finite measure the projection
is measurable.

The proof uses `Measurable.exists_eq_measurable_comp_prodMap` to encode the measurable set
by countably many Boolean coordinates. Only the target coordinate is replaced:
the standard Borel factor remains available for the analytic projection theorem.
Universal measurability on the Boolean coding space then pulls back along its measurable code.
This is the measurable-projection input for debut arguments, not a measurable selection theorem.

## References

* D. L. Cohn, *Measure Theory*, second edition, Birkhäuser, 2013,
  Proposition 8.4.4 (measurable projection).
-/

public section

open Set MeasureTheory

namespace MeasurableSet

variable {X Ω : Type*} [MeasurableSpace X] [StandardBorelSpace X]
  [MeasurableSpace Ω] {s : Set (X × Ω)} {μ : Measure Ω} [SFinite μ]

/-- Projection along a standard Borel factor is null-measurable for every s-finite
measure `μ` on the target, even when the target is an arbitrary measurable space. -/
theorem nullMeasurableSet_image_snd (hs : MeasurableSet s) :
    NullMeasurableSet (Prod.snd '' s) μ := by
  classical
  have hf : Measurable (s.indicator fun _ ↦ (1 : ℝ)) := measurable_const.indicator hs
  obtain ⟨q, r, g, hq, hr, hg, he⟩ := hf.exists_eq_measurable_comp_prodMap
  let A : Set (X × (ℕ → Bool)) := {p | g (q p.1, p.2) = 1}
  have hA : MeasurableSet A :=
    measurableSet_eq_fun (hg.comp (hq.prodMap measurable_id)) measurable_const
  have hproj : AnalyticSet (Prod.snd '' A) := hA.analyticSet_image measurable_snd
  have heq : Prod.snd '' s = r ⁻¹' (Prod.snd '' A) := by
    ext ω
    simp only [mem_image, Prod.exists, exists_eq_right, mem_preimage]
    apply exists_congr
    intro t
    have h := congr_fun he (t, ω)
    dsimp only [Function.comp_def, Prod.map] at h
    simp only [A, mem_ofPred_eq, ← h]
    simp
  rw [heq]
  exact (hproj.nullMeasurableSet (μ.map r)).preimage (hr.quasiMeasurePreserving μ)

/-- On a complete s-finite measure space the projection of a product-measurable set along a
standard Borel factor is measurable. No topological assumption on the target is needed. -/
theorem image_snd_of_complete (hs : MeasurableSet s) (μ : Measure Ω)
    [SFinite μ] [μ.IsComplete] :
    MeasurableSet (Prod.snd '' s) :=
  (hs.nullMeasurableSet_image_snd (μ := μ)).measurable_of_complete

end MeasurableSet
