/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Support

/-!
# Strict positivity of Riemannian volume integrals

The Riemannian volume measure is positive on nonempty open sets. This file turns that local
property into the strict `lintegral` positivity statement for continuous functions that are
positive somewhere.
-/

public section

open Bundle MeasureTheory Set
open scoped ENNReal Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [T2Space M] [SigmaCompactSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

omit [T2Space M] in
/-- A continuous function that is positive somewhere has positive integral against Riemannian
volume. The statement uses the lower Lebesgue integral, so it remains informative when the function
is not Bochner-integrable. -/
theorem lintegral_riemannianVolume_pos {f : M → ℝ} (hf : Continuous f)
    (hpos : ∃ x, 0 < f x) :
    0 < ∫⁻ x, ENNReal.ofReal (f x) ∂TauCeti.riemannianVolume I M := by
  have hmeas : Measurable (fun x ↦ ENNReal.ofReal (f x)) :=
    ENNReal.measurable_ofReal.comp hf.measurable
  rw [lintegral_pos_iff_support hmeas]
  obtain ⟨x, hx⟩ := hpos
  let U : Set M := {y | 0 < f y}
  have hUopen : IsOpen U := isOpen_lt continuous_const hf
  have hUne : U.Nonempty := ⟨x, hx⟩
  have hUpos : 0 < TauCeti.riemannianVolume I M U := hUopen.measure_pos _ hUne
  refine hUpos.trans_le (measure_mono ?_)
  intro y hy
  exact (ENNReal.ofReal_pos.mpr hy).ne'

end TauCeti
