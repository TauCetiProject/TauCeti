/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import Mathlib.MeasureTheory.Measure.Real

/-!
# Total Riemannian volume

The Riemannian volume measure of a compact manifold has finite mass. Its total mass is
therefore a real number, `TauCeti.riemannianTotalVolume`. This is the volume associated
to the chosen Riemannian metric, and is preserved by differentiable isometries. The
construction also applies to compact manifolds with boundary or corners.

The volume is the total mass of the Riemannian density of J. M. Lee, *Introduction to
Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2.
-/

public section

open Bundle MeasureTheory Set
open scoped InnerProductSpace Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [CompactSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- The total volume of a compact Riemannian manifold, as a real number. -/
def riemannianTotalVolume (I : ModelWithCorners ℝ E H) (M : Type*)
    [TopologicalSpace M] [CompactSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    [MeasurableSpace M] [BorelSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)] : ℝ :=
  (riemannianVolume I M).real univ

/-- Total Riemannian volume is the real mass of the whole manifold. -/
theorem riemannianTotalVolume_def :
    riemannianTotalVolume I M = (riemannianVolume I M).real univ :=
  (rfl)

/-- The total volume recovers the finite mass of the Riemannian volume measure. -/
@[simp]
theorem ofReal_riemannianTotalVolume :
    ENNReal.ofReal (riemannianTotalVolume I M) = riemannianVolume I M univ := by
  rw [riemannianTotalVolume_def]
  exact ofReal_measureReal (by finiteness)

/-- Total Riemannian volume is nonnegative. -/
theorem riemannianTotalVolume_nonneg : 0 ≤ riemannianTotalVolume I M :=
  measureReal_nonneg

variable {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [CompactSpace N] [ChartedSpace H' N]
  [IsManifold I' 1 N]
  [MeasurableSpace N] [BorelSpace N]
  [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-- A differentiable isometry between compact Riemannian manifolds preserves total volume. -/
theorem _root_.Homeomorph.riemannianTotalVolume_eq (Φ : M ≃ₜ N)
    (hΦ : MDifferentiable I I' Φ)
    (hinner : ∀ x (v w : TangentSpace I x),
      ⟪mfderiv I I' Φ x v, mfderiv I I' Φ x w⟫_ℝ = ⟪v, w⟫_ℝ) :
    riemannianTotalVolume I M = riemannianTotalVolume I' N := by
  rw [riemannianTotalVolume_def, riemannianTotalVolume_def]
  have h := Φ.measurePreserving_riemannianVolume hΦ hinner
  apply congrArg ENNReal.toReal
  calc
    (riemannianVolume I M) univ = ((riemannianVolume I M).map Φ) univ := by
      rw [Measure.map_apply Φ.measurable MeasurableSet.univ, preimage_univ]
    _ = (riemannianVolume I' N) univ := congrArg (· univ) h.map_eq

end TauCeti
