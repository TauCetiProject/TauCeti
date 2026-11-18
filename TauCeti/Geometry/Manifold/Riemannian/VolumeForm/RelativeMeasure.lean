/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative
public import TauCeti.Geometry.Manifold.Riemannian.VolumeForm.Measure

/-!
# Relative Riemannian volume and oriented volume forms

The orientation-free relative density compares the measures induced by Riemannian
volume forms for any choices of source and target orientations. Reversing either
orientation leaves the positive measure unchanged.
-/

public noncomputable section
open Bundle Manifold Bundle.ContMDiffRiemannianMetric
open scoped ContDiff
namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M]
  [ChartedSpace H M] [IsManifold I 1 M] [LindelofSpace M] {n n' : ℕ∞ω} {m : ℕ}
  [Fact (Module.finrank ℝ E = m)]

/-- Relative density compares the measures of oriented volume forms, regardless of orientations. -/
theorem measure_riemannianVolumeForm_eq_map_withDensity_relativeVolumeDensity
    (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))
    (g' : ContMDiffRiemannianMetric I n' E (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I (WithMetric g) (Fin m))
    (o' : Manifold.Orientation I (WithMetric g') (Fin m)) :
    (riemannianVolumeForm o').measure =
      (((riemannianVolumeForm o).measure).withDensity fun x : WithMetric g ↦
          ENNReal.ofReal (relativeVolumeDensity g g' x.ofWithMetric)).map
        fun x ↦ WithMetric.toWithMetric g' x.ofWithMetric := by
  rw [measure_riemannianVolumeForm, measure_riemannianVolumeForm]
  exact riemannianVolume_eq_map_withDensity_relativeVolumeDensity (g := g) (g' := g')

/-- Reversing an orientation leaves the positive Riemannian measure unchanged. -/
theorem measure_riemannianVolumeForm_neg (g : ContMDiffRiemannianMetric I n E
    (fun x : M ↦ TangentSpace I x))
    (o : Manifold.Orientation I (WithMetric g) (Fin m)) :
    (riemannianVolumeForm (-o)).measure = (riemannianVolumeForm o).measure := by
  rw [measure_riemannianVolumeForm, measure_riemannianVolumeForm]

end TauCeti
