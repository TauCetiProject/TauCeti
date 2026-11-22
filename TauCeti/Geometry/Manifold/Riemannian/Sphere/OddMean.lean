/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry

/-!
# Odd functions on a round sphere have zero mean

The antipodal isometry preserves native Riemannian volume. Its odd functions therefore integrate
to zero. This is the mean-zero step in the stability calculation for the projective equator.

The proof originated in
[`ColdingMinicozziTheory`](https://github.com/riccardobrasca/ColdingMinicozziTheory/blob/1666783/ForTauCeti/Geometry/Manifold/Riemannian/Examples/Immersion/ProjectiveEquator/OddMean.lean).
-/

public noncomputable section

open MeasureTheory
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Negation preserves native Riemannian volume on the round unit sphere. -/
theorem measurePreserving_neg_riemannianVolume_sphere :
    MeasurePreserving (fun x : Metric.sphere (0 : E) 1 => -x)
      (riemannianVolume (𝓡 n) (Metric.sphere (0 : E) 1))
      (riemannianVolume (𝓡 n) (Metric.sphere (0 : E) 1)) := by
  let Φ := (LinearIsometryEquiv.neg ℝ (E := E)).unitSphereRiemannianIsometry
    (n := n) (k := n)
  have hΦ : (Φ : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1) = fun x => -x := by
    funext x
    apply Subtype.ext
    simp [Φ]
  rw [← hΦ]
  exact Φ.measurePreserving_riemannianVolume

/-- An antipodal-odd real function has zero integral for the native round-sphere volume. -/
theorem integral_odd_riemannianVolume_sphere_eq_zero
    (φ : Metric.sphere (0 : E) 1 → ℝ) (hodd : ∀ x, φ (-x) = -φ x) :
    ∫ x, φ x ∂riemannianVolume (𝓡 n) (Metric.sphere (0 : E) 1) = 0 := by
  let Φ := (LinearIsometryEquiv.neg ℝ (E := E)).unitSphereRiemannianIsometry
    (n := n) (k := n)
  have hΦ (x : Metric.sphere (0 : E) 1) : Φ x = -x := by
    apply Subtype.ext
    simp [Φ]
  have h := Φ.measurePreserving_riemannianVolume.integral_comp
    Φ.toDiffeomorph.toHomeomorph.measurableEmbedding φ
  have hfun : (fun x : Metric.sphere (0 : E) 1 => φ (Φ x)) = fun x => -φ x := by
    funext x
    rw [hΦ, hodd]
  rw [hfun, integral_neg] at h
  linarith

end TauCeti
