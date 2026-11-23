/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Riccardo Brasca
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.MeasureTheory.Integral.OddSymmetric

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

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {n : ℕ} [Fact (Module.finrank ℝ E = n + 1)]

/-- Native Riemannian volume on the round unit sphere is invariant under negation. -/
instance isNegInvariant_riemannianVolume_sphere :
    letI := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
    (riemannianVolume (𝓡 n) (Metric.sphere (0 : E) 1)).IsNegInvariant := by
  have := FiniteDimensional.of_fact_finrank_eq_succ (K := ℝ) (V := E) n
  let Φ := (LinearIsometryEquiv.neg ℝ (E := E)).unitSphereRiemannianIsometry
    (n := n) (k := n)
  have hΦ : (Φ : Metric.sphere (0 : E) 1 → Metric.sphere (0 : E) 1) = fun x => -x := by
    funext x
    rw [← RiemannianIsometry.coe_toDiffeomorph Φ]
    rw [LinearIsometryEquiv.unitSphereRiemannianIsometry_toDiffeomorph]
    exact LinearIsometryEquiv.unitSphereDiffeomorph_neg_apply x
  exact ⟨by simpa only [Measure.neg_def, hΦ] using Φ.measurePreserving_riemannianVolume.map_eq⟩

end TauCeti
