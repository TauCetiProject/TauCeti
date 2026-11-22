/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.Volume.Sphere
public import TauCeti.Geometry.Manifold.Riemannian.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Total
import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Hausdorff

/-!
# The Riemannian volume of the round sphere

The round metric on the unit sphere `Sⁿ` of a real inner product space `E` of dimension `n + 1`
(`TauCeti.sphereRoundMetric`) is induced by the inclusion of the sphere into `E`. Its Riemannian
volume is therefore the extrinsic surface measure of the sphere: the inclusion carries it to the
normalized `n`-dimensional Hausdorff measure `μHE[n]` of `E` restricted to the sphere. In
particular the round sphere has total volume `|Sⁿ| = TauCeti.roundSphereVolume n`, the constant in
the Yamabe invariant `Y(Sⁿ) = n (n - 1) |Sⁿ| ^ (2 / n)` of the round sphere.

## Main results

* `TauCeti.map_subtypeVal_riemannianVolume_sphere`: the inclusion of the sphere carries its
  Riemannian volume to `μHE[n]` restricted to the sphere.
* `TauCeti.riemannianTotalVolume_sphere`: the round sphere has total volume `|Sⁿ|`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (the round metric as an induced metric, and the Riemannian density).
-/

public section

open MeasureTheory Metric Module Set
open scoped Manifold

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {n : ℕ} [Fact (finrank ℝ E = n + 1)] [MeasurableSpace E] [BorelSpace E]

/-- **The Riemannian volume of the round sphere is its surface measure.** The inclusion of the unit
sphere `Sⁿ` into `E` carries the Riemannian volume of the round metric to the normalized
`n`-dimensional Hausdorff measure of `E` restricted to the sphere. -/
theorem map_subtypeVal_riemannianVolume_sphere :
    (riemannianVolume (𝓡 n) (sphere (0 : E) 1)).map ((↑) : sphere (0 : E) 1 → E) =
      (μHE[n]).restrict (sphere (0 : E) 1) := by
  have h := map_riemannianVolume_of_inner_mfderiv (I := 𝓡 n) (M := sphere (0 : E) 1)
    Subtype.val_injective fun x v w ↦ by
      rw [inner_tangentSpace_sphere, mvfderiv_apply_eq_mfderiv_apply,
        mvfderiv_apply_eq_mfderiv_apply]
      -- The two sides use the inner products of `TangentSpace 𝓘(ℝ, E) x` and of `E`, which agree.
      rfl
  rwa [finrank_euclideanSpace_fin, Subtype.range_coe] at h

/-- **The volume of the round sphere.** The unit sphere `Sⁿ` with its round metric has total volume
`|Sⁿ| = 2 π ^ ((n + 1) / 2) / Γ((n + 1) / 2)`. -/
@[simp]
theorem riemannianTotalVolume_sphere :
    riemannianTotalVolume (𝓡 n) (sphere (0 : E) 1) = roundSphereVolume n := by
  have h := congr($(map_subtypeVal_riemannianVolume_sphere (E := E) (n := n)) univ)
  rw [Measure.map_apply measurable_subtypeVal MeasurableSet.univ, preimage_univ,
    Measure.restrict_apply MeasurableSet.univ, univ_inter,
    euclideanHausdorffMeasure_sphere_eq_ofReal_roundSphereVolume Fact.out] at h
  rw [riemannianTotalVolume_def, measureReal_def, h,
    ENNReal.toReal_ofReal (roundSphereVolume_pos n).le]

end TauCeti
