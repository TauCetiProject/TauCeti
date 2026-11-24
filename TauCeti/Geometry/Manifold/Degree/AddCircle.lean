/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Degree.Global
public import TauCeti.Geometry.Manifold.Instances.AddCircle.Cover
public import TauCeti.Geometry.Manifold.Orientation.AddCircle

/-!
# The degree of the covering maps of circles

For positive periods `p = k q` with `k` a natural number, the covering map
`AddCircle.coverMap : ℝ / pℤ → ℝ / qℤ`, `[t]_p ↦ [t]_q`, is a smooth local diffeomorphism with
derivative `1`, so it preserves the positive orientations of the two circles
(`AddCircle.isOrientationPreservingAt_coverMap`), and each of its fibres has `k` points
(`AddCircle.ncard_preimage_coverMap_singleton`). Hence its mapping degree, for these orientations,
is `k` (`AddCircle.degree_coverMap`). The same holds for its product `id × coverMap` with the
identity of any connected oriented boundaryless manifold `X`, for the product orientations
(`AddCircle.degree_prodMap_id_coverMap`).

This is the degree with which the closed orbit, or the orbit torus `(s, θ) ↦ (s, [θ, x])`, of a
point of period `k d` covers that of the same point with period `d`: the former is the latter
precomposed with the covering map of the period circles
(`TauCeti.SmoothMappingTorus.orbitTorus_comp_prodMap_coverMap`). Its homological counterpart,
that `coverMap` carries the fundamental class of `ℝ / pℤ` to `k` times that of `ℝ / qℤ`, is
`AddCircle.singularHomologyMap_coverMap_fundamentalClass`.

## Main results

* `AddCircle.degree_coverMap`: the covering map `ℝ / (k q)ℤ → ℝ / qℤ` has degree `k`.
* `AddCircle.degree_prodMap_id_coverMap`: so does its product with the identity of a connected
  oriented manifold.

## References

* J. W. Milnor, *Topology from the Differentiable Viewpoint*, University Press of Virginia, 1965,
  §5 (the degree as a signed count of preimages).
-/

public section

noncomputable section

open Set TauCeti TauCeti.Manifold.Orientation
open scoped Manifold ContDiff

namespace AddCircle

variable {p q : ℝ} [Fact (0 < p)] [Fact (0 < q)] (h : p ∈ AddSubgroup.zmultiples q) {k : ℕ}

/-- For positive `p = k q` with `k` a natural number, the covering map `ℝ / pℤ → ℝ / qℤ` has degree
`k` for the positive orientations of the two circles. -/
theorem degree_coverMap (hp : p = k * q) :
    degree (AddCircle.orientation p) (AddCircle.orientation q) (coverMap h) = k := by
  rw [degree_eq_ncard_of_isOrientationPreservingAt _ _ (contMDiff_coverMap h ∞)
    (continuous_coverMap h).isProperMap (y := 0) fun z _ ↦ isOrientationPreservingAt_coverMap h z,
    ncard_preimage_coverMap_singleton h hp]

variable {E H X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace X] [ChartedSpace H X]
  [IsManifold I ∞ X] [BoundarylessManifold I X] [T2Space X] [SigmaCompactSpace X]
  [ConnectedSpace X] {m : ℕ}

/-- For positive `p = k q` with `k` a natural number and a connected oriented boundaryless
manifold `X`, the map `id × coverMap : X × ℝ / pℤ → X × ℝ / qℤ` has degree `k` for the product
orientations. -/
theorem degree_prodMap_id_coverMap (o : Manifold.Orientation I X (Fin m))
    (hp : p = k * q) :
    degree (o.prod (AddCircle.orientation p)) (o.prod (AddCircle.orientation q))
      (Prod.map id (coverMap h)) = k := by
  obtain ⟨x⟩ := ‹ConnectedSpace X›.toNonempty
  rw [degree_eq_ncard_of_isOrientationPreservingAt _ _
    (contMDiff_id.prodMap (contMDiff_coverMap h ∞))
    (isProperMap_id.prodMap (continuous_coverMap h).isProperMap) (y := (x, 0))
    fun z _ ↦ (isOrientationPreservingAt_id o z.1).prodMap
      (isOrientationPreservingAt_coverMap h z.2),
    ← singleton_prod_singleton, preimage_prod_map_prod, preimage_id, ncard_prod,
    ncard_singleton, one_mul, ncard_preimage_coverMap_singleton h hp]

end AddCircle
