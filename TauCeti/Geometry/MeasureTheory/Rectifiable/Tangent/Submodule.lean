/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.MeasureTheory.Rectifiable.TangentialFDeriv
import TauCeti.Geometry.Euclidean.Volume.Density

/-!
# Approximate tangent planes and tangential derivatives along a subspace

A `k`-dimensional subspace `S` of a finite-dimensional real inner product space `V` is its own
approximate tangent `k`-plane at each of its points, and no other subspace is
(`Submodule.isApproximateTangentPlane_iff`, `Submodule.approximateTangentPlane_eq`): `S` is the
image of the isometric inclusion `S → V`, so this is
`HasFDerivWithinAt.isApproximateTangentPlane_image_iff`. Consequently a map `g` with derivative
`L` within `S` at `x ∈ S` has tangential derivative `L ∘L π_S` along `S` at `x`, the extension by
zero of the restriction of `L` to `S` (`Submodule.hasTangentialFDerivAt_of_hasFDerivWithinAt`),
and its tangential Jacobian along `S` is the norm determinant of that restriction
(`Submodule.tangentialJacobian_eq_of_hasFDerivWithinAt`). For a continuous linear map `f`, the
tangential derivative is the restriction of `f` itself, and the tangential area formula is the
linear area formula `LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` for that
restriction (`ContinuousLinearMap.euclideanHausdorffMeasure_image_eq_tangentialJacobian_mul`).

## Main results

* `Submodule.isApproximateTangentPlane_iff`, `Submodule.approximateTangentPlane_eq`,
  `Submodule.approximateTangentProjection_eq`: the approximate tangent plane of `S` at `x ∈ S`.
* `Submodule.hasTangentialFDerivAt_of_hasFDerivWithinAt`,
  `Submodule.tangentialFDeriv_eq_of_hasFDerivWithinAt`,
  `Submodule.tangentialJacobian_eq_of_hasFDerivWithinAt`: the tangential derivative and Jacobian
  along `S` of a map differentiable within `S`.
* `ContinuousLinearMap.hasTangentialFDerivAt_submodule`,
  `ContinuousLinearMap.tangentialFDeriv_submodule`,
  `ContinuousLinearMap.tangentialJacobian_submodule`: the case of a continuous linear map.
* `ContinuousLinearMap.euclideanHausdorffMeasure_image_eq_tangentialJacobian_mul`: the tangential
  area formula for a continuous linear map along `S`, in its linear form; no injectivity is needed.

## References

* L. Simon, *Lectures on Geometric Measure Theory*, §12.
-/

public section

open Filter Function Metric MeasureTheory Measure Module Set
open scoped ENNReal NNReal Topology

namespace Submodule

open TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (S : Submodule ℝ V) {x : V}

/-- A subspace `S` is, at each of its points, an approximate tangent plane of itself of dimension
`dim S`, and the only one. -/
theorem isApproximateTangentPlane_iff (hx : x ∈ S) {Q : Submodule ℝ V} :
    IsApproximateTangentPlane (finrank ℝ S) (S : Set V) x Q ↔ Q = S := by
  have hf : HasFDerivWithinAt (S.subtypeL : S → V) S.subtypeL univ ⟨x, hx⟩ :=
    S.subtypeL.hasFDerivAt.hasFDerivWithinAt
  have h := hf.isApproximateTangentPlane_image_iff (Q := Q) S.injective_subtype
    (isometry_subtypeVal.antilipschitzWith.domRestrict univ) (mem_univ _)
    (tendsto_volume_inter_closedBall_div_of_mem_nhds univ_mem)
  rw [image_univ, coe_subtypeL, coe_subtype, Subtype.range_coe] at h
  convert h using 2
  ext v
  simp

/-- The approximate tangent plane of a subspace at each of its points is the subspace. -/
theorem approximateTangentPlane_eq (hx : x ∈ S) :
    approximateTangentPlane (finrank ℝ S) (S : Set V) x = S :=
  ((S.isApproximateTangentPlane_iff hx).mpr rfl).approximateTangentPlane_eq fun _ hQ ↦
    (S.isApproximateTangentPlane_iff hx).mp hQ

/-- The approximate tangent projection of a subspace at each of its points is the orthogonal
projection onto it. -/
theorem approximateTangentProjection_eq (hx : x ∈ S) :
    approximateTangentProjection (finrank ℝ S) (S : Set V) x = S.starProjection := by
  rw [TauCeti.approximateTangentProjection_eq, S.approximateTangentPlane_eq hx]

/-- A subspace has a unique approximate tangent plane of its dimension at each of its points. -/
theorem existsUnique_isApproximateTangentPlane (hx : x ∈ S) :
    ∃! Q : Submodule ℝ V, IsApproximateTangentPlane (finrank ℝ S) (S : Set V) x Q :=
  ⟨S, (S.isApproximateTangentPlane_iff hx).mpr rfl, fun _ hQ ↦
    (S.isApproximateTangentPlane_iff hx).mp hQ⟩

section Deriv

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] {g : V → W} {L : V →L[ℝ] W}

/-- Along a subspace `S`, a map `g` with derivative `L` within `S` at `x ∈ S` has tangential
derivative `L ∘L π_S` at `x`: the restriction of `L` to `S`, extended by zero on `Sᗮ`. -/
theorem hasTangentialFDerivAt_of_hasFDerivWithinAt (hx : x ∈ S)
    (hg : HasFDerivWithinAt g L (S : Set V) x) :
    HasTangentialFDerivAt (finrank ℝ S) (S : Set V) g (L ∘L S.starProjection) x := by
  simpa only [S.approximateTangentProjection_eq hx] using
    HasTangentialFDerivAt.of_hasFDerivWithinAt (S.existsUnique_isApproximateTangentPlane hx) hg

/-- The tangential derivative along a subspace `S` of a map with derivative `L` within `S`. -/
theorem tangentialFDeriv_eq_of_hasFDerivWithinAt (hx : x ∈ S)
    (hg : HasFDerivWithinAt g L (S : Set V) x) :
    tangentialFDeriv (finrank ℝ S) (S : Set V) g x = L ∘L S.starProjection :=
  (S.hasTangentialFDerivAt_of_hasFDerivWithinAt hx hg).tangentialFDeriv_eq

end Deriv

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] {g : V → W} {L : V →L[ℝ] W}

/-- The tangential Jacobian along a subspace `S` of a map with derivative `L` within `S` is the
norm determinant of the restriction of `L` to `S`. -/
theorem tangentialJacobian_eq_of_hasFDerivWithinAt (hx : x ∈ S)
    (hg : HasFDerivWithinAt g L (S : Set V) x) :
    tangentialJacobian (finrank ℝ S) (S : Set V) g x = (L.toLinearMap.domRestrict S).normDet := by
  rw [(S.hasTangentialFDerivAt_of_hasFDerivWithinAt hx hg).tangentialJacobian_eq,
    S.approximateTangentPlane_eq hx]
  congr 1
  ext v
  simp [Submodule.starProjection_eq_self_iff.mpr v.property]

end Submodule

namespace ContinuousLinearMap

open TauCeti

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V] (S : Submodule ℝ V) {x : V}

section NormedSpace

variable [NormedAddCommGroup W] [NormedSpace ℝ W] (f : V →L[ℝ] W)

/-- Along a subspace `S`, a continuous linear map `f` has tangential derivative `f ∘L π_S` at each
point of `S`: the restriction of `f` to `S`, extended by zero on `Sᗮ`. -/
theorem hasTangentialFDerivAt_submodule (hx : x ∈ S) :
    HasTangentialFDerivAt (finrank ℝ S) (S : Set V) f (f ∘L S.starProjection) x :=
  S.hasTangentialFDerivAt_of_hasFDerivWithinAt hx f.hasFDerivAt.hasFDerivWithinAt

/-- The tangential derivative of a continuous linear map along a subspace. -/
theorem tangentialFDeriv_submodule (hx : x ∈ S) :
    tangentialFDeriv (finrank ℝ S) (S : Set V) f x = f ∘L S.starProjection :=
  S.tangentialFDeriv_eq_of_hasFDerivWithinAt hx f.hasFDerivAt.hasFDerivWithinAt

end NormedSpace

variable [NormedAddCommGroup W] [InnerProductSpace ℝ W] (f : V →L[ℝ] W)

/-- The tangential Jacobian of a continuous linear map along a subspace `S` is the norm
determinant of its restriction to `S`. -/
theorem tangentialJacobian_submodule (hx : x ∈ S) :
    tangentialJacobian (finrank ℝ S) (S : Set V) f x = (f.toLinearMap.domRestrict S).normDet :=
  S.tangentialJacobian_eq_of_hasFDerivWithinAt hx f.hasFDerivAt.hasFDerivWithinAt

/-- **The tangential area formula along a subspace, in linear form.** For a continuous linear map
`f` and `A ⊆ S`, the `dim S`-dimensional measure of `f '' A` is the tangential Jacobian of `f` along
`S` times the measure of `A`, which is the linear area formula
`LinearMap.euclideanHausdorffMeasure_image_eq_normDet_mul_volume` for the restriction of `f`
to `S`. -/
theorem euclideanHausdorffMeasure_image_eq_tangentialJacobian_mul [MeasurableSpace W]
    [BorelSpace W] (hx : x ∈ S) {A : Set V} (hA : A ⊆ S) :
    μHE[finrank ℝ S] (f '' A) =
      ENNReal.ofReal (tangentialJacobian (finrank ℝ S) (S : Set V) f x) *
        μHE[finrank ℝ S] A := by
  -- `A` is the image of its preimage in `S` under the isometric inclusion
  obtain ⟨B, rfl⟩ : ∃ B : Set S, (↑) '' B = A :=
    ⟨(↑) ⁻¹' A, image_preimage_eq_of_subset (by simpa using hA)⟩
  have hiso : Isometry ((↑) : S → V) := isometry_subtypeVal
  have h :=
    (f.toLinearMap.domRestrict S).euclideanHausdorffMeasure_image_eq_normDet_mul_volume B
  rw [f.tangentialJacobian_submodule S hx, hiso.euclideanHausdorffMeasure_image,
    InnerProductSpace.euclideanHausdorffMeasure_eq_volume, ← h]
  congr 1
  ext
  simp

end ContinuousLinearMap
