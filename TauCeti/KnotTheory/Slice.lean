/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.ClosedBall
public import TauCeti.KnotTheory.SmoothCircle
import Mathlib.Analysis.Complex.Isometry

/-!
# Smoothly slice knots

A knot `K ⊆ S³` is **smoothly slice** if it bounds a smoothly embedded disc in the four-ball
`D⁴`: a disc `D ⊆ D⁴` meeting the boundary sphere exactly along its own boundary circle, with
`∂D = K`. This file states sliceness on the geometric presentation of a knot, a smooth circle
embedding `K : S¹ → Sⁿ` (`TauCeti.SmoothCircleEmbedding`), for the unit sphere of an
`(n + 1)`-dimensional real inner product space `E`, so that `S³ ⊆ ℝ⁴` is the case `n = 3`.

A **smooth slice disc** for `K` (`TauCeti.IsSmoothSliceDisc K Φ`) is a map `Φ` from the closed unit
disc of `ℂ` to the closed unit ball of `E` which

* is a smooth embedding in the sense of manifolds with boundary (`Manifold.IsSmoothEmbedding` for
  the half-space models of `TauCeti.instChartedSpaceClosedBall`);
* is properly embedded: the preimage of the manifold boundary of `Dⁿ⁺¹`, the unit sphere, is the
  manifold boundary of `D²`, the unit circle; and
* restricts to `K` on the boundary circle, through the inclusion
  `Set.inclusion Metric.sphere_subset_closedBall` of the circle into the disc.

No separate neatness condition is needed. Mathlib's `Manifold.IsImmersion` is a chart normal form,
not an injectivity condition on the differential: around every point there are half-space charts of
the disc and of the ball in which `Φ` is the restriction of a linear map `u ↦ equiv (u, 0)` on the
whole chart target (`Manifold.ImmersionAtProp`). The boundary coordinate of the ball therefore pulls
back to a linear functional on the model half-plane, nonnegative on the half-plane and, by
`preimage_boundary`, vanishing exactly on its boundary line; so it is a positive multiple of the
boundary coordinate of the disc. Hence a smooth slice disc is neat: it meets the boundary sphere
transversally, as in the usual notion of a properly embedded smooth slice disc.

`K` is smoothly slice (`TauCeti.IsSmoothlySlice K`) when such a disc exists. Topological
sliceness, where the disc is only required to be locally flat, is deliberately a separate notion:
the gap between the two is the content of Freedman's theorem that Alexander-polynomial-one knots
are topologically slice, and of the existence of topologically but not smoothly slice knots.

The predicate is exercised on the great circles: a great circle
`TauCeti.SmoothCircleEmbedding.greatCircle ι` bounds the flat disc `ι D²`, the restriction of the
linear isometry `ι` to the closed unit balls, which is a smooth embedding of manifolds with boundary
(`LinearIsometry.isSmoothEmbedding_unitClosedBallMap`). In particular the unknot is smoothly
slice.

## Main definitions

* `TauCeti.IsSmoothSliceDisc K Φ`: `Φ` is a smooth slice disc for `K`.
* `TauCeti.IsSmoothlySlice K`: `K` bounds a smooth slice disc.

Sliceness is invariant under the two canonical reparametrizations of the circle, rotation and
reversal: each reparametrizes the slice disc by the corresponding linear isometry of the plane,
which is a diffeomorphism of the disc (`LinearIsometryEquiv.unitClosedBallDiffeomorph`). In
particular sliceness does not depend on the orientation of the knot. Invariance under arbitrary
diffeomorphisms of the circle is not proved here.

## Main results

* `TauCeti.IsSmoothSliceDisc.norm_eq_one_iff`: a slice disc meets the unit sphere exactly along
  the unit circle.
* `TauCeti.IsSmoothSliceDisc.comp_unitClosedBallMap`: reparametrizing a slice disc by a linear
  isometry of the plane gives a slice disc for the correspondingly reparametrized knot.
* `TauCeti.isSmoothlySlice_rotate_iff`, `TauCeti.isSmoothlySlice_reverse_iff`: sliceness is
  invariant under rotation and reversal of the parametrization.
* `TauCeti.isSmoothSliceDisc_greatCircle_unitClosedBallMap`: the flat disc `ι D²` is a slice disc
  for the great circle `ι S¹`.
* `TauCeti.isSmoothlySlice_greatCircle`, `TauCeti.isSmoothlySlice_unknot`: great circles, and in
  particular the unknot, are smoothly slice.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 8, for
  slice knots.
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2, for smooth versus topological sliceness.
-/

public section

noncomputable section

open scoped EuclideanSpace

namespace TauCeti

open Manifold Metric Module Set
open scoped Manifold ContDiff

attribute [local instance] Complex.finrank_real_complex_fact

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ}
  [Fact (finrank ℝ E = n + 1)]

/-- A **smooth slice disc** for a smooth circle embedding `K : S¹ → Sⁿ` in the unit sphere of `E`:
a smooth embedding `Φ` of the closed unit disc of `ℂ` into the closed unit ball of `E`, in the sense
of manifolds with boundary, which is properly embedded (the preimage of the boundary sphere is the
boundary circle) and restricts to `K` on the boundary circle. -/
structure IsSmoothSliceDisc (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1))
    (Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1) : Prop where
  /-- The disc is a smooth embedding of manifolds with boundary. -/
  isSmoothEmbedding : IsSmoothEmbedding (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ Φ
  /-- The disc is properly embedded: it meets the boundary sphere exactly along its boundary
  circle. -/
  preimage_boundary : Φ ⁻¹' (𝓡∂ (n + 1)).boundary (closedBall (0 : E) 1) =
    (𝓡∂ 2).boundary (closedBall (0 : ℂ) 1)
  /-- The disc restricts to `K` on its boundary circle. -/
  apply_inclusion (z : Circle) : (Φ (Set.inclusion sphere_subset_closedBall z) : E) = K z

/-- A smooth circle embedding `K : S¹ → Sⁿ` is **smoothly slice** if it bounds a smooth slice disc
in the closed unit ball `Dⁿ⁺¹`. -/
def IsSmoothlySlice (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)) : Prop :=
  ∃ Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1, IsSmoothSliceDisc K Φ

variable {K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}

namespace IsSmoothSliceDisc

variable {Φ : closedBall (0 : ℂ) 1 → closedBall (0 : E) 1}

/-- A knot with a smooth slice disc is smoothly slice. -/
theorem isSmoothlySlice (h : IsSmoothSliceDisc K Φ) : IsSmoothlySlice K :=
  ⟨Φ, h⟩

/-- A smooth slice disc is a smooth map of manifolds with boundary. -/
theorem contMDiff (h : IsSmoothSliceDisc K Φ) : ContMDiff (𝓡∂ 2) (𝓡∂ (n + 1)) ∞ Φ :=
  h.isSmoothEmbedding.contMDiff

/-- A smooth slice disc is a topological embedding. -/
theorem isEmbedding (h : IsSmoothSliceDisc K Φ) : Topology.IsEmbedding Φ :=
  h.isSmoothEmbedding.isEmbedding

/-- A smooth slice disc is injective. -/
theorem injective (h : IsSmoothSliceDisc K Φ) : Function.Injective Φ :=
  h.isEmbedding.injective

/-- A slice disc meets the unit sphere exactly along the unit circle: a point of the disc is sent
to a unit vector exactly when it is a unit vector. -/
theorem norm_eq_one_iff (h : IsSmoothSliceDisc K Φ) (x : closedBall (0 : ℂ) 1) :
    ‖(Φ x : E)‖ = 1 ↔ ‖(x : ℂ)‖ = 1 := by
  have hx := congrArg (x ∈ ·) h.preimage_boundary
  simpa [boundary_closedBall] using hx

/-- The image of the boundary circle under a slice disc for `K` is the image of `K`. -/
theorem image_range_inclusion (h : IsSmoothSliceDisc K Φ) :
    (Subtype.val ∘ Φ) '' range (fun z : Circle ↦ Set.inclusion sphere_subset_closedBall z) =
      Subtype.val '' range K := by
  ext y
  simp only [mem_image, mem_range, exists_exists_eq_and, Function.comp_apply, h.apply_inclusion]

/-- Reparametrizing a slice disc for `K` by a linear isometry `e` of the plane gives a slice disc
for the reparametrization of `K` along the circle: if `σ : Circle → Circle` is `e` on the circle
and `K' = K ∘ σ`, then `Φ ∘ e` is a slice disc for `K'`. -/
theorem comp_unitClosedBallMap (h : IsSmoothSliceDisc K Φ) (e : ℂ ≃ₗᵢ[ℝ] ℂ) {σ : Circle → Circle}
    (hσ : ∀ z, (σ z : ℂ) = e z) {K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : E) 1)}
    (hK' : ∀ z, K' z = K (σ z)) :
    IsSmoothSliceDisc K' (Φ ∘ e.toLinearIsometry.unitClosedBallMap) where
  isSmoothEmbedding := by
    have := isSmoothEmbedding_comp_diffeomorph (e.unitClosedBallDiffeomorph (k := ∞))
      h.isSmoothEmbedding
    rwa [LinearIsometryEquiv.coe_unitClosedBallDiffeomorph] at this
  preimage_boundary := by
    rw [preimage_comp, h.preimage_boundary]
    ext x
    simp [boundary_closedBall]
  apply_inclusion z := by
    have hz : e.toLinearIsometry.unitClosedBallMap (Set.inclusion sphere_subset_closedBall z) =
        Set.inclusion sphere_subset_closedBall (σ z) :=
      Subtype.ext (by simp [hσ])
    rw [Function.comp_apply, hz, h.apply_inclusion, hK']

end IsSmoothSliceDisc

/-! ### Invariance under rotation and reversal -/

/-- Rotating the parametrization of a smoothly slice knot gives a smoothly slice knot. -/
theorem IsSmoothlySlice.rotate (h : IsSmoothlySlice K) (a : Circle) :
    IsSmoothlySlice (K.rotate a) := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨_, hΦ.comp_unitClosedBallMap (rotation a) (σ := (a * ·))
    (fun z ↦ by simp [rotation_apply]) fun z ↦ by simp⟩

/-- Smooth sliceness does not depend on the rotation of the parametrization. -/
@[simp]
theorem isSmoothlySlice_rotate_iff (a : Circle) :
    IsSmoothlySlice (K.rotate a) ↔ IsSmoothlySlice K :=
  ⟨fun h ↦ by simpa using h.rotate a⁻¹, fun h ↦ h.rotate a⟩

/-- Reversing the orientation of a smoothly slice knot gives a smoothly slice knot. -/
theorem IsSmoothlySlice.reverse (h : IsSmoothlySlice K) : IsSmoothlySlice K.reverse := by
  obtain ⟨Φ, hΦ⟩ := h
  exact ⟨_, hΦ.comp_unitClosedBallMap Complex.conjLIE (σ := (·⁻¹))
    (fun z ↦ (Circle.coe_inv_eq_conj z).trans (Complex.conjLIE_apply z).symm) fun z ↦ by simp⟩

/-- Smooth sliceness does not depend on the orientation of the knot. -/
@[simp]
theorem isSmoothlySlice_reverse_iff : IsSmoothlySlice K.reverse ↔ IsSmoothlySlice K :=
  ⟨fun h ↦ by simpa using h.reverse, fun h ↦ h.reverse⟩

/-- The flat disc `ι D²` is a smooth slice disc for the great circle `ι S¹`. -/
theorem isSmoothSliceDisc_greatCircle_unitClosedBallMap (ι : ℂ →ₗᵢ[ℝ] E) :
    IsSmoothSliceDisc (SmoothCircleEmbedding.greatCircle (n := n) ι) ι.unitClosedBallMap where
  isSmoothEmbedding := ι.isSmoothEmbedding_unitClosedBallMap
  preimage_boundary := by
    ext x
    simp [boundary_closedBall]
  apply_inclusion z := by simp

/-- **Great circles are smoothly slice**: they bound flat discs. -/
theorem isSmoothlySlice_greatCircle (ι : ℂ →ₗᵢ[ℝ] E) :
    IsSmoothlySlice (SmoothCircleEmbedding.greatCircle (n := n) ι) :=
  (isSmoothSliceDisc_greatCircle_unitClosedBallMap ι).isSmoothlySlice

/-- **The unknot is smoothly slice**: it bounds the flat disc of the first coordinate plane. -/
theorem isSmoothlySlice_unknot : IsSmoothlySlice unknot :=
  IsSmoothSliceDisc.isSmoothlySlice (Φ := complexToEuclideanFour.unitClosedBallMap)
    { isSmoothSliceDisc_greatCircle_unitClosedBallMap complexToEuclideanFour with
      apply_inclusion := fun z ↦ by simp }

end TauCeti
