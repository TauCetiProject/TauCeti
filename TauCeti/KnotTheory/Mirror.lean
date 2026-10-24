/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeomorphism.Sphere
public import TauCeti.Geometry.Manifold.SmoothEmbedding.Concordance
public import TauCeti.KnotTheory.Slice.TopologicalGenus

/-!
# The mirror image of a knot

The **mirror image** of a knot `K ⊆ S³` is its image under a reflection of the ambient sphere. Here
the knot is a smooth circle embedding `K : S¹ → Sⁿ` into the unit sphere of `ℝⁿ⁺¹`
(`TauCeti.SmoothCircleEmbedding`), with `S³ ⊆ ℝ⁴` the case `n = 3`, and its mirror image
`TauCeti.SmoothCircleEmbedding.mirror K` is `ρ ∘ K` for the reflection `ρ` of `ℝⁿ⁺¹` in the
coordinate hyperplane `xₙ = 0`, which negates the last coordinate. The reflection is Mathlib's
`Submodule.reflection` in the orthogonal complement of the last basis vector; it is a linear
isometry of determinant `-1` (`Submodule.det_reflection`), so it reverses the orientation of the
ambient sphere, and it restricts to a diffeomorphism of the sphere
(`LinearIsometryEquiv.unitSphereDiffeomorph`). Mirroring is the ambient transport of `K` along that
diffeomorphism, so it keeps the orientation of the knot given by its parametrization.

The mirror image is the inverse operation of the knot concordance group, together with reversal:
the inverse of the class of `K` is the class of the reverse of its mirror image. This file records
the elementary properties of mirroring that this rests on:

* mirroring is an involution which commutes with rotation and reversal of the parametrization;
* the unknot, the great circle of the first coordinate plane of `ℝ⁴`, is its own mirror image;
* smooth and topological sliceness, and the smooth and topological slice genera, are invariant
  under mirroring, since a slice disc or slice surface in the four-ball is reflected along with
  the knot (`TauCeti.isSmoothlySlice_congr_linearIsometryEquiv` and its companions);
* smooth concordance is preserved and reflected by mirroring, since the reflection is an ambient
  diffeomorphism.

Any two orientation-reversing linear isometries of `ℝⁿ⁺¹` differ by a rotation, which is isotopic to
the identity, so mathematically the choice of hyperplane only matters up to ambient isotopy; that
independence is not formalized here.

## Main definitions

* `TauCeti.SmoothCircleEmbedding.mirror`: the mirror image of a knot in the unit sphere of `ℝⁿ⁺¹`.

## Main results

* `TauCeti.SmoothCircleEmbedding.mirror_mirror`: mirroring is an involution.
* `TauCeti.SmoothCircleEmbedding.reverse_mirror`, `TauCeti.SmoothCircleEmbedding.rotate_mirror`:
  mirroring commutes with reversal and rotation.
* `TauCeti.SmoothCircleEmbedding.mirror_unknot`: the unknot is its own mirror image.
* `TauCeti.isSmoothlySlice_mirror_iff`, `TauCeti.isTopologicallySlice_mirror_iff`,
  `TauCeti.sliceGenus_mirror`, `TauCeti.topologicalSliceGenus_mirror`: sliceness and the slice
  genera are invariant under mirroring.
* `TauCeti.SmoothEmbedding.concordant_mirror_iff`: mirroring preserves and reflects smooth
  concordance.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1 (the
  mirror image and the reverse of a knot) and Chapter 8 (the inverse in the concordance group).
* C. Livingston, *A survey of classical knot concordance*, in *Handbook of Knot Theory* (2005),
  Section 2 (the concordance group).
-/

public section

noncomputable section

open Metric Module Set
open scoped Manifold ContDiff

namespace TauCeti

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

namespace SmoothCircleEmbedding

variable {n : ℕ} (K : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1))

/-- The **mirror image** of a knot `K` in the unit sphere of `ℝⁿ⁺¹`: its image under the reflection
of `ℝⁿ⁺¹` in the coordinate hyperplane `xₙ = 0`, an orientation-reversing isometry of the sphere.
The parametrization, and so the orientation of the knot, is carried along. -/
def mirror : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :=
  SmoothEmbedding.transDiffeomorph K
    ((ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection.unitSphereDiffeomorph ∞)

/-- The mirror image is the ambient transport of the knot along the reflection of the sphere in
the hyperplane `xₙ = 0`. -/
theorem mirror_def :
    K.mirror = SmoothEmbedding.transDiffeomorph K
      ((ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection.unitSphereDiffeomorph ∞) :=
  (rfl)

/-- The mirror image sends a point `z` of the circle to the reflection of `K z` in the hyperplane
`xₙ = 0`. -/
@[simp]
theorem coe_mirror_apply (z : Circle) :
    (K.mirror z : EuclideanSpace ℝ (Fin (n + 1))) =
      (ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection (K z) := by
  rw [mirror_def, SmoothEmbedding.transDiffeomorph_apply,
    LinearIsometryEquiv.coe_unitSphereDiffeomorph_apply]

/-- Mirroring twice gives back the knot. -/
@[simp]
theorem mirror_mirror : K.mirror.mirror = K :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by
    rw [coe_mirror_apply, coe_mirror_apply, Submodule.reflection_reflection]

/-- Mirroring is an involution. -/
theorem mirror_involutive :
    Function.Involutive
      (mirror : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) →
        SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)) :=
  mirror_mirror

/-- Mirror images of knots agree exactly when the knots do. -/
@[simp]
theorem mirror_inj
    {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)} :
    K.mirror = K'.mirror ↔ K = K' :=
  mirror_involutive.injective.eq_iff

/-- Reversing the mirror image is mirroring the reverse: the reflection acts on the ambient sphere
and the reversal on the circle. -/
@[simp]
theorem reverse_mirror : K.mirror.reverse = K.reverse.mirror :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by simp

/-- Rotating the parametrization of the mirror image is mirroring the rotated knot. -/
@[simp]
theorem rotate_mirror (a : Circle) : K.mirror.rotate a = (K.rotate a).mirror :=
  SmoothEmbedding.ext fun z ↦ Subtype.ext <| by simp

/-- The image of the mirror image is the reflection of the image of the knot. -/
theorem range_mirror :
    range K.mirror =
      (ℝ ∙ EuclideanSpace.single (Fin.last n) (1 : ℝ))ᗮ.reflection.unitSphereDiffeomorph
        (n := n) (k := n) ∞ '' range K :=
  SmoothEmbedding.range_transDiffeomorph _ _

end SmoothCircleEmbedding

/-- **The unknot is its own mirror image**: it lies in the hyperplane `x₃ = 0` of `ℝ⁴`, which the
reflection fixes pointwise. -/
@[simp]
theorem SmoothCircleEmbedding.mirror_unknot : unknot.mirror = unknot := by
  refine SmoothEmbedding.ext fun z ↦ Subtype.ext ?_
  rw [coe_mirror_apply]
  refine Submodule.reflection_mem_subspace_eq_self ?_
  rw [Submodule.mem_orthogonal_singleton_iff_inner_right]
  simp [EuclideanSpace.inner_single_left]

variable {n : ℕ}
  {K K' : SmoothCircleEmbedding (𝓡 n) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)}

/-! ### Sliceness and the slice genus -/

/-- A knot is smoothly slice exactly when its mirror image is: the reflection carries slice discs
in the four-ball to slice discs. -/
@[simp]
theorem isSmoothlySlice_mirror_iff : IsSmoothlySlice K.mirror ↔ IsSmoothlySlice K :=
  isSmoothlySlice_congr_linearIsometryEquiv _ K.coe_mirror_apply

/-- A knot is topologically slice exactly when its mirror image is. -/
@[simp]
theorem isTopologicallySlice_mirror_iff : IsTopologicallySlice K.mirror ↔ IsTopologicallySlice K :=
  isTopologicallySlice_congr_linearIsometryEquiv _ K.coe_mirror_apply

/-- A knot and its mirror image have the same slice genus. -/
@[simp]
theorem sliceGenus_mirror : sliceGenus K.mirror = sliceGenus K :=
  sliceGenus_congr_linearIsometryEquiv _ K.coe_mirror_apply

/-- A knot and its mirror image have the same topological slice genus. -/
@[simp]
theorem topologicalSliceGenus_mirror : topologicalSliceGenus K.mirror = topologicalSliceGenus K :=
  topologicalSliceGenus_congr_linearIsometryEquiv _ K.coe_mirror_apply

/-! ### Concordance -/

/-- Mirror images of smoothly concordant knots are smoothly concordant: the reflection is an
ambient diffeomorphism. -/
theorem SmoothEmbedding.Concordant.mirror (h : SmoothEmbedding.Concordant K K') :
    SmoothEmbedding.Concordant K.mirror K'.mirror :=
  h.transDiffeomorph _

/-- Two knots are smoothly concordant exactly when their mirror images are. -/
@[simp]
theorem SmoothEmbedding.concordant_mirror_iff :
    SmoothEmbedding.Concordant K.mirror K'.mirror ↔ SmoothEmbedding.Concordant K K' :=
  ⟨fun h ↦ by simpa using h.mirror, fun h ↦ h.mirror⟩

end TauCeti
