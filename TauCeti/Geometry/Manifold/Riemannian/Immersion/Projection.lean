/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Adjoint
import TauCeti.Analysis.InnerProductSpace.RangeProjection
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Tangent and normal projections along isometric immersions

For an isometric immersion `f : M → N`, the tangent space of the immersed source at `x`
is the range of `mfderiv I J f x` in `TangentSpace J (f x)`. Its orthogonal complement is
its normal space. Both orthogonal projections preserve the regularity of tangent fields
along `f`. In particular, projecting an ambient covariant derivative to its normal part
is a regular operation, as required in the construction of the second fundamental form
and the normal connection.

The projections use the native range, orthogonal complement and `Submodule.starProjection`.
They are taken separately over each source point, so the results apply to immersions with
self-intersections, not only to embeddings. The tangential projection is `df ∘ df†`, with
the adjoint formed using the two given metrics. No auxiliary metric or normal frame is
chosen. The statements allow models with corners and finite differentiability: `C^(n+1)`
regularity of the map and `C^n` regularity of both metrics suffice.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 8
  (tangential and normal projections in the Gauss formula).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle I n E (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {W : (x : M) → TangentSpace J (f x)} {x : M}

/-- Tangential projection along an isometric immersion preserves `C^n` regularity at a point.
It suffices that the differential be isometric near that point. -/
theorem ContMDiffAt.starProjection_range_mfderiv_apply
    (hf : ContMDiffAt I J (n + 1) f x)
    (hiso : ∀ᶠ y in 𝓝 x, Isometry (mfderiv I J f y))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) x := by
  -- Apply the tangent map to the adjoint field: this computes `df ∘ df†` along `f`.
  have h := (hf.contMDiffAt_tangentMap le_rfl).comp x (hf.mfderiv_adjoint_apply hW)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards [hiso] with y hy
  have heq := DFunLike.congr_fun
    (ContinuousLinearMap.comp_adjoint_eq_starProjection_range hy) (W y)
  exact congrArg (TotalSpace.mk' F (f y)) heq.symm

/-- Normal projection along an isometric immersion preserves `C^n` regularity at a point.
The normal space is the orthogonal complement of the differential's range in the ambient
metric, including when the immersion has self-intersections. -/
theorem ContMDiffAt.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiffAt I J (n + 1) f x)
    (hiso : ∀ᶠ y in 𝓝 x, Isometry (mfderiv I J f y))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) x := by
  refine (hW.sub_sectionAlong (hf.starProjection_range_mfderiv_apply hiso hW)).congr_of_eventuallyEq
    (Eventually.of_forall fun y ↦ ?_)
  simp [Submodule.starProjection_orthogonal]

/-- Tangential projection of a `C^n` field along a `C^(n+1)` isometric immersion is `C^n`.
Both metrics are allowed to vary with the point. -/
theorem ContMDiff.starProjection_range_mfderiv_apply
    (hf : ContMDiff I J (n + 1) f) (hiso : ∀ y, Isometry (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_range_mfderiv_apply (Eventually.of_forall hiso) (hW x)

/-- Normal projection of a `C^n` field along a `C^(n+1)` isometric immersion is `C^n`.
The projection is onto the normal space over the source point, not a space attached to the
possibly self-intersecting image. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiff I J (n + 1) f) (hiso : ∀ y, Isometry (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_orthogonal_range_mfderiv_apply
    (Eventually.of_forall hiso) (hW x)

variable [IsManifold J (n + 1) N]

/-- The tangential projections of an isometric immersion form a `C^n` endomorphism field
along the immersion. Equivalently, they are a regular section of the endomorphism bundle of
`f *ᵖ TangentSpace J`, via `Bundle.Pullback.contMDiff_hom_section_iff`. -/
theorem ContMDiff.starProjection_range_mfderiv
    (hf : ContMDiff I J (n + 1) f) (hiso : ∀ y, Isometry (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).range.starProjection) := by
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := n)
  intro a
  let e := trivializationAt F (TangentSpace J) (f a)
  let u := f ⁻¹' e.baseSet
  have hu : IsOpen u := e.open_baseSet.preimage hf.continuous
  have ha : a ∈ u := FiberBundle.mem_baseSet_trivializationAt F (TangentSpace J) (f a)
  have hs := TauCeti.Manifold.contMDiffOn_hom_of_localFrame
    (I := J) (J := I) (e := e) (e' := e) (Module.finBasis ℝ F)
    (hf.of_le le_self_add).contMDiffOn (u := u) (fun _ hy ↦ ⟨hy, hy⟩)
    (A := fun y ↦ (mfderiv I J f y).range.starProjection) (by
      intro j y hy
      have hframe := (e.contMDiffOn_localFrame_baseSet (I := J) n
        (Module.finBasis ℝ F) j).contMDiffAt (e.open_baseSet.mem_nhds hy)
      exact ((hf y).starProjection_range_mfderiv_apply (Eventually.of_forall hiso)
        (hframe.comp y ((hf.of_le le_self_add) y))).contMDiffWithinAt)
  exact hs.contMDiffAt (hu.mem_nhds ha)

/-- The normal projections of an isometric immersion form a `C^n` endomorphism field along
it, for the ambient metric. Thus projection onto the normal spaces is regular without
choosing a local normal frame. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv
    (hf : ContMDiff I J (n + 1) f) (hiso : ∀ y, Isometry (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).rangeᗮ.starProjection) := by
  let := TangentBundle.contMDiffVectorBundle (I := J) (M := N) (n := n)
  have hid : ContMDiff J (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun z : N ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z : N ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        z (ContinuousLinearMap.id ℝ (TangentSpace J z))) :=
    (TauCeti.contMDiff_hom_bundle_iff _).mpr contMDiff_id
  refine ((hid.comp (hf.of_le le_self_add)).sub_sectionAlong
    (hf.starProjection_range_mfderiv hiso)).congr fun y ↦ ?_
  simp [Submodule.starProjection_orthogonal]
