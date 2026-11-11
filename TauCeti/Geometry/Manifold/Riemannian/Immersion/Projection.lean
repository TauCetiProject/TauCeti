/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
public import Mathlib.Analysis.InnerProductSpace.Projection.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import TauCeti.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.Geometry.Manifold.VectorBundle.Translate
import TauCeti.Geometry.Manifold.VectorBundle.Hom

/-!
# Tangent and normal projections along immersions

For an immersion `f : M → N`, the tangent space of the immersed source at `x`
is the range of `mfderiv I J f x` in `TangentSpace J (f x)`. Its orthogonal complement is
its normal space. Both orthogonal projections preserve the regularity of tangent fields
along `f`. In particular, projecting an ambient covariant derivative to its normal part
is a regular operation, as required in the construction of the second fundamental form
and the normal connection.

The projections use the native range, orthogonal complement and `Submodule.starProjection`.
They are taken separately over each source point, so the results apply to immersions with
self-intersections, not only to embeddings. The proof orthogonalizes the image of a local
source frame. No source metric is required. The statements allow models with corners and
finite differentiability: `C^(n+1)` regularity of the map and `C^n` regularity of the ambient
metric suffice.

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
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)]
  [IsManifold I 1 M] [IsManifold J 1 N]
  {n : ℕ∞ω} [IsManifold I (n + 1) M]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {W : (x : M) → TangentSpace J (f x)} {x : M}

/-- Tangential projection preserves `C^n` regularity at a point where the differential is
injective. Only the ambient manifold needs a metric. -/
theorem ContMDiffAt.starProjection_range_mfderiv_apply
    (hf : ContMDiffAt I J (n + 1) f x)
    (hinj : Function.Injective (mfderiv I J f x))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) x := by
  classical
  -- Push a source frame forward, apply Gram–Schmidt, then sum the projections onto its lines.
  -- At arbitrary n this is a lemma, not an instance; it uses IsManifold I (n + 1) M.
  let := TangentBundle.contMDiffVectorBundle (I := I) (M := M) (n := n)
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  let v (i : Fin (Module.finrank ℝ E)) (y : M) :=
    mfderiv I J f y (e.localFrame b i y)
  have hv (i) : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (v i y)) x := by
    have hs := (e.contMDiffOn_localFrame_baseSet (I := I) n b i).contMDiffAt
      (e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x))
    exact hf.mfderiv_apply_sectionAlong hs
  have hli : LinearIndependent ℝ (fun i ↦ v i x) :=
    (e.isLocalFrameOn_localFrame_baseSet I n b).linearIndependent
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x) |>.map' _
        (LinearMap.ker_eq_bot.mpr hinj)
  let g (i : Fin (Module.finrank ℝ E)) (y : M) :=
    InnerProductSpace.gramSchmidtNormed ℝ (fun i ↦ v i y) i
  -- Pin the metric structure through its regularity witness: TangentSpace is reducible
  -- to the model, but its metric norm need not be the model norm.
  have hmetric : IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y) :=
    inferInstance
  have hg (i) : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (g i y)) x :=
    ContMDiffAt.gramSchmidtNormed_bundle (hmetric := hmetric) (b := f) (v := v) hv hli i
  have hc (i) := (hg i).inner_bundle (h := hmetric) hW
  have hs := ContMDiffAt.sum_sectionAlong Finset.univ _ (hf.of_le le_self_add)
    (fun i _ ↦ (hc i).smul_totalSpace (hg i))
  refine hs.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  apply congrArg (TotalSpace.mk' F (f y))
  have hspan : Submodule.span ℝ (Set.range (fun i ↦ v i y)) =
      (mfderiv I J f y).range :=
    e.span_range_localFrame_map b (mfderiv I J f y).toLinearMap hy
  rw [InnerProductSpace.starProjection_eq_sum_rankOne_gramSchmidtNormed (fun i ↦ v i y) hspan]
  simp [InnerProductSpace.rankOne_apply, g]

/-- Normal projection along an immersion preserves `C^n` regularity at a point.
The normal space is the orthogonal complement of the differential's range in the ambient
metric, including when the immersion has self-intersections. -/
theorem ContMDiffAt.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiffAt I J (n + 1) f x)
    (hinj : Function.Injective (mfderiv I J f x))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) x := by
  refine (hW.sub_sectionAlong (hf.starProjection_range_mfderiv_apply hinj hW)).congr_of_eventuallyEq
    (Eventually.of_forall fun y ↦ ?_)
  simp [Submodule.starProjection_orthogonal]

/-- Tangential projection of a `C^n` field along a `C^(n+1)` immersion is `C^n`.
The ambient metric is allowed to vary with the point. -/
theorem ContMDiff.starProjection_range_mfderiv_apply
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ y, Function.Injective (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_range_mfderiv_apply (hinj x) (hW x)

/-- Normal projection of a `C^n` field along a `C^(n+1)` immersion is `C^n`.
The projection is onto the normal space over the source point, not a space attached to the
possibly self-intersecting image. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ y, Function.Injective (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_orthogonal_range_mfderiv_apply (hinj x) (hW x)

variable [FiniteDimensional ℝ F] [IsManifold J (n + 1) N]

/-- The tangential projections of an immersion form a `C^n` endomorphism field
along the immersion. Equivalently, they are a regular section of the endomorphism bundle of
`f *ᵖ TangentSpace J`, via `Bundle.Pullback.contMDiff_hom_section_iff`. -/
theorem ContMDiff.starProjection_range_mfderiv
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).range.starProjection) := by
  -- At arbitrary n this is a lemma, not an instance; it uses IsManifold J (n + 1) N.
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
      exact ((hf y).starProjection_range_mfderiv_apply (hinj y)
        (hframe.comp y ((hf.of_le le_self_add) y))).contMDiffWithinAt)
  exact hs.contMDiffAt (hu.mem_nhds ha)

/-- The normal projections of an immersion form a `C^n` endomorphism field along
it, for the ambient metric. Thus projection onto the normal spaces is regular without
choosing a local normal frame. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv
    (hf : ContMDiff I J (n + 1) f) (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).rangeᗮ.starProjection) := by
  have hid := TauCeti.contMDiff_id_endomorphism
    (I := J) (M := N) (F₁ := F) (V := TangentSpace J) (n := n)
  refine ((hid.comp (hf.of_le le_self_add)).sub_sectionAlong
    (hf.starProjection_range_mfderiv hinj)).congr fun y ↦ ?_
  simp [Submodule.starProjection_orthogonal]
