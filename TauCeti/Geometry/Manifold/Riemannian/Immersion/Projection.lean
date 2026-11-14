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
import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.RankOne
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
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
metric suffice, with only `C^1` manifold structure on the source and target.

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
  [IsManifold J 1 N]
  {m n : ℕ∞ω} [IsManifold I 1 M]
  [IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y)]
  {f : M → N} {W : (x : M) → TangentSpace J (f x)} {x : M} {u : Set M}

/-- Tangential projections form a `C^n` endomorphism field at a point where the differential
is injective. Only the ambient manifold needs a metric; its model need not be finite-dimensional. -/
theorem ContMDiffAt.starProjection_range_mfderiv
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).range.starProjection) x := by
  classical
  -- A frame centered at x has constant coordinates there; smooth transitions are not needed.
  -- Push it forward, apply Gram–Schmidt, then sum the projections onto its lines.
  let e := trivializationAt E (TangentSpace I) x
  let b := Module.finBasis ℝ E
  let v (i : Fin (Module.finrank ℝ E)) (y : M) :=
    mfderiv I J f y (e.localFrame b i y)
  have hv (i) : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (v i y)) x := by
    have hs : ContMDiffAt I (I.prod 𝓘(ℝ, E)) n
        (fun y ↦ TotalSpace.mk' E y (e.localFrame b i y)) x := by
      rw [contMDiffAt_section_iff]
      refine (contMDiffAt_const (c := b i)).congr_of_eventuallyEq ?_
      filter_upwards [e.open_baseSet.mem_nhds
        (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
      -- Fold trivializationAt back to e so the trivialization lemmas match the coordinates.
      change (e ⟨y, e.localFrame b i y⟩).2 = b i
      rw [e.localFrame_apply_of_mem_baseSet b hy, Trivialization.basisAt,
        Module.Basis.map_apply, e.linearEquivAt_symm_apply, e.apply_mk_symm hy]
    exact hf.mfderiv_apply_sectionAlong hs hnm
  have hli : LinearIndependent ℝ (fun i ↦ v i x) := by
    have hx : x ∈ e.baseSet :=
      FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x
    have hframe : LinearIndependent ℝ (fun i ↦ e.localFrame b i x) := by
      simpa only [e.localFrame_apply_of_mem_baseSet b hx] using
        (e.basisAt b hx).linearIndependent
    exact hframe.map' _ (LinearMap.ker_eq_bot.mpr hinj)
  let g (i : Fin (Module.finrank ℝ E)) (y : M) :=
    InnerProductSpace.gramSchmidtNormed ℝ (fun i ↦ v i y) i
  -- Pin the metric structure through its regularity witness: TangentSpace is reducible
  -- to the model, but its metric norm need not be the model norm.
  have hmetric : IsContMDiffRiemannianBundle J n F (fun y : N ↦ TangentSpace J y) :=
    inferInstance
  have hg (i) : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (g i y)) x :=
    ContMDiffAt.gramSchmidtNormed_bundle (hmetric := hmetric) (b := f) (v := v) i
      (fun j _ ↦ hv j) (hli.linearIndepOn _)
  -- Pin the target norm too, so reducibility of TangentSpace does not select the model norm.
  have hs := ContMDiffAt.sum_sectionAlong Finset.univ _
    (hf.of_le (le_self_add.trans hnm))
    (fun i _ ↦ (hg i).rankOne_bundle (hmetric := hmetric)
      (W := TangentSpace J)
      (targetNorm := inferInstanceAs (∀ y : N, NormedAddCommGroup (TangentSpace J y))) (hg i))
  refine hs.congr_of_eventuallyEq ?_
  filter_upwards [e.open_baseSet.mem_nhds
    (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  apply congrArg (TotalSpace.mk' (F →L[ℝ] F) (f y))
  have hspan : Submodule.span ℝ (Set.range (fun i ↦ v i y)) =
      (mfderiv I J f y).range :=
    e.span_range_localFrame_map b (mfderiv I J f y).toLinearMap hy
  rw [InnerProductSpace.starProjection_eq_sum_rankOne_gramSchmidtNormed (fun i ↦ v i y) hspan]

/-- Normal projections form a `C^n` endomorphism field at a point where the differential
is injective, without choosing a local normal frame or a finite-dimensional ambient model. -/
theorem ContMDiffAt.starProjection_orthogonal_range_mfderiv
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).rangeᗮ.starProjection) x := by
  have hid := TauCeti.contMDiff_id_endomorphism
    (I := J) (M := N) (F₁ := F) (V := TangentSpace J) (n := n)
  refine (((hid (f x)).comp x (hf.of_le (le_self_add.trans hnm))).sub_sectionAlong
    (hf.starProjection_range_mfderiv hnm hinj)).congr_of_eventuallyEq
      (Eventually.of_forall fun y ↦ ?_)
  simp [Submodule.starProjection_orthogonal]

/-- Tangential projection preserves regularity within a set for a field along a map
regular at the point, with injective differential there. -/
theorem ContMDiffWithinAt.starProjection_range_mfderiv_apply
    (hW : ContMDiffWithinAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) u x)
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffWithinAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) u x :=
  (hf.starProjection_range_mfderiv hnm hinj).contMDiffWithinAt.clm_bundle_apply hW

/-- Normal projection preserves regularity within a set for a field along a map
regular at the point, with injective differential there. -/
theorem ContMDiffWithinAt.starProjection_orthogonal_range_mfderiv_apply
    (hW : ContMDiffWithinAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) u x)
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffWithinAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) u x :=
  (hf.starProjection_orthogonal_range_mfderiv hnm hinj).contMDiffWithinAt.clm_bundle_apply hW

/-- Tangential projection preserves `C^n` regularity at a point where the differential is
injective. Only the ambient manifold needs a metric. -/
theorem ContMDiffAt.starProjection_range_mfderiv_apply
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) x :=
  hW.contMDiffWithinAt.starProjection_range_mfderiv_apply hf hnm hinj

/-- Normal projection along an immersion preserves `C^n` regularity at a point.
The normal space is the orthogonal complement of the differential's range in the ambient
metric, including when the immersion has self-intersections. -/
theorem ContMDiffAt.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : Function.Injective (mfderiv I J f x))
    (hW : ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) x) :
    ContMDiffAt I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) x :=
  hW.contMDiffWithinAt.starProjection_orthogonal_range_mfderiv_apply hf hnm hinj

/-- Tangential projection preserves regularity on a set for a field along a map regular
at the points of the set, with injective differential there. -/
theorem ContMDiffOn.starProjection_range_mfderiv_apply
    (hW : ContMDiffOn I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) u)
    (hf : ∀ x ∈ u, ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : ∀ x ∈ u, Function.Injective (mfderiv I J f x)) :
    ContMDiffOn I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) u :=
  fun x hx ↦ (hW x hx).starProjection_range_mfderiv_apply (hf x hx) hnm (hinj x hx)

/-- Normal projection preserves regularity on a set for a field along a map regular
at the points of the set, with injective differential there. -/
theorem ContMDiffOn.starProjection_orthogonal_range_mfderiv_apply
    (hW : ContMDiffOn I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y)) u)
    (hf : ∀ x ∈ u, ContMDiffAt I J m f x) (hnm : n + 1 ≤ m)
    (hinj : ∀ x ∈ u, Function.Injective (mfderiv I J f x)) :
    ContMDiffOn I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) u :=
  fun x hx ↦ (hW x hx).starProjection_orthogonal_range_mfderiv_apply (hf x hx) hnm (hinj x hx)

/-- Tangential projection of a `C^n` field along a `C^(n+1)` immersion is `C^n`.
The ambient metric is allowed to vary with the point. -/
theorem ContMDiff.starProjection_range_mfderiv_apply
    (hf : ContMDiff I J m f) (hnm : n + 1 ≤ m)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).range.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_range_mfderiv_apply hnm (hinj x) (hW x)

/-- Normal projection of a `C^n` field along a `C^(n+1)` immersion is `C^n`.
The projection is onto the normal space over the source point, not a space attached to the
possibly self-intersecting image. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv_apply
    (hf : ContMDiff I J m f) (hnm : n + 1 ≤ m)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y))
    (hW : ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) (W y))) :
    ContMDiff I (J.prod 𝓘(ℝ, F)) n
      (fun y ↦ TotalSpace.mk' F (f y) ((mfderiv I J f y).rangeᗮ.starProjection (W y))) :=
  fun x ↦ (hf x).starProjection_orthogonal_range_mfderiv_apply hnm (hinj x) (hW x)

/-- The tangential projections of an immersion form a `C^n` endomorphism field
along the immersion. Equivalently, they are a regular section of the endomorphism bundle of
`f *ᵖ TangentSpace J`, via `Bundle.Pullback.contMDiff_hom_section_iff`. -/
theorem ContMDiff.starProjection_range_mfderiv
    (hf : ContMDiff I J m f) (hnm : n + 1 ≤ m)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).range.starProjection) :=
  fun x ↦ (hf x).starProjection_range_mfderiv hnm (hinj x)

/-- The normal projections of an immersion form a `C^n` endomorphism field along
it, for the ambient metric. Thus projection onto the normal spaces is regular without
choosing a local normal frame. -/
theorem ContMDiff.starProjection_orthogonal_range_mfderiv
    (hf : ContMDiff I J m f) (hnm : n + 1 ≤ m)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I (J.prod 𝓘(ℝ, F →L[ℝ] F)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F)
        (E := fun z ↦ TangentSpace J z →L[ℝ] TangentSpace J z)
        (f y) (mfderiv I J f y).rangeᗮ.starProjection) :=
  fun x ↦ (hf x).starProjection_orthogonal_range_mfderiv hnm (hinj x)
