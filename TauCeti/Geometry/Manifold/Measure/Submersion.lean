/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure.AE
public import TauCeti.Geometry.Manifold.Submersion.Split
import TauCeti.Geometry.Manifold.Measure.Atlas
import TauCeti.MeasureTheory.Measure.Haar.Disintegration

/-!
# Submersions pull null sets back to null sets

Let `M` be a manifold modelled on a finite-dimensional real normed space and let `f : M → N` be a
`C^n` submersion, `1 ≤ n`, in the sense of Mathlib's chart normal form
(`Manifold.IsSubmersionAt`). Then the preimage under `f` of a null set of `N`
(`TauCeti.IsNullSet`) is null in `M`, so a property holding almost everywhere on `N` holds at
`f x` for almost every `x` in `M`. The source and target may have different dimensions, and
`f` need not be injective, proper or surjective.

In the normal-form charts `f` reads as a surjective linear projection, which pulls back Haar-null
sets to Haar-null sets (`LinearMap.quasiMeasurePreserving_of_surjective`); nullity is local
(`TauCeti.isNullSet_iff_forall_exists_nhds`), so the chart statements assemble without a
countability assumption on `M`. For maps between finite-dimensional manifolds with boundaryless
source, the normal form is supplied by surjectivity of the differential
(`ContMDiffOn.isSubmersionAtOfComplement_of_surjective_mfderiv`).

The hypothesis `1 ≤ n` cannot be dropped: a `C⁰` submersion is a topological projection, and
homeomorphisms of `ℝ` need not preserve null sets. Nor can submersions be replaced by `C¹` maps: a
constant map `ℝ → ℝ` has the non-null preimage `ℝ` of a point.

## Main results

* `TauCeti.IsNullSet.inter_preimage_of_isSubmersionAt`: the points of `f ⁻¹' s` at which `f` is a
  submersion form a null set, when `s` is null.
* `TauCeti.IsNullSet.preimage_of_isSubmersionAt`: a map that is a submersion at every point has
  null preimages of null sets.
* `Manifold.IsSubmersion.isNullSet_preimage`, `Manifold.IsSubmersion.tendsto_ae`: a submersion has
  null preimages of null sets, and pulls back the almost-everywhere filter.
* `TauCeti.IsNullSet.inter_preimage_of_surjective_mfderiv`: the same for a map that is `C¹` on an
  open set, at the points where its differential is surjective, between finite-dimensional
  manifolds with boundaryless source.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 6 (sets of measure zero in manifolds).
-/

public section

open Filter Function MeasureTheory Measure Set
open scoped ContDiff Manifold Topology

namespace TauCeti

universe u

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ E' G}
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N] [IsManifold J 1 N]
  {n : ℕ∞ω} {f : M → N} {s : Set N}

/-- In the domain chart of a submersion, the preimage of a null set is null. -/
private theorem IsNullSet.preimage_inter_domChart_source {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] (hs : IsNullSet J s) (hn : 1 ≤ n) {x : M}
    (h : Manifold.IsSubmersionAtOfComplement F I J n f x) :
    IsNullSet I (f ⁻¹' s ∩ h.domChart.source) := by
  let P : E →ₗ[ℝ] E' := h.projection
  have hP : Surjective P := fun v ↦ ⟨h.equiv.symm (v, 0), by simp [P]⟩
  have : FiniteDimensional ℝ E' := Module.Finite.of_surjective P hP
  -- In the normal-form charts, the chart image of `f ⁻¹' s` lies over the chart image of `s`.
  refine isNullSet_of_measure_extend_image_eq_zero inter_subset_right
    (IsManifold.maximalAtlas_subset_of_le hn h.domChart_mem_maximalAtlas) addHaar ?_
  refine measure_mono_null ?_ <|
    (P.quasiMeasurePreserving_of_surjective hP addHaar addHaar).preimage_null
      (hs.measure_extend_image_eq_zero
        (IsManifold.maximalAtlas_subset_of_le hn h.codChart_mem_maximalAtlas) addHaar)
  rintro _ ⟨y, ⟨hys, hy⟩, rfl⟩
  exact ⟨f y, ⟨hys, h.source_subset_preimage_source hy⟩, h.codChart_extend_apply hy⟩

/-- **Submersions pull null sets back to null sets.** If `s` is null in `N`, the points of `t`
mapped into `s` form a null set of `M`, provided `f` is a `C^n` submersion, `1 ≤ n`, at each of
them. -/
theorem IsNullSet.inter_preimage_of_isSubmersionAt (hs : IsNullSet J s) (hn : 1 ≤ n)
    {t : Set M} (hf : ∀ x ∈ t ∩ f ⁻¹' s, Manifold.IsSubmersionAt I J n f x) :
    IsNullSet I (t ∩ f ⁻¹' s) := by
  refine isNullSet_iff_forall_exists_nhds.2 fun x hx ↦ ?_
  have h := (hf x hx).isSubmersionAtOfComplement_complement
  exact ⟨h.domChart.source, h.domChart.open_source.mem_nhds h.mem_domChart_source,
    (hs.preimage_inter_domChart_source hn h).mono fun y hy ↦ ⟨hy.1.2, hy.2⟩⟩

/-- A map that is a `C^n` submersion, `1 ≤ n`, at every point pulls null sets back to null sets.
The complements in the normal forms may vary from point to point. -/
theorem IsNullSet.preimage_of_isSubmersionAt (hs : IsNullSet J s)
    (hf : ∀ x, Manifold.IsSubmersionAt I J n f x) (hn : 1 ≤ n) : IsNullSet I (f ⁻¹' s) := by
  simpa using hs.inter_preimage_of_isSubmersionAt hn (t := univ) fun x _ ↦ hf x

/-- A `C^n` submersion, `1 ≤ n`, pulls null sets back to null sets. -/
theorem _root_.Manifold.IsSubmersion.isNullSet_preimage (hf : Manifold.IsSubmersion I J n f)
    (hn : 1 ≤ n) (hs : IsNullSet J s) : IsNullSet I (f ⁻¹' s) :=
  hs.preimage_of_isSubmersionAt hf.isSubmersionAt hn

/-- A `C^n` submersion, `1 ≤ n`, pulls back the almost-everywhere filter: if a property holds
almost everywhere on `N`, it holds at `f x` for almost every `x` in `M`. -/
theorem _root_.Manifold.IsSubmersion.tendsto_ae (hf : Manifold.IsSubmersion I J n f)
    (hn : 1 ≤ n) : Tendsto f (TauCeti.Manifold.ae I M) (TauCeti.Manifold.ae J N) := fun _ ht ↦
  TauCeti.Manifold.mem_ae_iff.2 <| hf.isNullSet_preimage hn (TauCeti.Manifold.mem_ae_iff.1 ht)

/-- Let `f` be `C¹` on an open set `U` of a manifold with boundaryless finite-dimensional model,
and let `s` be null. If the differential of `f` is surjective at each point of `U` mapped into
`s`, then these points form a null set. -/
theorem IsNullSet.inter_preimage_of_surjective_mfderiv [I.Boundaryless] (hs : IsNullSet J s)
    {U : Set M} (hf : ContMDiffOn I J 1 f U) (hU : IsOpen U)
    (hsurj : ∀ x ∈ U ∩ f ⁻¹' s, Surjective (mfderiv I J f x)) : IsNullSet I (U ∩ f ⁻¹' s) := by
  refine hs.inter_preimage_of_isSubmersionAt le_rfl fun x hx ↦ ?_
  -- The tangent spaces are the model spaces, so the target model is finite-dimensional.
  let D : E →L[ℝ] E' := mfderiv I J f x
  have : FiniteDimensional ℝ E' := Module.Finite.of_surjective D.toLinearMap (hsurj x hx)
  exact (hf.isSubmersionAtOfComplement_of_surjective_mfderiv hU hx.1 le_rfl
    (hsurj x hx)).isSubmersionAt

end TauCeti
