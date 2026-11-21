/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Submersion
public import TauCeti.Geometry.Manifold.Measure
import TauCeti.Geometry.Manifold.Boundary.Basic
import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Geometry.Manifold.Submersion.Basic
import TauCeti.MeasureTheory.Measure.Haar.Submersion

/-!
# Null preimages under submersions of manifolds

Let `M'` and `M` be real manifolds, possibly with boundary or corners, modelled on
finite-dimensional normed spaces `E'` and `E`. A map `θ : M' → M` that is a `C¹` submersion at
every point of a set `A` pulls null sets of `M` back to sets whose intersection with `A` is null in
`M'` (`TauCeti.IsNullSet.preimage_inter_of_isSubmersionAt`), and a map that is a `C¹` submersion
at every point pulls null sets back to null sets (`TauCeti.IsNullSet.preimage_of_isSubmersionAt`,
`TauCeti.IsNullSet.preimage_of_isSubmersion`). The dimensions of `M'` and `M` may differ, and `θ`
need not be injective or proper. No measurable structure on `M'` or `M` is used. Thus a property
holding off a null set of `M` holds, after composing with `θ`, off a null set of `M'`.

The boundary of `M'` is null, so only interior points of `A` matter. In the extended charts at
`z ∈ M'` and `y ∈ M` the map reads as `extChartAt I y ∘ θ ∘ (extChartAt I' z).symm`, which is
`C¹` with surjective derivative at the chart image of every interior point of `A` seen by both
charts. Its preimages of Haar-null sets are therefore Haar-null there
(`TauCeti.addHaar_preimage_inter_eq_zero_of_surjective_fderiv`), and countably many target charts
cover the chart image of `A`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, second edition, Springer GTM 218 (2013),
  Chapter 6 (sets of measure zero in manifolds).
-/

public section

open MeasureTheory Set Function Manifold
open scoped Manifold Topology ContDiff

namespace TauCeti

variable {E' E H' H M' M : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [FiniteDimensional ℝ E'] [MeasurableSpace E'] [BorelSpace E']
  [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
  [TopologicalSpace H'] [TopologicalSpace H]
  {I' : ModelWithCorners ℝ E' H'} {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M'] [ChartedSpace H' M'] [TopologicalSpace M] [ChartedSpace H M]
  {n : WithTop ℕ∞} [IsManifold I' n M'] [IsManifold I n M]
  {θ : M' → M} {A : Set M'} {s : Set M}

/-- Interior case of `TauCeti.IsNullSet.preimage_inter_of_isSubmersionAt`: if `A` consists of
interior points, read in the extended charts the map is `C¹` with surjective derivative on the
chart image of `A`, so the Euclidean statement applies chart by chart. -/
private theorem IsNullSet.preimage_inter_of_isSubmersionAt_of_subset_interior
    [FiniteDimensional ℝ E] (hs : IsNullSet I s) (hθ : ∀ x ∈ A, IsSubmersionAt I' I n θ x)
    (hn : 1 ≤ n) (hA : A ⊆ I'.interior M') : IsNullSet I' (θ ⁻¹' s ∩ A) := by
  have : IsManifold I' 1 M' := .of_le hn
  have : IsManifold I 1 M := .of_le hn
  have hn₀ : n ≠ 0 := (zero_lt_one.trans_le hn).ne'
  refine (isNullSet_iff _ _).2 fun z ν _ ↦ ?_
  set e := extChartAt I' z
  -- The chart images of the points of `A`, and those seen by the target chart at `y`.
  let S : Set E' := e '' (A ∩ e.source)
  let V : M → Set E' := fun y ↦ e.symm ⁻¹' (θ ⁻¹' (extChartAt I y).source)
  have hV : ∀ w ∈ S, V (θ (e.symm w)) ∈ 𝓝[S] w := by
    rintro _ ⟨p, ⟨hpA, hpe⟩, rfl⟩
    rw [e.left_inv hpe]
    have hc : ContinuousAt (θ ∘ e.symm) (e p) :=
      (hθ p hpA).contMDiffAt.continuousAt.comp_of_eq (continuousAt_extChartAt_symm' hpe)
        (e.left_inv hpe)
    apply mem_nhdsWithin_of_mem_nhds
    dsimp only [V]
    rw [← Set.preimage_comp]
    refine hc.preimage_mem_nhds ?_
    rw [comp_apply, e.left_inv hpe]
    exact extChartAt_source_mem_nhds (θ p)
  -- There the coordinate expression of `θ` is `C¹` with surjective derivative.
  let Θ : M → E' → E := fun y ↦ extChartAt I y ∘ θ ∘ e.symm
  have hΘ : ∀ y, ∀ w ∈ S ∩ V y, ContDiffAt ℝ 1 (Θ y) w ∧ Surjective (fderiv ℝ (Θ y) w) := by
    rintro y _ ⟨⟨p, ⟨hpA, hpe⟩, rfl⟩, hpy⟩
    rw [mem_preimage, mem_preimage, e.left_inv hpe] at hpy
    have hz : p ∈ (chartAt H' z).source := by rwa [← extChartAt_source (I := I')]
    have hy : θ p ∈ (chartAt H y).source := by rwa [← extChartAt_source (I := I)]
    have hrange : range I' ∈ 𝓝 (e p) := Filter.mem_of_superset
      (ModelWithCorners.extChartAt_target_mem_nhds_of_isInteriorPoint hn₀ z hpe (hA hpA))
      (extChartAt_target_subset_range z)
    refine ⟨((contMDiffAt_iff_of_mem_source hz hy).1
      ((hθ p hpA).contMDiffAt.of_le hn)).2.contDiffAt hrange, ?_⟩
    rw [← fderivWithin_of_mem_nhds hrange]
    exact (isRegularPoint_iff_surjective_fderivWithin
      ((hθ p hpA).contMDiffAt.mdifferentiableAt hn₀) hz hy).1
      (isRegularPoint_iff.2 ((hθ p hpA).surjective_mfderiv hn₀))
  -- Each chart image of `s` is null, so the preimage is locally null.
  have hpiece : ∀ y, ν ((Θ y) ⁻¹' (extChartAt I y '' (s ∩ (extChartAt I y).source))
      ∩ (S ∩ V y)) = 0 := fun y ↦
    addHaar_preimage_inter_eq_zero_of_surjective_fderiv (μ := Measure.addHaar) ν
      (fun w hw ↦ (hΘ y w hw).1) (fun w hw ↦ (hΘ y w hw).2) (hs.chartwise y _)
  let B := e '' ((θ ⁻¹' s ∩ A) ∩ e.source)
  have hBS : B ⊆ S := image_mono (inter_subset_inter_left _ inter_subset_right)
  refine measure_null_of_locally_null B fun w hw ↦ ?_
  refine ⟨_, Filter.mem_of_superset
    (Filter.inter_mem self_mem_nhdsWithin (nhdsWithin_mono w hBS (hV w (hBS hw)))) ?_,
    hpiece (θ (e.symm w))⟩
  rintro _ ⟨⟨p, ⟨⟨hps, hpA⟩, hpe⟩, rfl⟩, hpw⟩
  refine ⟨⟨θ p, ⟨hps, ?_⟩, ?_⟩, ⟨p, ⟨hpA, hpe⟩, rfl⟩, hpw⟩
  · simpa [V, e.left_inv hpe] using hpw
  · simp [Θ, e.left_inv hpe]

/-- **Submersions pull back null sets.** If `θ : M' → M` is a `C¹` submersion at every point of
`A`, then the preimage of a null set of `M` meets `A` in a null set of `M'`. -/
theorem IsNullSet.preimage_inter_of_isSubmersionAt (hs : IsNullSet I s)
    (hθ : ∀ x ∈ A, IsSubmersionAt I' I n θ x) (hn : 1 ≤ n) :
    IsNullSet I' (θ ⁻¹' s ∩ A) := by
  have : IsManifold I' 1 M' := .of_le hn
  rcases A.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
  · exact (isNullSet_iff _ _).2 fun _ _ _ ↦ by simp
  -- The target model is finite-dimensional, as a quotient of the source model.
  have : FiniteDimensional ℝ (TangentSpace I (θ x)) := Module.Finite.of_surjective
    (mfderiv I' I θ x : TangentSpace I' x →ₗ[ℝ] TangentSpace I (θ x))
    ((hθ x hx).surjective_mfderiv (zero_lt_one.trans_le hn).ne')
  have : FiniteDimensional ℝ E := this
  -- The boundary of `M'` is null, so it suffices to treat the interior points of `A`.
  refine ((hs.preimage_inter_of_isSubmersionAt_of_subset_interior (A := A ∩ I'.interior M')
    (fun x hx ↦ hθ x hx.1) hn inter_subset_right).union isNullSet_boundary).mono fun p hp ↦ ?_
  have hp' : p ∈ I'.interior M' ∪ I'.boundary M' := by
    rw [ModelWithCorners.interior_union_boundary_eq_univ]; trivial
  rcases hp' with hpi | hpb
  exacts [Or.inl ⟨hp.1, hp.2, hpi⟩, Or.inr hpb]

/-- **Submersions pull back null sets.** The preimage of a null set of `M` under a map
`θ : M' → M` that is a `C¹` submersion at every point is a null set of `M'`. -/
theorem IsNullSet.preimage_of_isSubmersionAt (hs : IsNullSet I s)
    (hθ : ∀ x, IsSubmersionAt I' I n θ x) (hn : 1 ≤ n) :
    IsNullSet I' (θ ⁻¹' s) := by
  simpa using hs.preimage_inter_of_isSubmersionAt (A := univ) (fun x _ ↦ hθ x) hn

/-- **Submersions pull back null sets.** The preimage of a null set of `M` under a `C¹`
submersion `θ : M' → M` is a null set of `M'`. -/
theorem IsNullSet.preimage_of_isSubmersion (hs : IsNullSet I s)
    (hθ : IsSubmersion I' I n θ) (hn : 1 ≤ n) :
    IsNullSet I' (θ ⁻¹' s) :=
  hs.preimage_of_isSubmersionAt hθ.isSubmersionAt hn

end TauCeti
