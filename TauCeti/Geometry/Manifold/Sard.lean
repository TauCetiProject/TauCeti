/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.Geometry.Manifold.RegularValue
import TauCeti.Analysis.Calculus.Sard.EqualDimension

/-!
# Sard's theorem for maps between manifolds of equal dimension

Let `f : M → N` be a differentiable map between real manifolds modelled on finite-dimensional
spaces of the same dimension, where `M` is Lindelöf (for instance σ-compact or second countable).
The image of the set of non-regular points of `f` is a null set of `N`, read through charts
against Haar measure on the model, and consequently the regular values of `f` are dense in `N`.
The manifolds may have boundary or corners.

The proof reads `f` in pairs of extended charts and applies the flat equal-dimensional Sard lemma
`TauCeti.addHaar_image_eq_zero_of_not_surjective_fderivWithin`, which only needs derivatives
within the model range `range I`. Countably many charts cover `M` by the Lindelöf property.
Only first derivatives enter: in equal dimensions no higher regularity is needed.

## Main results

* `TauCeti.isNullSet_image_of_not_isRegularPoint`: the image of any set of non-regular points at
  which `f` is differentiable is null.
* `TauCeti.isNullSet_image_criticalPoints`: the critical values of a differentiable map form a
  null set.
* `TauCeti.dense_isRegularValue`: the regular values of a differentiable map are dense.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Graduate Texts in Mathematics 218,
  Springer, 2013, Theorem 6.10.
-/

public section

open Function Module Set MeasureTheory
open scoped Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N]
  {f : M → N} {s : Set M}

/-- The local form of Sard's theorem: the image of the non-regular points of `s` lying in one chart
of `M` is null in `N`. -/
private theorem isNullSet_image_inter_chartAt_source [MeasurableSpace E'] [BorelSpace E']
    (hdim : finrank ℝ E = finrank ℝ E') (hf : ∀ x ∈ s, MDifferentiableAt I J f x)
    (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) (x₀ : M) :
    IsNullSet J (f '' (s ∩ (chartAt H x₀).source)) := by
  borelize E
  rw [isNullSet_iff]
  intro y₀ μ _
  -- Read `f` in the extended charts at `x₀` and `y₀`, on the points both charts see.
  let g : E → E' := extChartAt J y₀ ∘ f ∘ (extChartAt I x₀).symm
  let u : Set M := s ∩ (chartAt H x₀).source ∩ f ⁻¹' (chartAt H' y₀).source
  have hu : extChartAt J y₀ '' (f '' (s ∩ (chartAt H x₀).source) ∩ (extChartAt J y₀).source) =
      g '' (extChartAt I x₀ '' u) := by
    rw [extChartAt_source, ← image_inter_preimage, image_image, image_image]
    refine image_congr fun x hx ↦ ?_
    have hx' : x ∈ (extChartAt I x₀).source := by rw [extChartAt_source]; exact hx.1.2
    simp only [g, comp_apply, (extChartAt I x₀).left_inv hx']
  rw [hu]
  refine addHaar_image_eq_zero_of_not_surjective_fderivWithin μ hdim
    (f' := fun z ↦ fderivWithin ℝ g (range I) z) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    have hg := (hf x hx.1.1).hasMFDerivAt.hasFDerivWithinAt_of_mem_source hx.1.2 hx.2
    refine hg.differentiableWithinAt.hasFDerivWithinAt.mono ?_
    rintro _ ⟨x', hx', rfl⟩
    exact extChartAt_target_subset_range x₀
      ((extChartAt I x₀).map_source (by rw [extChartAt_source]; exact hx'.1.2))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← isRegularPoint_iff_surjective_fderivWithin (hf x hx.1.1) hx.1.2 hx.2]
    exact hs x hx.1.1

/-- **Sard's theorem in equal dimensions**, for a set of non-regular points. Let `M` and `N` be
real manifolds whose finite-dimensional models have the same dimension, with `M` Lindelöf. If `f`
is differentiable at every point of `s` and no point of `s` is regular, then `f '' s` is null in
`N`. -/
theorem isNullSet_image_of_not_isRegularPoint [LindelofSpace M] [MeasurableSpace E']
    [BorelSpace E'] (hdim : finrank ℝ E = finrank ℝ E')
    (hf : ∀ x ∈ s, MDifferentiableAt I J f x) (hs : ∀ x ∈ s, ¬ IsRegularPoint I J f x) :
    IsNullSet J (f '' s) := by
  obtain ⟨t, htc, -, hcover⟩ := isLindelof_univ.elim_nhds_subcover
    (fun x : M ↦ (chartAt H x).source) fun x _ ↦ chart_source_mem_nhds H x
  have hst : s = ⋃ x ∈ t, s ∩ (chartAt H x).source := by
    rw [← inter_iUnion₂, eq_comm, inter_eq_left]
    exact (subset_univ s).trans hcover
  rw [hst, image_iUnion₂]
  exact IsNullSet.biUnion htc fun x _ ↦ isNullSet_image_inter_chartAt_source hdim hf hs x

/-- **Sard's theorem in equal dimensions.** The critical values of a differentiable map from a
Lindelöf manifold to a manifold whose finite-dimensional model has the same dimension form a
null set. -/
theorem isNullSet_image_criticalPoints [LindelofSpace M] [MeasurableSpace E'] [BorelSpace E']
    (hdim : finrank ℝ E = finrank ℝ E') (hf : MDifferentiable I J f) :
    IsNullSet J (f '' {x | ¬ IsRegularPoint I J f x}) :=
  isNullSet_image_of_not_isRegularPoint hdim (fun x _ ↦ hf x) fun _ hx ↦ hx

/-- The regular values of a differentiable map from a Lindelöf manifold to a manifold whose
finite-dimensional model has the same dimension are dense. -/
theorem dense_isRegularValue [LindelofSpace M] (hdim : finrank ℝ E = finrank ℝ E')
    (hf : MDifferentiable I J f) : Dense {y | IsRegularValue I J f y} := by
  borelize E'
  rw [setOf_isRegularValue_eq_compl_image]
  exact (isNullSet_image_criticalPoints hdim hf).dense_compl

end TauCeti
