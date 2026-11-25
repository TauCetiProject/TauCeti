/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
public import Mathlib.Topology.MetricSpace.HausdorffDimension
import TauCeti.Analysis.Calculus.Sard.LowDimension

/-!
# Lower-dimensional simplices of a smooth triangulation are null

A `C¹` immersion `g` of the closed simplex on a vertex set `σ` into a manifold `M` modelled on a
finite-dimensional space `E` is the restriction of a map `F : (σ → ℝ) → M` that is `C¹` within
the standard simplex. The simplex lies in the affine hyperplane `∑ v = 1`, whose Hausdorff
dimension is `|σ| - 1`, so when `|σ| ≤ dim E` the chart images of `range g` are null for every
Haar measure (`DifferentiableOn.addHaar_image_eq_zero_of_dimH_lt_finrank`): `range g` is a null
set of `M` (`TauCeti.IsSimplexImmersion.isNullSet_range`).

For a smooth triangulation `κ : |K| ≃ₜ M`, the image of every closed simplex of dimension below
`dim E` is null (`TauCeti.IsSmoothTriangulation.isNullSet_image_range_faceInclusion`), and so is
the image of the union of all of them when the vertex set is countable
(`TauCeti.IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion`).

This is the null-image statement of §6.1 ("Smooth triangulations of boundaryless manifolds") of the
QuasiregularMaps roadmap, by its route through
`DifferentiableOn.addHaar_image_eq_zero_of_finrank_lt_finrank` in charts.
-/

public section

open Set Function Module MeasureTheory AbstractSimplicialComplex TauCeti.SetLike
open scoped Manifold

namespace TauCeti

variable {ι : Type*}
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M] {n : WithTop ℕ∞}

/-- The weight vectors of the standard simplex on a vertex set `σ`, as a subset of `σ → ℝ`, have
Hausdorff dimension below `|σ|`. -/
theorem dimH_range_stdSimplex_weights_lt {σ : Finset ι} (hσ : σ.Nonempty) :
    dimH (range fun t : Convexity.StdSimplex ℝ σ ↦ ⇑t.weights) < σ.card := by
  classical
  obtain ⟨a₀, ha₀⟩ := hσ
  set s : (σ → ℝ) →ₗ[ℝ] ℝ := ∑ a : σ, LinearMap.proj a
  have hs (v : σ → ℝ) : s v = ∑ a, v a := by simp [s, LinearMap.sum_apply]
  have hsub : (range fun t : Convexity.StdSimplex ℝ σ ↦ ⇑t.weights) ⊆ s ⁻¹' {1} := by
    rintro _ ⟨t, rfl⟩
    rw [mem_preimage, mem_singleton_iff, hs, ← t.total, Finsupp.sum_fintype _ _ (by simp)]
  have hne : (s ⁻¹' {1}).Nonempty := ⟨Pi.single ⟨a₀, ha₀⟩ 1, by simp [hs]⟩
  have hspan : vectorSpan ℝ (s ⁻¹' {1}) ≤ LinearMap.ker s := by
    rw [vectorSpan_def, Submodule.span_le]
    rintro _ ⟨v, hv, w, hw, rfl⟩
    simp only [mem_preimage, mem_singleton_iff] at hv hw
    simp [hv, hw]
  have hker : LinearMap.ker s ≠ ⊤ := fun h ↦ by
    have := (LinearMap.ker_eq_top.mp h) ▸ (hs (Pi.single ⟨a₀, ha₀⟩ 1)).symm
    simp at this
  have hlt : finrank ℝ (vectorSpan ℝ (s ⁻¹' {1})) < σ.card := by
    refine (Submodule.finrank_mono hspan).trans_lt ?_
    simpa using Submodule.finrank_lt hker
  calc dimH (range fun t : Convexity.StdSimplex ℝ σ ↦ ⇑t.weights) ≤ dimH (s ⁻¹' {1}) :=
        dimH_mono hsub
    _ = finrank ℝ (vectorSpan ℝ (s ⁻¹' {1})) :=
        Real.Convex.dimH_eq_finrank_vectorSpan ((convex_singleton (1 : ℝ)).linear_preimage s) hne
    _ < σ.card := by exact_mod_cast hlt

/-- A `C¹` immersion of the closed simplex on a vertex set `σ` with `|σ| ≤ dim E` into a manifold
modelled on `E` has null image: the simplex has dimension below that of the manifold. -/
theorem IsSimplexImmersion.isNullSet_range (hn : 1 ≤ n) {σ : Finset ι}
    {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g) (hσ : σ.card ≤ finrank ℝ E) :
    IsNullSet I (range g) := by
  rw [isNullSet_iff]
  intro x μ _
  rcases σ.eq_empty_or_nonempty with rfl | hne
  · have : IsEmpty (StandardSimplex (∅ : Finset ι)) := ⟨fun y ↦ by simpa using y.property⟩
    rw [range_eq_empty g, empty_inter, image_empty, measure_empty]
  obtain ⟨F, hFg, hFs, -⟩ := isSimplexImmersion_iff.mp h
  set S := range fun t : Convexity.StdSimplex ℝ σ ↦ ⇑t.weights with hS
  have hrange : range g = F '' S := by
    rw [hS, ← Finset.range_standardSimplex_coordinates, ← range_comp]
    exact congrArg range (funext fun y ↦ (hFg y).symm)
  have hdiff : DifferentiableOn ℝ (extChartAt I x ∘ F) (S ∩ F ⁻¹' (extChartAt I x).source) := by
    rintro t ⟨ht, htx⟩
    have hF := ((hFs t ht).mdifferentiableWithinAt (zero_lt_one.trans_le hn).ne')
    rw [extChartAt_source] at htx
    have := ((mdifferentiableWithinAt_iff_of_mem_source (x := t)
      (mem_chart_source _ t) htx).mp hF).2
    simp only [extChartAt_model_space_eq_id, PartialEquiv.refl_symm, PartialEquiv.refl_coe,
      CompTriple.comp_eq, preimage_id_eq, id_eq, modelWithCornersSelf_coe, range_id,
      inter_univ] at this
    exact this.mono inter_subset_left
  have hdim : dimH (S ∩ F ⁻¹' (extChartAt I x).source) < finrank ℝ E :=
    (dimH_mono inter_subset_left).trans_lt
      ((dimH_range_stdSimplex_weights_lt hne).trans_le (by exact_mod_cast hσ))
  refine measure_mono_null ?_ (hdiff.addHaar_image_eq_zero_of_dimH_lt_finrank μ hdim)
  rw [hrange]
  rintro _ ⟨_, ⟨⟨t, ht, rfl⟩, hts⟩, rfl⟩
  exact ⟨t, ⟨ht, hts⟩, rfl⟩

/-- In a `C¹` smooth triangulation of a manifold modelled on `E`, the image of every closed simplex
with at most `dim E` vertices is null. -/
theorem IsSmoothTriangulation.isNullSet_image_range_faceInclusion (hn : 1 ≤ n)
    {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n κ)
    (σ : Face K) (hσ : σ.val.card ≤ finrank ℝ E) :
    IsNullSet I (κ '' range (faceInclusion K σ)) := by
  rw [← range_comp]
  exact (isSmoothTriangulation_iff.mp h σ).isNullSet_range hn hσ

/-- In a `C¹` smooth triangulation of a manifold modelled on `E` by a complex with countably many
vertices, the image of the union of the closed simplices of dimension below `dim E` is null. -/
theorem IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion [Countable ι]
    (hn : 1 ≤ n) {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M}
    (h : IsSmoothTriangulation I n κ) :
    IsNullSet I (⋃ σ ∈ {σ : Face K | σ.val.card ≤ finrank ℝ E},
      κ '' range (faceInclusion K σ)) :=
  IsNullSet.biUnion (to_countable _) fun σ hσ ↦ h.isNullSet_image_range_faceInclusion hn σ hσ

end TauCeti
