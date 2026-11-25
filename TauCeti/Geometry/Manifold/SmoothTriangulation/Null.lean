/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.SmoothTriangulation.Basic
public import TauCeti.Geometry.Manifold.Measure
public import TauCeti.AlgebraicTopology.SimplicialComplex.Simplex.Realization
public import TauCeti.Geometry.Manifold.SmoothTriangulation.LocallyFinite
import TauCeti.Analysis.Convex.StdSimplex.HausdorffDimension
import TauCeti.Geometry.Manifold.Sard.Basic

/-!
# Lower-dimensional simplices of a smooth triangulation are null

A `C¹` immersion `g` of the closed simplex on a vertex set `σ` into a manifold `M` modelled on a
finite-dimensional space `E` is the restriction of a map `F : (σ → ℝ) → M` that is `C¹` within
the standard simplex. The standard simplex has Hausdorff dimension below `|σ|`
(`Convexity.StdSimplex.dimH_range_weights_lt_card`), so when `|σ| ≤ dim E` its image under `F` is
null (`MDifferentiableOn.isNullSet_image_of_dimH_lt_finrank`): `range g` is a null set of `M`
(`TauCeti.IsSimplexImmersion.isNullSet_range`).

For a smooth triangulation `κ : |K| ≃ₜ M`, the image of every closed simplex of dimension below
`dim E` is null (`TauCeti.IsSmoothTriangulation.isNullSet_image_range_faceInclusion`), and so is
the image of the union of all of them when the complex has countably many simplices
(`TauCeti.IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion`). When `E` is
finite-dimensional no countability is needed
(`TauCeti.IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion_of_finiteDimensional`):
nullity is local (`TauCeti.isNullSet_iff_forall_exists_nhds`), and a compact neighbourhood of a
point meets only finitely many closed simplices
(`AbstractSimplicialComplex.finite_setOf_image_range_faceInclusion_inter_nonempty_of_manifold`).
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

/-- A `C¹` immersion of the closed simplex on a vertex set `σ` with `|σ| ≤ dim E` into a manifold
modelled on `E` has null image: the simplex has dimension below that of the manifold. -/
theorem IsSimplexImmersion.isNullSet_range (hn : 1 ≤ n) {σ : Finset ι}
    {g : StandardSimplex σ → M} (h : IsSimplexImmersion I n g) (hσ : σ.card ≤ finrank ℝ E) :
    IsNullSet I (range g) := by
  rcases σ.eq_empty_or_nonempty with rfl | hne
  · have : IsEmpty (StandardSimplex (∅ : Finset ι)) := ⟨fun y ↦ by simpa using y.property⟩
    rw [range_eq_empty g, isNullSet_iff]
    simp
  have : Nonempty σ := hne.to_subtype
  obtain ⟨F, hFg, hFs, -⟩ := isSimplexImmersion_iff.mp h
  have hrange : range g = F '' range fun t : Convexity.StdSimplex ℝ σ ↦ ⇑t.weights := by
    rw [← Finset.range_standardSimplex_coordinates, ← range_comp]
    exact congrArg range (funext fun y ↦ (hFg y).symm)
  rw [hrange]
  refine (hFs.mdifferentiableOn (zero_lt_one.trans_le hn).ne').isNullSet_image_of_dimH_lt_finrank
    (Convexity.StdSimplex.dimH_range_weights_lt_card.trans_le ?_)
  exact_mod_cast (Fintype.card_coe σ).trans_le hσ

/-- In a `C¹` smooth triangulation of a manifold modelled on `E`, the image of every closed simplex
with at most `dim E` vertices is null. -/
theorem IsSmoothTriangulation.isNullSet_image_range_faceInclusion (hn : 1 ≤ n)
    {K : AbstractSimplicialComplex ι} {κ : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n κ)
    (σ : Face K) (hσ : σ.val.card ≤ finrank ℝ E) :
    IsNullSet I (κ '' range (faceInclusion K σ)) := by
  rw [← range_comp]
  exact (isSmoothTriangulation_iff.mp h σ).isNullSet_range hn hσ

/-- In a `C¹` smooth triangulation of a manifold modelled on `E` by a complex with countably many
simplices, the image of the union of the closed simplices of dimension below `dim E` is null. -/
theorem IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion (hn : 1 ≤ n)
    {K : AbstractSimplicialComplex ι} [Countable (Face K)] {κ : Realization K ≃ₜ M}
    (h : IsSmoothTriangulation I n κ) :
    IsNullSet I (⋃ σ ∈ {σ : Face K | σ.val.card ≤ finrank ℝ E},
      κ '' range (faceInclusion K σ)) :=
  IsNullSet.biUnion (to_countable _) fun σ hσ ↦ h.isNullSet_image_range_faceInclusion hn σ hσ

/-- In a `C¹` smooth triangulation of a manifold modelled on a finite-dimensional space `E`, the
image of the union of the closed simplices of dimension below `dim E` is null. The complex may
have uncountably many simplices: nullity is local, and a compact neighbourhood of a point meets
only finitely many closed simplices. -/
theorem IsSmoothTriangulation.isNullSet_biUnion_image_range_faceInclusion_of_finiteDimensional
    [FiniteDimensional ℝ E] (hn : 1 ≤ n) {K : AbstractSimplicialComplex ι}
    {κ : Realization K ≃ₜ M} (h : IsSmoothTriangulation I n κ) :
    IsNullSet I (⋃ σ ∈ {σ : Face K | σ.val.card ≤ finrank ℝ E},
      κ '' range (faceInclusion K σ)) := by
  have : LocallyCompactSpace M := Manifold.locallyCompact_of_finiteDimensional I
  refine isNullSet_iff_forall_exists_nhds.2 fun x _ ↦ ?_
  obtain ⟨C, hC, hCx⟩ := exists_compact_mem_nhds x
  refine ⟨C, hCx, ?_⟩
  -- Only the finitely many closed simplices meeting `C` contribute.
  have hfin := finite_setOf_image_range_faceInclusion_inter_nonempty_of_manifold I κ hC
  refine (IsNullSet.biUnion
      (hfin.inter_of_left {σ : Face K | σ.val.card ≤ finrank ℝ E}).countable
      fun σ hσ ↦ h.isNullSet_image_range_faceInclusion hn σ hσ.2).mono ?_
  rintro y ⟨hy, hyC⟩
  simp only [mem_iUnion] at hy ⊢
  obtain ⟨σ, hσ, hyσ⟩ := hy
  exact ⟨σ, ⟨⟨y, hyσ, hyC⟩, hσ⟩, hyσ⟩

end TauCeti
