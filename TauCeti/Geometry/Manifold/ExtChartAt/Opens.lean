/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ExtChartAt

/-!
# Extended charts of open submanifolds and subordinate compact chart covers

An open subset `U` of a manifold `M` inherits its charts from `M`: the extended chart of `U` at a
point `x` has the points of `U` in the source of the extended chart of `M` at `x` as its source
(`TopologicalSpace.Opens.extChartAt_source_eq`), and agrees with it there
(`TopologicalSpace.Opens.extChartAt_apply`). Its target and inverse are described by
`TopologicalSpace.Opens.extChartAt_target_eq` and
`TopologicalSpace.Opens.coe_extChartAt_symm_apply`.

A compact manifold modelled on a locally compact space is covered by the relative interiors of
finitely many compact coordinate sets (`TauCeti.exists_finite_compact_chart_cover`). When `M` is
covered by open sets `U i`, the coordinate sets can be taken in charts of the open submanifolds
`U i` (`TauCeti.exists_finite_subordinate_compact_chart_cover`). This is the form needed for data
that live only on the members of the cover, such as the coefficients of bundle sections in local
frames.
-/

public section

open Set TopologicalSpace
open scoped Manifold

namespace TopologicalSpace.Opens

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- The source of an inherited extended chart consists of the points of the open subset in the
ambient chart source. -/
theorem extChartAt_source_eq (U : Opens M) (x : U) :
    (extChartAt I x).source = Subtype.val ⁻¹' (extChartAt I (x : M)).source := by
  simp [extChartAt, chartAt_eq]

/-- An inherited extended chart is the ambient extended chart on the points of the open subset. -/
theorem extChartAt_apply (U : Opens M) (x w : U) :
    extChartAt I x w = extChartAt I (x : M) (w : M) := by
  simp [extChartAt, chartAt_eq]

end TopologicalSpace.Opens

namespace TauCeti

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]

/-- **Finite compact chart covers subordinate to an open cover.** A compact manifold modelled on a
locally compact space and covered by open sets `U i` is covered by the relative interiors of
finitely many compact coordinate sets `K j`, each in the extended chart of one of the open
submanifolds `U (r j)` at a point `c j` of it. -/
theorem exists_finite_subordinate_compact_chart_cover [CompactSpace M] [LocallyCompactSpace H]
    {ι : Type*} (U : ι → Opens M) (hU : ∀ y : M, ∃ i, y ∈ U i) :
    ∃ (t : Finset M) (r : t → ι) (c : ∀ j, U (r j))
      (K : ∀ j, Compacts (extChartAt I (c j)).target),
      ∀ y : M, ∃ j, ∃ hy : y ∈ U (r j),
        ∃ hy' : (⟨y, hy⟩ : U (r j)) ∈ (extChartAt I (c j)).source,
          (⟨extChartAt I (c j) ⟨y, hy⟩, (extChartAt I (c j)).map_source hy'⟩ :
            (extChartAt I (c j)).target) ∈
            interior (K j : Set (extChartAt I (c j)).target) := by
  choose i hi using hU
  -- A chart neighbourhood of `y` in the open submanifold `U (i y)`, with compact coordinates.
  choose u b hu hyu hsource hb htarget himage using fun y : M ↦
    exists_precompact_extChartAt_neighborhood (I := I) (⟨y, hi y⟩ : U (i y))
  have hopen (y : M) : IsOpen (Subtype.val '' u y : Set M) :=
    (U (i y)).isOpen.isOpenMap_subtype_val _ (hu y)
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover
    (fun y ↦ Subtype.val '' u y) hopen fun y _ ↦ mem_iUnion.mpr ⟨y, _, hyu y, rfl⟩
  have hK (y : M) :
      IsCompact (Subtype.val ⁻¹' b y : Set (extChartAt I (⟨y, hi y⟩ : U (i y))).target) := by
    rw [Subtype.isCompact_iff, Subtype.image_preimage_coe, inter_eq_right.mpr (htarget y)]
    exact hb y
  refine ⟨t, fun j ↦ i j, fun j ↦ ⟨j, hi j⟩, fun j ↦ ⟨_, hK j⟩, fun y ↦ ?_⟩
  obtain ⟨z, hz, w, hw, rfl⟩ := mem_iUnion₂.mp (ht (mem_univ y))
  refine ⟨⟨z, hz⟩, w.2, hsource z hw, ?_⟩
  -- The coordinate points whose inverse chart lies in `u z` form a relatively open set inside
  -- the compact piece.
  have hO : IsOpen {p : (extChartAt I (⟨z, hi z⟩ : U (i z))).target |
      (extChartAt I (⟨z, hi z⟩ : U (i z))).symm p ∈ u z} :=
    (hu z).preimage (continuousOn_iff_continuous_domRestrict.mp
      (continuousOn_extChartAt_symm (⟨z, hi z⟩ : U (i z))))
  refine interior_maximal (fun p hp ↦ ?_) hO ?_
  · have hmem := himage z (mem_image_of_mem _ hp)
    rwa [(extChartAt I (⟨z, hi z⟩ : U (i z))).right_inv p.2] at hmem
  · simpa only [mem_ofPred_eq, (extChartAt I (⟨z, hi z⟩ : U (i z))).left_inv
      (hsource z hw)] using hw

end TauCeti
