/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier
import TauCeti.Analysis.Convex.Extreme

/-!
# Extending a subdivision of a subcomplex

For a locally finite complex in a finite-dimensional real normed space, a locally finite
subdivision of a subcomplex extends to a locally finite subdivision of the whole complex,
without changing the prescribed triangulation on the subcomplex.
This is the relative subdivision theorem used to make triangulations agree on overlaps.

The restriction of a subdivision to any original simplex triangulates that simplex.
Consequently the prescribed triangulation meets each remaining simplex in a subcomplex
of its boundary, and the cell-extension theorem applies to the remaining simplices.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 2,
relative subdivisions of simplicial complexes. The construction uses the cell-coning
extension in `TauCeti.Analysis.Convex.SimplicialComplex.Subdivision`.
-/

public section

open Set

namespace Geometry.SimplicialComplex

section LinearOrderedField

variable {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup E] [Module 𝕜 E] {K L A : SimplicialComplex 𝕜 E} {s : Finset E}

/-- A subdivision of a subcomplex restricts to its intersection with every simplex of the
containing complex. -/
theorem IsSubdivision.space_restrict_of_le (h : L.IsSubdivision A) (hAK : A ≤ K)
    (hs : s ∈ K.faces) :
    (L.restrict (convexHull 𝕜 (s : Set E))).space = L.space ∩ convexHull 𝕜 (s : Set E) := by
  classical
  refine (space_restrict_subset (convex_convexHull 𝕜 _)).antisymm ?_
  rintro x ⟨hxL, hxs⟩
  obtain ⟨t, ht, hxt⟩ := mem_space_iff.mp hxL
  obtain ⟨u, hu, htu⟩ := h.exists_convexHull_subset ht
  have hext : IsExtreme 𝕜 (convexHull 𝕜 (u : Set E))
      (convexHull 𝕜 ((u : Set E) ∩ s)) := by
    have him : ((↑) : u → E) '' {v : u | (v : E) ∈ s} = (u : Set E) ∩ s := by
      ext v
      simp [and_comm]
    have hr : range ((↑) : u → E) = (u : Set E) := by
      ext v
      simp
    simpa only [hr, him] using
      (K.indep (hAK hu)).isExtreme_convexHull {v : u | (v : E) ∈ s}
  have hxus := K.inter_subset_convexHull (hAK hu) hs ⟨htu hxt, hxs⟩
  have hx' := hext.convexHull_inter_subset htu ⟨hxt, hxus⟩
  have hsub : (t : Set E) ∩ convexHull 𝕜 ((u : Set E) ∩ s) ⊆
      ↑(t.filter fun v => v ∈ convexHull 𝕜 (s : Set E)) := by
    intro v hv
    exact Finset.mem_filter.mpr ⟨hv.1, convexHull_mono inter_subset_right hv.2⟩
  have hxfilter := convexHull_mono hsub hx'
  have hne := convexHull_nonempty_iff.mp (Set.nonempty_of_mem hxfilter)
  exact mem_space_iff.mpr ⟨_, mem_restrict_faces.mpr
    ⟨L.down_closed ht (Finset.filter_subset _ _) hne,
      fun v hv => (Finset.mem_filter.mp hv).2⟩, hxfilter⟩

/-- The restriction of a subdivision to an original simplex triangulates that simplex. -/
theorem IsSubdivision.space_restrict (h : L.IsSubdivision K) (hs : s ∈ K.faces) :
    (L.restrict (convexHull 𝕜 (s : Set E))).space = convexHull 𝕜 (s : Set E) := by
  rw [h.space_restrict_of_le le_rfl hs, h.space_eq,
    inter_eq_right.mpr (convexHull_subset_space hs)]

end LinearOrderedField

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L A : SimplicialComplex ℝ E}

variable [FiniteDimensional ℝ E]

/-- In a finite-dimensional real normed space, a locally finite subdivision of a subcomplex
of a locally finite complex extends to a locally finite subdivision of the whole complex.
Its restriction to the original subcomplex is exactly the prescribed subdivision, so no new
simplex with all vertices there is introduced. -/
theorem IsSubdivision.exists_extension (h : L.IsSubdivision A) (hAK : A ≤ K)
    (hK : LocallyFinite fun s : K.faces => convexHull ℝ (s : Set E))
    (hL : LocallyFinite fun s : L.faces => convexHull ℝ (s : Set E)) :
    ∃ M : SimplicialComplex ℝ E, M.IsSubdivision K ∧ M.restrict A.space = L ∧
      LocallyFinite fun s : M.faces => convexHull ℝ (s : Set E) := by
  classical
  -- Attach exactly the original simplices which are outside the prescribed subcomplex.
  let J := {s : K.faces // s.1 ∉ A.faces}
  let P : J → Set E := fun s => convexHull ℝ (s.1.1 : Set E)
  have hPc (s : J) : IsCompact (P s) := s.1.1.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hPv (s : J) : Convex ℝ (P s) := convex_convexHull ℝ _
  have hPne (s : J) : (P s).Nonempty :=
    convexHull_nonempty_iff.mpr (K.nonempty_of_mem_faces s.1.2)
  choose p hp using fun s ↦ (hPne s).intrinsicInterior (hPv s)
  have hP : LocallyFinite P := hK.comp_injective Subtype.val_injective
  have hri : Pairwise fun s t : J => Disjoint (intrinsicInterior ℝ (P s))
      (intrinsicInterior ℝ (P t)) :=
    K.pairwise_disjoint_intrinsicInterior.comp_of_injective Subtype.val_injective
  have hfr (s : J) : intrinsicFrontier ℝ (P s) ⊆
      L.space ∪ ⋃ (t : J) (_ : t ≠ s ∧ P t ⊆ P s), P t := by
    intro x hx
    obtain ⟨t, ht, hts, hxt⟩ := exists_mem_faces_subset_mem_intrinsicInterior s.1.2
      (intrinsicFrontier_subset (hPc s).isClosed hx)
    by_cases htA : t ∈ A.faces
    · exact .inl (h.space_eq.symm ▸ convexHull_subset_space htA (intrinsicInterior_subset hxt))
    · let j : J := ⟨⟨t, ht⟩, htA⟩
      refine .inr (mem_iUnion₂.mpr ⟨j, ⟨?_, convexHull_mono (Finset.coe_subset.mpr hts)⟩,
        intrinsicInterior_subset hxt⟩)
      intro hjs
      have hxi : x ∉ intrinsicInterior ℝ (P s) := by
        rw [← intrinsicClosure_sdiff_intrinsicInterior] at hx
        exact hx.2
      exact hxi (hjs ▸ hxt)
  have hLi (s : J) : Disjoint (intrinsicInterior ℝ (P s)) L.space := by
    rw [h.space_eq]
    exact disjoint_intrinsicInterior_space_of_not_mem hAK s.1.2 s.2
  -- Each attachment meets the prescribed subdivision in finitely many boundary simplices.
  obtain ⟨M, hML, hMs, hMP, hMf⟩ := exists_subdivision_extending L P hPc hPv p hp hP hri hfr
    (fun s x ⟨hxP, hxL⟩ => (h.space_restrict_of_le hAK s.1.2).symm ▸ ⟨hxL, hxP⟩)
    hLi (fun s => finite_faces_restrict hL (hPc s))
  have hMf' : ∀ s ∈ M.faces, s ∈ L.faces ∨ ∃ i, (s : Set E) ⊆ P i := by
    intro s hs
    exact (hMf s hs).imp id fun ⟨i, _, hi⟩ ↦ ⟨i, hi⟩
  -- The prescribed part and the remaining original simplices cover the whole complex.
  have hspace : M.space = K.space := by
    rw [hMs, h.space_eq]
    refine Subset.antisymm ?_ ?_
    · rintro x (hxA | hxP)
      · exact space_mono hAK hxA
      · obtain ⟨s, hxs⟩ := mem_iUnion.mp hxP
        exact convexHull_subset_space s.1.2 hxs
    · intro x hxK
      obtain ⟨s, hs, hxs⟩ := mem_space_iff.mp hxK
      by_cases hsA : s ∈ A.faces
      · exact .inl (convexHull_subset_space hsA hxs)
      · exact .inr (mem_iUnion.mpr ⟨⟨⟨s, hs⟩, hsA⟩, hxs⟩)
  refine ⟨M, ⟨hspace, ?_⟩, h.space_eq ▸ hML,
    locallyFinite_convexHull_of_finite_restrict hPv hP hL (fun s => (hMP s).2) hMf'⟩
  intro s hs
  rcases hMf' s hs with hsL | ⟨t, hst⟩
  · obtain ⟨t, ht, hst⟩ := h.exists_convexHull_subset hsL
    exact ⟨t, hAK ht, hst⟩
  · exact ⟨t.1.1, t.1.2, convexHull_min hst (hPv t)⟩

/-- A finite subdivision of a subcomplex of a finite complex extends to a finite subdivision
of the whole complex, retaining the prescribed triangulation exactly. -/
theorem IsSubdivision.exists_finite_extension (h : L.IsSubdivision A) (hAK : A ≤ K)
    (hK : K.faces.Finite) (hL : L.faces.Finite) :
    ∃ M : SimplicialComplex ℝ E, M.IsSubdivision K ∧ M.restrict A.space = L ∧ M.faces.Finite := by
  let := hK.fintype
  let := hL.fintype
  obtain ⟨M, hMK, hMA, hM⟩ := h.exists_extension hAK
    (locallyFinite_of_finite _) (locallyFinite_of_finite _)
  have hc : IsCompact K.space := hK.isCompact_biUnion fun s _ =>
    s.finite_toSet.isCompact_convexHull (𝕜 := ℝ)
  have hfin := finite_faces_restrict hM (hMK.space_eq.symm ▸ hc)
  rw [restrict_eq_self_of_space_subset Subset.rfl] at hfin
  exact ⟨M, hMK, hMA, hfin⟩

end Geometry.SimplicialComplex
