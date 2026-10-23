/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Orientation
public import TauCeti.Analysis.Complex.UpperHalfPlane.Geodesic.Segment
public import TauCeti.Analysis.Complex.UpperHalfPlane.Triangle
import TauCeti.Analysis.Complex.NormSq
import TauCeti.Analysis.Complex.UpperHalfPlane.PSL.Translation

/-!
# Triangles are compact and lie in every half-plane containing their vertices

Closed sides and triangles are convex: they contain the geodesic segment between any two of their
points (`geodesicSegment_subset_closedSide`, `geodesicSegment_subset_triangle`). A nondegenerate
triangle is compact (`isCompact_triangle`), its trace on the line through two
vertices is the side between them (`triangle_inter_range_geodesicLine`), and it lies in every
closed half-plane containing its three vertices (`triangle_subset_closure_leftHalfPlane`,
`triangle_subset_closure_rightHalfPlane`): the triangle defined as an intersection of three
closed sides is the convex hull of its vertices.

The file also records basic facts about closed sides and triangles that the above needs: a
closed side is the closed half-plane of its reference point when that point is off the line
(`closedSide_eq_closure_leftHalfPlane_of_mem`, `closedSide_eq_closure_rightHalfPlane_of_mem`),
and the frontiers of a closed side and of a triangle lie on the bounding lines
(`UpperHalfPlane.frontier_closedSide_subset`, `UpperHalfPlane.frontier_triangle_subset`).

Source: Walkden, *Hyperbolic geometry* (MATH32051), §14.2 (convex polygons as intersections of
half-planes); Katok, *Fuchsian groups, geodesic flows…*, Clay Math. Proc. 10 (2010), p. 20 (the
angular defect). The hull statement is evident in the sources; the proof is ours.
-/

public section

noncomputable section

open Matrix.ProjectiveSpecialLinearGroup MeasureTheory Set UpperHalfPlane
open scoped MatrixGroups Pointwise Real

namespace UpperHalfPlane

open TauCeti.UpperHalfPlane

/-! ### The frontiers of closed sides and triangles -/

/-- The frontier of a closed side lies on its bounding line. -/
theorem frontier_closedSide_subset (z w u : ℍ) :
    frontier (closedSide z w u) ⊆ Set.range (geodesicLine (geodesicBetween z w)) := by
  rw [closedSide_def]
  split_ifs
  · exact frontier_closure_subset.trans (frontier_rightHalfPlane _).subset
  · exact frontier_closure_subset.trans (frontier_leftHalfPlane _).subset

/-- The frontier of a triangle lies on the union of its three side lines. -/
theorem frontier_triangle_subset (A B C : ℍ) :
    frontier (triangle A B C) ⊆
      Set.range (geodesicLine (geodesicBetween A B)) ∪
        Set.range (geodesicLine (geodesicBetween B C)) ∪
        Set.range (geodesicLine (geodesicBetween C A)) := by
  rw [triangle_def]
  intro w hw
  rcases frontier_inter_subset _ _ hw with ⟨hw, -⟩ | ⟨-, hw⟩
  · rcases frontier_inter_subset _ _ hw with ⟨hw, -⟩ | ⟨-, hw⟩
    · exact Or.inl (Or.inl (frontier_closedSide_subset _ _ _ hw))
    · exact Or.inl (Or.inr (frontier_closedSide_subset _ _ _ hw))
  · exact Or.inr (frontier_closedSide_subset _ _ _ hw)

end UpperHalfPlane

namespace TauCeti.UpperHalfPlane

/-! ### Closed sides and triangles -/

/-- The closed side containing a point of the open left half-plane is the closed left half-plane. -/
theorem closedSide_eq_closure_leftHalfPlane_of_mem {z w u : ℍ}
    (hu : u ∈ leftHalfPlane (geodesicBetween z w)) :
    closedSide z w u = closure (leftHalfPlane (geodesicBetween z w)) := by
  rw [closedSide_def,
    ite_eq_right (Set.disjoint_right.1 (disjoint_rightHalfPlane_leftHalfPlane _) hu)]

/-- The closed side containing a point of the open right half-plane is the closed right
half-plane. -/
theorem closedSide_eq_closure_rightHalfPlane_of_mem {z w u : ℍ}
    (hu : u ∈ rightHalfPlane (geodesicBetween z w)) :
    closedSide z w u = closure (rightHalfPlane (geodesicBetween z w)) := by
  rw [closedSide_def, ite_eq_left hu]

/-- Closed sides are convex. -/
theorem geodesicSegment_subset_closedSide {u v x z w : ℍ} (hz : z ∈ closedSide u v x)
    (hw : w ∈ closedSide u v x) : geodesicSegment z w ⊆ closedSide u v x := by
  rw [closedSide_def] at hz hw ⊢
  split_ifs at hz hw ⊢
  · exact geodesicSegment_subset_closure_rightHalfPlane hz hw
  · exact geodesicSegment_subset_closure_leftHalfPlane hz hw

/-- Triangles are convex. -/
theorem geodesicSegment_subset_triangle {A B C z w : ℍ} (hz : z ∈ triangle A B C)
    (hw : w ∈ triangle A B C) : geodesicSegment z w ⊆ triangle A B C := by
  rw [triangle_def] at hz hw ⊢
  exact subset_inter (subset_inter (geodesicSegment_subset_closedSide hz.1.1 hw.1.1)
    (geodesicSegment_subset_closedSide hz.1.2 hw.1.2))
    (geodesicSegment_subset_closedSide hz.2 hw.2)

/-! ### The trace of a triangle on a side line -/

/-- If the boundary line of a closed side meets the line `g` only at the parameter `t₀`, then
two points of `g` in that closed side cannot lie on either side of `t₀`: the open half-plane
would contain the boundary point at `t₀`, as its parameters form an interval. -/
private theorem eq_of_mem_closedSide {g : PSL(2, ℝ)} {x y u : ℍ} {t₀ t₁ t : ℝ}
    (h₀ : geodesicLine g t₀ ∈ Set.range (geodesicLine (geodesicBetween x y)))
    (hmeet : ∀ s, geodesicLine g s ∈ Set.range (geodesicLine (geodesicBetween x y)) → s = t₀)
    (h₁ : geodesicLine g t₁ ∈ closedSide x y u) (ht₁ : t₁ ≠ t₀)
    (h : geodesicLine g t ∈ closedSide x y u) (ht : t₀ ∈ uIcc t t₁) : t = t₀ := by
  by_contra hne
  rw [closedSide_def] at h₁ h
  split_ifs at h₁ h
  · rw [closure_rightHalfPlane] at h₁ h
    exact Set.disjoint_left.1 (disjoint_rightHalfPlane_range_geodesicLine _)
      ((ordConnected_preimage_geodesicLine_rightHalfPlane g _).uIcc_subset
        (Or.resolve_right h fun h' ↦ hne (hmeet t h'))
        (Or.resolve_right h₁ fun h' ↦ ht₁ (hmeet t₁ h')) ht) h₀
  · rw [closure_leftHalfPlane] at h₁ h
    exact Set.disjoint_left.1 (disjoint_leftHalfPlane_range_geodesicLine _)
      ((ordConnected_preimage_geodesicLine_leftHalfPlane g _).uIcc_subset
        (Or.resolve_right h fun h' ↦ hne (hmeet t h'))
        (Or.resolve_right h₁ fun h' ↦ ht₁ (hmeet t₁ h')) ht) h₀

/-- The trace of a nondegenerate triangle on the line through two of its vertices is the side
between them. -/
theorem triangle_inter_range_geodesicLine {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) :
    triangle A B C ∩ Set.range (geodesicLine (geodesicBetween A B)) = geodesicSegment A B := by
  refine Set.Subset.antisymm ?_ (Set.subset_inter (geodesicSegment_subset_triangle
    (left_mem_triangle A B C) (triangle_rotate A B C ▸ left_mem_triangle B C A))
    (geodesicSegment_subset_range_geodesicLine A B))
  rintro _ ⟨hp, t, rfl⟩
  rw [triangle_def] at hp
  have hd : 0 < dist A B := dist_pos.2 hAB
  refine (mem_geodesicSegment_iff _ _ _).2 ⟨t, ⟨not_lt.1 fun ht ↦ ?_, not_lt.1 fun ht ↦ ?_⟩, rfl⟩
  · -- the line `C A` meets the line `A B` only at `A`, the parameter `0`
    have h₀ : geodesicLine (geodesicBetween A B) 0 ∈
        Set.range (geodesicLine (geodesicBetween C A)) := by
      rw [geodesicLine_geodesicBetween_zero]
      exact mem_range_geodesicLine_geodesicBetween_right C A
    refine ht.ne (eq_of_mem_closedSide h₀ (fun s hs ↦ eq_of_mem_range_geodesicLine hC
      (mem_range_geodesicLine_geodesicBetween_left C A) h₀ hs) ?_ hd.ne' hp.2 ?_)
    · rw [geodesicLine_geodesicBetween_dist]
      exact mem_closedSide_self C A B
    · exact Set.mem_uIcc.2 (Or.inl ⟨ht.le, hd.le⟩)
  · -- the line `B C` meets the line `A B` only at `B`, the parameter `dist A B`
    have h₀ : geodesicLine (geodesicBetween A B) (dist A B) ∈
        Set.range (geodesicLine (geodesicBetween B C)) := by
      rw [geodesicLine_geodesicBetween_dist]
      exact mem_range_geodesicLine_geodesicBetween_left B C
    refine ht.ne' (eq_of_mem_closedSide h₀ (fun s hs ↦ eq_of_mem_range_geodesicLine hC
      (mem_range_geodesicLine_geodesicBetween_right B C) h₀ hs) ?_ hd.ne hp.1.2 ?_)
    · rw [geodesicLine_geodesicBetween_zero]
      exact mem_closedSide_self B C A
    · exact Set.mem_uIcc.2 (Or.inr ⟨hd.le, ht.le⟩)

/-! ### Compactness -/

/-- In normal form, the triangle lies in a compact rectangle of the upper half-plane. -/
private theorem isCompact_triangle_of_normal_form {d : ℝ} (hd : 0 < d) {C : ℍ} (hC : 0 < C.re) :
    IsCompact (triangle UpperHalfPlane.I (geodesicLine 1 d) C) := by
  set c₁ := circleCenter (geodesicLine 1 d) C
  set c₂ := circleCenter UpperHalfPlane.I C with hc₂
  have hcc : c₁ < c₂ := circleCenter_lt_of_normal_form hd hC
  -- the power of `C` with respect to the semicircle through `I` and `C` is that of `I`
  have hI : Complex.normSq ((C : ℂ) - c₂) = c₂ ^ 2 + 1 := by
    rw [hc₂, normSq_sub_circleCenter (UpperHalfPlane.I_re.trans_ne hC.ne),
      UpperHalfPlane.coe_I, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.I_re, Complex.ofReal_re, zero_sub, Complex.sub_im,
      Complex.I_im, Complex.ofReal_im, sub_zero]
    ring
  have hm : 0 < min 1 C.im := lt_min one_pos C.im_pos
  set K : Set ℂ :=
    Icc 0 C.re ×ℂ Icc (min 1 C.im) (Real.sqrt (Complex.normSq ((C : ℂ) - c₁))) with hK
  have hKsub : K ⊆ Set.range UpperHalfPlane.coe := fun w hw ↦ by
    rw [UpperHalfPlane.range_coe]
    exact hm.trans_le (Complex.mem_reProdIm.1 hw).2.1
  refine ((isOpenEmbedding_coe.isInducing.isCompact_preimage_iff hKsub).2
    (isCompact_Icc.reProdIm isCompact_Icc)).of_isClosed_subset (isClosed_triangle _ _ _)
    fun z hz ↦ ?_
  obtain ⟨hre, h₁, h₂⟩ := (mem_triangle_normal_form_iff hd hC z).1 hz
  have hrad := Complex.normSq_sub_ofReal_sub_normSq_sub_ofReal (c₁ := c₁) (c₂ := c₂) C z
  rw [UpperHalfPlane.coe_re, UpperHalfPlane.coe_re] at hrad
  have hzim := z.im_pos
  have hzre : z.re ≤ C.re := by nlinarith
  rw [Set.mem_preimage, hK, Complex.mem_reProdIm, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im]
  refine ⟨⟨hre, hzre⟩, ?_, Real.le_sqrt_of_sq_le ?_⟩
  · -- the lower bound on `z.im`: over `0 ≤ z.re ≤ C.re`, the second circle inequality is
    -- weakest at an endpoint, where it reads `1 ≤ z.im ^ 2` or `C.im ^ 2 ≤ z.im ^ 2`
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
      Complex.ofReal_im, sub_zero, UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at h₂ hI
    rcases le_or_gt z.re c₂ with h | h
    · exact (min_le_left _ _).trans (by nlinarith)
    · exact (min_le_right _ _).trans (by nlinarith)
  · have := Complex.normSq_apply ((z : ℂ) - c₁)
    simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, sub_zero,
      UpperHalfPlane.coe_re, UpperHalfPlane.coe_im] at this
    nlinarith

/-- Nondegenerate triangles are compact. -/
theorem isCompact_triangle {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) : IsCompact (triangle A B C) := by
  have hAC : A ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_left A B)
  have hBC : B ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_right A B)
  obtain ⟨h, d, hd, hCre, hcase⟩ := exists_smul_eq_normal_form hAB hC
  rw [← inv_smul_smul h (triangle A B C)]
  refine IsCompact.smul _ ?_
  rcases hcase with ⟨hA, hB⟩ | ⟨hB, hA⟩
  · rw [smul_triangle h hAB hBC hAC.symm, hA, hB]
    exact isCompact_triangle_of_normal_form hd hCre
  · rw [← triangle_swap_left hC, smul_triangle h hAB.symm hAC hBC.symm, hA, hB]
    exact isCompact_triangle_of_normal_form hd hCre

/-! ### The hull property -/

/-- The hull property for the closed half-plane `{re ≤ 0}`: if the vertices have `re ≤ 0`, so
does every point of the triangle. The maximiser of `re` on the compact triangle is a frontier
point, so it lies on a side, whose endpoints have `re ≤ 0`; by convexity of `{re < max}` this is
absurd unless the maximum is `≤ 0`. -/
private theorem re_nonpos_of_mem_triangle {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) (hA : A.re ≤ 0) (hB : B.re ≤ 0)
    (hC' : C.re ≤ 0) {z : ℍ} (hz : z ∈ triangle A B C) : z.re ≤ 0 := by
  have hAC : A ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_left A B)
  have hBC : B ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_right A B)
  -- `A` is off the line `B C`, and `B` is off the line `C A`: otherwise that line would be `A B`
  have hA' : A ∉ Set.range (geodesicLine (geodesicBetween B C)) := fun hA ↦ hC
    ((range_geodesicLine_geodesicBetween_of_mem hA
      (mem_range_geodesicLine_geodesicBetween_left B C) hAB).symm ▸
      mem_range_geodesicLine_geodesicBetween_right B C)
  have hB' : B ∉ Set.range (geodesicLine (geodesicBetween C A)) := fun hB ↦ hC
    ((range_geodesicLine_geodesicBetween_of_mem (mem_range_geodesicLine_geodesicBetween_right C A)
      hB hAB).symm ▸ mem_range_geodesicLine_geodesicBetween_left C A)
  by_contra! hzre
  obtain ⟨w, hwT, hw⟩ := (isCompact_triangle hAB hC).exists_isMaxOn ⟨z, hz⟩
    UpperHalfPlane.continuous_re.continuousOn
  rw [isMaxOn_iff] at hw
  have hwre : 0 < w.re := hzre.trans_le (hw z hz)
  -- `w` is not an interior point: the translates `ε +ᵥ w` have larger real part
  have hint : w ∉ interior (triangle A B C) := fun hint ↦ by
    have ht : Filter.Tendsto (fun ε : ℝ ↦ ε +ᵥ w) (nhdsWithin 0 (Ioi 0)) (nhds w) :=
      ((continuous_induced_rng.2 (Complex.continuous_ofReal.add continuous_const) :
        Continuous fun ε : ℝ ↦ ε +ᵥ w).tendsto' 0 w (zero_vadd ℝ w)).mono_left nhdsWithin_le_nhds
    obtain ⟨ε, hεT, hε⟩ := ((ht.eventually_mem (mem_interior_iff_mem_nhds.1 hint)).and
      self_mem_nhdsWithin).exists
    have := hw _ hεT
    rw [vadd_re] at this
    linarith [Set.mem_Ioi.1 hε]
  -- a side with endpoints of nonpositive real part cannot contain `w`
  have key : ∀ {x y : ℍ}, x.re ≤ 0 → y.re ≤ 0 → w ∈ geodesicSegment x y → False := fun hx hy hw' ↦
    lt_irrefl w.re ((mem_leftHalfPlane_upperRightHom_iff w.re w).1
      (geodesicSegment_subset_leftHalfPlane
        ((mem_leftHalfPlane_upperRightHom_iff _ _).2 (hx.trans_lt hwre))
        ((mem_leftHalfPlane_upperRightHom_iff _ _).2 (hy.trans_lt hwre)) hw'))
  rcases frontier_triangle_subset A B C ⟨subset_closure hwT, hint⟩ with (hl | hl) | hl
  · exact key hA hB ((triangle_inter_range_geodesicLine hAB hC).subset ⟨hwT, hl⟩)
  · rw [← triangle_rotate A B C] at hwT
    exact key hB hC' ((triangle_inter_range_geodesicLine hBC hA').subset ⟨hwT, hl⟩)
  · rw [triangle_rotate C A B] at hwT
    exact key hC' hA ((triangle_inter_range_geodesicLine hAC.symm hB').subset ⟨hwT, hl⟩)

/-- **A nondegenerate triangle lies in every closed left half-plane containing its vertices.** -/
theorem triangle_subset_closure_leftHalfPlane {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) {g : PSL(2, ℝ)}
    (hA : A ∈ closure (leftHalfPlane g)) (hB : B ∈ closure (leftHalfPlane g))
    (hC' : C ∈ closure (leftHalfPlane g)) : triangle A B C ⊆ closure (leftHalfPlane g) := by
  have hAC : A ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_left A B)
  have hBC : B ≠ C := fun h ↦ hC (h ▸ mem_range_geodesicLine_geodesicBetween_right A B)
  have hAB' : g⁻¹ • A ≠ g⁻¹ • B := (MulAction.injective _).ne hAB
  have hC'' : g⁻¹ • C ∉ Set.range (geodesicLine (geodesicBetween (g⁻¹ • A) (g⁻¹ • B))) := by
    rw [geodesicBetween_smul _ hAB, ← smul_range_geodesicLine, Set.smul_mem_smul_set_iff]
    exact hC
  intro z hz
  rw [mem_closure_leftHalfPlane_iff] at hA hB hC' ⊢
  refine re_nonpos_of_mem_triangle hAB' hC'' hA hB hC' ?_
  rw [← smul_triangle g⁻¹ hAB hBC hAC.symm, Set.smul_mem_smul_set_iff]
  exact hz

/-- **A nondegenerate triangle lies in every closed right half-plane containing its vertices.** -/
theorem triangle_subset_closure_rightHalfPlane {A B C : ℍ} (hAB : A ≠ B)
    (hC : C ∉ Set.range (geodesicLine (geodesicBetween A B))) {g : PSL(2, ℝ)}
    (hA : A ∈ closure (rightHalfPlane g)) (hB : B ∈ closure (rightHalfPlane g))
    (hC' : C ∈ closure (rightHalfPlane g)) : triangle A B C ⊆ closure (rightHalfPlane g) := by
  rw [← leftHalfPlane_mul_pslS] at hA hB hC' ⊢
  exact triangle_subset_closure_leftHalfPlane hAB hC hA hB hC'

/-! ### The angular defect -/

end TauCeti.UpperHalfPlane
