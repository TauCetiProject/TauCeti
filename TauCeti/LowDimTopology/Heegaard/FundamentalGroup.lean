/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Rank
public import TauCeti.LowDimTopology.Handlebody.FundamentalGroup
public import TauCeti.LowDimTopology.Heegaard.Frontier

import TauCeti.AlgebraicTopology.FundamentalGroup.Basic
import TauCeti.AlgebraicTopology.FundamentalGroup.BasepointChange
import TauCeti.AlgebraicTopology.FundamentalGroup.CoverGeneration
import TauCeti.AlgebraicTopology.FundamentalGroup.HomotopyEquiv
import TauCeti.Topology.Homotopy.DeformationRetract
import TauCeti.Topology.Homotopy.HomotopyEquiv

/-!
# The fundamental group of a manifold with a Heegaard splitting

Let `M` be a `3`-manifold without boundary with a Heegaard splitting of genus `g` into two
handlebodies `H₁` and `H₂` meeting in their common boundary surface. Then the inclusion of either
handlebody induces a surjection `π₁(Hᵢ) → π₁(M)` at every base point of `Hᵢ`. Since `π₁(Hᵢ)` is
free of rank `g` (`TauCeti.nonempty_fundamentalGroup_handlebody_mulEquiv_freeGroup`), the
fundamental group of `M` is finitely generated, and its rank, the least number of generators
(`Group.rank`), is at most `g`. Taking a splitting of least genus, the rank of `π₁(M)` is at most
the Heegaard genus of `M`. This is the inequality whose equality case is Waldhausen's
rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`).

The surjectivity is the generation half of the Seifert–van Kampen theorem
(`TauCeti.FundamentalGroup.range_map_subtypeVal_sup_eq_top`), applied to the cover of `M` by
`H₂` and a thickening `N` of `H₁`: the union of `H₁` with an open neighbourhood `W` of the boundary
surface in `H₂` that deformation retracts onto it
(`TauCeti.exists_deformation_frontier_handlebody`). The interiors of `N` and `H₂` cover `M`,
because by invariance of domain the frontier of `H₂` is the boundary surface
(`TauCeti.HeegaardSplitting.coe_mem_left_iff`). Since `N` deformation retracts
onto `H₁`, loops in `N` come from `H₁`; since the boundary surface carries the fundamental group of
`H₂` (`TauCeti.fundamentalGroup_map_frontier_handlebody_surjective`), loops in `H₂` are homotopic
in `H₂` to loops on the boundary surface, which lies in `H₁`.

## Main results

* `TauCeti.HeegaardSplitting.fundamentalGroup_map_left_surjective` and
  `TauCeti.HeegaardSplitting.fundamentalGroup_map_right_surjective`: the fundamental group of
  either handlebody surjects onto the fundamental group of the manifold.
* `TauCeti.HeegaardSplitting.fg_fundamentalGroup`: the fundamental group of the manifold is
  finitely generated.
* `TauCeti.HeegaardSplitting.rank_fundamentalGroup_le_genus`: its rank is at most the genus of the
  splitting.
* `TauCeti.rank_fundamentalGroup_le_heegaardGenus`: its rank is at most the Heegaard genus.

## References

* J. Hempel, *3-Manifolds*, Annals of Mathematics Studies 86, Princeton University Press (1976),
  Chapter 2.
* M. Scharlemann, *Heegaard splittings of compact 3-manifolds*, in *Handbook of Geometric
  Topology*, North-Holland (2002), Section 2.
* A. Hatcher, *Algebraic Topology*, Cambridge University Press (2002), Section 1.2 (the
  Seifert–van Kampen theorem).
-/

public section

open Module Set
open scoped ContinuousMap

namespace TauCeti

namespace HeegaardSplitting

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M] (s : HeegaardSplitting M)

/-- A handlebody of a splitting has a finitely generated fundamental group, of rank at most the
genus. -/
private theorem exists_fg_rank_le {A : Set M} (e : A ≃ₜ handlebody s.genus) (x : A) :
    ∃ _ : Group.FG (FundamentalGroup A x), Group.rank (FundamentalGroup A x) ≤ s.genus := by
  let φ := e.toHomotopyEquiv.fundamentalGroupMulEquiv x
  have : Group.FG (FundamentalGroup A x) :=
    Group.fg_of_surjective (f := φ.symm.toMonoidHom) φ.symm.surjective
  exact ⟨this, (Group.rank_congr φ).trans_le (rank_fundamentalGroup_handlebody_le _)⟩

/-- **The cover of the van Kampen argument.** If `W` is relatively open in the second handlebody
and contains the Heegaard surface, then the interiors of the union of the first handlebody with
`W` and of the second handlebody cover the space. -/
private theorem interior_union_interior_right_eq_univ {W : Set M}
    (hW : IsOpen ((↑) ⁻¹' W : Set s.right)) (hLRW : s.left ∩ s.right ⊆ W) :
    interior (s.left ∪ W) ∪ interior s.right = univ := by
  have hLR (p : M) : p ∈ s.left ∪ s.right := s.union_eq_univ ▸ mem_univ p
  obtain ⟨O, hO, hOW⟩ := isOpen_induced_iff.1 hW
  have hint : O ∪ s.rightᶜ ⊆ interior (s.left ∪ W) := by
    refine interior_maximal ?_ (hO.union s.isClosed_right.isOpen_compl)
    rintro p (hpO | hpR)
    · by_cases hpR : p ∈ s.right
      · have hp : (⟨p, hpR⟩ : s.right) ∈ (↑) ⁻¹' O := hpO
        rw [hOW] at hp
        exact .inr hp
      · exact .inl ((hLR p).resolve_right hpR)
    · exact .inl ((hLR p).resolve_right hpR)
  refine eq_univ_of_forall fun p ↦ ?_
  by_cases hpR : p ∈ s.right
  · by_cases hpL : p ∈ s.left
    · have hp : (⟨p, hpR⟩ : s.right) ∈ (↑) ⁻¹' W := hLRW ⟨hpL, hpR⟩
      rw [← hOW] at hp
      exact .inl (hint (.inl hp))
    · -- A point of the second handlebody off the first is off the frontier of the second.
      refine .inr ?_
      rw [← self_sdiff_frontier, ← s.inter_eq_frontier_right]
      exact ⟨hpR, fun h ↦ hpL h.1⟩
  · exact .inl (hint (.inr hpR))

/-- **Loops in the second handlebody come from the first.** At a point of the Heegaard surface,
every loop in the second handlebody is homotopic in it to a loop on the boundary surface, which
lies in the first handlebody. -/
private theorem range_map_right_le_range_map_left (hE : finrank ℝ E = 3)
    (e : s.right ≃ₜ handlebody s.genus)
    (y : {y : handlebody s.genus | (y : ℂ × ℝ) ∈ frontier (handlebody s.genus)})
    (hy : ((e.symm y : s.right) : M) ∈ s.left) :
    (FundamentalGroup.map (ContinuousMap.subtypeVal s.right) (e.symm y)).range ≤
      (FundamentalGroup.map (ContinuousMap.subtypeVal s.left) ⟨_, hy⟩).range := by
  let j : C({y : handlebody s.genus | (y : ℂ × ℝ) ∈ frontier (handlebody s.genus)}, s.left) :=
    ⟨fun p ↦ ⟨e.symm p, by rw [s.coe_mem_left_iff hE e, Homeomorph.apply_symm_apply]; exact p.2⟩,
      by fun_prop⟩
  have hbij := e.symm.toHomotopyEquiv.fundamentalGroup_map_bijective (y : handlebody s.genus)
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, rfl⟩ := hbij.2 γ
  obtain ⟨ε, rfl⟩ := fundamentalGroup_map_frontier_handlebody_surjective y δ
  refine ⟨FundamentalGroup.map j y ε, ?_⟩
  -- Both sides are induced by the map `p ↦ e⁻¹ p` from the boundary surface to `M`.
  have h₁ := DFunLike.congr_fun
    (_root_.FundamentalGroup.map_comp (ContinuousMap.subtypeVal s.left) j y) ε
  have h₂ := DFunLike.congr_fun (_root_.FundamentalGroup.map_comp
    ((ContinuousMap.subtypeVal s.right).comp e.symm.toHomotopyEquiv.toFun)
    (ContinuousMap.subtypeVal _) y) ε
  have h₃ := DFunLike.congr_fun (_root_.FundamentalGroup.map_comp
    (ContinuousMap.subtypeVal s.right) e.symm.toHomotopyEquiv.toFun (y : handlebody s.genus))
    (FundamentalGroup.map (ContinuousMap.subtypeVal _) y ε)
  simp only [MonoidHom.comp_apply] at h₁ h₂ h₃
  -- The composites `(subtypeVal s.left).comp j` in `h₁` and
  -- `((subtypeVal s.right).comp e.symm).comp (subtypeVal _)` in `h₂` are both `p ↦ e⁻¹ p` by
  -- definition, and `j y` is by definition the base point `⟨_, hy⟩`. Rewriting one composite into
  -- the other is not possible, as the base point of the target group depends on the map, so the
  -- chain closes by unfolding.
  exact h₁.symm.trans (h₂.trans h₃)

/-- **The thickened first handlebody deformation retracts onto it.** Let `F` deform an open
neighbourhood `V` of the boundary surface in the standard handlebody onto the boundary surface,
fixing it, and let `W` be the corresponding neighbourhood of the Heegaard surface in the second
handlebody. Then the union of the first handlebody with `W` deformation retracts onto the first
handlebody: the deformation is the identity on the first handlebody and `F` on `W`. -/
private theorem exists_homotopyEquiv_left_union (hE : finrank ℝ E = 3)
    (e : s.right ≃ₜ handlebody s.genus) {V : Set (handlebody s.genus)}
    (hSV : {x : handlebody s.genus | (x : ℂ × ℝ) ∈ frontier (handlebody s.genus)} ⊆ V)
    (F : C(unitInterval × V, V)) (hF₀ : ∀ x, F (0, x) = x)
    (hF₁ : ∀ x, ((F (1, x) : handlebody s.genus) : ℂ × ℝ) ∈ frontier (handlebody s.genus))
    (hFfix : ∀ t (x : V), ((x : handlebody s.genus) : ℂ × ℝ) ∈ frontier (handlebody s.genus) →
      F (t, x) = x) :
    ∃ eN : s.left ≃ₕ ↥(s.left ∪ (↑) '' (e ⁻¹' V)),
      eN.toFun = ContinuousMap.inclusion subset_union_left := by
  classical
  have hmem (p : s.right) := s.coe_mem_left_iff hE e p
  have hmemW (p : s.right) : (p : M) ∈ ((↑) '' (e ⁻¹' V) : Set M) ↔ e p ∈ V :=
    Subtype.val_injective.mem_set_image
  have hLR (p : M) : p ∈ s.left ∪ s.right := s.union_eq_univ ▸ mem_univ p
  have hV (a : ↥(s.left ∪ (↑) '' (e ⁻¹' V))) (ha : (a : M) ∈ s.right) : e ⟨a, ha⟩ ∈ V := by
    rcases a.2 with haL | haW
    · exact hSV ((hmem ⟨a, ha⟩).1 haL)
    · exact (hmemW ⟨a, ha⟩).1 haW
  let H : unitInterval × ↥(s.left ∪ (↑) '' (e ⁻¹' V)) → M := fun q ↦
    if hq : (q.2 : M) ∈ s.right then ((e.symm (F (q.1, ⟨e ⟨q.2, hq⟩, hV q.2 hq⟩)) : s.right) : M)
    else q.2
  have hHL (q : unitInterval × ↥(s.left ∪ (↑) '' (e ⁻¹' V))) (hq : (q.2 : M) ∈ s.left) :
      H q = q.2 := by
    simp only [H]
    split_ifs with hqR
    · rw [hFfix _ _ ((hmem ⟨q.2, hqR⟩).1 hq), Homeomorph.symm_apply_apply]
    · rfl
  -- `H` is continuous on the two closed pieces where the point lies in the first, respectively
  -- the second, handlebody.
  have hHc : Continuous H := by
    have hcov : (univ : Set (unitInterval × ↥(s.left ∪ (↑) '' (e ⁻¹' V)))) =
        {q | (q.2 : M) ∈ s.left} ∪ {q | (q.2 : M) ∈ s.right} :=
      (eq_univ_of_forall fun q ↦ hLR q.2).symm
    rw [← continuousOn_univ, hcov]
    refine ContinuousOn.union_of_isClosed ?_ ?_ (s.isClosed_left.preimage (by fun_prop))
      (s.isClosed_right.preimage (by fun_prop))
    · exact (continuous_subtype_val.comp continuous_snd).continuousOn.congr fun q hq ↦ hHL q hq
    · rw [continuousOn_iff_continuous_domRestrict]
      have hres : domRestrict {q | (q.2 : M) ∈ s.right} H = fun q ↦
          ((e.symm (F (q.1.1, ⟨e ⟨q.1.2, q.2⟩, hV q.1.2 q.2⟩)) : s.right) : M) := by
        funext q
        have hq : ((q.1.2 : ↥(s.left ∪ (↑) '' (e ⁻¹' V))) : M) ∈ s.right := q.2
        simp only [domRestrict_apply, H, hq, ↓reduceDIte]
      rw [hres]
      fun_prop
  refine ⟨ContinuousMap.HomotopyEquiv.ofWeakDeformationRetraction subset_union_left H hHc
    (fun q ↦ ?_) (fun a ↦ ?_) (fun a ↦ ?_) (fun t a ha ↦ (hHL (t, a) ha).symm ▸ ha),
    ContinuousMap.ext fun a ↦ Subtype.ext
      (ContinuousMap.HomotopyEquiv.coe_ofWeakDeformationRetraction_apply _ _ _ _ _ _ _ a)⟩
  · simp only [H]
    split_ifs
    exacts [.inr ⟨_, by simp, rfl⟩, q.2.2]
  · simp only [H]
    split_ifs
    · rw [hF₀, Homeomorph.symm_apply_apply]
    · rfl
  · simp only [H]
    split_ifs with haR
    · rw [hmem, Homeomorph.apply_symm_apply]
      exact hF₁ _
    · exact (hLR a).resolve_right haR

/-- **The van Kampen argument.** At some point of the Heegaard surface, the fundamental group of
the first handlebody surjects onto that of the manifold. The space is covered by the second
handlebody and the union `N` of the first with a neighbourhood `W` of the Heegaard surface in the
second; loops in `N` come from the first handlebody since `N` deformation retracts onto it, and
so do loops in the second handlebody. -/
private theorem exists_fundamentalGroup_map_left_surjective (hE : finrank ℝ E = 3) :
    ∃ x : s.left, Function.Surjective
      (FundamentalGroup.map (ContinuousMap.subtypeVal s.left) x) := by
  obtain ⟨e⟩ := s.nonempty_homeomorph_right
  obtain ⟨V, hVo, hVc, hSV, F, hF₀, hF₁, hFfix⟩ := exists_deformation_frontier_handlebody s.genus
  obtain ⟨eN, heN⟩ := s.exists_homotopyEquiv_left_union hE e hSV F hF₀ hF₁ hFfix
  have hWc : IsPathConnected ((↑) '' (e ⁻¹' V) : Set M) := by
    rw [← e.image_symm]
    exact (hVc.image e.symm.continuous).image continuous_subtype_val
  let W : Set M := (↑) '' (e ⁻¹' V)
  have hmemW (p : s.right) : (p : M) ∈ W ↔ e p ∈ V := Subtype.val_injective.mem_set_image
  have hLRW {p : M} (hpL : p ∈ s.left) (hpR : p ∈ s.right) : p ∈ W :=
    (hmemW ⟨p, hpR⟩).2 (hSV ((s.coe_mem_left_iff hE e ⟨p, hpR⟩).1 hpL))
  have hNR : (s.left ∪ W) ∩ s.right = W := by
    refine Subset.antisymm ?_ fun p hp ↦ ⟨.inr hp, Subtype.coe_image_subset _ _ hp⟩
    rintro p ⟨hpL | hpW, hpR⟩
    exacts [hLRW hpL hpR, hpW]
  have hcover : interior (s.left ∪ W) ∪ interior s.right = univ :=
    s.interior_union_interior_right_eq_univ
      (by rw [Subtype.val_injective.preimage_image]; exact hVo.preimage e.continuous)
      fun p hp ↦ hLRW hp.1 hp.2
  -- The base point: the point of the Heegaard surface over a point of the boundary surface.
  obtain ⟨y₀, hy₀, -⟩ := isPathConnected_frontier_handlebody s.genus
  let y : {y : handlebody s.genus | (y : ℂ × ℝ) ∈ frontier (handlebody s.genus)} :=
    ⟨⟨y₀, (isClosed_handlebody s.genus).frontier_subset hy₀⟩, hy₀⟩
  have hyL : ((e.symm y : s.right) : M) ∈ s.left := by
    rw [s.coe_mem_left_iff hE e, Homeomorph.apply_symm_apply]
    exact y.2
  refine ⟨⟨_, hyL⟩, MonoidHom.range_eq_top.1 (eq_top_iff.2 ?_)⟩
  have : PathConnectedSpace s.left :=
    s.nonempty_homeomorph_left.some.symm.toHomotopyEquiv.pathConnectedSpace
  have : PathConnectedSpace s.right := e.symm.toHomotopyEquiv.pathConnectedSpace
  refine (FundamentalGroup.range_map_subtypeVal_sup_eq_top hcover
    (isPathConnected_iff_pathConnectedSpace.2 eN.pathConnectedSpace)
    (isPathConnected_iff_pathConnectedSpace.2 inferInstance) (by rw [hNR]; exact hWc) (.inl hyL)
    (e.symm y).2).ge.trans (sup_le ?_ (s.range_map_right_le_range_map_left hE e y hyL))
  -- Loops in `N` come from the first handlebody.
  have hbij := eN.fundamentalGroup_map_bijective ⟨_, hyL⟩
  rw [heN] at hbij
  rintro _ ⟨γ, rfl⟩
  obtain ⟨δ, rfl⟩ := hbij.2 γ
  have h := DFunLike.congr_fun (_root_.FundamentalGroup.map_comp
    (ContinuousMap.subtypeVal (s.left ∪ W)) (ContinuousMap.inclusion subset_union_left)
    ⟨_, hyL⟩) δ
  rw [MonoidHom.comp_apply] at h
  -- The composite `(subtypeVal (s.left ∪ W)).comp (inclusion subset_union_left)` in `h` is
  -- `subtypeVal s.left` by definition; as the base point of the target group depends on the map,
  -- `h` is used up to this unfolding rather than rewritten.
  exact ⟨δ, h⟩

/-- **The fundamental group of the first handlebody of a Heegaard splitting surjects onto that of
the manifold.** For a Heegaard splitting of a manifold without boundary charted on a
three-dimensional real normed space, the inclusion of the first handlebody induces a surjection
of fundamental groups at every base point in it. -/
theorem fundamentalGroup_map_left_surjective (hE : finrank ℝ E = 3) (x : s.left) :
    Function.Surjective (FundamentalGroup.map (ContinuousMap.subtypeVal s.left) x) := by
  obtain ⟨x₀, hx₀⟩ := s.exists_fundamentalGroup_map_left_surjective hE
  have : PathConnectedSpace s.left :=
    s.nonempty_homeomorph_left.some.symm.toHomotopyEquiv.pathConnectedSpace
  exact FundamentalGroup.map_surjective_of_path _ (PathConnectedSpace.somePath x₀ x) hx₀

/-- **The fundamental group of the second handlebody of a Heegaard splitting surjects onto that of
the manifold.** For a Heegaard splitting of a manifold without boundary charted on a
three-dimensional real normed space, the inclusion of the second handlebody induces a surjection
of fundamental groups at every base point in it. -/
theorem fundamentalGroup_map_right_surjective (hE : finrank ℝ E = 3) (x : s.right) :
    Function.Surjective (FundamentalGroup.map (ContinuousMap.subtypeVal s.right) x) := by
  have h := s.symm.fundamentalGroup_map_left_surjective hE
  rw [symm_left] at h
  exact h x

include s in
/-- **The fundamental group of a manifold with a Heegaard splitting is finitely generated.** This
holds for a manifold without boundary charted on a three-dimensional real normed space, at every
base point. -/
theorem fg_fundamentalGroup (hE : finrank ℝ E = 3) (x : M) : Group.FG (FundamentalGroup M x) := by
  rcases (s.union_eq_univ ▸ mem_univ x : x ∈ s.left ∪ s.right) with hx | hx
  · obtain ⟨_, -⟩ := s.exists_fg_rank_le s.nonempty_homeomorph_left.some ⟨x, hx⟩
    exact Group.fg_of_surjective (s.fundamentalGroup_map_left_surjective hE ⟨x, hx⟩)
  · obtain ⟨_, -⟩ := s.exists_fg_rank_le s.nonempty_homeomorph_right.some ⟨x, hx⟩
    exact Group.fg_of_surjective (s.fundamentalGroup_map_right_surjective hE ⟨x, hx⟩)

/-- **The rank of the fundamental group is at most the genus of a Heegaard splitting.** For a
manifold without boundary charted on a three-dimensional real normed space, the fundamental group
is generated by as many elements as the genus of any Heegaard splitting, at every base point. -/
theorem rank_fundamentalGroup_le_genus (hE : finrank ℝ E = 3) (x : M)
    [Group.FG (FundamentalGroup M x)] : Group.rank (FundamentalGroup M x) ≤ s.genus := by
  rcases (s.union_eq_univ ▸ mem_univ x : x ∈ s.left ∪ s.right) with hx | hx
  · obtain ⟨_, hrank⟩ :=
      s.exists_fg_rank_le s.nonempty_homeomorph_left.some ⟨x, hx⟩
    exact (Group.rank_le_of_surjective (H := FundamentalGroup M x) _
      (s.fundamentalGroup_map_left_surjective hE ⟨x, hx⟩)).trans hrank
  · obtain ⟨_, hrank⟩ :=
      s.exists_fg_rank_le s.nonempty_homeomorph_right.some ⟨x, hx⟩
    exact (Group.rank_le_of_surjective (H := FundamentalGroup M x) _
      (s.fundamentalGroup_map_right_surjective hE ⟨x, hx⟩)).trans hrank

end HeegaardSplitting

/-- **The rank of the fundamental group is at most the Heegaard genus.** For a manifold without
boundary charted on a three-dimensional real normed space and admitting a Heegaard splitting, the
fundamental group is generated by as many elements as its Heegaard genus, at every base point.
Waldhausen's rank-versus-genus conjecture (`TauCeti.RankGenusConjecture`) asks for equality. -/
theorem rank_fundamentalGroup_le_heegaardGenus {E M : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace M] [ChartedSpace E M] (hE : finrank ℝ E = 3)
    [Nonempty (HeegaardSplitting M)] (x : M) [Group.FG (FundamentalGroup M x)] :
    Group.rank (FundamentalGroup M x) ≤ heegaardGenus M := by
  obtain ⟨s, hs⟩ := exists_genus_eq_heegaardGenus M
  exact hs ▸ s.rank_fundamentalGroup_le_genus hE x

end TauCeti
