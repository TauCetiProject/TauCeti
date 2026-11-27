/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Basic

/-!
# Right fibrations and equivalences

A right fibration `q : X ⟶ Y` lifts the horns `Λ[2, 2]` and `Λ[1, 1]`; in terms of edges and
`2`-simplices, it lifts composition triangles with two prescribed faces, and edges with
prescribed target. Lifting inverses this way shows that, when `X` is a quasicategory, `q`
reflects equivalences (Kerodon Proposition 4.4.2.11), and that `q` lifts equivalences of `Y`
with prescribed source (compare Kerodon Example 4.4.1.11).

## Main results

* `SSet.Edge.exists_compStruct_of_hasLiftingProperty_horn₂₂`,
  `SSet.Edge.exists_edge_of_hasLiftingProperty_horn₁₁`: lifting against `Λ[2, 2] ⟶ Δ[2]` and
  `Λ[1, 1] ⟶ Δ[1]`, in terms of edges and `2`-simplices.
* `SSet.Edge.isEquivalence_map_iff_of_rightFibration`: a right fibration from a quasicategory
  reflects equivalences.
* `SSet.RightFibration.hasLift_of_isEquivalence`: a right fibration lifts equivalences with
  prescribed source.

## References

* J. Lurie, *Kerodon*, Proposition 4.4.2.11 and Example 4.4.1.11.
-/

public section

open CategoryTheory Limits Simplicial Opposite

universe u

namespace SSet

variable {X Y : SSet.{u}}

namespace Edge

variable {x₀ x₁ x₂ : X _⦋0⦌}

/-- If `q : X ⟶ Y` has the right lifting property with respect to `Λ[2, 2] ⟶ Δ[2]`, edges
`e₁₂ : x₁ ⟶ x₂` and `e₀₂ : x₀ ⟶ x₂` of `X` lying over the faces `δ 0 s` and `δ 1 s` of a
`2`-simplex `s` of `Y` are two faces of a `2`-simplex of `X`, a composition structure
`e₀₁ ≫ e₁₂ = e₀₂`, whose third face `e₀₁ : x₀ ⟶ x₁` lies over `δ 2 s`. -/
lemma exists_compStruct_of_hasLiftingProperty_horn₂₂ (q : X ⟶ Y)
    [HasLiftingProperty Λ[2, 2].ι q] (e₁₂ : Edge x₁ x₂) (e₀₂ : Edge x₀ x₂) (s : Y _⦋2⦌)
    (h₀ : Y.δ 0 s = q.app _ e₁₂.edge) (h₁ : Y.δ 1 s = q.app _ e₀₂.edge) :
    ∃ e₀₁ : Edge x₀ x₁, Nonempty (CompStruct e₀₁ e₁₂ e₀₂) ∧ q.app _ e₀₁.edge = Y.δ 2 s := by
  obtain ⟨t, ht₁, ht₀⟩ := horn₂₂.isPushout.exists_desc (yonedaEquiv.symm e₀₂.edge)
    (yonedaEquiv.symm e₁₂.edge) (by
      rw [stdSimplex.δ_comp_yonedaEquiv_symm, stdSimplex.δ_comp_yonedaEquiv_symm, e₀₂.tgt_eq,
        e₁₂.tgt_eq])
  have sq : CommSq t Λ[2, 2].ι q (yonedaEquiv.symm s) := ⟨horn₂₂.isPushout.hom_ext
    (by rw [reassoc_of% ht₁, horn.ι_ι_assoc, yonedaEquiv_symm_comp,
      stdSimplex.δ_comp_yonedaEquiv_symm, h₁])
    (by rw [reassoc_of% ht₀, horn.ι_ι_assoc, yonedaEquiv_symm_comp,
      stdSimplex.δ_comp_yonedaEquiv_symm, h₀])⟩
  obtain ⟨σ, hσ⟩ := yonedaEquiv.symm.surjective sq.lift
  have hσ₁ : X.δ 1 σ = e₀₂.edge := yonedaEquiv.symm.injective (by
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, hσ, ← horn.ι_ι_assoc (n := 1) 2 1 (by decide),
      sq.fac_left, ht₁])
  have hσ₀ : X.δ 0 σ = e₁₂.edge := yonedaEquiv.symm.injective (by
    rw [← stdSimplex.δ_comp_yonedaEquiv_symm, hσ, ← horn.ι_ι_assoc (n := 1) 2 0 (by decide),
      sq.fac_left, ht₀])
  have hqσ : q.app _ σ = s := yonedaEquiv.symm.injective (by
    rw [← yonedaEquiv_symm_comp, hσ, sq.fac_right])
  have hsrc : X.δ 1 (X.δ 2 σ) = x₀ := by
    rw [← e₀₂.src_eq, ← hσ₁]
    exact (δ_comp_δ_self_apply (i := 1) σ).symm
  have htgt : X.δ 0 (X.δ 2 σ) = x₁ := by
    rw [← e₁₂.src_eq, ← hσ₀]
    exact δ_comp_δ_apply (i := 0) (j := 1) (by decide) σ
  exact ⟨Edge.mk (X.δ 2 σ) hsrc htgt, ⟨CompStruct.mk σ rfl hσ₀ hσ₁⟩,
    (δ_naturality_apply q 2 σ).trans (by rw [hqσ])⟩

/-- If `q : X ⟶ Y` has the right lifting property with respect to `Λ[1, 1] ⟶ Δ[1]`, every edge
of `Y` ending at the image of a vertex `x` of `X` is the image of an edge of `X` ending at `x`. -/
lemma exists_edge_of_hasLiftingProperty_horn₁₁ (q : X ⟶ Y) [HasLiftingProperty Λ[1, 1].ι q]
    (x : X _⦋0⦌) (f : Y _⦋1⦌) (hf : Y.δ 0 f = q.app _ x) :
    ∃ g : X _⦋1⦌, X.δ 0 g = x ∧ q.app _ g = f := by
  have hc : horn.IsCompatible (fun (j : Fin 2) (_ : j ≠ 1) ↦ yonedaEquiv.symm x) :=
    (horn.isCompatible_zero_iff_true _).2 trivial
  have sq : CommSq hc.desc Λ[1, 1].ι q (yonedaEquiv.symm f) := ⟨horn.hom_ext' fun j hj ↦ by
    obtain rfl : j = 0 := by fin_cases j <;> simp_all
    rw [hc.ι_desc_assoc, horn.ι_ι_assoc, yonedaEquiv_symm_comp,
      stdSimplex.δ_comp_yonedaEquiv_symm, hf]⟩
  obtain ⟨g, hg⟩ := yonedaEquiv.symm.surjective sq.lift
  refine ⟨g, yonedaEquiv.symm.injective ?_, yonedaEquiv.symm.injective ?_⟩
  · rw [← stdSimplex.δ_comp_yonedaEquiv_symm, hg, ← horn.ι_ι_assoc (n := 0) 1 0 (by decide),
      sq.fac_left, hc.ι_desc]
  · rw [← yonedaEquiv_symm_comp, hg, sq.fac_right]

/-- If `q` lifts `Λ[2, 2]`, an edge `e : x₀ ⟶ x₁` of `X` whose image is an equivalence has a
right inverse `v` up to a `2`-simplex, with `v ≫ e = id x₁`, whose image is again an
equivalence. -/
private lemma exists_compStruct_id_of_isEquivalence_map (q : X ⟶ Y)
    [HasLiftingProperty Λ[2, 2].ι q] {e : Edge x₀ x₁} (he : (e.map q).IsEquivalence) :
    ∃ v : Edge x₁ x₀, Nonempty (CompStruct v e (id x₁)) ∧ (v.map q).IsEquivalence := by
  let I := he.invStruct
  obtain ⟨v, hv, hqv⟩ := exists_compStruct_of_hasLiftingProperty_horn₂₂ q e (id x₁)
    I.invHomId.simplex (by rw [I.invHomId.d₀, map_edge]) (by rw [I.invHomId.d₁, ← map_id x₁ q,
      map_edge])
  refine ⟨v, hv, (isEquivalence_iff_of_edge_eq (e' := I.inv) ?_).2
    (InvStruct.isEquivalence { inv := e.map q, homInvId := I.invHomId, invHomId := I.homInvId })⟩
  rw [map_edge, hqv, I.invHomId.d₂]

/-- **Right fibrations reflect equivalences** (Kerodon Proposition 4.4.2.11): for a right
fibration `q : X ⟶ Y` whose source is a quasicategory, an edge of `X` is an equivalence exactly
when its image in `Y` is. -/
theorem isEquivalence_map_iff_of_rightFibration [Quasicategory X] (q : X ⟶ Y)
    [RightFibration q] (e : Edge x₀ x₁) : (e.map q).IsEquivalence ↔ e.IsEquivalence := by
  open Truncated.HomotopyCategory₂ in
  refine ⟨fun he ↦ ?_, fun he ↦ he.map q⟩
  have := (rightFibration_iff_hasLiftingProperty q).1 inferInstance (2 : Fin 3) (by decide)
  -- Lifting twice gives `v ≫ e = id` and `w ≫ v = id`, so in the homotopy category `v` has a left
  -- and a right inverse, and `e` is its inverse.
  obtain ⟨v, ⟨c₁⟩, hv⟩ := exists_compStruct_id_of_isEquivalence_map q he
  obtain ⟨w, ⟨c₂⟩, -⟩ := exists_compStruct_id_of_isEquivalence_map q hv
  have h₁ : homMk v.toTruncated ≫ homMk e.toTruncated = 𝟙 _ := by
    rw [c₁.toTruncated.homotopyCategory₂_fac, toTruncated_id]
    exact homMk_id (.mk _)
  have h₂ : homMk w.toTruncated ≫ homMk v.toTruncated = 𝟙 _ := by
    rw [c₂.toTruncated.homotopyCategory₂_fac, toTruncated_id]
    exact homMk_id (.mk _)
  have hwe : homMk w.toTruncated = homMk e.toTruncated := by
    rw [← Category.comp_id (homMk w.toTruncated), ← h₁, ← Category.assoc, h₂, Category.id_comp]
  rw [isEquivalence_iff_isIso]
  exact ⟨homMk v.toTruncated, by rw [← hwe, h₂], h₁⟩

end Edge

open Edge

/-- **Right fibrations lift equivalences with prescribed source** (compare Kerodon
Example 4.4.1.11): for a right fibration `q : X ⟶ Y`, a commutative square from the inclusion
`Λ[1, 0] ⟶ Δ[1]` of the vertex `0` to `q` has a lift when its bottom edge is an equivalence. -/
theorem RightFibration.hasLift_of_isEquivalence (q : X ⟶ Y) [RightFibration q]
    {t : (Λ[1, 0] : SSet) ⟶ X} {b : Δ[1] ⟶ Y} (sq : CommSq t Λ[1, 0].ι q b)
    (hb : (Edge.mk' (yonedaEquiv b)).IsEquivalence) : sq.HasLift := by
  have := (rightFibration_iff_hasLiftingProperty q).1 inferInstance (1 : Fin 2) (by decide)
  have := (rightFibration_iff_hasLiftingProperty q).1 inferInstance (2 : Fin 3) (by decide)
  -- Lift an inverse `g` of the edge `e` given by `b` to an edge ending at the vertex `x` given by
  -- `t`, then lift the `2`-simplex exhibiting `e ≫ g = id` to a `2`-simplex of `X` with faces the
  -- lift of `g` and `id x`: its remaining face is a lift of `e` starting at `x`.
  let x := yonedaEquiv (horn.ι 0 1 (by decide) ≫ t)
  have hx : Y.δ 1 (yonedaEquiv b) = q.app _ x := by
    rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc (n := 0) 0 1 (by decide), ← sq.w,
      ← Category.assoc, yonedaEquiv_comp]
  let e : Edge (q.app _ x) (Y.δ 0 (yonedaEquiv b)) := Edge.mk (yonedaEquiv b) hx rfl
  let I := ((isEquivalence_iff_of_edge_eq (e := Edge.mk' (yonedaEquiv b)) (e' := e) rfl).1
    hb).invStruct
  obtain ⟨g, hg₀, hgq⟩ := exists_edge_of_hasLiftingProperty_horn₁₁ q x I.inv.edge I.inv.tgt_eq
  obtain ⟨e', -, he'⟩ := exists_compStruct_of_hasLiftingProperty_horn₂₂ q (Edge.mk g rfl hg₀)
    (Edge.id x) I.homInvId.simplex (by rw [I.homInvId.d₀]; exact hgq.symm)
    (by rw [I.homInvId.d₁, ← map_id x q, map_edge])
  refine ⟨⟨{ l := yonedaEquiv.symm e'.edge, fac_left := ?_, fac_right := ?_ }⟩⟩
  · refine horn.hom_ext' fun j hj ↦ ?_
    obtain rfl : j = 1 := by fin_cases j <;> simp_all
    rw [horn.ι_ι_assoc, stdSimplex.δ_comp_yonedaEquiv_symm, e'.src_eq]
    exact yonedaEquiv.symm_apply_apply _
  · rw [yonedaEquiv_symm_comp, he', I.homInvId.d₂]
    exact yonedaEquiv.symm_apply_apply b

end SSet
