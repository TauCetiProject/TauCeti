/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Core
public import TauCeti.AlgebraicTopology.Quasicategory.Slice

/-!
# Joyal's theorem on special outer horns

In a quasicategory `C`, the outer horns `Λ[n + 2, 0]` cannot be filled in general, but they can
when their initial edge, from `0` to `1`, is an equivalence. Conversely, an edge all of whose
outer horns `Λ[n + 2, 0]` can be filled is an equivalence (HTT Proposition 1.2.4.3). Together
with its dual for the horns `Λ[n + 2, n + 2]`, which is not proved here, this is the input for
showing that the core of a quasicategory and its right mapping spaces are Kan complexes.

The proof follows Kerodon: under the isomorphism `Δ[1] ⋆ Δ[n] ≅ Δ[n + 2]`, the horn
`Λ[n + 2, 0]` is the pushout-join `(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n])`, so filling it amounts to
lifting an edge, with prescribed source, along the restriction of cones
`C_{/σ} ⟶ C_{/∂σ}` for the face `σ : Δ[n] ⟶ C` opposite to the vertices `0` and `1`. This
restriction is a right fibration, and right fibrations lift equivalences with prescribed source.
The edge to be lifted is an equivalence because its image in `C` is, and the projection
`C_{/∂σ} ⟶ C` is a right fibration, which reflects equivalences.

## Main results

* `SSet.Edge.exists_compStruct_of_hasLiftingProperty_horn₂₂`,
  `SSet.Edge.exists_edge_of_hasLiftingProperty_horn₁₁`: lifting against `Λ[2, 2] ⟶ Δ[2]` and
  `Λ[1, 1] ⟶ Δ[1]`, in terms of edges and `2`-simplices.
* `SSet.Edge.isEquivalence_map_iff_of_rightFibration`: a right fibration from a quasicategory
  reflects equivalences.
* `SSet.RightFibration.hasLift_of_isEquivalence`: a right fibration lifts equivalences with
  prescribed source.
* `SSet.slice.hasLift_of_isEquivalence`: for a monomorphism `j : L ⟶ K`, the restriction of
  cones `C_{/p} ⟶ C_{/j ≫ p}` lifts, with prescribed source, every edge whose image in `C` is an
  equivalence.
* `SSet.Quasicategory.hornFilling_zero`: **Joyal's theorem**, a horn `Λ[n + 2, 0]` in a
  quasicategory whose initial edge is an equivalence can be filled.
* `SSet.Edge.isEquivalence_iff_hornFilling_zero`: an edge of a quasicategory is an equivalence
  exactly when every horn `Λ[n + 2, 0]` with that initial edge can be filled.

## References

* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), Theorem 1.3.
* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6, Proposition 4.4.2.11, Proposition 4.4.2.13 and
  Example 4.4.1.11.
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
`2`-simplex `s` of `Y` are two faces of a `2`-simplex of `X` over `s`. Its third face is an
edge `x₀ ⟶ x₁` over `δ 2 s`. -/
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

namespace slice

variable {K L C : SSet.{u}}

/-- For a quasicategory `C`, a diagram `p : K ⟶ C` and a monomorphism `j : L ⟶ K`, **the
restriction of cones `C_{/p} ⟶ C_{/j ≫ p}` lifts, with prescribed source, every edge whose image
in `C` is an equivalence**: a commutative square from `Λ[1, 0] ⟶ Δ[1]` to it has a lift when the
edge of `C` underlying its bottom edge is an equivalence. Through the universal property of the
slice, maps `(Λ[1, 0] ⋆ K) ∪ (Δ[1] ⋆ L) ⟶ C` extend to `Δ[1] ⋆ K` when their edge `Δ[1] ⟶ C` is an
equivalence. -/
theorem hasLift_of_isEquivalence [Quasicategory C] (p : K ⟶ C) (j : L ⟶ K) [Mono j]
    {t : (Λ[1, 0] : SSet) ⟶ slice p} {b : Δ[1] ⟶ slice (j ≫ p)}
    (sq : CommSq t Λ[1, 0].ι (map j (𝟙 C) (by simp)) b)
    (hb : (Edge.mk' (yonedaEquiv (b ≫ π (j ≫ p)))).IsEquivalence) : sq.HasLift :=
  RightFibration.hasLift_of_isEquivalence _ sq
    ((isEquivalence_map_iff_of_rightFibration (π (j ≫ p)) _).1
      ((isEquivalence_iff_of_edge_eq (by rw [map_edge, mk'_edge, mk'_edge, yonedaEquiv_comp])).2
        hb))

end slice

namespace Quasicategory

variable {C : SSet.{u}}

/-- Under `Δ[1] ⋆ Δ[n] ≅ Δ[n + 2]`, the horn `Λ[n + 2, 0]` is the pushout-join
`(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n])`: a horn `Λ[N, 0]`, `2 ≤ N`, whose initial edge is an
equivalence extends along it by `SSet.slice.hasLift_of_isEquivalence` for `∂Δ[n] ⟶ Δ[n]`. -/
private lemma hornFilling_zero_aux [Quasicategory C] (N : ℕ) (hN : 2 ≤ N)
    (σ₀ : (Λ[N, 0] : SSet) ⟶ C) (H : Finset.card {(0 : Fin (N + 1)), 0, 1} ≤ N)
    (h : (Edge.mk' (σ₀.app _ (horn.edge N 0 0 1 (Fin.zero_le _) H))).IsEquivalence) :
    ∃ σ : Δ[N] ⟶ C, σ₀ = Λ[N, 0].ι ≫ σ := by
  obtain ⟨n, rfl⟩ : ∃ n, N = 1 + n + 1 := ⟨N - 2, by omega⟩
  let E := join.stdSimplexIso 1 n
  let U := Subcomplex.unionJoin Λ[1, 0] ∂Δ[n]
  have hU : U.preimage E.inv = Λ[1 + n + 1, 0] := by
    rw [join.preimage_unionJoin_horn_boundary n one_ne_zero 0, Fin.castLE_zero]
  have hle : U ≤ Λ[1 + n + 1, 0].preimage E.hom := by
    rw [← hU, ← Subcomplex.preimage_comp, E.hom_inv_id, Subcomplex.preimage_id]
  -- The isomorphism `E` restricts to inverse maps `φ` and `ψ` between `U` and the horn.
  let φ : (U : SSet) ⟶ Λ[1 + n + 1, 0] :=
    Subcomplex.homOfLE hle ≫ Subcomplex.fromPreimage _ E.hom
  have hφ : φ ≫ Λ[1 + n + 1, 0].ι = U.ι ≫ E.hom := by simp [φ]
  let ψ : (Λ[1 + n + 1, 0] : SSet) ⟶ U :=
    Subcomplex.homOfLE hU.ge ≫ Subcomplex.fromPreimage _ E.inv
  have hψ : ψ ≫ U.ι = Λ[1 + n + 1, 0].ι ≫ E.inv := by simp [ψ]
  have hψφ : ψ ≫ φ = 𝟙 _ := by
    rw [← cancel_mono Λ[1 + n + 1, 0].ι, Category.assoc, hφ, reassoc_of% hψ, E.inv_hom_id,
      Category.comp_id, Category.id_comp]
  -- The two pieces `a` and `b` of `φ ≫ σ₀` on `Λ[1, 0] ⋆ Δ[n]` and `Δ[1] ⋆ ∂Δ[n]`, a vertex
  -- `A` of `C_{/p}` for the face `p : Δ[n] ⟶ C` and an edge `B` of `C_{/∂p}` from its restriction.
  have hpush := Subcomplex.unionJoin.isPushout Λ[1, 0] ∂Δ[n]
  let a := Subcomplex.unionJoin.ι₁ Λ[1, 0] ∂Δ[n] ≫ φ ≫ σ₀
  let b := Subcomplex.unionJoin.ι₂ Λ[1, 0] ∂Δ[n] ≫ φ ≫ σ₀
  let p := join.inr _ _ ≫ a
  have hw : join.map (𝟙 _) ∂Δ[n].ι ≫ a = join.map Λ[1, 0].ι (𝟙 _) ≫ b := hpush.w_assoc _
  have hb : join.inr _ _ ≫ b = ∂Δ[n].ι ≫ p := by
    calc join.inr _ _ ≫ b = join.inr _ _ ≫ join.map Λ[1, 0].ι (𝟙 _) ≫ b := by
          rw [join.inr_map_assoc, Category.id_comp]
      _ = ∂Δ[n].ι ≫ p := by rw [← hw, join.inr_map_assoc]
  let A : (Λ[1, 0] : SSet) ⟶ slice p := slice.homEquiv.symm ⟨a, rfl⟩
  let B : Δ[1] ⟶ slice (∂Δ[n].ι ≫ p) := slice.homEquiv.symm ⟨b, hb⟩
  have sq : CommSq A Λ[1, 0].ι (slice.map ∂Δ[n].ι (𝟙 C) (by simp)) B :=
    ⟨slice.hom_ext (by
      rw [slice.homEquiv_comp_map_coe, slice.homEquiv_comp_coe, Equiv.apply_symm_apply,
        Equiv.apply_symm_apply, Category.comp_id, hw])⟩
  -- The edge underlying `B` is the initial edge of `σ₀`.
  have hB : (Edge.mk' (yonedaEquiv (B ≫ slice.π (∂Δ[n].ι ≫ p)))).IsEquivalence := by
    have hedge : yonedaEquiv (join.inl _ _ ≫ Subcomplex.unionJoin.ι₂ Λ[1, 0] ∂Δ[n] ≫ φ) =
        horn.edge (1 + n + 1) 0 0 1 (Fin.zero_le _) H := by
      refine injective_of_mono (Subcomplex.ι.{u} Λ[1 + n + 1, 0] |>.app _) ?_
      rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, hφ,
        Subcomplex.unionJoin.ι₂_ι_assoc, join.inl_map_assoc, Category.id_comp]
      simp only [Subfunctor.ι_app]
      refine stdSimplex.ext _ _ fun j ↦ ?_
      rw [join.yonedaEquiv_inl_comp_stdSimplexIso_hom]
      fin_cases j <;> rfl
    refine (isEquivalence_iff_of_edge_eq ?_).1 h
    rw [mk'_edge, mk'_edge, slice.comp_π, Equiv.apply_symm_apply, ← hedge, ← yonedaEquiv_comp]
    simp only [b, Category.assoc]
  have := slice.hasLift_of_isEquivalence p ∂Δ[n].ι sq hB
  let τ := (slice.homEquiv sq.lift).1
  have hτ : U.ι ≫ τ = φ ≫ σ₀ := hpush.hom_ext
    (by
      rw [Subcomplex.unionJoin.ι₁_ι_assoc, ← slice.homEquiv_comp_coe, sq.fac_left,
        Equiv.apply_symm_apply])
    (by
      have h := congrArg (fun F ↦ (slice.homEquiv F).1) sq.fac_right
      rw [slice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
      rw [Subcomplex.unionJoin.ι₂_ι_assoc, h])
  exact ⟨E.inv ≫ τ, by rw [← reassoc_of% hψ, hτ, ← Category.assoc, hψφ, Category.id_comp]⟩

/-- **Joyal's theorem on special outer horns** (HTT Proposition 1.2.4.3): in a quasicategory, a
horn `Λ[n + 2, 0]` whose initial edge, from `0` to `1`, is an equivalence can be filled. -/
theorem hornFilling_zero [Quasicategory C] {n : ℕ} (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C)
    (h : (Edge.mk' (σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)))).IsEquivalence) :
    ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ :=
  hornFilling_zero_aux (n + 2) (by omega) σ₀ _ h

end Quasicategory

namespace Edge

variable {C : SSet.{u}}

/-- A compatible family of faces of `Λ[n + 2, 0]` whose induced horn can be filled consists of
the faces of an `(n + 2)`-simplex. -/
private lemma exists_δ_eq_of_isCompatible {n : ℕ}
    {f : ∀ j : Fin (n + 3), j ≠ 0 → (Δ[n + 1] ⟶ C)} (hf : horn.IsCompatible f)
    (h : ∃ σ : Δ[n + 2] ⟶ C, hf.desc = Λ[n + 2, 0].ι ≫ σ) :
    ∃ w : C _⦋n + 2⦌, ∀ j hj, C.δ j w = yonedaEquiv (f j hj) := by
  obtain ⟨σ, hσ⟩ := h
  refine ⟨yonedaEquiv σ, fun j hj ↦ ?_⟩
  rw [← stdSimplex.yonedaEquiv_δ_comp, ← horn.ι_ι_assoc 0 j hj, ← hσ, hf.ι_desc]

/-- The horn induced by a compatible family sends a simplex `g` of the face `j` to the
corresponding simplex `g ≫ f j hj`. -/
private lemma isCompatible_desc_app {n : ℕ} {f : ∀ j : Fin (n + 3), j ≠ 0 → (Δ[n + 1] ⟶ C)}
    (hf : horn.IsCompatible f) (j : Fin (n + 3)) (hj : j ≠ 0) {d : ℕ} (g : Δ[d] ⟶ Δ[n + 1]) :
    hf.desc.app _ ((horn.ι 0 j hj).app _ (yonedaEquiv g)) = yonedaEquiv (g ≫ f j hj) := by
  rw [← yonedaEquiv_comp, ← yonedaEquiv_comp, Category.assoc, hf.ι_desc]

/-- The initial edge of `Λ[2, 0]` is the edge of its face `2`. -/
private lemma horn_edge_two :
    horn.edge.{u} 2 0 0 1 (Fin.zero_le _) (by simp) =
      (horn.ι 0 2 (by decide)).app _ (yonedaEquiv (𝟙 Δ[1])) := by
  refine injective_of_mono (Subcomplex.ι.{u} Λ[2, 0] |>.app _) ?_
  rw [← NatTrans.comp_app_apply, horn.ι_ι]
  refine stdSimplex.ext _ _ fun j ↦ ?_
  fin_cases j <;> rfl

/-- The initial edge of `Λ[3, 0]` is the edge `δ 2` of its face `3`. -/
private lemma horn_edge_three :
    horn.edge.{u} 3 0 0 1 (Fin.zero_le _) (by simp) =
      (horn.ι 0 3 (by decide)).app _ (yonedaEquiv (stdSimplex.δ 2)) := by
  refine injective_of_mono (Subcomplex.ι.{u} Λ[3, 0] |>.app _) ?_
  rw [← NatTrans.comp_app_apply, horn.ι_ι]
  refine stdSimplex.ext _ _ fun j ↦ ?_
  fin_cases j <;> rfl

/-- **Joyal's characterization of equivalences by special outer horns** (HTT Proposition
1.2.4.3): an edge `e` of a quasicategory is an equivalence exactly when every horn
`Λ[n + 2, 0]` whose initial edge is `e` can be filled. -/
theorem isEquivalence_iff_hornFilling_zero [Quasicategory C] {x y : C _⦋0⦌} (e : Edge x y) :
    e.IsEquivalence ↔ ∀ (n : ℕ) (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ C),
      σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = e.edge →
        ∃ σ : Δ[n + 2] ⟶ C, σ₀ = Λ[n + 2, 0].ι ≫ σ := by
  refine ⟨fun he n σ₀ h ↦ Quasicategory.hornFilling_zero σ₀
    ((isEquivalence_iff_of_edge_eq (e := mk' _) (e' := e) h).2 he), fun H ↦ ?_⟩
  -- A right inverse `g`, from the horn `Λ[2, 0]` with faces `e` (from `0` to `1`) and `id x`
  -- (from `0` to `2`).
  let f : ∀ j : Fin 3, j ≠ 0 → (Δ[1] ⟶ C) := fun j _ ↦
    ![yonedaEquiv.symm e.edge, yonedaEquiv.symm (id x).edge, yonedaEquiv.symm e.edge] j
  have hf : horn.IsCompatible f := by
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢
    simp [f, stdSimplex.δ_comp_yonedaEquiv_symm, -id_edge]
  obtain ⟨w, hw⟩ := exists_δ_eq_of_isCompatible hf (H 0 hf.desc (by
    rw [horn_edge_two, isCompatible_desc_app, Category.id_comp]
    exact yonedaEquiv.apply_symm_apply _))
  have hw₁ : C.δ 1 w = (id x).edge := by simpa [f, -id_edge] using hw 1 (by decide)
  have hw₂ : C.δ 2 w = e.edge := by simpa [f] using hw 2 (by decide)
  have hsrc : C.δ 1 (C.δ 0 w) = y := by
    rw [← e.tgt_eq, ← hw₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) w).symm
  have htgt : C.δ 0 (C.δ 0 w) = x := by
    rw [← (id x).tgt_eq, ← hw₁]
    exact δ_comp_δ_self_apply (i := 0) w
  let g : Edge y x := Edge.mk (C.δ 0 w) hsrc htgt
  let c₁ : CompStruct e g (id x) := CompStruct.mk w hw₂ rfl hw₁
  -- `g` is also a left inverse, from the horn `Λ[3, 0]` with faces `id x ≫ e = e` (on `0, 2, 3`),
  -- `e ≫ id y = e` (on `0, 1, 3`) and `e ≫ g = id x` (on `0, 1, 2`).
  let f' : ∀ j : Fin 4, j ≠ 0 → (Δ[2] ⟶ C) := fun j _ ↦
    ![yonedaEquiv.symm c₁.simplex, yonedaEquiv.symm (CompStruct.idComp e).simplex,
      yonedaEquiv.symm (CompStruct.compId e).simplex, yonedaEquiv.symm c₁.simplex] j
  have hf' : horn.IsCompatible f' := by
    have h₂ : Fin.castPred (2 : Fin 4) (by decide) = 2 := rfl
    rw [horn.isCompatible_iff]
    intro j k hj hk hjk
    fin_cases j <;> fin_cases k <;> simp at hj hk hjk ⊢ <;>
      simp [f', c₁, g, h₂, stdSimplex.δ_comp_yonedaEquiv_symm, -id_edge,
        -CompStruct.idComp_simplex, -CompStruct.compId_simplex]
  obtain ⟨w', hw'⟩ := exists_δ_eq_of_isCompatible hf' (H 1 hf'.desc (by
    rw [horn_edge_three, isCompatible_desc_app]
    simp [f', c₁, stdSimplex.δ_comp_yonedaEquiv_symm, hw₂]))
  have hw'₁ : C.δ 1 w' = (CompStruct.idComp e).simplex := by
    simpa [f', -CompStruct.idComp_simplex] using hw' 1 (by decide)
  have hw'₂ : C.δ 2 w' = (CompStruct.compId e).simplex := by
    simpa [f', -CompStruct.compId_simplex] using hw' 2 (by decide)
  have hw'₃ : C.δ 3 w' = c₁.simplex := by simpa [f'] using hw' 3 (by decide)
  have h₂ : C.δ 2 (C.δ 0 w') = g.edge := by
    rw [← c₁.d₀, ← hw'₃]
    exact (δ_comp_δ_apply (i := 0) (j := 2) (by decide) w').symm
  have h₀ : C.δ 0 (C.δ 0 w') = e.edge := by
    rw [← (CompStruct.idComp e).d₀, ← hw'₁]
    exact δ_comp_δ_self_apply (i := 0) w'
  have h₁ : C.δ 1 (C.δ 0 w') = (id y).edge := by
    rw [← (CompStruct.compId e).d₀, ← hw'₂]
    exact (δ_comp_δ_apply (i := 0) (j := 1) (by decide) w').symm
  exact InvStruct.isEquivalence
    { inv := g, homInvId := c₁, invHomId := CompStruct.mk (C.δ 0 w') h₂ h₀ h₁ }

end Edge

end SSet
