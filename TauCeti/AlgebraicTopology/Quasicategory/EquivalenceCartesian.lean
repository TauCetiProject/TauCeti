/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian
public import TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic

/-!
# Equivalences are the edges Cartesian over a point

Let `X` be a quasicategory and `f : x ⟶ y` an edge of `X`. The following are equivalent
(HTT Proposition 2.4.1.5 over a point, Joyal):

* `f` is an equivalence;
* the restriction of cones `X_{/f} ⟶ X_{/y}` is a trivial fibration, that is, has the right
  lifting property with respect to all monomorphisms;
* `f` is Cartesian for the map from `X` to a terminal simplicial set.

The second and the third conditions agree for every simplicial set `X`
(`SSet.Edge.isCartesian_iff_rlp_slice_map`, in `TauCeti.AlgebraicTopology.Quasicategory.Cartesian`):
over a terminal simplicial set `S` every slice of `S` is terminal (`SSet.slice.isTerminal`), so
the map `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` defining Cartesian edges is the restriction of
cones `X_{/f} ⟶ X_{/y}` followed by an isomorphism.

For the first two, a lifting problem of the boundary inclusion `∂Δ[n] ⟶ Δ[n]` against
`X_{/f} ⟶ X_{/y}` is, by the universal property of the slice, an extension problem for maps into
`X` along `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1]) ⟶ Δ[n] ⋆ Δ[1]`, where `Λ[1, 1]` is the target vertex
of `Δ[1]`. Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]` this is the horn inclusion
`Λ[n + 2, n + 2] ⟶ Δ[n + 2]` (`SSet.join.preimage_unionJoin_boundary_horn`), and the final edge of
the horn, from `n + 1` to `n + 2`, is `f`. By Mathlib's description of the trivial fibrations
as the maps lifting against boundary inclusions (`SSet.rlp_monomorphisms`), the restriction of
cones is a trivial fibration exactly when all these horns can be filled, which by Joyal's
characterization of equivalences (`SSet.Edge.isEquivalence_iff_hornFilling_last`) means that `f`
is an equivalence. This reduction of outer horn filling to lifting against a restriction of cones,
through the identification of the horn with a pushout-join, is the method of Kerodon's proof of
Joyal's theorem (Kerodon Theorem 4.4.2.6), used in the same way in
`TauCeti.AlgebraicTopology.Quasicategory.OuterHorn.Basic`.

The same identification, applied to the relative restriction of cones
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` of a map `p : X ⟶ S`, gives the horn criterion for
Cartesian edges: an edge `f` is `p`-Cartesian as soon as the horns `Λ[n + 2, n + 2]` whose final
edge is `f` lift along `p` over every `(n + 2)`-simplex of `S` (HTT Remark 2.4.1.4). Reversing
simplices through `SSet.horn.opIso` gives the dual criterion for coCartesian edges, with the horns
`Λ[n + 2, 0]` whose initial edge is `f`. For instance, these criteria show that strongly
coCartesian morphisms of ordinary categories give coCartesian edges of nerves
(`TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Nerve`).

## Main results

* `SSet.Edge.isCartesian_of_hornFilling_last`, `SSet.Edge.isCoCartesian_of_hornFilling_zero`: the
  horn criteria for `p`-Cartesian and `p`-coCartesian edges.

* `SSet.Edge.isEquivalence_iff_rlp_slice_map`: an edge `f : x ⟶ y` of a quasicategory is an
  equivalence exactly when the restriction of cones `X_{/f} ⟶ X_{/y}` is a trivial fibration.
* `SSet.Edge.isEquivalence_iff_isCartesian`: **an edge of a quasicategory is an equivalence
  exactly when it is Cartesian over a point.**
* `SSet.Edge.isCartesian_of_kanComplex`, `CategoryTheory.nerve.isCartesian_edgeMk_iff`,
  `SSet.stdSimplex.not_isCartesian_of_lt`: every edge of a Kan complex, for example of the nerve
  of a groupoid, is Cartesian over a point; an edge of the nerve of a category is Cartesian over
  a point exactly when its morphism is an isomorphism; and an edge of `Δ[n]` between distinct
  vertices, such as the edge from `0` to `1` of `Δ[1]`, is not.

## References

* J. Lurie, *Higher Topos Theory*, Proposition 1.2.4.3, Proposition 2.4.1.5, Remark 2.4.1.4 and
  Remark 2.4.1.9.
* A. Joyal, *Quasi-categories and Kan complexes*, J. Pure Appl. Algebra 175 (2002), Theorem 1.3.
* J. Lurie, *Kerodon*, Theorem 4.4.2.6 (the pushout-join description of outer horns, used for the
  equivalence of the first two conditions).
-/

public section

open CategoryTheory Limits MorphismProperty Simplicial

universe v u

namespace SSet

namespace Edge

variable {X : SSet.{u}}

section boundary

/-! ### Lifting boundaries against the restriction of cones to the target -/

variable (n : ℕ)

/-- Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]`, the pushout-join `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1])` is the
horn `Λ[n + 2, n + 2]`. -/
private lemma preimage_unionJoin_eq :
    (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).preimage (join.stdSimplexIso.{u} n 1).inv =
      Λ[n + 2, Fin.last (n + 2)] := by
  rw [join.preimage_unionJoin_boundary_horn n one_ne_zero 1]
  -- The horn vertex `Fin.cast _ (Fin.natAdd (n + 1) 1)` of `Δ[n + 1 + 1]` is `Fin.last (n + 2)`
  -- by definition, `n + 1 + 1` and `n + 2` being definitionally equal.
  rfl

/-- The isomorphism of the pushout-join `(∂Δ[n] ⋆ Δ[1]) ∪ (Δ[n] ⋆ Λ[1, 1])` with the horn
`Λ[n + 2, n + 2]`. -/
private noncomputable def unionJoinIso :
    (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1] : SSet.{u}) ≅ Λ[n + 2, Fin.last (n + 2)] :=
  Subcomplex.isoOfPreimageEq (join.stdSimplexIso n 1) (preimage_unionJoin_eq n)

/-- Under the isomorphism with the horn, the edge `Δ[1]` of the pushout-join is the final edge of
`Λ[n + 2, n + 2]`, from `n + 1` to `n + 2`. -/
private lemma yonedaEquiv_inr_comp_unionJoinIso_hom :
    yonedaEquiv (join.inr (∂Δ[n] : SSet.{u}) Δ[1] ≫
        Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] ≫ (unionJoinIso n).hom) =
      horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
        (Fin.le_last _) (by simp) := by
  refine injective_of_mono (Subcomplex.ι.{u} Λ[n + 2, Fin.last (n + 2)] |>.app _) ?_
  rw [← yonedaEquiv_comp, Category.assoc, Category.assoc, unionJoinIso,
    Subcomplex.isoOfPreimageEq_hom_ι, Subcomplex.unionJoin.ι₁_ι_assoc, join.inr_map_assoc,
    Category.id_comp]
  refine stdSimplex.ext _ _ fun j ↦ ?_
  rw [join.yonedaEquiv_inr_comp_stdSimplexIso_hom]
  fin_cases j <;> rfl

variable {n}

/-- Horn filling over `S` gives the extensions of cones `Δ[n] ⋆ Δ[1] ⟶ X` that the map
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` lifts. Let `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` be a cone over the edge
`f` given by `s` and `B : Δ[n] ⋆ Δ[0] ⟶ X` a cone agreeing with `A` on `∂Δ[n] ⋆ Δ[0]`, both lying
under `C : Δ[n] ⋆ Δ[1] ⟶ S`. Under `Δ[n] ⋆ Δ[1] ≅ Δ[n + 2]`, they glue to a horn
`Λ[n + 2, n + 2]` with final edge `s` over `C`, and a filler over `C` is the required
extension. -/
private lemma exists_lift_join_of_hornFilling {S : SSet.{u}} (p : X ⟶ S) (s : X _⦋1⦌)
    (H : ∀ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ)
    (A : join (∂Δ[n] : SSet.{u}) Δ[1] ⟶ X) (B : join Δ[n] Δ[0] ⟶ X) (C : join Δ[n] Δ[1] ⟶ S)
    (hA : join.inr _ _ ≫ A = yonedaEquiv.symm s)
    (hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ B)
    (hAC : A ≫ p = join.map ∂Δ[n].ι (𝟙 _) ≫ C)
    (hBC : B ≫ p = join.map (𝟙 _) (stdSimplex.δ 0) ≫ C) :
    ∃ L : join Δ[n] Δ[1] ⟶ X, join.map ∂Δ[n].ι (𝟙 _) ≫ L = A ∧
      join.map (𝟙 _) (stdSimplex.δ 0) ≫ L = B ∧ L ≫ p = C := by
  -- The horn `Λ[1, 1]` is the target vertex of `Δ[1]`.
  let t := stdSimplex.isTerminalObj₀.{u}.from (Λ[1, 1] : SSet)
  have hΛ : Λ[1, 1].ι = t ≫ stdSimplex.δ 0 := by
    rw [horn_one_ι_eq_const, stdSimplex.δ_zero_eq_const, comp_const]
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[1, 1]
  have hw' : join.map (𝟙 _) Λ[1, 1].ι ≫ A = join.map ∂Δ[n].ι (𝟙 _) ≫ join.map (𝟙 _) t ≫ B := by
    rw [hΛ, ← Category.id_comp (𝟙 (∂Δ[n] : SSet)), join.map_comp_assoc, hw]
    simp only [← join.map_comp_assoc, Category.id_comp, Category.comp_id, t]
  -- `A` and `B` glue to a map `φ` on the pushout-join, a horn `Λ[n + 2, n + 2]` over `C`.
  let φ := hpush.desc A (join.map (𝟙 _) t ≫ B) hw'
  have hφ : φ ≫ p = (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ C := by
    refine hpush.hom_ext ?_ ?_
    · rw [hpush.inl_desc_assoc, hAC, Subcomplex.unionJoin.ι₁_ι_assoc]
    · rw [hpush.inr_desc_assoc, Category.assoc, hBC, Subcomplex.unionJoin.ι₂_ι_assoc, hΛ,
        ← join.map_comp_assoc, Category.id_comp]
  have hE : (unionJoinIso.{u} n).hom ≫ Λ[n + 2, Fin.last (n + 2)].ι =
      (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ (join.stdSimplexIso.{u} n 1).hom :=
    Subcomplex.isoOfPreimageEq_hom_ι _ _
  obtain ⟨τ, hτ, hτp⟩ := H ((unionJoinIso n).inv ≫ φ) ((join.stdSimplexIso n 1).inv ≫ C) (by
    rw [← yonedaEquiv_inr_comp_unionJoinIso_hom, ← yonedaEquiv_comp]
    simp [φ, hA]) (by
    rw [Category.assoc, hφ, ← Iso.inv_hom_id_assoc (unionJoinIso n) Λ[n + 2, _].ι, hE]
    simp)
  -- The filler, read on `Δ[n] ⋆ Δ[1]`, extends `φ` and lies over `C`.
  let L := (join.stdSimplexIso n 1).hom ≫ τ
  have hL : (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ L = φ := by
    rw [← Subcomplex.isoOfPreimageEq_hom_ι_assoc (join.stdSimplexIso n 1) (preimage_unionJoin_eq n),
      ← unionJoinIso, hτ, Iso.hom_inv_id_assoc]
  have hL₂ : join.map (𝟙 _) Λ[1, 1].ι ≫ L = join.map (𝟙 _) t ≫ B := by
    rw [← Subcomplex.unionJoin.ι₂_ι_assoc, hL, hpush.inr_desc]
  refine ⟨L, by rw [← Subcomplex.unionJoin.ι₁_ι_assoc, hL, hpush.inl_desc], ?_,
    by rw [Category.assoc, hτp, Iso.hom_inv_id_assoc]⟩
  calc _ = join.map (𝟙 _) (horn.ι 1 0 (by decide)) ≫ join.map (𝟙 _) Λ[1, 1].ι ≫ L := by
        rw [← join.map_comp_assoc, Category.id_comp, horn.ι_ι]
    _ = B := by
        rw [hL₂, ← join.map_comp_assoc, Category.id_comp,
          stdSimplex.isTerminalObj₀.hom_ext (horn.ι 1 0 _ ≫ t) (𝟙 _), join.map_id,
          Category.id_comp]

/-- A lifting problem of `∂Δ[n] ⟶ Δ[n]` against the map `X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}`
for the edge `f` given by `s` has a solution when every horn `Λ[n + 2, n + 2]` with final edge `s`
lifts along `p` over every `(n + 2)`-simplex of `S`. -/
private lemma hasLiftingProperty_of_hornFilling {S : SSet.{u}} (p : X ⟶ S) (s : X _⦋1⦌)
    (H : ∀ (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    HasLiftingProperty ∂Δ[n].ι (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm s)) := by
  refine ⟨fun {a b} sq ↦ ?_⟩
  -- The square amounts to cones `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` over `s` and `B : Δ[n] ⋆ Δ[0] ⟶ X`
  -- agreeing on `∂Δ[n] ⋆ Δ[0]`, under a cone `C : Δ[n] ⋆ Δ[1] ⟶ S`.
  have hw : join.map (𝟙 _) (stdSimplex.δ 0) ≫ (slice.homEquiv a).val =
      join.map ∂Δ[n].ι (𝟙 _) ≫ (slice.homEquiv (b ≫ pullback.fst _ _)).val := by
    have h := congrArg (fun F ↦ (slice.homEquiv F).val) (sq.w =≫ pullback.fst _ _)
    rwa [Category.assoc, slice.homEquiv_comp_restrictionMap_fst_coe, Category.assoc,
      slice.homEquiv_comp_coe] at h
  have hAC : (slice.homEquiv a).val ≫ p =
      join.map ∂Δ[n].ι (𝟙 _) ≫ (slice.homEquiv (b ≫ pullback.snd _ _)).val := by
    have h := congrArg (fun F ↦ (slice.homEquiv F).val) (sq.w =≫ pullback.snd _ _)
    rwa [Category.assoc, slice.homEquiv_comp_restrictionMap_snd_coe, Category.assoc,
      slice.homEquiv_comp_coe] at h
  have hBC : (slice.homEquiv (b ≫ pullback.fst _ _)).val ≫ p =
      join.map (𝟙 _) (stdSimplex.δ 0) ≫ (slice.homEquiv (b ≫ pullback.snd _ _)).val := by
    have h := b ≫= pullback.condition
    rw [← Category.assoc b, ← Category.assoc b] at h
    have h' := congrArg (fun F ↦ (slice.homEquiv F).val) h
    rwa [slice.homEquiv_comp_map_coe, slice.homEquiv_comp_map_coe, join.map_id, Category.id_comp,
      Category.comp_id] at h'
  obtain ⟨L, hL₁, hL₂, hLC⟩ := exists_lift_join_of_hornFilling p s H _ _ _
    (slice.homEquiv a).property hw hAC hBC
  refine ⟨⟨⟨slice.homEquiv.symm ⟨L, ?_⟩, ?_, ?_⟩⟩⟩
  · have hinr : join.inr (∂Δ[n] : SSet.{u}) Δ[1] ≫ join.map ∂Δ[n].ι (𝟙 _) = join.inr _ _ := by
      rw [join.inr_map, Category.id_comp]
    rw [← hinr, Category.assoc, hL₁]
    exact (slice.homEquiv a).property
  · exact slice.hom_ext (by rw [slice.homEquiv_comp_coe, Equiv.apply_symm_apply, hL₁])
  · refine pullback.hom_ext (slice.hom_ext ?_) (slice.hom_ext ?_)
    · rw [Category.assoc, slice.homEquiv_comp_restrictionMap_fst_coe, Equiv.apply_symm_apply, hL₂]
    · rw [Category.assoc, slice.homEquiv_comp_restrictionMap_snd_coe, Equiv.apply_symm_apply, hLC]

/-- Every horn `Λ[n + 2, n + 2]` with final edge `s` can be filled when `∂Δ[n] ⟶ Δ[n]` lifts
against the restriction of cones `X_{/f} ⟶ X_{/y}` for the edge `f` given by `s`. -/
private lemma hornFilling_of_hasLiftingProperty (s : X _⦋1⦌)
    [HasLiftingProperty ∂Δ[n].ι (slice.map (stdSimplex.δ 0) (𝟙 X) (by simp) :
      slice (yonedaEquiv.symm s) ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm s))]
    (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X)
    (hσ₀ : σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
      (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = s) :
    ∃ σ : Δ[n + 2] ⟶ X, σ₀ = Λ[n + 2, Fin.last (n + 2)].ι ≫ σ := by
  -- The horn `Λ[1, 1]` is the target vertex `e` of `Δ[1]`.
  let e : Δ[0] ⟶ (Λ[1, 1] : SSet.{u}) := horn.ι 1 0 (by decide)
  let t := stdSimplex.isTerminalObj₀.{u}.from (Λ[1, 1] : SSet)
  have hΛ : Λ[1, 1].ι = t ≫ stdSimplex.δ 0 := by
    rw [horn_one_ι_eq_const, stdSimplex.δ_zero_eq_const, comp_const]
  have hte : t ≫ e = 𝟙 _ := by
    rw [← cancel_mono Λ[1, 1].ι, Category.assoc, horn.ι_ι, Category.id_comp, hΛ]
  have hpush := Subcomplex.unionJoin.isPushout ∂Δ[n] Λ[1, 1]
  -- Read on the pushout-join, `σ₀` consists of maps `A : ∂Δ[n] ⋆ Δ[1] ⟶ X` and
  -- `B : Δ[n] ⋆ Δ[0] ⟶ X`, cones over the edge `s` and over its target.
  let φ := (unionJoinIso n).hom ≫ σ₀
  let A := Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] ≫ φ
  let B := join.map (𝟙 _) e ≫ Subcomplex.unionJoin.ι₂ ∂Δ[n] Λ[1, 1] ≫ φ
  have hA : join.inr _ _ ≫ A = yonedaEquiv.symm s := by
    rw [← hσ₀, ← yonedaEquiv_inr_comp_unionJoinIso_hom, ← yonedaEquiv_comp, Equiv.symm_apply_apply]
    simp [A, φ]
  have hι : join.inr (Δ[n] : SSet.{u}) _ ≫ Subcomplex.unionJoin.ι₂ ∂Δ[n] Λ[1, 1] =
      Λ[1, 1].ι ≫ join.inr _ _ ≫ Subcomplex.unionJoin.ι₁ ∂Δ[n] Λ[1, 1] := by
    rw [← cancel_mono (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι]
    simp
  have hB : join.inr _ _ ≫ B = stdSimplex.δ 0 ≫ yonedaEquiv.symm s := by
    simp only [B, join.inr_map_assoc, reassoc_of% hι, ← hA, A]
    rw [horn.ι_ι_assoc]
  let a : (∂Δ[n] : SSet) ⟶ slice (yonedaEquiv.symm s) := slice.homEquiv.symm ⟨A, hA⟩
  let b : Δ[n] ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm s) := slice.homEquiv.symm ⟨B, hB⟩
  have sq : CommSq a ∂Δ[n].ι (slice.map (stdSimplex.δ 0) (𝟙 X) (by simp)) b := ⟨slice.hom_ext (by
    rw [slice.homEquiv_comp_map_coe, slice.homEquiv_comp_coe, Equiv.apply_symm_apply,
      Equiv.apply_symm_apply, Category.comp_id]
    simp only [A, B]
    rw [← horn.ι_ι (n := 0) 1 0 (by decide), ← Category.id_comp (𝟙 (∂Δ[n] : SSet)),
      join.map_comp_assoc, hpush.w_assoc]
    simp only [← join.map_comp_assoc, Category.id_comp, Category.comp_id, e])⟩
  -- The lift is a map `Δ[n] ⋆ Δ[1] ⟶ X` extending `φ`, hence a filler of the horn.
  let L := (slice.homEquiv sq.lift).val
  have hL : (Subcomplex.unionJoin ∂Δ[n] Λ[1, 1]).ι ≫ L = φ := by
    refine hpush.hom_ext ?_ ?_
    · rw [Subcomplex.unionJoin.ι₁_ι_assoc, ← slice.homEquiv_comp_coe, sq.fac_left,
        Equiv.apply_symm_apply]
    · have h := congrArg (fun F ↦ (slice.homEquiv F).val) sq.fac_right
      rw [slice.homEquiv_comp_map_coe, Equiv.apply_symm_apply, Category.comp_id] at h
      rw [Subcomplex.unionJoin.ι₂_ι_assoc, hΛ, ← Category.id_comp (𝟙 (Δ[n] : SSet)),
        join.map_comp_assoc, h]
      simp only [B]
      rw [← join.map_comp_assoc, Category.id_comp, hte, join.map_id, Category.id_comp]
  refine ⟨(join.stdSimplexIso n 1).inv ≫ L, ?_⟩
  rw [← Subcomplex.isoOfPreimageEq_inv_ι_assoc (join.stdSimplexIso n 1) (preimage_unionJoin_eq n),
    hL, ← unionJoinIso, Iso.inv_hom_id_assoc]

end boundary

variable {x y : X _⦋0⦌}

/-- **The horn criterion for Cartesian edges** (HTT Remark 2.4.1.4). An edge `f` of `X` is
`p`-Cartesian for `p : X ⟶ S` as soon as every horn `Λ[n + 2, n + 2] ⟶ X` whose final edge, from
`n + 1` to `n + 2`, is `f`, lying over an `(n + 2)`-simplex `τ` of `S`, extends to an
`(n + 2)`-simplex of `X` over `τ`. -/
theorem isCartesian_of_hornFilling_last {S : SSet.{u}} (f : Edge x y) (p : X ⟶ S)
    (H : ∀ (n : ℕ) (σ₀ : (Λ[n + 2, Fin.last (n + 2)] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc
        (Fin.last (n + 2)) (Fin.le_last _) (by simp)) = f.edge →
      σ₀ ≫ p = Λ[n + 2, Fin.last (n + 2)].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, Fin.last (n + 2)].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    f.IsCartesian p := by
  rw [isCartesian_iff, rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  exact hasLiftingProperty_of_hornFilling p f.edge (H n)

/-- **The horn criterion for coCartesian edges** (HTT Remark 2.4.1.4, in the dual form of
Remark 2.4.1.9). An edge `f` of `X` is `p`-coCartesian for `p : X ⟶ S` as soon as every horn
`Λ[n + 2, 0] ⟶ X` whose initial edge, from `0` to `1`, is `f`, lying over an `(n + 2)`-simplex `τ`
of `S`, extends to an `(n + 2)`-simplex of `X` over `τ`. -/
theorem isCoCartesian_of_hornFilling_zero {S : SSet.{u}} (f : Edge x y) (p : X ⟶ S)
    (H : ∀ (n : ℕ) (σ₀ : (Λ[n + 2, 0] : SSet) ⟶ X) (τ : Δ[n + 2] ⟶ S),
      σ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = f.edge →
      σ₀ ≫ p = Λ[n + 2, 0].ι ≫ τ →
        ∃ σ : Δ[n + 2] ⟶ X, Λ[n + 2, 0].ι ≫ σ = σ₀ ∧ σ ≫ p = τ) :
    f.IsCoCartesian p := by
  rw [isCoCartesian_iff_isCartesian_opEquiv]
  refine isCartesian_of_hornFilling_last _ _ fun n σ₀ τ hσ₀ hτ ↦ ?_
  -- Reversing the vertices, through `Λ[n + 2, 0]ᵒᵖ ≅ Λ[n + 2, n + 2]` and `Δ[n + 2]ᵒᵖ ≅ Δ[n + 2]`,
  -- turns the horn `σ₀` of `Xᵒᵖ` over `τ` into a horn `ρ₀ : Λ[n + 2, 0] ⟶ X` over `τ'`.
  -- The reversed vertex `Fin.rev 0` is `Fin.last (n + 2)` by definition.
  let e : opFunctor.obj (Λ[n + 2, 0] : SSet.{u}) ≅ (Λ[n + 2, Fin.last (n + 2)] : SSet.{u}) :=
    horn.opIso (n + 2) 0
  let ρ₀ : (Λ[n + 2, 0] : SSet) ⟶ X := opFunctor.preimage (e.hom ≫ σ₀)
  let τ' : Δ[n + 2] ⟶ S := opFunctor.preimage ((stdSimplex.opIso ⦋n + 2⦌).hom ≫ τ)
  have hι : e.hom ≫ Λ[n + 2, Fin.last (n + 2)].ι =
      opFunctor.map Λ[n + 2, 0].ι ≫ (stdSimplex.opIso ⦋n + 2⦌).hom :=
    horn.opIso_hom_ι _ _
  -- The initial edge of `ρ₀` is `f`: horn reversal sends the edge from `0` to `1` to the edge
  -- from `n + 1` to `n + 2`.
  have hedge : ρ₀.app _ (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)) = f.edge := by
    have h₁ : e.hom.app _ (opObjEquiv.symm (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp))) =
        horn.edge (n + 2) (Fin.last (n + 2)) (Fin.last (n + 1)).castSucc (Fin.last (n + 2))
          (Fin.le_last _) (by simp) := by
      rw [← horn.opIso_inv_app_edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)
        (by simpa using Finset.card_le_two.trans (by omega))]
      exact Iso.inv_hom_id_app_apply e _ _
    have h₂ := congrArg (fun g ↦ g.app _ (opObjEquiv.symm
      (horn.edge (n + 2) 0 0 1 (Fin.zero_le _) (by simp)))) (opFunctor.map_preimage (e.hom ≫ σ₀))
    simp only [opFunctor_map, NatTrans.comp_app_apply, h₁, hσ₀, opEquiv_edge,
      Equiv.apply_symm_apply] at h₂
    exact opObjEquiv.symm.injective h₂
  obtain ⟨ρ, hρ, hρp⟩ := H n ρ₀ τ' hedge (opFunctor.map_injective (by
    rw [Functor.map_comp, Functor.map_preimage, Functor.map_comp, Functor.map_preimage,
      Category.assoc, hτ, reassoc_of% hι]))
  -- The reversal of the filler `ρ` fills `σ₀` over `τ`.
  have hι' : Λ[n + 2, Fin.last (n + 2)].ι ≫ (stdSimplex.opIso ⦋n + 2⦌).inv =
      e.inv ≫ opFunctor.map Λ[n + 2, 0].ι := by
    rw [Iso.eq_inv_comp, ← Category.assoc, hι, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  refine ⟨(stdSimplex.opIso ⦋n + 2⦌).inv ≫ opFunctor.map ρ, ?_, ?_⟩
  · rw [reassoc_of% hι', ← Functor.map_comp, hρ, Functor.map_preimage, Iso.inv_hom_id_assoc]
  · rw [Category.assoc, ← Functor.map_comp, hρp, Functor.map_preimage, Iso.inv_hom_id_assoc]

/-- **An edge `f : x ⟶ y` of a quasicategory is an equivalence exactly when the restriction of
cones `X_{/f} ⟶ X_{/y}` is a trivial fibration**, that is, has the right lifting property with
respect to every monomorphism. -/
theorem isEquivalence_iff_rlp_slice_map [Quasicategory X] (f : Edge x y) :
    f.IsEquivalence ↔ (monomorphisms SSet.{u}).rlp (slice.map (stdSimplex.δ 0) (𝟙 X) (by simp) :
      slice (yonedaEquiv.symm f.edge) ⟶ slice (stdSimplex.δ 0 ≫ yonedaEquiv.symm f.edge)) := by
  rw [isEquivalence_iff_hornFilling_last]
  refine ⟨fun H ↦ (isCartesian_iff_rlp_slice_map f (stdSimplex.isTerminalObj₀.from X)
    stdSimplex.isTerminalObj₀).1 (isCartesian_of_hornFilling_last f _ fun n σ₀ _ hσ₀ _ ↦ ?_),
    fun H n ↦ ?_⟩
  · -- Over the terminal `Δ[0]`, every filler lies over the given simplex.
    obtain ⟨σ, hσ⟩ := H n σ₀ hσ₀
    exact ⟨σ, hσ.symm, stdSimplex.isTerminalObj₀.hom_ext _ _⟩
  · rw [rlp_monomorphisms] at H
    have := H _ (modelCategoryQuillen.boundary_ι_mem_I n)
    exact hornFilling_of_hasLiftingProperty f.edge

/-- **An edge of a quasicategory is an equivalence exactly when it is Cartesian over a point**
(HTT Proposition 2.4.1.5 over a point): for the map `p` to a terminal simplicial set, the
`p`-Cartesian edges are the equivalences. -/
theorem isEquivalence_iff_isCartesian [Quasicategory X] (f : Edge x y) {S : SSet.{u}}
    (p : X ⟶ S) (hS : IsTerminal S) : f.IsEquivalence ↔ f.IsCartesian p := by
  rw [isEquivalence_iff_rlp_slice_map, isCartesian_iff_rlp_slice_map f p hS]

/-- Every edge of a Kan complex, for example of the nerve of a groupoid, is Cartesian over a
point. -/
lemma isCartesian_of_kanComplex [KanComplex X] (f : Edge x y) {S : SSet.{u}} (p : X ⟶ S)
    (hS : IsTerminal S) : f.IsCartesian p :=
  (isEquivalence_iff_isCartesian f p hS).1 (isEquivalence_of_kanComplex f)

end Edge

namespace stdSimplex

/-- An edge of `Δ[n]` from a vertex `a` to a vertex `b > a`, such as the edge from `0` to `1` of
`Δ[1]`, is not Cartesian over a point: it has no inverse. -/
lemma not_isCartesian_of_lt {n : ℕ} {a b : Fin (n + 1)} (hab : a < b)
    (f : Edge (obj₀Equiv.{u}.symm a) (obj₀Equiv.symm b)) {S : SSet.{u}} (p : Δ[n] ⟶ S)
    (hS : IsTerminal S) : ¬ f.IsCartesian p := fun h ↦
  hab.not_ge ((nonempty_edge_iff b a).1
    ⟨((Edge.isEquivalence_iff_isCartesian f p hS).2 h).invStruct.inv⟩)

end stdSimplex

end SSet

namespace CategoryTheory.nerve

open SSet

variable {C : Type u} [Category.{v} C]

/-- An edge of the nerve of a category is Cartesian over a point exactly when the corresponding
morphism is an isomorphism. -/
lemma isCartesian_edgeMk_iff {x y : C} (f : x ⟶ y) {S : SSet.{max u v}} (p : nerve C ⟶ S)
    (hS : IsTerminal S) : (edgeMk f).IsCartesian p ↔ IsIso f :=
  (Edge.isEquivalence_iff_isCartesian (edgeMk f) p hS).symm.trans (isEquivalence_edgeMk_iff f)

end CategoryTheory.nerve
