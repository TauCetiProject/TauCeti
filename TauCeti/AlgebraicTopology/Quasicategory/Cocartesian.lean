/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import TauCeti.AlgebraicTopology.SimplicialSet.AnodyneExtensions.LeftRight.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Coslice
public import TauCeti.AlgebraicTopology.SimplicialSet.Join.StdSimplex

/-!
# CoCartesian edges and coCartesian fibrations

Let `p : X ⟶ S` be a map of simplicial sets. An edge `f : x ⟶ y` of `X` is `p`-coCartesian when
the map of coslices
`X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}`
is a trivial fibration, that is, has the right lifting property with respect to all
monomorphisms. Here `X_{x/}` is the coslice under the restriction of `f` to its source vertex, and
the map is `SSet.coslice.restrictionMap`. A coCartesian fibration is an inner fibration `p` along
which every edge of `S` starting at the image of a vertex `x` of `X` lifts to a `p`-coCartesian
edge starting at `x`.

These are the duals of `p`-Cartesian edges and Cartesian fibrations (`SSet.Edge.IsCartesian`,
`SSet.CartesianFibration`). Lurie calls `f` `p`-coCartesian when it is Cartesian for
`pᵒᵖ : Xᵒᵖ ⟶ Sᵒᵖ`; this unwinds to the condition above, because the coslices of `X` are the
opposites of the slices of `Xᵒᵖ` and trivial fibrations are invariant under taking opposites.
CoCartesian fibrations over `S` are the fibrations which straightening identifies with covariant
functors from `S` to `∞`-categories. This file sets up the definitions, their stability under
isomorphisms, base change and composition, and shows that every edge of a left fibration is
coCartesian, so that left fibrations are coCartesian fibrations.

## Main definitions

* `SSet.Edge.IsCocartesian f p`: the edge `f` is `p`-coCartesian.
* `SSet.CocartesianFibration p`: the inner fibration `p` admits coCartesian lifts of all edges
  with specified source.

## Main results

* `SSet.Edge.isCocartesian_of_isIso`: every edge is coCartesian along an isomorphism.
* `SSet.Edge.IsCocartesian.of_isPullback`: in a pullback square, an edge is coCartesian along the
  pulled-back map when its image is coCartesian along the original one.
* `SSet.Edge.IsCocartesian.comp`: if `f` is `p`-coCartesian and `p f` is `r`-coCartesian, then `f`
  is `p ≫ r`-coCartesian.
* `SSet.Edge.isCocartesian_of_leftFibration`: every edge of a left fibration is coCartesian.
* `SSet.CocartesianFibration.of_isPullback`, `SSet.CocartesianFibration.comp`: coCartesian
  fibrations are stable under base change and composition, and isomorphisms and left fibrations
  are coCartesian fibrations.

## Implementation notes

That an edge `f : Δ[1] ⟶ X` of a left fibration `p` is coCartesian is a lifting property of the
boundary inclusions `∂Δ[n] ⟶ Δ[n]` against the restriction map. Through the universal property of
the coslice (`SSet.coslice.hasLiftingProperty_restrictionMap`) it becomes a lifting property of
the pushout-join `(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n]) ⟶ Δ[1] ⋆ Δ[n]` against `p`, and this inclusion
is the left horn `Λ[n + 2, 0] ⟶ Δ[n + 2]` (`SSet.join.preimage_unionJoin_horn_boundary`).

## References

* J. Lurie, *Higher Topos Theory*, Definitions 2.4.1.1 and 2.4.2.1, Proposition 2.4.1.3, the
  definition of `p`-coCartesian edges before Proposition 2.4.1.8, and Propositions 2.4.2.3
  and 2.4.2.4.
-/
public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

namespace Edge

variable {X S : SSet.{u}} {x y : X _⦋0⦌}

/-- An edge `f : x ⟶ y` of `X` is `p`-coCartesian for `p : X ⟶ S` if the map
`X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}` restricting a cocone under `f` to the source vertex `x` and
pushing it forward along `p` is a trivial fibration. -/
def IsCocartesian (f : Edge x y) (p : X ⟶ S) : Prop :=
  (monomorphisms SSet.{u}).rlp
    (coslice.restrictionMap (stdSimplex.δ 1) p (yonedaEquiv.symm f.edge))

/-- An edge is `p`-coCartesian exactly when its restriction map
`SSet.coslice.restrictionMap (stdSimplex.δ 1) p` is a trivial fibration. -/
lemma isCocartesian_iff (f : Edge x y) (p : X ⟶ S) :
    f.IsCocartesian p ↔
      (monomorphisms SSet.{u}).rlp
        (coslice.restrictionMap (stdSimplex.δ 1) p (yonedaEquiv.symm f.edge)) :=
  Iff.rfl

/-- Being `p`-coCartesian only depends on the underlying `1`-simplex of an edge. -/
lemma IsCocartesian.of_edge_eq {x' y' : X _⦋0⦌} {f : Edge x y} {f' : Edge x' y'} {p : X ⟶ S}
    (hf : f.IsCocartesian p) (h : f.edge = f'.edge) : f'.IsCocartesian p := by
  rwa [isCocartesian_iff, ← h]

/-- Every edge is coCartesian along an isomorphism. -/
lemma isCocartesian_of_isIso (f : Edge x y) (p : X ⟶ S) [IsIso p] : f.IsCocartesian p :=
  rlp_of_isIso _ _

/-- CoCartesian edges are stable under base change: given a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, an edge of `X'` is `p'`-coCartesian
when its image in `X` is `p`-coCartesian. -/
lemma IsCocartesian.of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
    {b : S' ⟶ S} (sq : IsPullback t p' p b) {x' y' : X' _⦋0⦌} {f : Edge x' y'}
    (hf : (f.map t).IsCocartesian p) : f.IsCocartesian p' := by
  rw [isCocartesian_iff, map_edge, ← yonedaEquiv_symm_comp] at hf
  exact (monomorphisms SSet.{u}).rlp.of_isPullback
    (coslice.isPullback_restrictionMap sq (stdSimplex.δ 1) (yonedaEquiv.symm f.edge)) hf

/-- If `f` is `p`-coCartesian and its image `p f` is `r`-coCartesian, then `f` is
`p ≫ r`-coCartesian: the restriction map for `p ≫ r` is the restriction map for `p` followed by a
base change of the restriction map for `r` at `p f`. -/
lemma IsCocartesian.comp {Z : SSet.{u}} {f : Edge x y} {p : X ⟶ S} {r : S ⟶ Z}
    (hf : f.IsCocartesian p) (hpf : (f.map p).IsCocartesian r) : f.IsCocartesian (p ≫ r) := by
  rw [isCocartesian_iff, map_edge, ← yonedaEquiv_symm_comp] at hpf
  rw [isCocartesian_iff, coslice.restrictionMap_comp]
  exact (monomorphisms SSet.{u}).rlp.comp_mem _ _ hf
    ((monomorphisms SSet.{u}).rlp.of_isPullback
      (coslice.isPullback_restrictionMapComp _ _ _ _) hpf)

/-- **Every edge of a left fibration is coCartesian.** Lifting a boundary inclusion
`∂Δ[n] ⟶ Δ[n]` against the restriction map of an edge amounts to lifting the left horn
`Λ[n + 2, 0] ⟶ Δ[n + 2]`, the pushout-join `(Λ[1, 0] ⋆ Δ[n]) ∪ (Δ[1] ⋆ ∂Δ[n]) ⟶ Δ[1] ⋆ Δ[n]`,
against `p`. -/
theorem isCocartesian_of_leftFibration (f : Edge x y) (p : X ⟶ S) [LeftFibration p] :
    f.IsCocartesian p := by
  rw [isCocartesian_iff, rlp_monomorphisms]
  rintro _ _ _ ⟨n⟩
  have : HasLiftingProperty
      ((Subcomplex.range (stdSimplex.δ (1 : Fin 2))).unionJoin ∂Δ[n]).ι p := by
    rw [stdSimplex.range_δ_eq_horn_one]
    refine leftAnodyneExtensions.hasLiftingProperty ?_ p
    refine (Subcomplex.morphismProperty_ι_iff_of_preimage_eq _ (join.stdSimplexIso 1 n)
      (join.preimage_unionJoin_horn_boundary n one_ne_zero _)).2
      (leftAnodyneExtensions.horn_ι ?_)
    simp [Fin.lt_def]
  exact coslice.hasLiftingProperty_restrictionMap _ _ _ _

end Edge

/-- A map `p : X ⟶ S` is a coCartesian fibration if it is an inner fibration and every edge
`e : p x ⟶ s` of `S` starting at the image of a vertex `x` of `X` lifts to a `p`-coCartesian edge
`f : x ⟶ y` with `p f = e`. -/
class CocartesianFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop extends InnerFibration p where
  exists_isCocartesian_lift {x : X _⦋0⦌} {s : S _⦋0⦌} (e : Edge (p.app _ x) s) :
    ∃ (y : X _⦋0⦌) (f : Edge x y), f.IsCocartesian p ∧ (f.map p).edge = e.edge

namespace CocartesianFibration

variable {X S : SSet.{u}}

/-- An isomorphism is a coCartesian fibration. -/
instance of_isIso (p : X ⟶ S) [IsIso p] : CocartesianFibration p where
  mem := innerFibrations.of_isIso p
  exists_isCocartesian_lift {x s} e :=
    ⟨_, Edge.mk ((inv p).app _ e.edge) (by rw [← δ_naturality_apply, e.src_eq]; simp) rfl,
      Edge.isCocartesian_of_isIso _ _, by simp⟩

/-- CoCartesian fibrations are stable under base change: in a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, the map `p'` is a coCartesian
fibration when `p` is. A coCartesian lift of an edge `e` of `S'` is assembled from `e` and a
coCartesian lift of its image in `S`. -/
lemma of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S} {b : S' ⟶ S}
    (sq : IsPullback t p' p b) [CocartesianFibration p] : CocartesianFibration p' where
  mem := innerFibrations.of_isPullback sq (mem_innerFibrations p)
  exists_isCocartesian_lift {x' s'} e' := by
    have hx : b.app _ (p'.app _ x') = p.app _ (t.app _ x') := by
      simpa using (ConcreteCategory.congr_hom (NatTrans.congr_app sq.w _) x').symm
    obtain ⟨y, f, hf, hfe⟩ := exists_isCocartesian_lift (p := p) (x := t.app _ x')
      (Edge.mk (b.app _ e'.edge) (by rw [← δ_naturality_apply, e'.src_eq, hx])
        (by rw [← δ_naturality_apply, e'.tgt_eq]))
    simp only [Edge.map_edge, Edge.mk_edge] at hfe
    -- The lift in `X'` of the edge `f` of `X` and the edge `e'` of `S'`.
    let φ : Δ[1] ⟶ X' := sq.lift (yonedaEquiv.symm f.edge) (yonedaEquiv.symm e'.edge)
      (by rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, hfe])
    have hsrc : X'.δ 1 (yonedaEquiv φ) = x' := by
      apply yonedaEquiv.symm.injective
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
      refine sq.hom_ext ?_ ?_
      · rw [Category.assoc, sq.lift_fst, stdSimplex.δ_comp_yonedaEquiv_symm, f.src_eq,
          yonedaEquiv_symm_comp]
      · rw [Category.assoc, sq.lift_snd, stdSimplex.δ_comp_yonedaEquiv_symm, e'.src_eq,
          yonedaEquiv_symm_comp]
    refine ⟨_, Edge.mk (yonedaEquiv φ) hsrc rfl, Edge.IsCocartesian.of_isPullback sq
      (hf.of_edge_eq ?_), ?_⟩
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_fst, Equiv.apply_symm_apply]
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_snd, Equiv.apply_symm_apply]

/-- A composite of coCartesian fibrations is a coCartesian fibration: lift an edge first along `r`
and then along `p`. -/
instance comp {Z : SSet.{u}} (p : X ⟶ S) (r : S ⟶ Z) [CocartesianFibration p]
    [CocartesianFibration r] : CocartesianFibration (p ≫ r) where
  mem := innerFibrations.comp_mem _ _ (mem_innerFibrations p) (mem_innerFibrations r)
  exists_isCocartesian_lift {x z} e := by
    obtain ⟨s, g, hg, hge⟩ := exists_isCocartesian_lift (p := r) (x := p.app _ x)
      (Edge.mk e.edge (by rw [e.src_eq]; simp) e.tgt_eq)
    obtain ⟨y, f, hf, hfe⟩ := exists_isCocartesian_lift (p := p) (x := x) g
    refine ⟨y, f, hf.comp (hg.of_edge_eq hfe.symm), ?_⟩
    simp only [Edge.map_edge, Edge.mk_edge] at hge hfe ⊢
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hfe, hge]

/-- **Left fibrations are coCartesian fibrations**: every edge of a left fibration is coCartesian
(`SSet.Edge.isCocartesian_of_leftFibration`), and edges lift with specified source since
`stdSimplex.δ 1 : Δ[0] ⟶ Δ[1]` is left anodyne. -/
instance of_leftFibration (p : X ⟶ S) [LeftFibration p] : CocartesianFibration p where
  exists_isCocartesian_lift {x s} e := by
    have sq : CommSq (yonedaEquiv.symm x) (stdSimplex.δ 1) p (yonedaEquiv.symm e.edge) :=
      ⟨by rw [yonedaEquiv_symm_comp, stdSimplex.δ_comp_yonedaEquiv_symm, e.src_eq]⟩
    have := leftAnodyneExtensions.stdSimplex_δ_one.hasLiftingProperty p
    have hsrc : X.δ 1 (yonedaEquiv sq.lift) = x := by
      apply yonedaEquiv.symm.injective
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply, sq.fac_left]
    refine ⟨_, Edge.mk (yonedaEquiv sq.lift) hsrc rfl,
      Edge.isCocartesian_of_leftFibration _ p, ?_⟩
    simp only [Edge.map_edge, Edge.mk_edge]
    rw [← yonedaEquiv_comp, sq.fac_right, Equiv.apply_symm_apply]

end CocartesianFibration

end SSet
