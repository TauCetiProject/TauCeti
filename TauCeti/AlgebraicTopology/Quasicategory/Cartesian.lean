/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.Quasicategory.InnerFibration
public import Mathlib.AlgebraicTopology.SimplicialSet.CompStruct
public import TauCeti.AlgebraicTopology.SimplicialSet.Slice

/-!
# Cartesian edges and Cartesian fibrations

Let `p : X ⟶ S` be a map of simplicial sets. An edge `f : x ⟶ y` of `X` is `p`-Cartesian when the
map of slices
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}`
is a trivial fibration, that is, has the right lifting property with respect to all
monomorphisms. Here `X_{/y}` is the slice over the restriction of `f` to its target vertex, and
the map is `SSet.slice.restrictionMap`. A Cartesian fibration is an inner fibration `p` along which
every edge of `S` ending at the image of a vertex `y` of `X` lifts to a `p`-Cartesian edge ending
at `y`.

Cartesian fibrations over `S` are the fibrations which straightening identifies with contravariant
functors from `S` to `∞`-categories; coCartesian fibrations, their duals, correspond to covariant
functors. This file sets up the definitions and their formal properties: stability under
isomorphisms, base change and composition.

## Main definitions

* `SSet.Edge.IsCartesian f p`: the edge `f` is `p`-Cartesian.
* `SSet.CartesianFibration p`: the inner fibration `p` admits Cartesian lifts of all edges with
  specified target.

## Main results

* `SSet.Edge.isCartesian_of_isIso`: every edge is Cartesian along an isomorphism.
* `SSet.Edge.IsCartesian.of_isPullback`: in a pullback square, an edge is Cartesian along the
  pulled-back map when its image is Cartesian along the original one.
* `SSet.Edge.IsCartesian.comp`: if `f` is `p`-Cartesian and `p f` is `r`-Cartesian, then `f` is
  `p ≫ r`-Cartesian.
* `SSet.CartesianFibration.of_isPullback`, `SSet.CartesianFibration.comp`: Cartesian fibrations
  are stable under base change and composition, and isomorphisms are Cartesian fibrations.

## References

* J. Lurie, *Higher Topos Theory*, Definition 2.4.1.1, Proposition 2.4.1.3, Definition 2.4.2.1
  and Proposition 2.4.2.3.
-/
public section

open CategoryTheory Limits MorphismProperty Simplicial

universe u

namespace SSet

namespace Edge

variable {X S : SSet.{u}} {x y : X _⦋0⦌}

/-- An edge `f : x ⟶ y` of `X` is `p`-Cartesian for `p : X ⟶ S` if the map
`X_{/f} ⟶ X_{/y} ×_{S_{/p y}} S_{/p f}` restricting a cone over `f` to the target vertex `y` and
pushing it forward along `p` is a trivial fibration. -/
def IsCartesian (f : Edge x y) (p : X ⟶ S) : Prop :=
  (monomorphisms SSet.{u}).rlp (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm f.edge))

/-- An edge is `p`-Cartesian exactly when its restriction map
`SSet.slice.restrictionMap (stdSimplex.δ 0) p` is a trivial fibration. -/
lemma isCartesian_iff (f : Edge x y) (p : X ⟶ S) :
    f.IsCartesian p ↔
      (monomorphisms SSet.{u}).rlp
        (slice.restrictionMap (stdSimplex.δ 0) p (yonedaEquiv.symm f.edge)) :=
  Iff.rfl

/-- Being `p`-Cartesian only depends on the underlying `1`-simplex of an edge. -/
lemma IsCartesian.of_edge_eq {x' y' : X _⦋0⦌} {f : Edge x y} {f' : Edge x' y'} {p : X ⟶ S}
    (hf : f.IsCartesian p) (h : f.edge = f'.edge) : f'.IsCartesian p := by
  rwa [isCartesian_iff, ← h]

/-- Every edge is Cartesian along an isomorphism. -/
lemma isCartesian_of_isIso (f : Edge x y) (p : X ⟶ S) [IsIso p] : f.IsCartesian p :=
  rlp_of_isIso _ _

/-- Cartesian edges are stable under base change: given a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, an edge of `X'` is `p'`-Cartesian when
its image in `X` is `p`-Cartesian. -/
lemma IsCartesian.of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
    {b : S' ⟶ S} (sq : IsPullback t p' p b) {x' y' : X' _⦋0⦌} {f : Edge x' y'}
    (hf : (f.map t).IsCartesian p) : f.IsCartesian p' := by
  rw [isCartesian_iff, map_edge, ← yonedaEquiv_symm_comp] at hf
  exact (monomorphisms SSet.{u}).rlp.of_isPullback
    (slice.isPullback_restrictionMap sq (stdSimplex.δ 0) (yonedaEquiv.symm f.edge)) hf

/-- If `f` is `p`-Cartesian and its image `p f` is `r`-Cartesian, then `f` is `p ≫ r`-Cartesian:
the restriction map for `p ≫ r` is the restriction map for `p` followed by a base change of the
restriction map for `r` at `p f`. -/
lemma IsCartesian.comp {Z : SSet.{u}} {f : Edge x y} {p : X ⟶ S} {r : S ⟶ Z}
    (hf : f.IsCartesian p) (hpf : (f.map p).IsCartesian r) : f.IsCartesian (p ≫ r) := by
  rw [isCartesian_iff, map_edge, ← yonedaEquiv_symm_comp] at hpf
  rw [isCartesian_iff, slice.restrictionMap_comp]
  exact (monomorphisms SSet.{u}).rlp.comp_mem _ _ hf
    ((monomorphisms SSet.{u}).rlp.of_isPullback (slice.isPullback_restrictionMapComp _ _ _ _) hpf)

end Edge

/-- A map `p : X ⟶ S` is a Cartesian fibration if it is an inner fibration and every edge
`e : s ⟶ p y` of `S` ending at the image of a vertex `y` of `X` lifts to a `p`-Cartesian edge
`f : x ⟶ y` with `p f = e`. -/
class CartesianFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop extends InnerFibration p where
  exists_isCartesian_lift {y : X _⦋0⦌} {s : S _⦋0⦌} (e : Edge s (p.app _ y)) :
    ∃ (x : X _⦋0⦌) (f : Edge x y), f.IsCartesian p ∧ (f.map p).edge = e.edge

namespace CartesianFibration

variable {X S : SSet.{u}}

/-- An isomorphism is a Cartesian fibration. -/
instance of_isIso (p : X ⟶ S) [IsIso p] : CartesianFibration p where
  mem := innerFibrations.of_isIso p
  exists_isCartesian_lift {y s} e :=
    ⟨_, Edge.mk ((inv p).app _ e.edge) rfl
      (by rw [← δ_naturality_apply, e.tgt_eq]; simp),
      Edge.isCartesian_of_isIso _ _, by simp⟩

/-- Cartesian fibrations are stable under base change: in a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, the map `p'` is a Cartesian fibration
when `p` is. A Cartesian lift of an edge `e` of `S'` is assembled from `e` and a Cartesian lift of
its image in `S`. -/
lemma of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S} {b : S' ⟶ S}
    (sq : IsPullback t p' p b) [CartesianFibration p] : CartesianFibration p' where
  mem := innerFibrations.of_isPullback sq (mem_innerFibrations p)
  exists_isCartesian_lift {y' s'} e' := by
    have hy : b.app _ (p'.app _ y') = p.app _ (t.app _ y') := by
      simpa using (ConcreteCategory.congr_hom (NatTrans.congr_app sq.w _) y').symm
    obtain ⟨x, f, hf, hfe⟩ := exists_isCartesian_lift (p := p) (y := t.app _ y')
      (Edge.mk (b.app _ e'.edge) (by rw [← δ_naturality_apply, e'.src_eq])
        (by rw [← δ_naturality_apply, e'.tgt_eq, hy]))
    simp only [Edge.map_edge, Edge.mk_edge] at hfe
    -- The lift in `X'` of the edge `f` of `X` and the edge `e'` of `S'`.
    let φ : Δ[1] ⟶ X' := sq.lift (yonedaEquiv.symm f.edge) (yonedaEquiv.symm e'.edge)
      (by rw [yonedaEquiv_symm_comp, yonedaEquiv_symm_comp, hfe])
    have htgt : X'.δ 0 (yonedaEquiv φ) = y' := by
      apply yonedaEquiv.symm.injective
      rw [← stdSimplex.δ_comp_yonedaEquiv_symm, Equiv.symm_apply_apply]
      refine sq.hom_ext ?_ ?_
      · rw [Category.assoc, sq.lift_fst, stdSimplex.δ_comp_yonedaEquiv_symm, f.tgt_eq,
          yonedaEquiv_symm_comp]
      · rw [Category.assoc, sq.lift_snd, stdSimplex.δ_comp_yonedaEquiv_symm, e'.tgt_eq,
          yonedaEquiv_symm_comp]
    refine ⟨_, Edge.mk (yonedaEquiv φ) rfl htgt, Edge.IsCartesian.of_isPullback sq
      (hf.of_edge_eq ?_), ?_⟩
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_fst, Equiv.apply_symm_apply]
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_snd, Equiv.apply_symm_apply]

/-- A composite of Cartesian fibrations is a Cartesian fibration: lift an edge first along `r`
and then along `p`. -/
instance comp {Z : SSet.{u}} (p : X ⟶ S) (r : S ⟶ Z) [CartesianFibration p]
    [CartesianFibration r] : CartesianFibration (p ≫ r) where
  mem := innerFibrations.comp_mem _ _ (mem_innerFibrations p) (mem_innerFibrations r)
  exists_isCartesian_lift {y z} e := by
    obtain ⟨s, g, hg, hge⟩ := exists_isCartesian_lift (p := r) (y := p.app _ y)
      (Edge.mk e.edge e.src_eq (by rw [e.tgt_eq]; simp))
    obtain ⟨x, f, hf, hfe⟩ := exists_isCartesian_lift (p := p) (y := y) g
    refine ⟨x, f, hf.comp (hg.of_edge_eq hfe.symm), ?_⟩
    simp only [Edge.map_edge, Edge.mk_edge] at hge hfe ⊢
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hfe, hge]

end CartesianFibration

end SSet
