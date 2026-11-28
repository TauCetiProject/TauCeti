/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.Cartesian.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.Fiber
public import TauCeti.AlgebraicTopology.SimplicialSet.Op
public import TauCeti.AlgebraicTopology.SimplicialSet.StdSimplex

/-!
# CoCartesian edges and coCartesian fibrations

Let `p : X ⟶ S` be a map of simplicial sets. An edge `f : x ⟶ y` of `X` is `p`-coCartesian when
the reversed edge `y ⟶ x` of the opposite simplicial set `Xᵒᵖ` is Cartesian for the opposite map
`pᵒᵖ : Xᵒᵖ ⟶ Sᵒᵖ` (`SSet.Edge.IsCartesian`). Since slices of `Xᵒᵖ` are the opposites of coslices
of `X` (`SSet.coslice.opSliceIso`), this says that the map of coslices
`X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}` is a trivial fibration. A coCartesian fibration is an
inner fibration `p` along which every edge of `S` starting at the image of a vertex `x` of `X`
lifts to a `p`-coCartesian edge starting at `x`.

CoCartesian fibrations over `S` are the fibrations which straightening identifies with covariant
functors from `S` to `∞`-categories. For instance, symmetric monoidal quasicategories are
coCartesian fibrations over the nerve of the category of finite pointed sets. This file sets up
the definitions and their formal properties: stability under isomorphisms, base change and
composition, deduced from the corresponding properties of Cartesian edges.

An edge `e : s ⟶ t` of `S` acts on the fibers of a coCartesian fibration through the functors
associated to it: a map `F : X_s ⟶ X_t` of fibers is associated to `e` when it is the end of a
homotopy `X_s × Δ[1] ⟶ X` over `e`, starting at the inclusion of `X_s`, whose edges
`{x} × Δ[1]` are all `p`-coCartesian. Such a homotopy, with its end, is recorded by the structure
`SSet.CoCartesianTransport p e`.

## Main definitions

* `SSet.Edge.IsCoCartesian f p`: the edge `f` is `p`-coCartesian.
* `SSet.CoCartesianFibration p`: the inner fibration `p` admits coCartesian lifts of all edges
  with specified source.
* `SSet.CoCartesianTransport p e`: a functor `X_s ⟶ X_t` of fibers associated to the edge
  `e : s ⟶ t`, with a coCartesian homotopy exhibiting it.

## Main results

* `SSet.Edge.isCoCartesian_of_isIso`: every edge is coCartesian along an isomorphism.
* `SSet.Edge.IsCoCartesian.of_isPullback`: in a pullback square, an edge is coCartesian along the
  pulled-back map when its image is coCartesian along the original one.
* `SSet.Edge.IsCoCartesian.comp`: if `f` is `p`-coCartesian and `p f` is `r`-coCartesian, then
  `f` is `p ≫ r`-coCartesian.
* `SSet.CoCartesianFibration.of_isPullback`, `SSet.CoCartesianFibration.comp`: coCartesian
  fibrations are stable under base change and composition, and isomorphisms are coCartesian
  fibrations.

## References

* J. Lurie, *Higher Topos Theory*, Remark 2.4.1.9 and Definition 2.4.2.1 (the dual notions),
  and §2.4.1 for the functors associated to an edge.
-/
public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory Simplicial

universe u

namespace SSet

namespace Edge

variable {X S : SSet.{u}} {x y : X _⦋0⦌}

/-- An edge `f : x ⟶ y` of `X` is `p`-coCartesian for `p : X ⟶ S` if the reversed edge
`y ⟶ x` of `Xᵒᵖ` is Cartesian for `pᵒᵖ : Xᵒᵖ ⟶ Sᵒᵖ`, that is, if the map of coslices
`X_{f/} ⟶ X_{x/} ×_{S_{p x/}} S_{p f/}` is a trivial fibration. -/
def IsCoCartesian (f : Edge x y) (p : X ⟶ S) : Prop :=
  (opEquiv f).IsCartesian (opFunctor.map p)

/-- An edge is `p`-coCartesian exactly when the reversed edge of the opposite simplicial set is
Cartesian for the opposite of `p`. -/
lemma isCoCartesian_iff_isCartesian_opEquiv (f : Edge x y) (p : X ⟶ S) :
    f.IsCoCartesian p ↔ (opEquiv f).IsCartesian (opFunctor.map p) :=
  Iff.rfl

/-- Being `p`-coCartesian only depends on the underlying `1`-simplex of an edge. -/
lemma IsCoCartesian.of_edge_eq {x' y' : X _⦋0⦌} {f : Edge x y} {f' : Edge x' y'} {p : X ⟶ S}
    (hf : f.IsCoCartesian p) (h : f.edge = f'.edge) : f'.IsCoCartesian p :=
  IsCartesian.of_edge_eq hf (by simp [h])

/-- Every edge is coCartesian along an isomorphism. -/
lemma isCoCartesian_of_isIso (f : Edge x y) (p : X ⟶ S) [IsIso p] : f.IsCoCartesian p :=
  isCartesian_of_isIso _ _

/-- CoCartesian edges are stable under base change: given a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, an edge of `X'` is `p'`-coCartesian
when its image in `X` is `p`-coCartesian. -/
lemma IsCoCartesian.of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S}
    {b : S' ⟶ S} (sq : IsPullback t p' p b) {x' y' : X' _⦋0⦌} {f : Edge x' y'}
    (hf : (f.map t).IsCoCartesian p) : f.IsCoCartesian p' :=
  IsCartesian.of_isPullback (sq.map opFunctor) (IsCartesian.of_edge_eq hf (opEquiv_map_edge f t))

/-- If `f` is `p`-coCartesian and its image `p f` is `r`-coCartesian, then `f` is
`p ≫ r`-coCartesian. -/
lemma IsCoCartesian.comp {Z : SSet.{u}} {f : Edge x y} {p : X ⟶ S} {r : S ⟶ Z}
    (hf : f.IsCoCartesian p) (hpf : (f.map p).IsCoCartesian r) : f.IsCoCartesian (p ≫ r) := by
  rw [IsCoCartesian, Functor.map_comp]
  exact IsCartesian.comp hf (IsCartesian.of_edge_eq hpf (opEquiv_map_edge f p))

end Edge

/-- A map `p : X ⟶ S` is a coCartesian fibration if it is an inner fibration and every edge
`e : p x ⟶ t` of `S` starting at the image of a vertex `x` of `X` lifts to a `p`-coCartesian edge
`f : x ⟶ y` with `p f = e`. -/
class CoCartesianFibration {X S : SSet.{u}} (p : X ⟶ S) : Prop extends InnerFibration p where
  exists_isCoCartesian_lift {x : X _⦋0⦌} {t : S _⦋0⦌} (e : Edge (p.app _ x) t) :
    ∃ (y : X _⦋0⦌) (f : Edge x y), f.IsCoCartesian p ∧ (f.map p).edge = e.edge

namespace CoCartesianFibration

variable {X S : SSet.{u}}

/-- An isomorphism is a coCartesian fibration. -/
instance of_isIso (p : X ⟶ S) [IsIso p] : CoCartesianFibration p where
  mem := innerFibrations.of_isIso p
  exists_isCoCartesian_lift {x t} e :=
    ⟨_, Edge.mk ((inv p).app _ e.edge)
      (by rw [← δ_naturality_apply, e.src_eq]; simp) rfl,
      Edge.isCoCartesian_of_isIso _ _, by simp⟩

/-- CoCartesian fibrations are stable under base change: in a pullback square with sides
`t : X' ⟶ X`, `p' : X' ⟶ S'`, `p : X ⟶ S` and `b : S' ⟶ S`, the map `p'` is a coCartesian
fibration when `p` is. A coCartesian lift of an edge `e` of `S'` is assembled from `e` and a
coCartesian lift of its image in `S`. -/
lemma of_isPullback {X' S' : SSet.{u}} {t : X' ⟶ X} {p' : X' ⟶ S'} {p : X ⟶ S} {b : S' ⟶ S}
    (sq : IsPullback t p' p b) [CoCartesianFibration p] : CoCartesianFibration p' where
  mem := innerFibrations.of_isPullback sq (mem_innerFibrations p)
  exists_isCoCartesian_lift {x' t'} e' := by
    have hx : b.app _ (p'.app _ x') = p.app _ (t.app _ x') := by
      simpa using (ConcreteCategory.congr_hom (NatTrans.congr_app sq.w _) x').symm
    obtain ⟨y, f, hf, hfe⟩ := exists_isCoCartesian_lift (p := p) (x := t.app _ x')
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
    refine ⟨_, Edge.mk (yonedaEquiv φ) hsrc rfl, Edge.IsCoCartesian.of_isPullback sq
      (hf.of_edge_eq ?_), ?_⟩
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_fst, Equiv.apply_symm_apply]
    · simp only [Edge.map_edge, Edge.mk_edge]
      rw [← yonedaEquiv_comp, sq.lift_snd, Equiv.apply_symm_apply]

/-- A composite of coCartesian fibrations is a coCartesian fibration: lift an edge first along
`r` and then along `p`. -/
instance comp {Z : SSet.{u}} (p : X ⟶ S) (r : S ⟶ Z) [CoCartesianFibration p]
    [CoCartesianFibration r] : CoCartesianFibration (p ≫ r) where
  mem := innerFibrations.comp_mem _ _ (mem_innerFibrations p) (mem_innerFibrations r)
  exists_isCoCartesian_lift {x z} e := by
    obtain ⟨s, g, hg, hge⟩ := exists_isCoCartesian_lift (p := r) (x := p.app _ x)
      (Edge.mk e.edge (by rw [e.src_eq]; simp) e.tgt_eq)
    obtain ⟨y, f, hf, hfe⟩ := exists_isCoCartesian_lift (p := p) (x := x) g
    refine ⟨y, f, hf.comp (hg.of_edge_eq hfe.symm), ?_⟩
    simp only [Edge.map_edge, Edge.mk_edge] at hge hfe ⊢
    rw [NatTrans.comp_app, ConcreteCategory.comp_apply, hfe, hge]

end CoCartesianFibration

/-- A coCartesian transport of the fibers of `p : X ⟶ S` along an edge `e : s ⟶ t` of `S`: a
map of fibers `X_s ⟶ X_t` together with a homotopy `X_s × Δ[1] ⟶ X` lying over `e`, from the
inclusion of the fiber `X_s` to this map, whose edge `{x} × Δ[1]` is `p`-coCartesian for every
vertex `x` of `X_s`. The map of fibers is then a functor *associated to* `e`. -/
structure CoCartesianTransport {X S : SSet.{u}} (p : X ⟶ S) {s t : S _⦋0⦌} (e : Edge s t) where
  /-- The functor `X_s ⟶ X_t` of fibers associated to the edge `e`. -/
  functor : (fiber p s : SSet) ⟶ (fiber p t : SSet)
  /-- The homotopy from the inclusion of the fiber `X_s` to `functor`. -/
  homotopy : (fiber p s : SSet) ⊗ Δ[1] ⟶ X
  ι₀_homotopy : ι₀ ≫ homotopy = (fiber p s).ι
  ι₁_homotopy : ι₁ ≫ homotopy = functor ≫ (fiber p t).ι
  homotopy_comp : homotopy ≫ p = snd _ _ ≫ yonedaEquiv.symm e.edge
  /-- The edges `{x} × Δ[1]` of the homotopy are `p`-coCartesian. -/
  isCoCartesian (x : (fiber p s : SSet) _⦋0⦌) :
    (Edge.mk' (yonedaEquiv (lift (const x) (𝟙 Δ[1]) ≫ homotopy))).IsCoCartesian p

namespace CoCartesianTransport

attribute [reassoc (attr := simp)] ι₀_homotopy ι₁_homotopy homotopy_comp

variable {X S : SSet.{u}}

/-- Along an isomorphism `p`, every edge `e` of the base has a coCartesian transport: the
fibers are terminal, and the homotopy is `e` lifted along the inverse of `p`. -/
noncomputable def ofIsIso (p : X ⟶ S) [IsIso p] {s t : S _⦋0⦌} (e : Edge s t) :
    CoCartesianTransport p e where
  functor := (fiber.isTerminalOfIsIso p t).from _
  homotopy := snd _ _ ≫ yonedaEquiv.symm e.edge ≫ inv p
  ι₀_homotopy := by
    rw [← cancel_mono p]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [ι₀_snd_assoc, const_comp, Edge.yonedaEquiv_symm_edge_app_zero, fiber.ι_comp]
  ι₁_homotopy := by
    rw [← cancel_mono p]
    simp only [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
    rw [ι₁_snd_assoc, const_comp, Edge.yonedaEquiv_symm_edge_app_one, fiber.ι_comp,
      comp_const]
  homotopy_comp := by simp
  isCoCartesian _ := Edge.isCoCartesian_of_isIso _ _

end CoCartesianTransport

end SSet
