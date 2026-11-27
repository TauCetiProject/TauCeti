/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CoCartesian.Nerve
public import TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad.Basic
import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
import TauCeti.AlgebraicTopology.SimplicialSet.Discrete
import TauCeti.CategoryTheory.ComposableArrows.Basic
import TauCeti.CategoryTheory.FiberedCategory.HomLift

/-!
# Nerves of categories of operators are `∞`-operads

A functor `F : E ⥤ Fin_*` to the category `TauCeti.FinPointed` of finite pointed sets gives a map
of nerves `nerveMap F : N(E) ⟶ N(Fin_*)`. This file gives conditions on `F` under which this map is
an `∞`-operad (`SSet.InfinityOperad.of_nerveMap`). They apply to the categories of operators of the
associative operad and of the operad `LM` of left modules
(`TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad.Assoc` and
`TauCeti.AlgebraicTopology.Quasicategory.InfinityOperad.LM`).

The conditions on `F` are the ordinary counterparts of the axioms of an `∞`-operad:

1. every inert map `F.obj x ⟶ n` lifts to a strongly coCartesian morphism with source `x`;
2. every family of objects `cᵢ` over `⟨1⟩` is the family of targets of strongly coCartesian lifts
   `y ⟶ cᵢ` of the inert projections `ρ i : ⟨n⟩ ⟶ ⟨1⟩`;
3. for every family `φᵢ : y ⟶ cᵢ` of morphisms over the projections `ρ i`, every object `x` and
   every map `e : F.obj x ⟶ F.obj y`, postcomposition with the `φᵢ` is a bijection from the
   morphisms `x ⟶ y` over `e` to the families of morphisms `x ⟶ cᵢ` over `e ≫ ρ i`.

The nerve of a category is an `∞`-category whose right mapping spaces are discrete
(`SSet.rightMappingSpace.constEdgeIso`), so the Segal maps of `nerveMap F` are maps between
discrete simplicial sets, and they are isomorphisms as soon as they are bijective on vertices,
which is condition 3. Strongly coCartesian morphisms give coCartesian edges of the nerve
(`CategoryTheory.nerve.isCoCartesian_edgeMk_of_isStronglyCocartesian`), which gives the lifts.
Condition 3 is asked for all morphisms over the projections, not only for the strongly
coCartesian ones: in `Assoc^⊗` and `LM^⊗`, whose only unary operations are identities, a morphism
over a given inert map is determined by its source and target, so the morphisms over the
projections are the strongly coCartesian lifts.

## Main results

* `SSet.InfinityOperad.of_nerveMap`: a functor to `Fin_*` satisfying the three conditions above
  has an `∞`-operad as its nerve.

## References

* J. Lurie, *Higher Algebra*, §2.1.1 (the nerve of the category of operators of a colored operad
  is an `∞`-operad).
-/

public section

universe u

open CategoryTheory Functor Limits HomotopicalAlgebra Opposite Simplicial TauCeti

namespace SSet

variable {E B : Type u} [SmallCategory E] [SmallCategory B]

/-! ### Mapping spaces of nerves over an edge -/

/-- The vertices of the space `Hom^R(x, y)_e` of maps lying over an edge `e`, for the map of nerves
induced by a functor `F`, are the morphisms `nerveEquiv x ⟶ nerveEquiv y` sent by `F` to the
morphism `t` of `e`. -/
private noncomputable def obj₀EquivOver (F : E ⥤ B) {x y : (nerve E) _⦋0⦌}
    (e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y)) (t : F.obj (nerveEquiv x) ⟶
      F.obj (nerveEquiv y)) (ht : nerve.homEquiv e = t) :
    (rightMappingSpaceOver (nerveMap F) e : SSet.{u}) _⦋0⦌ ≃
      {g : nerveEquiv x ⟶ nerveEquiv y // F.map g = t} where
  toFun v := ⟨nerve.homEquiv (rightMappingSpace.obj₀Equiv v.val), by
    rw [← ht, ← nerve.homEquiv_map_nerveMap, (rightMappingSpaceOver.mem_obj₀_iff e v.val).1
      v.property]⟩
  invFun g := ⟨rightMappingSpace.obj₀Equiv.symm (nerve.homEquiv.symm g.val),
    (rightMappingSpaceOver.mem_obj₀_iff e _).2 (nerve.homEquiv.injective (by
      rw [Equiv.apply_symm_apply, nerve.homEquiv_map_nerveMap, Equiv.apply_symm_apply, g.property,
        ht]))⟩
  left_inv v := by simp
  right_inv g := by simp

/-- Postcomposition with an edge `g` of the nerve composes the corresponding morphisms. -/
private lemma obj₀EquivOver_postcomp (F : E ⥤ B) {x y z : (nerve E) _⦋0⦌} (g : Edge y z)
    {e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y)}
    {e' : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ z)}
    (h : nerve.homEquiv e ≫ nerve.homEquiv (g.map (nerveMap F)) = nerve.homEquiv e') {t t'}
    (ht : nerve.homEquiv e = t) (ht' : nerve.homEquiv e' = t')
    (v : (rightMappingSpaceOver (nerveMap F) e : SSet.{u}) _⦋0⦌) :
    (obj₀EquivOver F e' t' ht' ((rightMappingSpaceOver.postcomp g h).app _ v)).val =
      (obj₀EquivOver F e t ht v).val ≫ nerve.homEquiv g := by
  obtain ⟨c⟩ := rightMappingSpace.postcomp_compStruct g (rightMappingSpace.obj₀Equiv v.val)
  rw [Equiv.symm_apply_apply] at c
  have hv := ConcreteCategory.congr_hom
    (NatTrans.congr_app (rightMappingSpaceOver.postcomp_ι g h) (op ⦋0⦌)) v
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hv
  -- The inclusion of `Hom^R(x, z)_{e'}` into `Hom^R(x, z)` takes a vertex to its underlying vertex.
  exact (congrArg (fun w ↦ nerve.homEquiv (rightMappingSpace.obj₀Equiv w)) hv).trans
    (nerve.homEquiv_comp c).symm

/-! ### The criterion -/

namespace InfinityOperad

variable (F : E ⥤ FinPointed.{u})

/-- The lifts `y ⟶ cᵢ` of inert projections in the nerve are morphisms of `E` over the inert
projections. -/
private lemma isHomLift_homEquiv_edge {y : (nerve E) _⦋0⦌}
    (L : InertProjectionLifts.{u} (nerveMap F) (F.obj (nerveEquiv y)) y)
    (i : Fin (F.obj (nerveEquiv y)).len) :
    F.IsHomLift (FinPointed.ρ i) (nerve.homEquiv (L.edge i)) := by
  refine isHomLift_iff_arrow_mk_eq.2 (ComposableArrows.mk₁_eq_mk₁_iff.1 ?_)
  rw [← nerve.edge_map_nerveMap, L.map_edge i, nerve.edgeMk_edge]

/-- On vertices, the Segal map of the nerve of `F` is postcomposition of morphisms of `E` with the
lifts of the inert projections, so it is bijective when that postcomposition is. -/
private lemma bijective_segalMap_app_zero {x y : (nerve E) _⦋0⦌}
    (L : InertProjectionLifts.{u} (nerveMap F) (F.obj (nerveEquiv y)) y)
    (e : Edge ((nerveMap F).app _ x) ((nerveMap F).app _ y))
    (segal : ∃ Φ : {g : nerveEquiv x ⟶ nerveEquiv y // F.IsHomLift (nerve.homEquiv e) g} ≃
      ∀ i, {h : nerveEquiv x ⟶ nerveEquiv (L.color i) //
        F.IsHomLift (nerve.homEquiv e ≫ FinPointed.ρ i) h},
      ∀ g i, (Φ g i).val = g.val ≫ nerve.homEquiv (L.edge i)) :
    Function.Bijective ((L.segalMap x e).app (op ⦋0⦌)) := by
  let φ (i : Fin (F.obj (nerveEquiv y)).len) := nerve.homEquiv (L.edge i)
  have ht (i : Fin (F.obj (nerveEquiv y)).len) :
      nerve.homEquiv (nerve.homEquiv.symm (nerve.homEquiv e ≫
        nerve.homEquiv ((L.edge i).map (nerveMap F)))) = nerve.homEquiv e ≫ F.map (φ i) := by
    rw [Equiv.apply_symm_apply, nerve.homEquiv_map_nerveMap]
    -- `φ i` is `nerve.homEquiv (L.edge i)` by definition.
    rfl
  let M (i : Fin (F.obj (nerveEquiv y)).len) : SSet.{u} := rightMappingSpaceOver (nerveMap F)
    (nerve.homEquiv.symm (nerve.homEquiv e ≫ nerve.homEquiv ((L.edge i).map (nerveMap F))))
  -- The vertices of the product are the families of vertices of the factors.
  have hπ : Function.Bijective fun (w : (∏ᶜ M) _⦋0⦌) i ↦ (Pi.π M i).app _ w := by
    convert (piObjIso M (op ⦋0⦌) ≪≫ Types.productIso.{0, u} _).toEquiv.bijective using 1
    funext w i
    rw [← piObjIso_hom_comp_π M (op ⦋0⦌) i, ← Types.productIso_hom_comp_eval.{0, u}]
    rfl
  refine (Function.Bijective.of_comp_iff' ((Equiv.piCongrRight fun i ↦
    obj₀EquivOver F _ _ (ht i)).bijective.comp hπ) _).1 ?_
  -- Read on morphisms of `E`, the Segal map is postcomposition with the `φ i`.
  have hvert : (fun (w : (∏ᶜ M) _⦋0⦌) i ↦ obj₀EquivOver F _ _ (ht i)
      ((Pi.π M i).app _ w)) ∘ (L.segalMap x e).app _ =
      (fun g i ↦ ⟨g.val ≫ φ i,
        (F.map_comp _ _).trans (congrArg (· ≫ F.map (φ i)) g.property)⟩) ∘
        obj₀EquivOver F e (nerve.homEquiv e) rfl := by
    funext v
    refine funext fun i ↦ Subtype.ext ?_
    dsimp only [Function.comp_apply]
    rw [← NatTrans.comp_app_apply, InertProjectionLifts.segalMap_π]
    exact obj₀EquivOver_postcomp F _ _ _ _ _
  obtain ⟨Φ, hΦ⟩ := segal
  let Ψ := ((Equiv.subtypeEquivRight fun g ↦ isHomLift_iff_map_eq.symm).trans Φ).trans
    (Equiv.piCongrRight fun i ↦ Equiv.subtypeEquivRight fun h ↦
      isHomLift_comp_iff_map_eq (isHomLift_homEquiv_edge F L i))
  have hΨ : ⇑Ψ = fun g i ↦ ⟨g.val ≫ φ i,
      (F.map_comp _ _).trans (congrArg (· ≫ F.map (φ i)) g.property)⟩ :=
    funext fun g ↦ funext fun i ↦ Subtype.ext (hΦ _ i)
  exact (congrArg Function.Bijective hvert).mpr
    (hΨ ▸ Ψ.bijective.comp (obj₀EquivOver F e _ rfl).bijective)

/-- **The nerve of a category of operators is an `∞`-operad.** Let `F : E ⥤ Fin_*` be a functor
such that inert maps lift to strongly coCartesian morphisms with any given source (`lift`), every
family of objects over `⟨1⟩` is the family of targets of strongly coCartesian lifts of the inert
projections from one object (`tuple`), and, for every family of morphisms `φ i : y ⟶ c i` over
the inert projections `ρ i`, postcomposition with the `φ i` is a bijection from the morphisms
`x ⟶ y` over a map `e` to the families of morphisms `x ⟶ c i` over `e ≫ ρ i` (`segal`).
Then the map of nerves `nerveMap F : N(E) ⟶ N(Fin_*)` is an `∞`-operad. -/
theorem of_nerveMap
    (lift : ∀ {x : E} {n : FinPointed.{u}} (g : F.obj x ⟶ n), g.IsInert →
      ∃ (y : E) (φ : x ⟶ y), F.IsStronglyCocartesian g φ)
    (tuple : ∀ (n : FinPointed.{u}) (c : Fin n.len → E), (∀ i, F.obj (c i) = FinPointed.mk 1) →
      ∃ (y : E) (φ : ∀ i, y ⟶ c i), F.obj y = n ∧
        ∀ i, F.IsStronglyCocartesian (FinPointed.ρ i) (φ i))
    (segal : ∀ {x y : E} {c : Fin (F.obj y).len → E} (φ : ∀ i, y ⟶ c i),
      (∀ i, F.IsHomLift (FinPointed.ρ i) (φ i)) → ∀ e : F.obj x ⟶ F.obj y,
        ∃ Φ : {g : x ⟶ y // F.IsHomLift e g} ≃
          ∀ i, {h : x ⟶ c i // F.IsHomLift (e ≫ FinPointed.ρ i) h},
          ∀ g i, (Φ g i).val = g.val ≫ φ i) :
    InfinityOperad.{u} (nerveMap F) where
  exists_isCoCartesian_lift_of_inert {x t} e he := by
    -- The morphism of `e` is `e.edge.hom` up to the identification of its endpoints.
    have h₀ := ComposableArrows.mk₁_eq_mk₁_iff.1 (nerve.mk₁_homEquiv_apply e)
    have hinert : (nerve.homEquiv e).IsInert := by
      obtain ⟨hX, hY, h⟩ := (Arrow.mk_eq_mk_iff _ _).1 h₀
      exact (FinPointed.inert_iff _).1 (FinPointed.inert.of_eq he hX.symm hY.symm h)
    obtain ⟨y, φ, hφ⟩ := lift (x := nerveEquiv x) (n := nerveEquiv t) (nerve.homEquiv e) hinert
    refine ⟨nerveEquiv.symm y, nerve.homEquiv.symm φ,
      (nerve.isCoCartesian_edgeMk_of_isStronglyCocartesian (R := F.obj (nerveEquiv x)) F
        (nerve.homEquiv e) φ).of_edge_eq rfl,
      (Edge.map_edge _ _).trans ((nerveMap_app_mk₁ F φ).trans ?_)⟩
    exact (ComposableArrows.mk₁_eq_mk₁_iff.2 ((isHomLift_iff_arrow_mk_eq.1 hφ.toIsHomLift).trans
      h₀)).trans (ComposableArrows.mk₁_hom e.edge)
  exists_inertProjectionLifts n c hc := by
    obtain ⟨y, φ, hy, hφ⟩ := tuple n (fun i ↦ nerveEquiv (c i)) fun i ↦
      (congrArg nerveEquiv (hc i)).trans (Equiv.apply_symm_apply _ _)
    refine ⟨nerveEquiv.symm y,
      { app_eq := by rw [nerveMap_app_nerveEquiv_symm, hy]
        color := c
        edge i := nerve.homEquiv.symm (φ i)
        isCoCartesian i :=
          (nerve.isCoCartesian_edgeMk_of_isStronglyCocartesian F (FinPointed.ρ i) (φ i)).of_edge_eq
            rfl
        map_edge i := (Edge.map_edge _ _).trans ((nerveMap_app_mk₁ F (φ i)).trans
          (ComposableArrows.mk₁_eq_mk₁_iff.2 (isHomLift_iff_arrow_mk_eq.1 inferInstance))) }, rfl⟩
  weakEquivalence_segalMap {n y} L x e := by
    -- The vertex `y` lies over `⟨n⟩`.
    obtain rfl : F.obj (nerveEquiv y) = n :=
      (congrArg nerveEquiv L.app_eq).trans (Equiv.apply_symm_apply _ _)
    -- The Segal map is a map of discrete simplicial sets, hence an isomorphism as soon as it is
    -- bijective on vertices.
    have hdisc (z : (nerve E) _⦋0⦌) (s) (n : ℕ) := Subcomplex.surjective_map_const
      (A := rightMappingSpaceOver (nerveMap F) (x := x) (y := z) s)
      (rightMappingSpace.surjective_map_const_of_isStrictSegal) n
    have := isIso_of_bijective_app_zero (L.segalMap x e) (hdisc _ _)
      (surjective_piObj_map_const _ fun _ ↦ hdisc _ _)
      (bijective_segalMap_app_zero F L e (segal _ (isHomLift_homEquiv_edge F L) _))
    infer_instance

end InfinityOperad

end SSet
