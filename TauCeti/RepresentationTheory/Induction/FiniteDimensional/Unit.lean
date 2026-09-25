/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Induction.FiniteDimensional.Basic
public import TauCeti.RepresentationTheory.Induction.Restriction

/-!
# The unit map into an induced representation

For a finite-index subgroup `S` of a group `G`, every finite-dimensional representation `A` of
`S` maps naturally into the restriction of `Ind_S^G A`.  On Mathlib's induced carrier this is the
map `a ↦ ⟦1 ⊗ a⟧`; this file transports the unit of Mathlib's adjunction `Rep.indResAdjunction`
to the small carrier used by `TauCeti.indFDRep`.

The map is natural in `A` and injective.  Injectivity is the representation-theoretic statement
that the identity coset supplies a distinguished copy of `A` inside the restriction of its induced
representation.  It is used in Clifford theory to show that induction preserves the property of
lying over a constituent.

The scalar field and the group share one universe: `Rep.indResAdjunction` relates functors on a
single `Rep` carrier universe, so its unit at the forgotten `A` lives in the same universe as `G`,
exactly as for `TauCeti.indFDRepForgetIso` and `TauCeti.finrank_hom_indFDRep`.

## Main definitions

* `FDRep.indFDRepUnit`: the canonical map `A ⟶ Res_S (Ind_S^G A)`.

## Main statements

* `FDRep.forget₂_map_indFDRepUnit`: after forgetting finite-dimensionality, the unit is Mathlib's
  adjunction unit followed by the small-carrier comparison.
* `FDRep.indFDRepUnit_naturality`: the unit commutes with induction of intertwiners.
* `FDRep.indFDRepUnit_apply`: the map on the induced-representation model.
* `FDRep.indFDRepUnit_injective`: the unit map is injective.
-/

public section

open CategoryTheory

universe u

namespace FDRep

open TauCeti

variable {k G : Type u} [Field k] [Group G] {S : Subgroup G} [S.FiniteIndex]

/-- The unit of induction--restriction on finite-dimensional representations: the unit of
Mathlib's adjunction `Rep.indResAdjunction`, transported to the small carrier of `indFDRep`
along `indFDRepForgetIso`.  Under that comparison it sends `a` to the generator `⟦1 ⊗ a⟧`. -/
noncomputable def indFDRepUnit (A : FDRep k S) : A ⟶ resFDRep S (indFDRep A) :=
  -- The universes of `Rep.indResAdjunction` are pinned: left to unification, the constraint
  -- `max u u ?w = u` makes elaborating this composite cost most of a second (see #8353).
  (forget₂ (FDRep k S) (Rep k S)).preimage <|
    (Rep.indResAdjunction.{u, u, u, u} k S.subtype).unit.app
        ((forget₂ (FDRep k S) (Rep k S)).obj A) ≫
      (Rep.resFunctor S.subtype).map (indFDRepForgetIso A).inv

/-- After forgetting finite-dimensionality, `indFDRepUnit` is Mathlib's adjunction unit followed
by the restricted small-carrier comparison. -/
theorem forget₂_map_indFDRepUnit (A : FDRep k S) :
    (forget₂ (FDRep k S) (Rep k S)).map (indFDRepUnit A) =
      (Rep.indResAdjunction k S.subtype).unit.app ((forget₂ (FDRep k S) (Rep k S)).obj A) ≫
        (Rep.resFunctor S.subtype).map (indFDRepForgetIso A).inv :=
  Functor.map_preimage _ _

/-- **Naturality of the unit**: for an intertwiner `f : A ⟶ B`, following `indFDRepUnit A` by the
restriction of `indFDRepMap f` is the same as following `f` by `indFDRepUnit B`. -/
theorem indFDRepUnit_naturality {A B : FDRep k S} (f : A ⟶ B) :
    indFDRepUnit A ≫ (Action.res (FGModuleCat k) S.subtype).map (indFDRepMap f) =
      f ≫ indFDRepUnit B := by
  apply (forget₂ (FDRep k S) (Rep k S)).map_injective
  rw [Functor.map_comp, Functor.map_comp, MonoidHom.forget₂_map_actionRes,
    forget₂_map_indFDRepUnit,
    forget₂_map_indFDRepUnit, forget₂_map_indFDRepMap, Functor.map_comp, Functor.map_comp]
  -- `forget₂_map_indFDRepUnit` puts Mathlib's adjunction unit into the goal, and its domain and
  -- codomain are `(𝟭 (Rep k S)).obj ((forget₂ (FDRep k S) (Rep k S)).obj A)` and
  -- `(Rep.resFunctor S.subtype).obj ((forget₂ (FDRep k G) (Rep k G)).obj (indFDRep A))`, which
  -- match the goal's `(forget₂ (FDRep k S) (Rep k S)).obj A` and its `resFDRep S (indFDRep A)`
  -- counterpart only definitionally.  The rewritten composite is therefore not type-correct at
  -- `implicit` transparency, so `rw [Category.assoc]` fails to find `(?f ≫ ?g) ≫ ?h` in it; no
  -- rewrite can repair a wrapper mismatch in the *type* of a morphism, and restating the goal
  -- re-elaborates the composite with the functor applications the remaining rewrites match on.
  change _ ≫ (Rep.resFunctor S.subtype).map (indFDRepForgetIso A).hom ≫
      (Rep.resFunctor S.subtype).map
        ((Rep.indFunctor k S.subtype).map
          ((forget₂ (FDRep k S) (Rep k S)).map f)) ≫
        (Rep.resFunctor S.subtype).map (indFDRepForgetIso B).inv = _
  rw [Category.assoc, Iso.map_inv_hom_id_assoc]
  -- `rw` performs this last rewrite as well, but the two sides then still differ in the instance
  -- paths behind the `resFDRep` and `Rep.resFunctor` wrappers, which its closing reducible `rfl`
  -- does not see; `erw` finishes up to those.
  erw [Adjunction.unit_naturality_assoc]

/-- On Mathlib's induced carrier, `indFDRepUnit` is the generator map `a ↦ ⟦1 ⊗ a⟧`. -/
theorem indFDRepUnit_apply (A : FDRep k S) (a : A) :
    (indFDRepForgetIso A).hom.hom (indFDRepUnit A a) =
      Representation.IndV.mk S.subtype
        ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 a := by
  -- Applying an `FDRep` morphism to an element is applying its forgotten intertwiner, so the goal
  -- can be restated through `forget₂_map_indFDRepUnit`.
  change (indFDRepForgetIso A).hom.hom
    (((forget₂ (FDRep k S) (Rep k S)).map (indFDRepUnit A)).hom a) = _
  rw [forget₂_map_indFDRepUnit]
  -- The composite's codomain is `Rep.resFunctor`'s restriction while the goal's is `resFDRep`'s,
  -- so the `Semiring k` instance paths differ and `rw` cannot match these lemmas; `erw` can.
  erw [Rep.hom_comp, Representation.IntertwiningMap.comp_apply, Rep.resMap_hom_apply S.subtype,
    Rep.hom_inv_apply]
  simp [Rep.indResAdjunction, Rep.indResHomEquiv]

/-- The unit map from a representation to the restriction of its induction is injective. -/
theorem indFDRepUnit_injective (A : FDRep k S) : Function.Injective (indFDRepUnit A) := by
  intro a b hab
  have h : (indFDRepForgetIso A).hom.hom (indFDRepUnit A a) =
      (indFDRepForgetIso A).hom.hom (indFDRepUnit A b) :=
    congrArg (indFDRepForgetIso A).hom.hom hab
  rw [indFDRepUnit_apply, indFDRepUnit_apply] at h
  let _ : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  -- The universes of `Rep.indCoindIso` are pinned throughout: left to unification, the
  -- constraint `max ?w u = u` makes the `rw [show …]` below cost seconds (see #8353).
  have h' := congrArg
    (fun x => ((Rep.indCoindIso.{u, u, u}
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom x).1 1) h
  have heval (x : (forget₂ (FDRep k S) (Rep k S)).obj A) :
      ((Rep.indCoindIso.{u, u, u} ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom
        (Representation.IndV.mk S.subtype
          ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 x)).1 1 = x := by
    -- Pass from the bundled representation morphism to its linear map so the generated
    -- `indCoindIso_hom_hom_toLinearMap` equation can rewrite it.
    change (((Rep.indCoindIso.{u, u, u}
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom.toLinearMap
        (Representation.IndV.mk S.subtype
          ((forget₂ (FDRep k S) (Rep k S)).obj A).ρ 1 x))).1 1 = x
    rw [show (Rep.indCoindIso.{u, u, u}
      ((forget₂ (FDRep k S) (Rep k S)).obj A)).hom.hom.toLinearMap =
        Rep.indToCoind ((forget₂ (FDRep k S) (Rep k S)).obj A) from
      Rep.indCoindIso_hom_hom_toLinearMap.{u, u, u} _]
    simp only [FGModuleCat.obj_carrier, LinearMap.coe_comp, Function.comp_apply,
      TensorProduct.mk_apply, Representation.Coinvariants.lift_mk, TensorProduct.lift.tmul,
      LinearEquiv.coe_coe, MonoidAlgebra.coeffLinearEquiv_apply,
      MonoidAlgebra.coeff_single, Finsupp.linearCombination_single, one_smul]
    -- The remaining subtype coercion is the defining codomain restriction in `indToCoind`.
    change (Rep.indToCoindAux
      ((forget₂ (FDRep k S) (Rep k S)).obj A) 1 x) 1 = x
    exact Rep.indToCoindAux_self 1 x
  exact (heval a).symm.trans (h'.trans (heval b))

end FDRep
