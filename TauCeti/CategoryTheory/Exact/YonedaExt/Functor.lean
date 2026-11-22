/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.Grp.Preadditive
public import Mathlib.Algebra.Group.Shrink
public import Mathlib.CategoryTheory.Preadditive.Opposite
public import TauCeti.CategoryTheory.Exact.YonedaExt.Injective

/-!
# `Ext¹` of an exact category as a bifunctor

Let `E` be an exact structure on `C`, with `C : Type u` and `Category.{v} C`. The Yoneda groups
`Ext¹_E(Z, X)` live in `Type (max u v)`. This file introduces the assumption
`E.HasSmallExt1.{w}` that every `Ext¹_E(Z, X)` is `w`-small, and under it the bifunctor
`Ext¹_E(-, -) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}`, with values the groups `Ext¹_E(Z, X)` shrunk to
`Type w`. The variable `X` acts by cobase change and the variable `Z` by base change; these
commute (`TauCeti.ExactStructure.Ext1.pushout_pullback`), and both are additive.

The contravariant functor `Ext¹_E(-, X)` kills the projectively trivial morphisms, so it
descends to the quotient `E/𝒫` by the ideal `𝒫` of projectively trivial morphisms. Dually, the
covariant functor `Ext¹_E(Z, -)` descends to the quotient `E/ℐ` by the ideal `ℐ` of injectively
trivial morphisms.

With enough projectives or enough injectives, `E.HasSmallExt1.{v}` holds: for an injective
presentation `X ⟶ I ⟶ K`, every class in `Ext¹_E(W, X)` is the base change of the presentation
along some `W ⟶ K`, and dually for a projective presentation of `W`.

## Main definitions

* `TauCeti.ExactStructure.HasSmallExt1`: every `Ext¹_E(Z, X)` is `w`-small.
* `TauCeti.ExactStructure.ext1Functor`: the bifunctor `Ext¹_E(-, -)`, with partial functors
  `E.ext1Functor.obj (op Z) = Ext¹_E(Z, -)` and `E.ext1Functor.flip.obj X = Ext¹_E(-, X)`.
* `TauCeti.ExactStructure.stableExt1Functor`: `Ext¹_E(-, X)` as a functor on `E/𝒫`.
* `TauCeti.ExactStructure.costableExt1Functor`: `Ext¹_E(Z, -)` as a functor on `E/ℐ`.

## Main results

* `TauCeti.ExactStructure.HasSmallExt1.standard`: `Ext¹` is `max u v`-small.
* `TauCeti.ExactStructure.EnoughInjectives.hasSmallExt1` and
  `TauCeti.ExactStructure.EnoughProjectives.hasSmallExt1`: with enough injectives or enough
  projectives, `Ext¹` is `v`-small.
* `TauCeti.ExactStructure.quotientFunctor_op_comp_stableExt1Functor` and
  `TauCeti.ExactStructure.quotientFunctor_comp_costableExt1Functor`: the descended functors
  restrict to `Ext¹_E(-, X)` and `Ext¹_E(Z, -)` along the quotient functors.

## Implementation notes

The setup follows Mathlib's `Ext` groups of an abelian category
(`Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic`): the smallness assumption
`TauCeti.ExactStructure.HasSmallExt1` is, like `CategoryTheory.HasExt`, an abbreviation for a
family of `Small` instances, so that it can be assumed as an instance argument, and the universe
`max u v` in which it always holds is provided by a lemma rather than an instance. As for
`CategoryTheory.HasExt`, instances of `TauCeti.ExactStructure.HasSmallExt1` should be introduced
selectively, since two of them in different universes would make the universe of `Ext¹`
ambiguous. Like `CategoryTheory.extFunctor`, the bifunctor takes values in `AddCommGrpCat.{w}`;
the elements of its values are those of `Shrink.{w} (E.Ext1 Z X)`, and the simp lemmas describe
its action through `equivShrink`.

## References

* Osamu Iyama, Hiroyuki Nakaoka, Yann Palu, *Auslander–Reiten theory in extriangulated
  categories*, <https://arxiv.org/abs/1805.03776> (v3), Definition 1.21, for the ideals `𝒫` and
  `ℐ` as the kernels of `Ext¹` from the left and from the right.
-/

public section

universe w v u

open CategoryTheory Limits Opposite

namespace TauCeti

namespace ExactStructure

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]
  (E : ExactStructure C)

/-! ### Smallness of `Ext¹` -/

/-- The property that every group `Ext¹_E(Z, X)` is `w`-small. Like Mathlib's
`CategoryTheory.HasExt`, it is an abbreviation for a family of `Small` instances. -/
abbrev HasSmallExt1 : Prop :=
  ∀ Z X : C, Small.{w} (E.Ext1 Z X)

/-- The groups `Ext¹_E(Z, X)` are `max u v`-small, as they live in `Type (max u v)`. -/
theorem HasSmallExt1.standard : E.HasSmallExt1.{max u v} :=
  fun _ _ ↦ small_self _

variable {E}

/-- **With enough injectives, `Ext¹` is `v`-small.** For an injective presentation
`X ⟶ I ⟶ K`, every class in `Ext¹_E(Z, X)` is a base change of the presentation along some
`Z ⟶ K`. -/
theorem EnoughInjectives.hasSmallExt1 (h : E.EnoughInjectives) : E.HasSmallExt1.{v} :=
  fun _ X ↦
    let P := h.injectivePresentation X
    small_of_surjective (P.extension.exists_mk_pullback_eq_of_isInjective
      P.isInjective_extension_obj)

/-- **With enough projectives, `Ext¹` is `v`-small.** For a projective presentation
`K ⟶ P ⟶ Z`, every class in `Ext¹_E(Z, X)` is a cobase change of the presentation along some
`K ⟶ X`. -/
theorem EnoughProjectives.hasSmallExt1 (h : E.EnoughProjectives) : E.HasSmallExt1.{v} :=
  fun Z _ ↦
    let P := h.projectivePresentation Z
    small_of_surjective fun ξ ↦ (Ext1.pullback_g_eq_zero_iff ⟨P.P, P.i, P.p, P.zero, P.conflation⟩
      ξ).1 ((isProjective_iff_forall_ext1_eq_zero _).1 P.isProjective _ _)

/-! ### The bifunctor `Ext¹_E(-, -)` -/

variable [E.HasSmallExt1.{w}]

variable (E) in
/-- **The bifunctor `Ext¹_E(-, -) : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w}`**, with values the groups
`Ext¹_E(Z, X)` shrunk to `Type w`. The first variable acts by base change and the second by
cobase change, which commute (`TauCeti.ExactStructure.Ext1.pushout_pullback`). Its partial
functors are `E.ext1Functor.obj (op Z) = Ext¹_E(Z, -)` and
`E.ext1Functor.flip.obj X = Ext¹_E(-, X)`. -/
@[expose]
noncomputable def ext1Functor : Cᵒᵖ ⥤ C ⥤ AddCommGrpCat.{w} where
  obj Z :=
    { obj X := .of (Shrink.{w} (E.Ext1 Z.unop X))
      map v := AddCommGrpCat.ofHom <| Shrink.addEquiv.symm.toAddMonoidHom.comp <|
        (AddMonoidHom.mk' (fun ξ ↦ ξ.pushout v) fun _ _ ↦ Ext1.add_pushout _ _ v).comp
          Shrink.addEquiv.toAddMonoidHom
      map_id _ := by ext; simp [Shrink.addEquiv]
      map_comp _ _ := by ext; simp [Shrink.addEquiv] }
  map u :=
    { app X := AddCommGrpCat.ofHom <| Shrink.addEquiv.symm.toAddMonoidHom.comp <|
        (AddMonoidHom.mk' (fun ξ ↦ ξ.pullback u.unop) fun _ _ ↦ Ext1.add_pullback _ _ _).comp
          Shrink.addEquiv.toAddMonoidHom
      naturality _ _ v := by ext; simp [Shrink.addEquiv, Ext1.pushout_pullback] }
  map_id _ := by ext; simp [Shrink.addEquiv]
  map_comp _ _ := by ext; simp [Shrink.addEquiv]

/-- A morphism `v : X ⟶ X'` acts on `Ext¹_E(Z.unop, -)` by cobase change along `v`. -/
@[simp]
theorem ext1Functor_obj_map_apply (Z : Cᵒᵖ) {X X' : C} (v : X ⟶ X')
    (ξ : (E.ext1Functor.obj Z).obj X) :
    (E.ext1Functor.obj Z).map v ξ =
      equivShrink _ (((equivShrink _).symm ξ).pushout v) :=
  (rfl)

/-- A morphism `u : Z ⟶ Z'` of `Cᵒᵖ` acts on `Ext¹_E(-, X)` by base change along `u.unop`. -/
@[simp]
theorem ext1Functor_map_app_apply {Z Z' : Cᵒᵖ} (u : Z ⟶ Z') (X : C)
    (ξ : (E.ext1Functor.obj Z).obj X) :
    (E.ext1Functor.map u).app X ξ =
      equivShrink _ (((equivShrink _).symm ξ).pullback u.unop) :=
  (rfl)

instance (Z : Cᵒᵖ) : (E.ext1Functor.obj Z).Additive where
  map_add := by
    intros
    ext
    simp only [ext1Functor_obj_map_apply, Ext1.pushout_add, AddCommGrpCat.hom_add_apply,
      equivShrink_add]
    -- The two sums differ only in the instance: `Shrink` versus the carrier of the group.
    rfl

instance : E.ext1Functor.Additive where
  map_add := by
    intros
    ext
    simp only [NatTrans.app_add, AddCommGrpCat.hom_add_apply, ext1Functor_map_app_apply,
      unop_add, Ext1.pullback_add, equivShrink_add]
    rfl

instance (X : C) : (E.ext1Functor.flip.obj X).Additive where
  map_add := by
    intros
    rw [Functor.flip_obj_map, Functor.flip_obj_map, Functor.flip_obj_map, Functor.map_add]
    rfl

/-! ### Descent to the stable categories -/

variable (E) in
/-- **`Ext¹_E(-, X)` on the projectively stable category `E/𝒫`.** Base change along a
projectively trivial morphism vanishes on `Ext¹`
(`TauCeti.ExactStructure.mem_projectivelyTrivialIdeal_iff_forall_ext1`), so `Ext¹_E(-, X)`
factors through the quotient by `𝒫`. -/
@[expose]
noncomputable def stableExt1Functor (X : C) :
    E.projectivelyTrivialIdeal.Quotientᵒᵖ ⥤ AddCommGrpCat.{w} :=
  (E.projectivelyTrivialIdeal.lift (E.ext1Functor.flip.obj X).rightOp
    fun _ _ _ hu ↦ (Functor.mem_kerIdeal_hom _).2 <| Quiver.Hom.unop_inj <|
      AddCommGrpCat.ext fun _ ↦
        (congrArg (equivShrink _) (mem_projectivelyTrivialIdeal_iff_forall_ext1.1 hu _ _)).trans
          ((Equiv.symm_apply_eq _).1 equivShrink_symm_zero).symm).leftOp

/-- `Ext¹_E(-, X)` on `E/𝒫` restricts to `Ext¹_E(-, X)` along the quotient functor. -/
theorem quotientFunctor_op_comp_stableExt1Functor (X : C) :
    E.projectivelyTrivialIdeal.quotientFunctor.op ⋙ E.stableExt1Functor X =
      E.ext1Functor.flip.obj X :=
  (rfl)

/-- The class of `u : Z' ⟶ Z` acts on `Ext¹_E(-, X)` by base change along `u`. -/
@[simp]
theorem stableExt1Functor_map_apply (X : C) {Z Z' : C} (u : Z' ⟶ Z)
    (ξ : (E.stableExt1Functor X).obj
      (Opposite.op (E.projectivelyTrivialIdeal.quotientFunctor.obj Z))) :
    (E.stableExt1Functor X).map (E.projectivelyTrivialIdeal.quotientFunctor.map u).op ξ =
      equivShrink _ (((equivShrink _).symm ξ).pullback u) :=
  (rfl)

instance (X : C) : (E.stableExt1Functor X).Additive :=
  inferInstanceAs (Functor.leftOp _).Additive

variable (E) in
/-- **`Ext¹_E(Z, -)` on the injectively costable category `E/ℐ`.** Cobase change along an
injectively trivial morphism vanishes on `Ext¹`
(`TauCeti.ExactStructure.mem_injectivelyTrivialIdeal_iff_forall_ext1`), so `Ext¹_E(Z, -)`
factors through the quotient by `ℐ`. -/
@[expose]
noncomputable def costableExt1Functor (Z : C) :
    E.injectivelyTrivialIdeal.Quotient ⥤ AddCommGrpCat.{w} :=
  E.injectivelyTrivialIdeal.lift (E.ext1Functor.obj (Opposite.op Z))
    fun _ _ _ hv ↦ (Functor.mem_kerIdeal_hom _).2 <| AddCommGrpCat.ext fun _ ↦
      (congrArg (equivShrink _) (mem_injectivelyTrivialIdeal_iff_forall_ext1.1 hv _ _)).trans
        ((Equiv.symm_apply_eq _).1 equivShrink_symm_zero).symm

/-- `Ext¹_E(Z, -)` on `E/ℐ` restricts to `Ext¹_E(Z, -)` along the quotient functor. -/
theorem quotientFunctor_comp_costableExt1Functor (Z : C) :
    E.injectivelyTrivialIdeal.quotientFunctor ⋙ E.costableExt1Functor Z =
      E.ext1Functor.obj (Opposite.op Z) :=
  (rfl)

/-- The class of `v : X ⟶ X'` acts on `Ext¹_E(Z, -)` by cobase change along `v`. -/
@[simp]
theorem costableExt1Functor_map_apply (Z : C) {X X' : C} (v : X ⟶ X')
    (ξ : (E.costableExt1Functor Z).obj (E.injectivelyTrivialIdeal.quotientFunctor.obj X)) :
    (E.costableExt1Functor Z).map (E.injectivelyTrivialIdeal.quotientFunctor.map v) ξ =
      equivShrink _ (((equivShrink _).symm ξ).pushout v) :=
  (rfl)

instance (Z : C) : (E.costableExt1Functor Z).Additive := by
  unfold costableExt1Functor
  infer_instance

end ExactStructure

end TauCeti
