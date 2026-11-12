/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual.Stable
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The Auslander–Reiten translate as a functor

Let `A` be an algebra over a commutative ring `R` and `E` an injective `R`-module, with
`D = Hom_R(-, E)`. The Auslander–Reiten translate `τ = D Tr` is a functor from finitely presented
`A`-modules modulo maps through projectives to `A`-modules modulo maps through injectives:

* the Auslander–Bridger transpose `Tr` is a functor from finitely presented left modules modulo
  projectives to the opposite of finitely presented right modules modulo projectives
  (`TauCeti.stableTranspose`);
* `D` sends projective right modules to injective left modules, so it carries maps through
  projectives to maps through injectives, and descends to a functor from the opposite of right
  modules modulo projectives to left modules modulo injectives (`TauCeti.stableMatlisDualOp`, in
  `TauCeti.Algebra.Category.ModuleCat.MatlisDual.Stable`).

Defining `τ` as the composite of these functors makes it a functor without choices beyond the
presentations defining `Tr`; changing them gives an isomorphic functor. Over a field, with
`E = k`, this is the translate of `TauCeti.AuslanderReitenTranslate`, in the stable category
(`TauCeti.AuslanderReitenTranslate.linearEquivMatlisDual`).

## Main definitions

* `TauCeti.stableTranslateFunctor` and `TauCeti.stableTranslate`: the translate `τ = D Tr`, from
  chosen presentations, and from the presentations of `TauCeti.stableTranspose`.

## Main results

* `TauCeti.stableTranslateFunctorIso`: the translate does not depend on the presentations, with
  components `TauCeti.stableTranslateFunctorIso_hom_app`.
* `TauCeti.stableTranslateFunctorObjIso` and `TauCeti.stableTranslateFunctor_map`: on objects and
  maps, the translate is the class of `D Tr`.
* `TauCeti.stableTranslate_def`: the translate is `stableTranslateFunctor` for the presentations of
  `TauCeti.stableTranspose`.
* `TauCeti.isZero_stableTranslateFunctor_obj`: the translate of a projective module vanishes.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Section IV.1.
* M. Auslander, M. Bridger, *Stable module theory*, Mem. Amer. Math. Soc. **94** (1969),
  Section 2.1.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type*) [CommRing R] {A : Type u} [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]

variable {R E}

variable (R E) in
/-- **The Auslander–Reiten translate** `τ = D Tr` determined by a choice of finite projective
presentations: the stable transpose followed by the Matlis dual on stable categories. -/
def stableTranslateFunctor (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  stableTransposeFunctor P ⋙ (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E

/-- The translate determined by presentations is the stable transpose followed by the stable
Matlis dual. -/
theorem stableTranslateFunctor_def (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    stableTranslateFunctor R E P =
      stableTransposeFunctor P ⋙ (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E :=
  (rfl)

variable (R E) in
/-- On objects, the translate is the stable Matlis dual of the transpose of the chosen
presentation. -/
theorem stableTranslateFunctor_obj (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTranslateFunctor R E P).obj M =
      (stableMatlisDualOp R E).obj
        (op ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.obj
          (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p)))) := by
  rw [stableTranslateFunctor, Functor.comp_obj, Functor.comp_obj, stableTransposeFunctor_obj]
  rfl

instance (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) : (stableTranslateFunctor R E P).Additive := by
  unfold stableTranslateFunctor
  infer_instance

variable (R E) in
/-- **The translate does not depend on the presentations**: two choices of finite projective
presentations give isomorphic translates. -/
def stableTranslateFunctorIso (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    stableTranslateFunctor R E P ≅ stableTranslateFunctor R E Q :=
  Functor.isoWhiskerRight (stableTransposeFunctorIso P Q) _

/-- The comparison of translates is the comparison of transposes, whiskered by the stable Matlis
dual. -/
theorem stableTranslateFunctorIso_def (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    stableTranslateFunctorIso R E P Q =
      eqToIso (stableTranslateFunctor_def P) ≪≫
        Functor.isoWhiskerRight (stableTransposeFunctorIso P Q)
          ((ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E) ≪≫
        eqToIso (stableTranslateFunctor_def Q).symm := by
  ext
  simp only [stableTranslateFunctorIso, Iso.trans_hom, eqToIso.hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, eqToHom_app]
  -- The two `eqToHom`s come from `stableTranslateFunctor_def`, whose sides agree by unfolding
  -- `stableTranslateFunctor` in this file; `erw` matches them with `eqToHom_refl` up to that
  -- unfolding.
  erw [eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id]

variable (R E) in
/-- On objects, the translate is the class of `D Tr M`, the Matlis dual of the transpose of the
chosen presentation of `M`. -/
def stableTranslateFunctorObjIso (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTranslateFunctor R E P).obj M ≅
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj
          (op (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p)))) :=
  -- `stableTransposeFunctor` is not exposed outside its module, so the object equation
  -- `stableTranslateFunctor_obj` holds by `rfl` only there, and is transported here by `eqToIso`.
  eqToIso (stableTranslateFunctor_obj R E P M) ≪≫ stableMatlisDualOpObjIso R E _

theorem stableTranslateFunctorObjIso_def (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) (M : FinitelyPresentedStableModule.{u, max u v} A) :
    stableTranslateFunctorObjIso R E P M =
      eqToIso (stableTranslateFunctor_obj R E P M) ≪≫ stableMatlisDualOpObjIso R E _ :=
  (rfl)

/-- **The translate of a map is the Matlis dual of its transpose**, through
`stableTranslateFunctorObjIso`: if a map `t` of right modules represents the stable transpose of
`g` (`AuslanderReitenTranspose.stableMap`), then the translate of `g` is the class of `D t`. -/
theorem stableTranslateFunctor_map (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) {M N : FinitelyPresentedStableModule.{u, max u v} A}
    (g : M ⟶ N) (t : ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P N).p) ⟶
      ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p))
    (ht : (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map t =
      AuslanderReitenTranspose.stableMap (P M).exact.linearMap_comp_eq_zero (P N).exact
        (P N).surjective g.hom) :
    (stableTranslateFunctor R E P).map g =
      (stableTranslateFunctorObjIso R E P M).hom ≫
        (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
          ((ModuleCat.matlisDualOp R E).map t.op) ≫
        (stableTranslateFunctorObjIso R E P N).inv := by
  simp only [stableTranslateFunctor, Functor.comp_obj, Functor.op_obj, ObjectProperty.ι_obj,
    Functor.comp_map, stableTransposeFunctor_map, ModuleCat.of_coe, ← ht, Functor.op_map, unop_comp,
    eqToHom_unop, Quiver.Hom.unop_op, Category.assoc, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom, ObjectProperty.homMk_hom,
    op_comp, eqToHom_op, Functor.map_comp, eqToHom_map,
    stableMatlisDualOp_map_projectiveStableFunctor_map, ModuleCat.matlisDualOp_map,
    stableTranslateFunctorObjIso, Iso.trans_hom, Iso.trans_inv]
  -- Both sides are now the same composite, up to the proofs inside the `eqToHom`s.
  rfl

/-- **The comparison of translates is the Matlis dual of the comparison of transposes**: if a map
`t` of right modules represents the comparison `Tr (Q M) ≅ Tr (P M)` of the two transposes of `M`,
then the component at `M` of the comparison of translates is the class of `D t`. -/
theorem stableTranslateFunctorIso_hom_app
    (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
      FiniteProjectivePresentation M.obj.as) (M : FinitelyPresentedStableModule.{u, max u v} A)
    (t : ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (Q M).p) ⟶
      ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p))
    (ht : (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map t =
      ((Q M).stableTransposeIso (P M)).hom.hom) :
    (stableTranslateFunctorIso R E P Q).hom.app M =
      (stableTranslateFunctorObjIso R E P M).hom ≫
        (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
          ((ModuleCat.matlisDualOp R E).map t.op) ≫
        (stableTranslateFunctorObjIso R E Q M).inv := by
  simp only [stableTranslateFunctorIso, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app]
  rw [← Iso.app_hom, stableTransposeFunctorIso_app]
  rw [FiniteProjectivePresentation.stableTransposeIso_hom] at ht
  simp only [Iso.trans_hom, eqToIso.hom, Iso.op_hom, Iso.symm_hom, eqToIso.inv, Functor.comp_map,
    Functor.op_obj, ObjectProperty.ι_obj, Functor.op_map, unop_comp, eqToHom_unop,
    Quiver.Hom.unop_op, Category.assoc, ObjectProperty.ι_map,
    ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.eqToHom_hom,
    FiniteProjectivePresentation.stableTransposeIso_hom, ModuleCat.of_coe, ← ht, op_comp,
    eqToHom_op, Functor.map_comp,
    eqToHom_map, stableMatlisDualOp_map_projectiveStableFunctor_map, ModuleCat.matlisDualOp_map,
    stableTranslateFunctorObjIso, Iso.trans_inv]
  -- Both sides are now the same composite, up to the proofs inside the `eqToHom`s.
  rfl

@[simp]
theorem stableTranslateFunctorIso_refl (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    stableTranslateFunctorIso R E P P = Iso.refl _ := by
  rw [stableTranslateFunctorIso, stableTransposeFunctorIso_refl, Functor.isoWhiskerRight_refl]
  rfl

@[simp]
theorem stableTranslateFunctorIso_trans
    (P Q Q' : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
      FiniteProjectivePresentation M.obj.as) :
    stableTranslateFunctorIso R E P Q ≪≫ stableTranslateFunctorIso R E Q Q' =
      stableTranslateFunctorIso R E P Q' := by
  rw [stableTranslateFunctorIso, stableTranslateFunctorIso, stableTranslateFunctorIso]
  exact (Functor.isoWhiskerRight_trans _ _ _).symm.trans
    (congrArg (Functor.isoWhiskerRight · _) (stableTransposeFunctorIso_trans P Q Q'))

@[simp]
theorem stableTranslateFunctorIso_symm (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    (stableTranslateFunctorIso R E P Q).symm = stableTranslateFunctorIso R E Q P := by
  rw [stableTranslateFunctorIso, stableTranslateFunctorIso]
  exact (Functor.isoWhiskerRight_symm _ _).trans
    (congrArg (Functor.isoWhiskerRight · _) (stableTransposeFunctorIso_symm P Q))

/-- **The translate of a projective module vanishes.** -/
theorem isZero_stableTranslateFunctor_obj (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) {M : FinitelyPresentedStableModule.{u, max u v} A}
    (hM : Module.Projective A M.obj.as) : IsZero ((stableTranslateFunctor R E P).obj M) := by
  have hM' := ((ExactStructure.abelian _).isZero_projectiveStableFunctor_obj_iff M.obj.as).2
    ((ExactStructure.abelian_isProjective_iff _).2
      (ModuleCat.projective_of_categoryTheory_projective _))
  rw [MorphismIdeal.quotientFunctor_obj_as] at hM'
  exact Functor.map_isZero _ (IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) M hM')

variable (R E A) in
/-- **The Auslander–Reiten translate** `τ = D Tr`, from finitely presented `A`-modules modulo
projectives to `A`-modules modulo injectives, with the presentations of
`TauCeti.stableTranspose`. -/
def stableTranslate :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  stableTranspose.{u, v} A ⋙ (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E

/-- The translate is `stableTranslateFunctor` for the presentations of `TauCeti.stableTranspose`, so
`stableTranslateFunctorObjIso`, `stableTranslateFunctor_map`, `stableTranslateFunctorIso` and
`isZero_stableTranslateFunctor_obj` apply to it. -/
theorem stableTranslate_def :
    stableTranslate R A E = stableTranslateFunctor R E (fun M ↦
      letI := M.property
      FiniteProjectivePresentation.ofFinitePresentation (M := M.obj.as)) := by
  rw [stableTranslate, stableTranspose_def, stableTranslateFunctor]

instance : (stableTranslate R A E).Additive := by
  unfold stableTranslate
  infer_instance

end TauCeti
