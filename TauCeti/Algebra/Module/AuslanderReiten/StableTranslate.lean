/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.AuslanderReiten.Functor
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Opposite
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor
public import TauCeti.CategoryTheory.Exact.Stable.Injective
import TauCeti.CategoryTheory.Exact.Injective
import TauCeti.CategoryTheory.Exact.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
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
  projectives to maps through injectives, and descends to a functor from right modules modulo
  projectives to the opposite of left modules modulo injectives (`TauCeti.stableMatlisDualOp`).

Defining `τ` as the composite of these functors makes it a functor without choices beyond the
presentations defining `Tr`; changing them gives an isomorphic functor. Over a field, with
`E = k`, this is the translate of `TauCeti.AuslanderReitenTranslate`, in the stable category.

## Main definitions

* `TauCeti.stableMatlisDualOp`: the Matlis dual on stable categories.
* `TauCeti.stableTranslateOf` and `TauCeti.stableTranslate`: the translate `τ = D Tr`, from
  chosen presentations, and from the presentations of `TauCeti.stableTranspose`.

## Main results

* `TauCeti.projectiveStableIdeal_op_le_comap_matlisDualOp`: the Matlis dual of a map through a
  projective right module factors through an injective left module.
* `TauCeti.stableTranslateOfIso`: the translate does not depend on the presentations.
* `TauCeti.stableTranslateOfObjIso`: on objects, the translate is the class of `D Tr M`.
* `TauCeti.isZero_stableTranslateOf_obj`: the translate of a projective module vanishes.
* `TauCeti.AuslanderReitenTranslate.linearEquivMatlisDual`: the translate of a presentation over a
  base `k` is the case `E = k`.

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

/-- **The translate of a presentation is a Matlis dual with values in the base.** For a
`k`-algebra `A` and a map `p₁ : P₁ → P₀`, `TauCeti.AuslanderReitenTranslate k p₁` is the Matlis
dual `Hom_k(Tr p₁, k)`, with the same action of `A`. -/
def AuslanderReitenTranslate.linearEquivMatlisDual {k : Type*} [CommRing k] [Algebra k A]
    {P₀ P₁ : Type*} [AddCommGroup P₀] [Module A P₀] [AddCommGroup P₁] [Module A P₁]
    (p₁ : P₁ →ₗ[A] P₀) :
    AuslanderReitenTranslate k p₁ ≃ₗ[A] MatlisDual k k (AuslanderReitenTranspose p₁) :=
  { (MatlisDual.equivLinearMap k k (AuslanderReitenTranspose p₁)).symm with
    map_smul' := fun a φ ↦ MatlisDual.ext fun x ↦ by
      simp [MatlisDual.smul_apply, AuslanderReitenTranslate.smul_apply] }

/-- **The Matlis dual of a map through a projective factors through an injective.** The dual
`D = Hom_R(-, E)` of a projective right `A`-module is an injective left `A`-module, so `D` carries
the ideal of maps through projective right modules into the ideal of maps through injective left
modules. -/
theorem projectiveStableIdeal_op_le_comap_matlisDualOp :
    (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableIdeal.op ≤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableIdeal.comap
        (ModuleCat.matlisDualOp R E (A := A)) := by
  intro X Y f hf
  rw [MorphismIdeal.mem_op_hom, ExactStructure.mem_projectiveStableIdeal_iff,
    ObjectProperty.factorsThrough_iff] at hf
  obtain ⟨P, hP, i, p, h⟩ := hf
  rw [MorphismIdeal.mem_comap_hom, ExactStructure.mem_injectiveStableIdeal_iff,
    ObjectProperty.factorsThrough_iff]
  have : Projective P := (ExactStructure.abelian_isProjective_iff P).1 hP
  have : Module.Projective Aᵐᵒᵖ P := P.projective_of_module_projective
  refine ⟨(ModuleCat.matlisDualOp R E).obj (op P), ?_, (ModuleCat.matlisDualOp R E).map p.op,
    (ModuleCat.matlisDualOp R E).map i.op, ?_⟩
  · rw [ExactStructure.abelian_isInjective_iff]
    have := Module.injective_object_of_injective_module A (MatlisDual R E P)
    exact Injective.of_iso (ModuleCat.matlisDualOpObjEquiv R E P).toModuleIso.symm this
  · rw [← Functor.map_comp, ← op_comp, ← h]
    rfl

/-- **The Matlis dual on stable categories**: `D = Hom_R(-, E)` as a functor from right
`A`-modules modulo projectives, contravariantly, to left `A`-modules modulo injectives. -/
def stableMatlisDualOp :
    ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).ProjectiveStableCategory)ᵒᵖ ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  (MorphismIdeal.opQuotientEquivalence _).inverse ⋙
    MorphismIdeal.map _ _ (ModuleCat.matlisDualOp R E)
      (projectiveStableIdeal_op_le_comap_matlisDualOp R E)

/-- On the class of a right module `N`, the stable Matlis dual is the class of `D N`. -/
def stableMatlisDualOpObjIso (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    (stableMatlisDualOp R E).obj
        (op ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.obj N)) ≅
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj (op N)) := by
  let I := (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableIdeal
  have h : op (I.quotientFunctor.obj N) =
      I.opQuotientEquivalence.functor.obj (I.op.quotientFunctor.obj (op N)) := by
    rw [MorphismIdeal.opQuotientEquivalence_functor, MorphismIdeal.opQuotientFunctor_obj]
  exact (MorphismIdeal.map _ _ _ (projectiveStableIdeal_op_le_comap_matlisDualOp R E)).mapIso
    ((I.opQuotientEquivalence.inverse.mapIso (eqToIso h)) ≪≫
        (I.opQuotientEquivalence.unitIso.app _).symm) ≪≫
    eqToIso (MorphismIdeal.map_obj_quotientFunctor_obj _ _ _ _ _)

instance : (stableMatlisDualOp R E (A := A)).Additive := by
  unfold stableMatlisDualOp
  infer_instance

variable {R E}

variable (R E) in
/-- **The Auslander–Reiten translate** `τ = D Tr` determined by a choice of finite projective
presentations: the stable transpose followed by the Matlis dual on stable categories. -/
def stableTranslateOf (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  stableTransposeFunctor P ⋙ (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E

instance (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) : (stableTranslateOf R E P).Additive := by
  unfold stableTranslateOf
  infer_instance

/-- **The translate does not depend on the presentations**: two choices of finite projective
presentations give isomorphic translates. -/
def stableTranslateOfIso (P Q : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) :
    stableTranslateOf R E P ≅ stableTranslateOf R E Q :=
  Functor.isoWhiskerRight (stableTransposeFunctorIso P Q) _

/-- On objects, the translate is the class of `D Tr M`, the Matlis dual of the transpose of the
chosen presentation of `M`. -/
def stableTranslateOfObjIso (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) (M : FinitelyPresentedStableModule.{u, max u v} A) :
    (stableTranslateOf R E P).obj M ≅
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj
          (op (ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p)))) :=
  eqToIso (by
    rw [stableTranslateOf, Functor.comp_obj, Functor.comp_obj, stableTransposeFunctor_obj]
    rfl) ≪≫ stableMatlisDualOpObjIso R E _

/-- **The translate of a projective module vanishes.** -/
theorem isZero_stableTranslateOf_obj (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) {M : FinitelyPresentedStableModule.{u, max u v} A}
    (hM : Module.Projective A M.obj.as) : IsZero ((stableTranslateOf R E P).obj M) := by
  have hM' : IsZero M.obj :=
    ((ExactStructure.abelian _).isZero_projectiveStableFunctor_obj_iff M.obj.as).2
      ((ExactStructure.abelian_isProjective_iff _).2
        (ModuleCat.projective_of_categoryTheory_projective _))
  refine Functor.map_isZero _ ((IsZero.iff_id_eq_zero _).2 (ObjectProperty.hom_ext _ ?_))
  simpa using hM'.eq_of_src (𝟙 _) 0

variable (R E A) in
/-- **The Auslander–Reiten translate** `τ = D Tr`, from finitely presented `A`-modules modulo
projectives to `A`-modules modulo injectives, with the presentations of
`TauCeti.stableTranspose`. -/
def stableTranslate :
    FinitelyPresentedStableModule.{u, max u v} A ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  stableTranspose.{u, v} A ⋙ (ObjectProperty.ι _).op ⋙ stableMatlisDualOp R E

instance : (stableTranslate R A E).Additive := by
  unfold stableTranslate
  infer_instance

end TauCeti
