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
  projectives to maps through injectives, and descends to a functor from right modules modulo
  projectives to the opposite of left modules modulo injectives (`TauCeti.stableMatlisDualOp`, in
  `TauCeti.Algebra.Category.ModuleCat.MatlisDual.Stable`).

Defining `τ` as the composite of these functors makes it a functor without choices beyond the
presentations defining `Tr`; changing them gives an isomorphic functor. Over a field, with
`E = k`, this is the translate of `TauCeti.AuslanderReitenTranslate`, in the stable category.

## Main definitions

* `TauCeti.stableTranslateOf` and `TauCeti.stableTranslate`: the translate `τ = D Tr`, from
  chosen presentations, and from the presentations of `TauCeti.stableTranspose`.

## Main results

* `TauCeti.stableTranslateOfIso`: the translate does not depend on the presentations.
* `TauCeti.stableTranslateOfObjIso` and `TauCeti.stableTranslateOf_map`: on objects and maps, the
  translate is the class of `D Tr`.
* `TauCeti.stableTranslate_def`: the translate is `stableTranslateOf` for the presentations of
  `TauCeti.stableTranspose`.
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

/-- **The translate of a map is the Matlis dual of its transpose**, through
`stableTranslateOfObjIso`: if a map `t` of right modules represents the stable transpose of `g`
(`AuslanderReitenTranspose.stableMap`), then the translate of `g` is the class of `D t`. -/
theorem stableTranslateOf_map (P : ∀ M : FinitelyPresentedStableModule.{u, max u v} A,
    FiniteProjectivePresentation M.obj.as) {M N : FinitelyPresentedStableModule.{u, max u v} A}
    (g : M ⟶ N) (t : ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P N).p) ⟶
      ModuleCat.of Aᵐᵒᵖ (AuslanderReitenTranspose (P M).p))
    (ht : (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map t =
      AuslanderReitenTranspose.stableMap (P M).exact.linearMap_comp_eq_zero (P N).exact
        (P N).surjective g.hom) :
    (stableTranslateOf R E P).map g =
      (stableTranslateOfObjIso P M).hom ≫
        (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
          ((ModuleCat.matlisDualOp R E).map t.op) ≫
        (stableTranslateOfObjIso P N).inv := by
  simp [stableTranslateOf, stableTranslateOfObjIso, ← ht,
    stableMatlisDualOp_map_projectiveStableFunctor_map, eqToHom_map]
  rfl

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

/-- The translate is `stableTranslateOf` for the presentations of `TauCeti.stableTranspose`, so
`stableTranslateOfObjIso`, `stableTranslateOf_map`, `stableTranslateOfIso` and
`isZero_stableTranslateOf_obj` apply to it. -/
theorem stableTranslate_def :
    stableTranslate R A E = stableTranslateOf R E (fun M ↦
      letI := M.property
      FiniteProjectivePresentation.ofFinitePresentation (M := M.obj.as)) := by
  rw [stableTranslate, stableTranspose_def, stableTranslateOf]

instance : (stableTranslate R A E).Additive := by
  unfold stableTranslate
  infer_instance

end TauCeti
