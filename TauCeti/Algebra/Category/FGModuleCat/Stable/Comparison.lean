/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.FGModuleCat.Injective
public import TauCeti.Algebra.Category.FGModuleCat.Projective
public import TauCeti.Algebra.Category.ModuleCat.InjectiveStable.FinitelyGenerated
public import TauCeti.Algebra.Category.ModuleCat.ProjectiveStable.FinitelyPresented
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.FullSubcategory

import Mathlib.CategoryTheory.Limits.Constructions.EpiMono

/-!
# Comparing stable quotients of finitely generated modules

Over a left Noetherian ring, the projective stable quotient of finitely generated modules
identifies with the finitely presented objects of the projective stable quotient of all modules.
A factorization through a projective module can be taken through a finitely generated projective
module by lifting its second leg along a finite free cover of the target.

If finitely generated modules have enough injectives, the analogous comparison holds for the
injective stable quotients. A factorization through an injective module can be taken through a
finitely generated injective module by extending its first leg across a finite injective
embedding of the source.

## References

* M. Auslander, I. Reiten, S. O. Smalø, *Representation Theory of Artin Algebras*, Cambridge
  University Press (1995), Chapter IV, Section 1, for stable morphisms and their factorizations.
-/

public section

open CategoryTheory Limits TauCeti

universe u v

namespace FGModuleCat

variable (A : Type u) [Ring A] [IsNoetherianRing A]

section Projective

variable [Small.{v} A]

/-- Between finitely generated modules, factoring through an arbitrary projective is equivalent
to factoring through a finitely generated projective. -/
theorem projectiveStableIdeal_eq_comap :
    (ExactStructure.abelian (FGModuleCat.{v} A)).projectiveStableIdeal =
      (ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableIdeal.comap
        (ModuleCat.isFG.{v} A).ι := by
  let F := (ModuleCat.isFG.{v} A).ι
  ext X Y f
  rw [MorphismIdeal.mem_comap_hom, ExactStructure.mem_projectiveStableIdeal_iff,
    ExactStructure.mem_projectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff,
    ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨P, hP, i, p, rfl⟩
    exact ⟨P.obj, (ExactStructure.abelian_isProjective_iff _).2
      (P.projective_obj_iff.2 ((ExactStructure.abelian_isProjective_iff _).1 hP)),
      F.map i, F.map p, F.map_comp _ _⟩
  · rintro ⟨P, hP, i, p, hf⟩
    let Q := Projective.over Y
    let q := Projective.π Y
    have : Epi (F.map q) :=
      preserves_epi_of_preservesColimit (forget₂ (FGModuleCat.{v} A) (ModuleCat.{v} A)) q
    have : Projective P := (ExactStructure.abelian_isProjective_iff _).1 hP
    let i' := F.preimage (i ≫ Projective.factorThru p (F.map q))
    refine ⟨Q, (ExactStructure.abelian_isProjective_iff _).2 inferInstance, i', q,
      F.map_injective ?_⟩
    simpa only [Functor.map_comp, i', Functor.map_preimage, Category.assoc,
      Projective.factorThru_comp] using hf

/-- The projective stable quotient of finitely generated modules is equivalent, by inclusion,
to finitely presented objects of the ambient projective stable quotient. -/
noncomputable def projectiveStableEquivalence :
    (ExactStructure.abelian (FGModuleCat.{v} A)).ProjectiveStableCategory ≌
      FinitelyPresentedStableModule.{u, v} A := by
  refine MorphismIdeal.mapFullSubcategoryEquivalence _ _ (ModuleCat.isFG.{v} A).ι
    (projectiveStableIdeal_eq_comap A) _ (fun X ↦ Module.finitePresentation_of_finite A X.obj) ?_
  intro Y
  have : Module.FinitePresentation A Y.obj.as := Y.property
  exact ⟨FGModuleCat.of A Y.obj.as, ⟨eqToIso (MorphismIdeal.quotientFunctor_obj_as _ Y.obj)⟩⟩

/-- On quotienting, the projective comparison is induced by the inclusion of finite modules. -/
noncomputable def projectiveStableFunctorCompEquivalenceIso :
    (ExactStructure.abelian (FGModuleCat.{v} A)).projectiveStableFunctor ⋙
      (projectiveStableEquivalence A).functor ⋙ ObjectProperty.ι _ ≅
      (ModuleCat.isFG.{v} A).ι ⋙
        (ExactStructure.abelian (ModuleCat.{v} A)).projectiveStableFunctor := by
  unfold projectiveStableEquivalence
  exact MorphismIdeal.quotientFunctorCompMapFullSubcategoryEquivalenceIso _ _ _ _ _ _ _

instance : (projectiveStableEquivalence.{u, v} A).functor.Additive := by
  unfold projectiveStableEquivalence
  infer_instance

open scoped ModuleCat.Algebra in
instance (R : Type*) [CommSemiring R] [Algebra R A] :
    (projectiveStableEquivalence.{u, v} A).functor.Linear R := by
  unfold projectiveStableEquivalence
  infer_instance

end Projective

section Injective

variable [Small.{v} A] [EnoughInjectives (FGModuleCat.{v} A)]

/-- Between finitely generated modules, factoring through an arbitrary injective is equivalent
to factoring through a finitely generated injective, provided the finite module category has
enough injectives. -/
theorem injectiveStableIdeal_eq_comap :
    (ExactStructure.abelian (FGModuleCat.{v} A)).injectiveStableIdeal =
      (ExactStructure.abelian (ModuleCat.{v} A)).injectiveStableIdeal.comap
        (ModuleCat.isFG.{v} A).ι := by
  let F := (ModuleCat.isFG.{v} A).ι
  ext X Y f
  rw [MorphismIdeal.mem_comap_hom, ExactStructure.mem_injectiveStableIdeal_iff,
    ExactStructure.mem_injectiveStableIdeal_iff, ObjectProperty.factorsThrough_iff,
    ObjectProperty.factorsThrough_iff]
  constructor
  · rintro ⟨I, hI, i, p, rfl⟩
    exact ⟨I.obj, (ExactStructure.abelian_isInjective_iff _).2
      (I.injective_obj_iff.2 ((ExactStructure.abelian_isInjective_iff _).1 hI)),
      F.map i, F.map p, F.map_comp _ _⟩
  · rintro ⟨I, hI, i, p, hf⟩
    let J := Injective.under X
    let j := Injective.ι X
    have : Mono (F.map j) := inferInstance
    have : Injective I := (ExactStructure.abelian_isInjective_iff _).1 hI
    let p' := F.preimage (Injective.factorThru i (F.map j) ≫ p)
    refine ⟨J, (ExactStructure.abelian_isInjective_iff _).2 inferInstance, j, p',
      F.map_injective ?_⟩
    simpa only [Functor.map_comp, p', Functor.map_preimage,
      Injective.comp_factorThru_assoc] using hf

/-- With enough finitely generated injectives, the injective stable quotient of finitely
generated modules is equivalent, by inclusion, to the finite objects of the ambient quotient. -/
noncomputable def injectiveStableEquivalence :
    (ExactStructure.abelian (FGModuleCat.{v} A)).InjectiveStableCategory ≌
      FinitelyGeneratedInjectiveStableModule.{u, v} A := by
  refine MorphismIdeal.mapFullSubcategoryEquivalence _ _ (ModuleCat.isFG.{v} A).ι
    (injectiveStableIdeal_eq_comap A) _ (fun X ↦ inferInstanceAs (Module.Finite A X.obj)) ?_
  intro Y
  have : Module.Finite A Y.obj.as := Y.property
  exact ⟨FGModuleCat.of A Y.obj.as, ⟨eqToIso (MorphismIdeal.quotientFunctor_obj_as _ Y.obj)⟩⟩

/-- On quotienting, the injective comparison is induced by the inclusion of finite modules. -/
noncomputable def injectiveStableFunctorCompEquivalenceIso :
    (ExactStructure.abelian (FGModuleCat.{v} A)).injectiveStableFunctor ⋙
      (injectiveStableEquivalence A).functor ⋙ ObjectProperty.ι _ ≅
      (ModuleCat.isFG.{v} A).ι ⋙
        (ExactStructure.abelian (ModuleCat.{v} A)).injectiveStableFunctor := by
  unfold injectiveStableEquivalence
  exact MorphismIdeal.quotientFunctorCompMapFullSubcategoryEquivalenceIso _ _ _ _ _ _ _

instance : (injectiveStableEquivalence.{u, v} A).functor.Additive := by
  unfold injectiveStableEquivalence
  infer_instance

open scoped ModuleCat.Algebra in
instance (R : Type*) [CommSemiring R] [Algebra R A] :
    (injectiveStableEquivalence.{u, v} A).functor.Linear R := by
  unfold injectiveStableEquivalence
  infer_instance

end Injective

end FGModuleCat
