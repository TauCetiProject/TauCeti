/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import TauCeti.Algebra.Category.ModuleCat.MatlisDual.Basic
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Opposite
public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Functor
public import TauCeti.CategoryTheory.Exact.Stable.Basic
public import TauCeti.CategoryTheory.Exact.Stable.Injective
import TauCeti.CategoryTheory.Exact.Injective
import TauCeti.CategoryTheory.Exact.Projective
import Mathlib.Algebra.Category.ModuleCat.Injective
import Mathlib.Algebra.Category.ModuleCat.Projective

/-!
# The Matlis dual on stable categories

Let `A` be an algebra over a commutative ring `R` and `E` an injective `R`-module, with
`D = Hom_R(-, E)`. The dual of a projective right `A`-module is an injective left `A`-module, so
`D` carries maps through projectives to maps through injectives. It therefore descends to a
functor from the opposite of right `A`-modules modulo projectives to left `A`-modules modulo
injectives.

## Main definitions

* `TauCeti.stableMatlisDualOp`: the Matlis dual on stable categories.
* `TauCeti.projectiveStableFunctorOpCompStableMatlisDualOpIso`: it is compatible with `D` through
  the quotient functors, with components `TauCeti.stableMatlisDualOpObjIso`.

## Main results

* `TauCeti.projectiveStableIdeal_op_le_comap_matlisDualOp`: the Matlis dual of a map through a
  projective right module factors through an injective left module.
* `TauCeti.stableMatlisDualOp_map_projectiveStableFunctor_map`: on the class of a module map, the
  stable Matlis dual is the class of its dual.
-/

public section

noncomputable section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Opposite

universe u v

attribute [local instance] ModuleCat.moduleOfAlgebra ModuleCat.isScalarTower_moduleOfAlgebra

variable (R : Type*) [CommRing R] {A : Type u} [Ring A] [Algebra R A] (E : Type v)
  [AddCommGroup E] [Module R E] [Module.Injective R E] [Small.{v} R]

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

/-- **The Matlis dual on stable categories**: `D = Hom_R(-, E)` as a functor from the opposite of
right `A`-modules modulo projectives to left `A`-modules modulo injectives. -/
def stableMatlisDualOp :
    ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).ProjectiveStableCategory)ᵒᵖ ⥤
      (ExactStructure.abelian (ModuleCat.{max u v} A)).InjectiveStableCategory :=
  (MorphismIdeal.opQuotientEquivalence _).inverse ⋙
    MorphismIdeal.map _ _ (ModuleCat.matlisDualOp R E)
      (projectiveStableIdeal_op_le_comap_matlisDualOp R E)

/-- The stable Matlis dual is the Matlis dual induced on the quotients, after identifying the
quotient of the opposite with the opposite of the quotient. -/
theorem stableMatlisDualOp_def :
    stableMatlisDualOp R E (A := A) =
      (MorphismIdeal.opQuotientEquivalence _).inverse ⋙
        MorphismIdeal.map _ _ (ModuleCat.matlisDualOp R E)
          (projectiveStableIdeal_op_le_comap_matlisDualOp R E) :=
  (rfl)

instance : (stableMatlisDualOp R E (A := A)).Additive := by
  unfold stableMatlisDualOp
  infer_instance

/-- **The stable Matlis dual is the Matlis dual on representatives**: passing to right modules
modulo projectives and then applying the stable Matlis dual is naturally isomorphic to applying
`D` and then passing to left modules modulo injectives. -/
def projectiveStableFunctorOpCompStableMatlisDualOpIso :
    (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.op ⋙
        stableMatlisDualOp R E ≅
      ModuleCat.matlisDualOp R E ⋙
        (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor := by
  let I := (ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableIdeal
  have h : I.quotientFunctor.op = I.op.quotientFunctor ⋙ I.opQuotientEquivalence.functor := by
    simp
  exact Functor.isoWhiskerRight (eqToIso h).compInverseIso _ ≪≫
    eqToIso (MorphismIdeal.quotientFunctor_comp_map _ _ _ _)

/-- On the class of a right module `N`, the stable Matlis dual is the class of `D N`. -/
def stableMatlisDualOpObjIso (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    (stableMatlisDualOp R E).obj
        (op ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.obj N)) ≅
      (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.obj
        ((ModuleCat.matlisDualOp R E).obj (op N)) :=
  (projectiveStableFunctorOpCompStableMatlisDualOpIso R E).app (op N)

@[simp]
theorem projectiveStableFunctorOpCompStableMatlisDualOpIso_app (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    (projectiveStableFunctorOpCompStableMatlisDualOpIso R E).app (op N) =
      stableMatlisDualOpObjIso R E N :=
  (rfl)

@[simp]
theorem projectiveStableFunctorOpCompStableMatlisDualOpIso_hom_app
    (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    (projectiveStableFunctorOpCompStableMatlisDualOpIso R E).hom.app (op N) =
      (stableMatlisDualOpObjIso R E N).hom :=
  (rfl)

@[simp]
theorem projectiveStableFunctorOpCompStableMatlisDualOpIso_inv_app
    (N : ModuleCat.{max u v} Aᵐᵒᵖ) :
    (projectiveStableFunctorOpCompStableMatlisDualOpIso R E).inv.app (op N) =
      (stableMatlisDualOpObjIso R E N).inv :=
  (rfl)

/-- **The stable Matlis dual of the class of a map is the class of its dual**, through
`stableMatlisDualOpObjIso`. -/
@[simp, reassoc]
theorem stableMatlisDualOp_map_projectiveStableFunctor_map {N N' : ModuleCat.{max u v} Aᵐᵒᵖ}
    (f : N ⟶ N') :
    (stableMatlisDualOp R E).map
        ((ExactStructure.abelian (ModuleCat.{max u v} Aᵐᵒᵖ)).projectiveStableFunctor.map f).op =
      (stableMatlisDualOpObjIso R E N').hom ≫
        (ExactStructure.abelian (ModuleCat.{max u v} A)).injectiveStableFunctor.map
          ((ModuleCat.matlisDualOp R E).map f.op) ≫
        (stableMatlisDualOpObjIso R E N).inv :=
  (NatIso.naturality_2 (projectiveStableFunctorOpCompStableMatlisDualOpIso R E) f.op).symm

end TauCeti
