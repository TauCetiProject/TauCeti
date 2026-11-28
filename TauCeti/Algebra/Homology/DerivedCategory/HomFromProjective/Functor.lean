/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.HomFromProjective.Basic
public import Mathlib.Algebra.Category.Grp.Ulift

/-!
# The additive Hom functor from a projective stalk complex

For a projective object `P`, morphisms from `P` placed in degree `n` are naturally the
morphisms from `P` to the `n`-th cohomology object. The comparison is an isomorphism of
abelian-group-valued functors, so preservation of coproducts transfers through it.

The comparison uses `TauCeti.homFromProjectiveSingleAddEquiv`. For arbitrary ordinary and
derived hom universes, both Hom functors are lifted to their common maximum universe. When
those universes agree, full faithfulness of the lift gives an unlifted comparison.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite DerivedCategory

universe w v u

namespace TauCeti

variable {C : Type u} [Category.{v} C] [Abelian C]

section Lifted

variable [HasDerivedCategory.{w} C]

/-- Taking cohomology identifies additive Hom from a projective stalk with ordinary additive
Hom into cohomology, after lifting both to a common universe. -/
def preadditiveCoyonedaSingleLiftIso (P : C) [Projective P] (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor C n).obj P)) ⋙
        AddCommGrpCat.uliftFunctor.{v, w} ≅
      (homologyFunctor C n ⋙ preadditiveCoyoneda.obj (op P)) ⋙
        AddCommGrpCat.uliftFunctor.{w, v} :=
  NatIso.ofComponents (fun E ↦
    ((AddEquiv.ulift.trans (homFromProjectiveSingleAddEquiv P E n)).trans
      AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun f ↦ by
      ext g
      -- Normalize the bundled Hom element type so rewriting can check the pointwise maps
      -- without unfolding the comparison equivalence.
      change ULift ((singleFunctor C n).obj P ⟶ _) at g
      change ULift.up (homFromProjectiveSingleAddEquiv P _ n
          ((preadditiveCoyonedaObj ((singleFunctor C n).obj P)).map f g.down)) =
        ULift.up ((preadditiveCoyonedaObj P).map ((homologyFunctor C n).map f)
          (homFromProjectiveSingleAddEquiv P _ n g.down))
      rw [preadditiveCoyonedaObj_map, preadditiveCoyonedaObj_map]
      -- Evaluate the displayed linear maps; keep the additive equivalence opaque.
      change ULift.up (homFromProjectiveSingleAddEquiv P _ n (g.down ≫ f)) =
        ULift.up (homFromProjectiveSingleAddEquiv P _ n g.down ≫ (homologyFunctor C n).map f)
      simp only [homFromProjectiveSingleAddEquiv_apply, Functor.map_comp, Category.assoc])

/-- The lifted comparison takes the cohomology map of the underlying derived morphism. -/
@[simp]
lemma preadditiveCoyonedaSingleLiftIso_hom_app_apply (P : C) [Projective P] (n : ℤ)
    (E : DerivedCategory C) (f : ULift.{v} ((singleFunctor C n).obj P ⟶ E)) :
    DFunLike.coe (F := ULift.{v} ((singleFunctor C n).obj P ⟶ E) →+
      ULift.{w} (P ⟶ (homologyFunctor C n).obj E))
      ((preadditiveCoyonedaSingleLiftIso P n).hom.app E).hom f =
      ULift.up ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
        (homologyFunctor C n).map f.down) := by
  -- Give the bundled component its explicit Hom type so the comparison formula can rewrite.
  change ULift.up (homFromProjectiveSingleAddEquiv P E n f.down) = _
  rw [homFromProjectiveSingleAddEquiv_apply]

/-- The inverse lifted comparison constructs a derived morphism from a cohomology map. -/
@[simp]
lemma preadditiveCoyonedaSingleLiftIso_inv_app_apply (P : C) [Projective P] (n : ℤ)
    (E : DerivedCategory C) (g : ULift.{w} (P ⟶ (homologyFunctor C n).obj E)) :
    DFunLike.coe (F := ULift.{w} (P ⟶ (homologyFunctor C n).obj E) →+
      ULift.{v} ((singleFunctor C n).obj P ⟶ E))
      ((preadditiveCoyonedaSingleLiftIso P n).inv.app E).hom g =
      ULift.up ((homFromProjectiveSingleAddEquiv P E n).symm g.down) := (rfl)

/-- Colimits of any shape transfer to additive Hom from a projective stalk when cohomology
and ordinary additive Hom preserve them. Universe lifts preserve and reflect colimits. -/
instance preservesColimitsOfShape_preadditiveCoyoneda_single
    (P : C) [Projective P] (n : ℤ) (J : Type*) [Category J]
    [PreservesColimitsOfShape J (homologyFunctor C n)]
    [PreservesColimitsOfShape J (preadditiveCoyoneda.obj (op P))] :
    PreservesColimitsOfShape J
      (preadditiveCoyoneda.obj (op ((singleFunctor C n).obj P))) := by
  have := preservesColimitsOfShape_of_natIso (J := J)
    (preadditiveCoyonedaSingleLiftIso P n).symm
  exact preservesColimitsOfShape_of_reflects_of_preserves _ AddCommGrpCat.uliftFunctor.{v, w}

end Lifted

variable [HasDerivedCategory.{v} C]

/-- With equal hom universes, taking cohomology gives an unlifted additive Hom comparison
for a projective object placed in degree `n`. -/
def preadditiveCoyonedaSingleIso (P : C) [Projective P] (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor C n).obj P)) ≅
      homologyFunctor C n ⋙ preadditiveCoyoneda.obj (op P) :=
  Functor.fullyFaithfulCancelRight AddCommGrpCat.uliftFunctor.{v, v}
    (preadditiveCoyonedaSingleLiftIso P n)

/-- The unlifted comparison takes the cohomology map and identifies its source with the
original projective object. -/
@[simp]
lemma preadditiveCoyonedaSingleIso_hom_app_apply (P : C) [Projective P] (n : ℤ)
    (E : DerivedCategory C) (f : (singleFunctor C n).obj P ⟶ E) :
    DFunLike.coe (F := ((singleFunctor C n).obj P ⟶ E) →+
      (P ⟶ (homologyFunctor C n).obj E))
      ((preadditiveCoyonedaSingleIso P n).hom.app E).hom f =
      (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
        (homologyFunctor C n).map f := by
  rw [preadditiveCoyonedaSingleIso, Functor.fullyFaithfulCancelRight_hom_app]
  have he := ConcreteCategory.congr_hom
    (AddCommGrpCat.uliftFunctor.{v, v}.map_preimage
      ((preadditiveCoyonedaSingleLiftIso P n).hom.app E)) (ULift.up f)
  simp only [AddCommGrpCat.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe] at he
  exact congrArg ULift.down
    (he.trans (preadditiveCoyonedaSingleLiftIso_hom_app_apply P n E (ULift.up f)))

/-- The inverse unlifted comparison constructs a derived morphism from a cohomology map. -/
@[simp]
lemma preadditiveCoyonedaSingleIso_inv_app_apply (P : C) [Projective P] (n : ℤ)
    (E : DerivedCategory C) (g : P ⟶ (homologyFunctor C n).obj E) :
    DFunLike.coe (F := (P ⟶ (homologyFunctor C n).obj E) →+
      ((singleFunctor C n).obj P ⟶ E))
      ((preadditiveCoyonedaSingleIso P n).inv.app E).hom g =
      (homFromProjectiveSingleAddEquiv P E n).symm g := by
  rw [preadditiveCoyonedaSingleIso, Functor.fullyFaithfulCancelRight_inv_app]
  have he := ConcreteCategory.congr_hom
    (AddCommGrpCat.uliftFunctor.{v, v}.map_preimage
      ((preadditiveCoyonedaSingleLiftIso P n).inv.app E)) (ULift.up g)
  simp only [AddCommGrpCat.uliftFunctor_map, AddEquiv.toAddMonoidHom_eq_coe] at he
  exact congrArg ULift.down
    (he.trans (preadditiveCoyonedaSingleLiftIso_inv_app_apply P n E (ULift.up g)))

end TauCeti
