/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.HomFromProjective.Basic

/-!
# The additive Hom functor from a projective stalk complex

For a projective object `P`, morphisms from `P` placed in degree `n` are naturally the
morphisms from `P` to the `n`-th cohomology object. The comparison is an isomorphism of
abelian-group-valued functors, so preservation of coproducts transfers through it.

The comparison uses `DerivedCategory.homologyFunctor_map_bijective_of_projective` and
Mathlib's `DerivedCategory.singleFunctorCompHomologyFunctorIso`. The hom universes of the
abelian category and its derived category agree, so both additive Hom functors take values
in the same category of abelian groups.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite

universe v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{v} C]

/-- Taking cohomology identifies the additive Hom functor from a projective object in
degree `n` with additive Hom from that object after taking `n`-th cohomology. -/
def preadditiveCoyonedaSingleIso (P : C) [Projective P] (n : ℤ) :
    preadditiveCoyoneda.obj (op ((singleFunctor C n).obj P)) ≅
      homologyFunctor C n ⋙ preadditiveCoyoneda.obj (op P) :=
  NatIso.ofComponents (fun E ↦
    (AddEquiv.ofBijective
      ({ toFun := fun f ↦ (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
          (homologyFunctor C n).map f
         map_zero' := by simp
         map_add' := by intros; simp [Preadditive.comp_add] } :
        ((singleFunctor C n).obj P ⟶ E) →+ (P ⟶ (homologyFunctor C n).obj E))
      (((singleFunctorCompHomologyFunctorIso C n).app P).homFromEquiv.bijective.comp
        (homologyFunctor_map_bijective_of_projective P E n))).toAddCommGrpIso)
    (fun f ↦ by
      ext g
      -- Unpack the abelian-group isomorphism to express naturality as composition in C.
      change (singleFunctor C n).obj P ⟶ _ at g
      change (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
          (homologyFunctor C n).map (g ≫ f) =
        ((singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
          (homologyFunctor C n).map g) ≫ (homologyFunctor C n).map f
      rw [(homologyFunctor C n).map_comp, Category.assoc])

/-- The comparison sends a morphism to its cohomology map, with the source identified with
the original projective object. -/
@[simp]
lemma preadditiveCoyonedaSingleIso_hom_app_apply (P : C) [Projective P] (n : ℤ)
    (E : DerivedCategory C) (f : (singleFunctor C n).obj P ⟶ E) :
    DFunLike.coe (F := ((singleFunctor C n).obj P ⟶ E) →+
      (P ⟶ (homologyFunctor C n).obj E))
      ((preadditiveCoyonedaSingleIso P n).hom.app E).hom f =
      (singleFunctorCompHomologyFunctorIso C n).inv.app P ≫
        (homologyFunctor C n).map f := (rfl)

/-- A projective object in a single degree has a coproduct-preserving additive Hom functor
whenever cohomology and the ordinary additive Hom functor preserve those coproducts. -/
instance preservesColimitsOfShape_preadditiveCoyoneda_single
    (P : C) [Projective P] (n : ℤ) (J : Type*)
    [PreservesColimitsOfShape (Discrete J) (homologyFunctor C n)]
    [PreservesColimitsOfShape (Discrete J) (preadditiveCoyoneda.obj (op P))] :
    PreservesColimitsOfShape (Discrete J)
      (preadditiveCoyoneda.obj (op ((singleFunctor C n).obj P))) :=
  preservesColimitsOfShape_of_natIso (preadditiveCoyonedaSingleIso P n).symm

end DerivedCategory
