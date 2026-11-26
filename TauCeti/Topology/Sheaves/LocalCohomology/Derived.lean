/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Sheaves.LocalCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived

/-!
# Local cohomology as derived supported sections

For a closed subset `S`, deriving the sheaf-valued supported-section functor gives the local
cohomology sheaf. On an injective resolution, cohomology before sheafification can be computed
on each open by the supported Ext comparison. Exactness of sheafification then identifies
the two sheaf-valued functors.

The cohomology of the bounded below derived functors on a sheaf placed in degree zero
therefore computes both the supported Ext groups on opens and the local cohomology sheaves.

## References

* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

universe u w

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)

local notation "J" => Opens.grothendieckTopology X
local notation "A" => ModuleCat R
local notation "P" => supportedSubmoduleFunctor (R := R) S ⋙ sheafToPresheaf J A

local notation "L" => presheafToSheaf J A
local notation "e" =>
  Functor.associator (supportedSubmoduleFunctor (R := R) S) (sheafToPresheaf J A) L ≪≫
    Functor.isoWhiskerLeft _ (Iso.symm (sheafificationNatIso J A)) ≪≫
    Functor.rightUnitor _ ≪≫ Iso.symm (Functor.leftUnitor _)

/-- The sheaf-valued right derived functors of supported sections are the local cohomology
sheaves, naturally in the coefficient sheaf. -/
def rightDerivedSupportedSubmoduleIso (n : ℕ) :
    (supportedSubmoduleFunctor (R := R) S).rightDerived n ≅
      supportedModuleHSheafFunctor (R := R) S n :=
  (Functor.leftUnitor _).symm ≪≫
    (Functor.rightDerivedCompIso P L (𝟭 _) (supportedSubmoduleFunctor S) e n).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedSupportedSubmodulePresheafIso (R := R) S n) L

/-- After comparing the derived functor with exact postcomposition by sheafification,
the local cohomology comparison is the sheafification of the supported Ext comparison. -/
@[reassoc]
lemma rightDerivedSupportedSubmoduleIso_hom_comp (n : ℕ) :
    (Functor.rightDerivedCompIso P L (𝟭 _) (supportedSubmoduleFunctor S) e n).hom ≫
      (Functor.leftUnitor _).hom ≫ (rightDerivedSupportedSubmoduleIso S n).hom =
        Functor.whiskerRight (rightDerivedSupportedSubmodulePresheafIso S n).hom L := by
  simp only [rightDerivedSupportedSubmoduleIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]
  exact (Functor.rightDerivedCompIso P L (𝟭 _) (supportedSubmoduleFunctor S) e n).hom_inv_id_assoc _

section BoundedBelow

open DerivedCategory

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]

/-- On a sheaf in degree zero, the bounded below derived supported-section sheaf has
cohomology equal to the local cohomology sheaf in every nonnegative degree. -/
def rightDerivedFunctorPlusSupportedSubmoduleHomologyIso (n : ℕ) :
    Plus.singleFunctor (Sheaf J (ModuleCat.{u} R)) 0 ⋙
        (supportedSubmoduleFunctor (R := R) S).rightDerivedFunctorPlus ⋙
        Plus.homologyFunctor (Sheaf J (ModuleCat.{u} R)) n ≅
      supportedModuleHSheafFunctor (R := R) S n :=
  (supportedSubmoduleFunctor (R := R) S).rightDerivedFunctorPlusHomologyIso n ≪≫
    rightDerivedSupportedSubmoduleIso S n

/-- The bounded below sheaf comparison is the classical local cohomology comparison
after identifying the bounded below cohomology with the classical derived functors. -/
@[reassoc]
lemma rightDerivedFunctorPlusSupportedSubmoduleHomologyIso_hom (n : ℕ) :
    (rightDerivedFunctorPlusSupportedSubmoduleHomologyIso (R := R) S n).hom =
      ((supportedSubmoduleFunctor (R := R) S).rightDerivedFunctorPlusHomologyIso n).hom ≫
        (rightDerivedSupportedSubmoduleIso S n).hom :=
  (rfl)

end BoundedBelow

end CategoryTheory.Sheaf
