/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.InternallyProjective
public import TauCeti.Condensed.Light.Free

import Mathlib.CategoryTheory.Adjunction.Additive
import TauCeti.CategoryTheory.Monoidal.Closed.Preadditive
import TauCeti.CategoryTheory.Monoidal.FunctorCategory
import TauCeti.CategoryTheory.Sites.Linear

/-!
# Additive sections of internal Hom

The tensor–Hom adjunction and the free test-object equivalence identify maps
`A ⊗ R[S] ⟶ B` additively with sections of the internal Hom on `S`. This refines the
set-valued comparison `LightCondensed.ihomPoints` with the additivity needed to
transport difference equations. Tensoring preserves coefficient scalars, so the generic
`TauCeti.curry_smul` and `TauCeti.uncurry_smul` apply to light condensed modules.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory

namespace LightCondensed

variable {R : Type u} [CommRing R]

/-- The tensor product of light condensed modules is additive in both variables. -/
instance monoidalPreadditive : MonoidalPreadditive (LightCondMod R) := by
  have : Limits.HasBinaryCoproducts (LightCondMod R) :=
    Limits.hasBinaryCoproducts_of_hasBinaryBiproducts
  exact TauCeti.monoidalPreadditive_of_isLeftAdjoint _

/-- The tensor product of light condensed modules is linear in both variables. -/
instance monoidalLinear : MonoidalLinear R (LightCondMod R) := by
  have (A : LightCondMod R) : (tensorLeft A).Linear R := by
    let J := coherentTopology LightProfinite.{u}
    let I := sheafToPresheaf J (ModuleCat.{u} R)
    let Q := presheafToSheaf J (ModuleCat.{u} R)
    let adj : Q ⊣ I := sheafificationAdjunction J (ModuleCat.{u} R)
    have e : (I ⋙ tensorLeft (I.obj A)) ⋙ Q ≅ tensorLeft A :=
      Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft I (Functor.Monoidal.commTensorLeft Q (I.obj A)).symm ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (asIso adj.counit) _ ≪≫
        Functor.leftUnitor _ ≪≫
        (tensoringLeft _).mapIso (asIso (adj.counit.app A))
    exact Functor.linear_of_iso _ e
  exact
    { whiskerLeft_smul A {_ _} r f := (tensorLeft A).map_smul r f
      smul_whiskerRight r {_ _} f A := by
        have := Functor.linear_of_iso R (BraidedCategory.tensorLeftIsoTensorRight A)
        exact (tensorRight A).map_smul r f }

variable (R)

/-- Tensor–Hom adjunction followed by free test-object evaluation, as an additive equivalence. -/
noncomputable def tensorHomSectionsAddEquiv (A B : LightCondMod R) (S : LightProfinite.{u}) :
    (A ⊗ (free R).obj S.toCondensed ⟶ B) ≃+
      (A ⟶[LightCondMod R] B).obj.obj (Opposite.op S) :=
  ((ihom.adjunction A).homAddEquiv _ _).trans S.freeModuleHomEquiv

/-- The comparison is currying followed by evaluation on the free test object. -/
lemma tensorHomSectionsAddEquiv_apply (A B : LightCondMod R) (S : LightProfinite.{u})
    (g : A ⊗ (free R).obj S.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A B S g = S.freeModuleHomEquiv (MonoidalClosed.curry g) := by
  simpa only [tensorHomSectionsAddEquiv, AddEquiv.trans_apply,
    MonoidalClosed.homEquiv_apply_eq] using
    congrArg S.freeModuleHomEquiv ((ihom.adjunction A).homAddEquiv_apply _ _ g)

/-- The inverse comparison evaluates a section as a free-object map and uncurries it. -/
lemma tensorHomSectionsAddEquiv_symm_apply (A B : LightCondMod R) (S : LightProfinite.{u})
    (s : (A ⟶[LightCondMod R] B).obj.obj (Opposite.op S)) :
    (tensorHomSectionsAddEquiv R A B S).symm s =
      MonoidalClosed.uncurry (S.freeModuleHomEquiv.symm s) := by
  simpa only [tensorHomSectionsAddEquiv, AddEquiv.symm_trans_apply,
    MonoidalClosed.homEquiv_symm_apply_eq] using
    (ihom.adjunction A).homAddEquiv_symm_apply _ _ (S.freeModuleHomEquiv.symm s)

/-- Precomposition in the first tensor factor acts by internal precomposition on sections. -/
lemma tensorHomSectionsAddEquiv_precomp {A A' B : LightCondMod R} (f : A' ⟶ A)
    (S : LightProfinite.{u}) (g : A ⊗ (free R).obj S.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A' B S ((f ▷ _) ≫ g) =
      ((MonoidalClosed.pre f).app B).hom.app (Opposite.op S)
        (tensorHomSectionsAddEquiv R A B S g) := by
  rw [tensorHomSectionsAddEquiv_apply, ← MonoidalClosed.curry_pre_app,
    LightProfinite.freeModuleHomEquiv_postcomp, tensorHomSectionsAddEquiv_apply]

/-- The additive comparison refines Mathlib's point comparison. -/
lemma tensorHomSectionsAddEquiv_toEquiv (A B : LightCondMod R) (S : LightProfinite.{u}) :
    (tensorHomSectionsAddEquiv R A B S).toEquiv = (ihomPoints R A B S).symm := by
  ext g
  exact (tensorHomSectionsAddEquiv_apply R A B S g).trans (by
    rw [ihomPoints_symm_apply, LightProfinite.freeModuleHomEquiv_apply]
    -- The source argument of homEquiv agrees because S.toCondensed is definitionally
    -- (coherentTopology LightProfinite).yoneda.obj S.
    rfl)

/-- Restricting the test object restricts the corresponding internal Hom section. -/
lemma tensorHomSectionsAddEquiv_naturality {A B : LightCondMod R}
    {S T : LightProfinite.{u}} (f : S ⟶ T)
    (g : A ⊗ (free R).obj T.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A B S
        ((A ◁ (free R).map (lightProfiniteToLightCondSet.map f)) ≫ g) =
      (A ⟶[LightCondMod R] B).obj.map f.op (tensorHomSectionsAddEquiv R A B T g) := by
  rw [tensorHomSectionsAddEquiv_apply, MonoidalClosed.curry_natural_left,
    LightProfinite.freeModuleHomEquiv_comp, tensorHomSectionsAddEquiv_apply]

/-- Postcomposition applies the corresponding internal Hom coefficient map to sections. -/
lemma tensorHomSectionsAddEquiv_postcomp {A B C : LightCondMod R} (f : B ⟶ C)
    (S : LightProfinite.{u}) (g : A ⊗ (free R).obj S.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A C S (g ≫ f) =
      ((ihom A).map f).hom.app (Opposite.op S) (tensorHomSectionsAddEquiv R A B S g) := by
  rw [tensorHomSectionsAddEquiv_apply, MonoidalClosed.curry_natural_right,
    LightProfinite.freeModuleHomEquiv_postcomp, tensorHomSectionsAddEquiv_apply]

end LightCondensed
