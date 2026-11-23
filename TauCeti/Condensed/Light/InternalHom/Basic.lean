/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import TauCeti.Condensed.Light.Free
public import Mathlib.Condensed.Light.Monoidal

import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-!
# Additive sections of internal Hom

The tensor–Hom adjunction and the free test-object equivalence identify maps
`A ⊗ R[S] ⟶ B` additively with sections of the internal Hom on `S`. This refines the
set-valued comparison `LightCondensed.ihomPoints` with the additivity needed to
transport difference equations.
-/

public section

universe u

open CategoryTheory Category MonoidalCategory

namespace LightCondensed

variable (R : Type u) [CommRing R]

/-- Tensor–Hom adjunction followed by free test-object evaluation, as an additive equivalence. -/
noncomputable def tensorHomSectionsAddEquiv (A B : LightCondMod R) (S : LightProfinite.{u}) :
    (A ⊗ (free R).obj S.toCondensed ⟶ B) ≃+
      (A ⟶[LightCondMod R] B).obj.obj (Opposite.op S) := by
  letI : (tensorLeft A).Additive := show (tensorLeft A).Additive from
    preservesFiniteColimits_le_additiveFunctor _ _ _ inferInstance
  exact ((ihom.adjunction A).homAddEquiv _ _).trans S.freeModuleHomEquiv

/-- The comparison is currying followed by evaluation on the free test object. -/
lemma tensorHomSectionsAddEquiv_apply (A B : LightCondMod R) (S : LightProfinite.{u})
    (g : A ⊗ (free R).obj S.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A B S g = S.freeModuleHomEquiv (MonoidalClosed.curry g) := by
  let : (tensorLeft A).Additive :=
    preservesFiniteColimits_le_additiveFunctor _ _ _ inferInstance
  simpa only [tensorHomSectionsAddEquiv, AddEquiv.trans_apply, MonoidalClosed.curry] using
    congrArg S.freeModuleHomEquiv ((ihom.adjunction A).homAddEquiv_apply _ _ g)

/-- The inverse comparison evaluates a section as a free-object map and uncurries it. -/
lemma tensorHomSectionsAddEquiv_symm_apply (A B : LightCondMod R) (S : LightProfinite.{u})
    (s : (A ⟶[LightCondMod R] B).obj.obj (Opposite.op S)) :
    (tensorHomSectionsAddEquiv R A B S).symm s =
      MonoidalClosed.uncurry (S.freeModuleHomEquiv.symm s) := by
  let : (tensorLeft A).Additive :=
    preservesFiniteColimits_le_additiveFunctor _ _ _ inferInstance
  simpa only [tensorHomSectionsAddEquiv, AddEquiv.symm_trans_apply, MonoidalClosed.uncurry] using
    (ihom.adjunction A).homAddEquiv_symm_apply _ _ (S.freeModuleHomEquiv.symm s)

/-- Precomposition in the first tensor factor acts by internal precomposition on sections. -/
lemma tensorHomSectionsAddEquiv_precomp {A A' B : LightCondMod R} (f : A' ⟶ A)
    (S : LightProfinite.{u}) (g : A ⊗ (free R).obj S.toCondensed ⟶ B) :
    tensorHomSectionsAddEquiv R A' B S ((f ▷ _) ≫ g) =
      ((MonoidalClosed.pre f).app B).hom.app (Opposite.op S)
        (tensorHomSectionsAddEquiv R A B S g) := by
  rw [tensorHomSectionsAddEquiv_apply, ← MonoidalClosed.curry_pre_app,
    LightProfinite.freeModuleHomEquiv_postcomp, tensorHomSectionsAddEquiv_apply]

end LightCondensed
