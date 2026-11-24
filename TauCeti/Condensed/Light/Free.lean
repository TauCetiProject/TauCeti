/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Module

import TauCeti.CategoryTheory.Sites.FreeYoneda

/-!
# Free light condensed modules on test spaces

The free-forgetful adjunction and the sheaf Yoneda equivalence identify maps out
of a free test object with sections on the test space.
-/

public section

universe u

open CategoryTheory LightCondensed

namespace LightProfinite

variable {R : Type u} [Ring R] {M : LightCondMod R}

/-- Maps from the free light condensed module on a test space correspond to sections there. -/
noncomputable def freeModuleHomEquiv (S : LightProfinite.{u}) :
    ((free R).obj S.toCondensed ⟶ M) ≃+ M.obj.obj (Opposite.op S) :=
  (ModuleCat.adj R).freeYonedaSectionsAddEquiv
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) S M

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T`
to `S` along `f`. -/
@[simp↓] -- Prefer restriction to coefficient naturality on this composite.
lemma freeModuleHomEquiv_comp {S T : LightProfinite.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((free R).map (lightProfiniteToLightCondSet.map f) ≫ g) =
      M.obj.map f.op (T.freeModuleHomEquiv g) := by
  exact (ModuleCat.adj R).freeYonedaSectionsAddEquiv_naturality_left
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) f M g

/-- Postcomposition by a module morphism applies its section map to the corresponding section. -/
@[simp]
lemma freeModuleHomEquiv_postcomp {S : LightProfinite.{u}} {N : LightCondMod R}
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app (Opposite.op S) (S.freeModuleHomEquiv g) := by
  exact (ModuleCat.adj R).freeYonedaSectionsAddEquiv_naturality_right
    (A := forget₂ (ModuleCat R) AddCommGrpCat) (coherentTopology LightProfinite) g f

/-- Postcomposing the map corresponding to a section applies the coefficient morphism. -/
@[simp]
lemma freeModuleHomEquiv_symm_postcomp {S : LightProfinite.{u}} {N : LightCondMod R}
    (s : M.obj.obj (Opposite.op S)) (f : M ⟶ N) :
    S.freeModuleHomEquiv.symm (f.hom.app (Opposite.op S) s) =
      S.freeModuleHomEquiv.symm s ≫ f := by
  rw [AddEquiv.symm_apply_eq, freeModuleHomEquiv_postcomp, AddEquiv.apply_symm_apply]

end LightProfinite
