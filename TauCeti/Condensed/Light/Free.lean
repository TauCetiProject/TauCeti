/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Module

import Mathlib.CategoryTheory.Adjunction.Additive
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
    ((free R).obj S.toCondensed ⟶ M) ≃+ M.obj.obj (Opposite.op S) where
  toEquiv := (ModuleCat.adj R).freeYonedaSectionsEquiv (coherentTopology LightProfinite) S M
  map_add' f g := by
    let e := (ModuleCat.adj R).freeYonedaSectionsEquiv (coherentTopology LightProfinite) S M
    change e (f + g) = (e f : M.obj.obj (Opposite.op S)) + e g
    dsimp only [e]
    erw [Adjunction.freeYonedaSectionsEquiv_apply, Adjunction.freeYonedaSectionsEquiv_apply,
      Adjunction.freeYonedaSectionsEquiv_apply]
    exact congrArg (fun k ↦ yonedaEquiv ((Adjunction.whiskerRight _ _).homEquiv _ _ k))
      (map_add ((sheafificationAdjunction (coherentTopology LightProfinite)
        (ModuleCat R)).homAddEquiv _ _) f g)

/-- Precomposing with the free map induced by `f : S ⟶ T` restricts a section on `T`
to `S` along `f`. -/
@[simp]
lemma freeModuleHomEquiv_comp {S T : LightProfinite.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((free R).map (lightProfiniteToLightCondSet.map f) ≫ g) =
      M.obj.map f.op (T.freeModuleHomEquiv g) :=
  (ModuleCat.adj R).freeYonedaSectionsEquiv_naturality_left
    (coherentTopology LightProfinite) f M g

/-- Postcomposition by a module morphism applies its section map to the corresponding section. -/
lemma freeModuleHomEquiv_postcomp {S : LightProfinite.{u}} {N : LightCondMod R}
    (g : (free R).obj S.toCondensed ⟶ M) (f : M ⟶ N) :
    S.freeModuleHomEquiv (g ≫ f) = f.hom.app (Opposite.op S) (S.freeModuleHomEquiv g) :=
  (ModuleCat.adj R).freeYonedaSectionsEquiv_naturality_right
    (coherentTopology LightProfinite) g f

end LightProfinite
