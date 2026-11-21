/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.Condensed.Light.Functors
public import Mathlib.Condensed.Light.Module

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
  toEquiv := ((freeForgetAdjunction R).homEquiv S.toCondensed M).trans
    (coherentTopology LightProfinite).yonedaEquiv
  map_add' _ _ := rfl

lemma freeModuleHomEquiv_comp {S T : LightProfinite.{u}} (f : S ⟶ T)
    (g : (free R).obj T.toCondensed ⟶ M) :
    S.freeModuleHomEquiv ((lightProfiniteToLightCondSet ⋙ free R).map f ≫ g) =
      M.obj.map f.op (T.freeModuleHomEquiv g) := by
  let J := coherentTopology LightProfinite.{u}
  let adj := freeForgetAdjunction R
  exact Eq.trans
    (congrArg J.yonedaEquiv (adj.homEquiv_naturality_left (lightProfiniteToLightCondSet.map f) g))
    (J.yonedaEquiv_naturality (adj.homEquiv T.toCondensed M g) f).symm

end LightProfinite
