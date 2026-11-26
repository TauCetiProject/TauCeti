/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Presentable.Finite
public import TauCeti.CategoryTheory.Sites.Coherent.Colimits
public import TauCeti.Condensed.Light.Free

import Mathlib.CategoryTheory.Limits.Preserves.Ulift

/-!
# Filtered colimits of light condensed modules

Filtered colimits are computed sectionwise. Consequently the free light condensed
modules on light profinite test spaces are finitely presentable.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace LightProfinite

/-- The free light condensed module on a test object is finitely presentable
for diagrams in the universe of its sections. -/
instance isFinitelyPresentable_free (R : Type u) [Ring R] (S : LightProfinite.{u}) :
    IsFinitelyPresentable.{u} ((LightCondensed.free R).obj S.toCondensed) := by
  rw [isFinitelyPresentable_iff_preservesFilteredColimitsOfSize]
  let E := sheafToPresheaf (coherentTopology LightProfinite.{u}) (ModuleCat.{u} R) ⋙
    (evaluation _ _).obj (op S) ⋙ forget (ModuleCat.{u} R) ⋙ uliftFunctor.{u + 1, u}
  let e : coyoneda.obj (op ((LightCondensed.free R).obj S.toCondensed)) ≅ E :=
    NatIso.ofComponents
      (fun M ↦ Equiv.toIso ((S.freeModuleHomEquiv (M := M)).toEquiv.trans Equiv.ulift.symm))
      (fun f ↦ by
        ext g
        exact congrArg ULift.up (S.freeModuleHomEquiv_postcomp g f))
  exact ⟨fun J _ _ ↦ preservesColimitsOfShape_of_natIso e.symm⟩

end LightProfinite
