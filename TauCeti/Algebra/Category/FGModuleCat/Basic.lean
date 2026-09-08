/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.FGModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Finiteness.Prod

/-!
# Finitely generated modules

This file provides general results about Mathlib's category of finitely generated modules.

## Main results

* `FGModuleCat.finrank_biprod`: rank is additive on biproducts of finite free modules.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The rank of a biproduct of finite free modules is the sum of their ranks. -/
theorem _root_.FGModuleCat.finrank_biprod (R : Type u) [Ring R] [StrongRankCondition R]
    (X Y : FGModuleCat.{v} R) [Module.Free R X] [Module.Free R Y] :
    Module.finrank R ((X ⊞ Y : FGModuleCat.{v} R) : Type v) =
      Module.finrank R X + Module.finrank R Y := by
  let F := forget₂ (FGModuleCat.{v} R) (ModuleCat.{v} R)
  let _ : PreservesBinaryBiproduct X Y F :=
    preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  let e : F.obj (X ⊞ Y) ≅ ModuleCat.of R (X × Y) :=
    F.mapBiprod X Y ≪≫ ModuleCat.biprodIsoProd X.obj Y.obj
  let e' : (X ⊞ Y : FGModuleCat.{v} R) ≅ FGModuleCat.of R (X × Y) := F.preimageIso e
  exact (FGModuleCat.isoToLinearEquiv e').finrank_eq.trans Module.finrank_prod

end TauCeti
