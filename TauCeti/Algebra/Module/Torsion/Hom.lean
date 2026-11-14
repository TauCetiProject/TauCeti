/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Hom
public import Mathlib.Algebra.Module.Torsion.Pi

/-!
# Torsion-freeness of bundled additive homomorphisms

Additive monoid homomorphisms `A →+ B` into a torsion-free `R`-module `B` form a torsion-free
`R`-module under the pointwise scalar action (`AddMonoidHom.instModuleIsTorsionFree`), since
evaluation embeds `A →+ B` `R`-linearly into `A → B`.
-/

public section

namespace AddMonoidHom

/-- Additive monoid homomorphisms into a torsion-free module form a torsion-free module. -/
instance instModuleIsTorsionFree {R A B : Type*} [Semiring R] [AddMonoid A] [AddCommMonoid B]
    [Module R B] [Module.IsTorsionFree R B] : Module.IsTorsionFree R (A →+ B) :=
  (DFunLike.coe_injective (F := A →+ B)).moduleIsTorsionFree DFunLike.coe fun _ _ ↦ rfl

end AddMonoidHom
