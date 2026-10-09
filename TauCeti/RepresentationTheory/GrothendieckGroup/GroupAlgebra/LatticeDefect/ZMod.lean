/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic

/-!
# Reduction classes of `ZMod n`-representations

A representation `ρ` of `G` over `ZMod n` is in particular a representation on an abelian group,
`ρ.restrictScalarsInt`. Its reduction `ZMod n ⊗_ℤ W` is `W` again
(`Representation.baseChangeRestrictScalarsIntEquiv`), so the reduction class of
`ρ.restrictScalarsInt` in `G₀(ZMod n[G])` is the class of `ρ` itself
(`TauCeti.reductionK0_restrictScalarsInt`).

This is how the reduction classes computed for groups such as `Lˣ ⧸ (Lˣ)^ℓ`, which are naturally
`ZMod ℓ`-modules, are compared with the classes of the corresponding `ZMod ℓ`-representations.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

variable {n : ℕ} {G : Type} [Monoid G] {W : Type} [AddCommGroup W] [Module (ZMod n) W]

/-- **The reduction class of a `ZMod n`-representation is its class.** In `G₀(ZMod n[G])`,
the class of `ZMod n ⊗_ℤ W` is the class of the `ZMod n[G]`-module of `ρ`. -/
theorem reductionK0_restrictScalarsInt [Module.Finite (ZMod n) W]
    (ρ : Representation (ZMod n) G W) :
    haveI : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
      Module.Finite.equiv ρ.baseChangeRestrictScalarsIntEquiv.toLinearEquiv.symm
    haveI : Module.Finite (ZMod n)[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
    reductionK0 (ZMod n) ρ.restrictScalarsInt =
      ExactK0.of (FGModuleCat.of (ZMod n)[G] ρ.asModule) := by
  have : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
    Module.Finite.equiv ρ.baseChangeRestrictScalarsIntEquiv.toLinearEquiv.symm
  have : Module.Finite (ZMod n)[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
  rw [reductionK0_def]
  exact ExactK0.of_congr
    (Representation.asModuleLinearEquivOfEquiv ρ.baseChangeRestrictScalarsIntEquiv).toFGModuleCatIso

end TauCeti
