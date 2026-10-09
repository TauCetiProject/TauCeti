/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic

/-!
# Reduction classes of representations over epimorphic `ℤ`-algebras

Let `A` be a commutative ring such that `ℤ → A` is an epimorphism, for example `A = ZMod n`.
A representation `ρ` of `G` over `A` is in particular a representation on an abelian group,
`ρ.restrictScalarsInt`. Its reduction `A ⊗_ℤ W` is `W` again
(`Representation.baseChangeRestrictScalarsIntEquiv`), so the reduction class of
`ρ.restrictScalarsInt` in `G₀(A[G])` is the class of `ρ` itself
(`TauCeti.reductionK0_restrictScalarsInt`).

This is how the reduction classes computed for groups such as `Lˣ ⧸ (Lˣ)^ℓ`, which are naturally
`ZMod ℓ`-modules, are compared with the classes of the corresponding `ZMod ℓ`-representations.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u

variable {A G W : Type u} [CommRing A] [Algebra.IsEpi ℤ A] [Monoid G] [AddCommGroup W]
  [Module A W]

/-- **The reduction class of a representation over an epimorphic `ℤ`-algebra is its class.**
If `ℤ → A` is an epimorphism, then in `G₀(A[G])` the class of `A ⊗_ℤ W` is the class of the
`A[G]`-module of `ρ`. -/
theorem reductionK0_restrictScalarsInt [Module.Finite A W] (ρ : Representation A G W) :
    haveI : Module.Finite A (A ⊗[ℤ] W) :=
      Module.Finite.equiv ρ.baseChangeRestrictScalarsIntEquiv.toLinearEquiv.symm
    haveI : Module.Finite A[G] ρ.asModule := Module.Finite.of_restrictScalars_finite A A[G] _
    reductionK0 A ρ.restrictScalarsInt = ExactK0.of (FGModuleCat.of A[G] ρ.asModule) := by
  have : Module.Finite A (A ⊗[ℤ] W) :=
    Module.Finite.equiv ρ.baseChangeRestrictScalarsIntEquiv.toLinearEquiv.symm
  have : Module.Finite A[G] ρ.asModule := Module.Finite.of_restrictScalars_finite A A[G] _
  rw [reductionK0_def]
  exact ExactK0.of_congr
    (Representation.asModuleLinearEquivOfEquiv ρ.baseChangeRestrictScalarsIntEquiv).toFGModuleCatIso

end TauCeti
