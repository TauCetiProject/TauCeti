/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.GrothendieckGroup.GroupAlgebra.LatticeDefect.Basic
public import TauCeti.RepresentationTheory.RestrictScalars

/-!
# Reduction classes of `ZMod n`-representations

A representation `ρ` of `G` over `ZMod n` is in particular a representation on an abelian group,
`ρ.restrictScalarsInt`. Its reduction `ZMod n ⊗_ℤ W` is `W` again: since every element of
`ZMod n` is the image of an integer, Mathlib's `TensorProduct.lidOfCompatibleSMul` identifies
`ZMod n ⊗_ℤ W` with `W` by `r ⊗ w ↦ r • w`, and this identification is `G`-equivariant
(`Representation.baseChangeRestrictScalarsIntEquiv`). Hence the reduction class of
`ρ.restrictScalarsInt` in `G₀(ZMod n[G])` is the class of `ρ` itself
(`TauCeti.reductionK0_restrictScalarsInt`).

This is how the reduction classes computed for groups such as `Lˣ ⧸ (Lˣ)^ℓ`, which are naturally
`ZMod ℓ`-modules, are compared with the classes of the corresponding `ZMod ℓ`-representations.
-/

public section

open TensorProduct
open scoped MonoidAlgebra

variable {n : ℕ} {G : Type} [Monoid G] {W : Type} [AddCommGroup W] [Module (ZMod n) W]

namespace Representation

/-- **The reduction of a `ZMod n`-module is itself**: `r ⊗ w ↦ r • w` is a `G`-equivariant
`ZMod n`-linear isomorphism `ZMod n ⊗_ℤ W ≃ W` for every representation `ρ` of `G` over
`ZMod n`. -/
noncomputable def baseChangeRestrictScalarsIntEquiv (ρ : Representation (ZMod n) G W) :
    (Representation.baseChange (ZMod n) ρ.restrictScalarsInt).Equiv ρ :=
  haveI : CompatibleSMul ℤ (ZMod n) (ZMod n) W :=
    .of_algebraMap_surjective _ _ ZMod.intCast_surjective
  .mk (TensorProduct.lidOfCompatibleSMul ℤ (ZMod n) W) fun g ↦ by
    ext w
    simp [TensorProduct.lidOfCompatibleSMul_tmul, Representation.baseChange_apply]

/-- The equivalence `ZMod n ⊗_ℤ W ≃ W` is the scalar multiplication on pure tensors. -/
@[simp]
theorem baseChangeRestrictScalarsIntEquiv_tmul (ρ : Representation (ZMod n) G W) (r : ZMod n)
    (w : W) : ρ.baseChangeRestrictScalarsIntEquiv (r ⊗ₜ w) = r • w :=
  (rfl)

end Representation

namespace TauCeti

/-- **The reduction class of a `ZMod n`-representation is its class.** In `G₀(ZMod n[G])`,
the class of `ZMod n ⊗_ℤ W` is the class of the `ZMod n[G]`-module of `ρ`. -/
theorem reductionK0_restrictScalarsInt [Module.Finite (ZMod n) W]
    (ρ : Representation (ZMod n) G W) :
    haveI : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
      Module.Finite.equiv (ρ.baseChangeRestrictScalarsIntEquiv).toLinearEquiv.symm
    haveI : Module.Finite (ZMod n)[G] ρ.asModule :=
      Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
    reductionK0 (ZMod n) ρ.restrictScalarsInt =
      ExactK0.of (FGModuleCat.of (ZMod n)[G] ρ.asModule) := by
  have : Module.Finite (ZMod n) (ZMod n ⊗[ℤ] W) :=
    Module.Finite.equiv (ρ.baseChangeRestrictScalarsIntEquiv).toLinearEquiv.symm
  have : Module.Finite (ZMod n)[G] ρ.asModule :=
    Module.Finite.of_restrictScalars_finite (ZMod n) (ZMod n)[G] _
  rw [reductionK0_def]
  exact ExactK0.of_congr
    (Representation.asModuleLinearEquivOfEquiv (ρ.baseChangeRestrictScalarsIntEquiv)
      ).toFGModuleCatIso

end TauCeti
