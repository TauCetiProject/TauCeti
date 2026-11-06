/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Derivation.Basic
public import TauCeti.Algebra.OreExtension.Basic

/-!
# Differential operator rings

An ordinary derivation `δ` of an associative `R`-algebra `A`, that is an element of the
derivation Lie algebra `TauCeti.derivationLieAlgebra R A`, is a skew derivation for the identity
twist (`TauCeti.derivationLieAlgebra.toSigmaDerivation`). The Ore extension `A[X; δ]` it defines
is the ring of differential operators with coefficients in `A`: its variable satisfies

`X * C a - C a * X = C (δ a)`,

so the inner derivation of `X` restricts to `δ` on the coefficients
(`TauCeti.OreExtension.X_mul_C_sub_C_mul_X`). For instance, the enveloping algebra of a Lie algebra
with an adjoined derivation is such a ring.

## References

* J. C. McConnell and J. C. Robson, *Noncommutative Noetherian Rings*, §1.2, for differential
  operator rings as Ore extensions with identity twist.
-/

public section

namespace TauCeti

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

namespace derivationLieAlgebra

/-- An ordinary derivation, as a skew derivation for the identity twist. -/
def toSigmaDerivation (δ : derivationLieAlgebra R A) : SigmaDerivation (AlgHom.id R A) where
  toLinearMap := δ
  leibniz' a b := by rw [leibniz, AlgHom.id_apply, add_comm]
  map_one' := apply_one_eq_zero δ

@[simp]
theorem coe_toSigmaDerivation (δ : derivationLieAlgebra R A) :
    ⇑(toSigmaDerivation δ) = ⇑(δ : Module.End R A) :=
  (rfl)

end derivationLieAlgebra

namespace OreExtension

/-- **The commutator of the variable with a coefficient** in the differential operator ring
`A[X; δ]` is `X * C a - C a * X = C (δ a)`. -/
theorem X_mul_C_sub_C_mul_X (δ : derivationLieAlgebra R A) (a : A) :
    X (σ := AlgHom.id R A) (δ := derivationLieAlgebra.toSigmaDerivation δ) * C a - C a * X =
      C ((δ : Module.End R A) a) := by
  rw [X_mul_C, AlgHom.id_apply, derivationLieAlgebra.coe_toSigmaDerivation, add_sub_cancel_left]

end OreExtension

end TauCeti
