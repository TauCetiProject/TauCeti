/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.Rees.Sl2Casimir.ZeroFiber
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Gradient

/-!
# Symmetric gradient of the `sl₂` Casimir symbol

Computes the explicit symmetric gradient `2ξ(h)h + 4ξ(f)e + 4ξ(e)f` of
`TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol R L h e f` at a dual vector
`ξ : Module.Dual R L`.
-/

public section

namespace Module.Basis

/-- Gradient of `TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol R L h e f` at
`ξ : Module.Dual R L`: `(2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f`. -/
theorem symmetricGradient_sl2CasimirSymbol {R L ι : Type*}
    [CommRing R] [LieRing L] [LieAlgebra R L] [Fintype ι]
    (b : Module.Basis ι R L) (h e f : L) (ξ : Module.Dual R L) :
    b.symmetricGradient (TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol R L h e f) ξ =
      (2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f := by
  rw [TauCeti.UniversalEnvelopingAlgebra.sl2CasimirSymbol_def, mul_assoc,
    b.symmetricGradient_add, b.symmetricGradient_pow, b.symmetricGradient_mul,
    b.symmetricGradient_mul, b.symmetricGradient_ι, b.symmetricGradient_ι,
    b.symmetricGradient_ι, b.symmetricGradient_ofNat]
  simp only [Nat.reduceSub, pow_one, nsmul_eq_mul, Nat.cast_ofNat, map_mul,
    SymmetricAlgebra.lift_ι_apply, map_ofNat, smul_zero, add_zero, smul_add, smul_smul]
  abel

end Module.Basis
