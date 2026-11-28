/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Sl2.Casimir.Symbol
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Gradient

/-!
# Symmetric gradient of the `sl₂` Casimir symbol

Computes the explicit symmetric gradient `2ξ(h)h + 4ξ(f)e + 4ξ(e)f` of
`TauCeti.sl2CasimirSymbol R L h e f` at a dual vector `ξ : Module.Dual R L`.
-/

public section

namespace TauCeti

/-- Gradient of `TauCeti.sl2CasimirSymbol R L h e f` at `ξ : Module.Dual R L`:
`(2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f`. -/
theorem gradient_sl2CasimirSymbol {R L : Type*}
    [CommSemiring R] [AddCommMonoid L] [Module R L]
    (h e f : L) (ξ : Module.Dual R L) :
    (sl2CasimirSymbol R L h e f).gradient ξ =
      (2 * ξ h) • h + (4 * ξ f) • e + (4 * ξ e) • f := by
  rw [sl2CasimirSymbol_def]
  simp [nsmul_eq_mul, smul_smul, map_ofNat, mul_comm (ξ f) 4]
  abel

end TauCeti
