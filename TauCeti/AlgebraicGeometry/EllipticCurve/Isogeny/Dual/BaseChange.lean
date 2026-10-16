/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Dual.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.Hom.BaseChange

/-!
# Base change of the dual of a morphism

The dual of a morphism of elliptic curves (`TauCeti.Isogeny.Hom.dual`) commutes with base change
along any homomorphism of fields. On an isogeny this is `TauCeti.Isogeny.dual_map`, and the zero
map is sent to zero on both sides.

## Main results

* `TauCeti.Isogeny.Hom.dual_map`: the dual of a morphism commutes with base change.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 (the dual isogeny).
-/

public section

namespace TauCeti.Isogeny.Hom

variable {F K : Type*} [Field F] [Field K] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  [W₂.IsElliptic]

/-- **The dual commutes with base change** along any homomorphism of fields. -/
@[simp]
theorem dual_map (f : Hom W₁ W₂) (σ : F →+* K) : f.dual.map σ = (f.map σ).dual := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

end TauCeti.Isogeny.Hom

end
