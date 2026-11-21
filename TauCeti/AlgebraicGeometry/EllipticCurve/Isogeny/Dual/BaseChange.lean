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

* `TauCeti.Isogeny.ofIsogeny_dual_map` and `TauCeti.Isogeny.ofIsogeny_dual_baseChange`: the dual
  commutes with base change on `Hom` carriers.
* `TauCeti.Isogeny.Hom.dual_map`: the dual of a morphism commutes with base change.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.6.1 (the dual isogeny).
-/

public section

namespace TauCeti.Isogeny

open WeierstrassCurve

variable {F K : Type*} [Field F] [Field K] {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic]
  [W₂.IsElliptic] (φ : Isogeny W₁ W₂)

/-- Base change commutes with the dual isogeny on `Hom` carriers. -/
theorem ofIsogeny_dual_map (f : F →+* K) :
    Hom.ofIsogeny (φ.dual.map f) = Hom.ofIsogeny (φ.map f).dual :=
  congrArg Hom.ofIsogeny (φ.dual_map f)

/-- Base change along `algebraMap F L` commutes with the dual isogeny on `Hom` carriers.
Stated separately from `ofIsogeny_dual_map` so that the implicit curve parameters match
`(W₂⁄L).toAffine` and `(W₁⁄L).toAffine` at reducible transparency. -/
theorem ofIsogeny_dual_baseChange {W₁ W₂ : WeierstrassCurve F} [W₁.IsElliptic] [W₂.IsElliptic]
    (φ : Isogeny W₁.toAffine W₂.toAffine) (L : Type*) [Field L] [Algebra F L] :
    Hom.ofIsogeny (φ.dual.baseChange L) = Hom.ofIsogeny (φ.baseChange L).dual :=
  congrArg Hom.ofIsogeny (φ.dual_map (algebraMap F L))

namespace Hom

variable {W₁ W₂ : WeierstrassCurve.Affine F} [W₁.IsElliptic] [W₂.IsElliptic]

/-- **The dual commutes with base change** along any homomorphism of fields. -/
@[simp]
theorem dual_map (f : Hom W₁ W₂) (σ : F →+* K) : f.dual.map σ = (f.map σ).dual := by
  rcases eq_zero_or_exists_ofIsogeny f with rfl | ⟨φ, rfl⟩ <;> simp

end Hom

end TauCeti.Isogeny

end
