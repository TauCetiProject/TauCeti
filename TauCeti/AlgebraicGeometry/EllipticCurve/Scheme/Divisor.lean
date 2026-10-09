/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EffectiveCartierDivisor.Section
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.BaseChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Scheme.Smooth

/-!
# The zero-section divisor of a projective Weierstrass model

For an elliptic Weierstrass curve `W` over a commutative ring, the zero section
`[0 : 1 : 0] : Spec R ⟶ projModel W` cuts out a relative effective Cartier divisor. This file
defines its ideal sheaf as `WeierstrassCurve.zeroSectionDivisor` and proves the same result for
every nonnegative multiple `n[0]`, represented by the power of that ideal sheaf.

The construction commutes with arbitrary change of the coefficient ring. Thus these divisors can
be used uniformly in families, including over nonreduced bases, as the divisors underlying the
pole sheaves `𝒪(n[0])`.

## Main results

* `WeierstrassCurve.isRelativeEffectiveCartier_zeroSectionDivisor`: `[0]` is a relative effective
  Cartier divisor.
* `WeierstrassCurve.isRelativeEffectiveCartier_zeroSectionDivisor_pow`: every `n[0]` is a relative
  effective Cartier divisor.
* `WeierstrassCurve.zeroSectionDivisor_map`: `[0]` commutes with arbitrary base change.
* `WeierstrassCurve.zeroSectionDivisor_pow_map`: the same is true for `n[0]`.

## References

* N. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, §2.2.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe u

namespace WeierstrassCurve

variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The relative divisor `[0]` on the projective Weierstrass model, represented by the ideal
sheaf of the zero section `[0 : 1 : 0]`. -/
noncomputable def zeroSectionDivisor : W.projModel.IdealSheafData :=
  W.projModelZero.ker

/-- The zero-section divisor is the ideal sheaf of `projModelZero`. -/
theorem zeroSectionDivisor_def : W.zeroSectionDivisor = W.projModelZero.ker :=
  (rfl)

/-- **The zero section cuts out a relative effective Cartier divisor.** The projective model of
an elliptic Weierstrass curve is a separated smooth relative curve, so its zero section is a
relative effective Cartier divisor over the coefficient scheme. -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor [W.IsElliptic] :
    W.zeroSectionDivisor.IsRelativeEffectiveCartier W.projModelOver := by
  rw [zeroSectionDivisor_def]
  exact AlgebraicGeometry.Scheme.Hom.isRelativeEffectiveCartier_ker_of_smoothOfRelativeDimension
    W.projModelZero W.projModelZero_projModelOver

/-- **Every nonnegative multiple `n[0]` is a relative effective Cartier divisor.** Multiplication
of ideal sheaves represents addition of effective Cartier divisors, so the power
`zeroSectionDivisor W ^ n` represents `n[0]`. -/
theorem isRelativeEffectiveCartier_zeroSectionDivisor_pow [W.IsElliptic] (n : ℕ) :
    (W.zeroSectionDivisor ^ n).IsRelativeEffectiveCartier W.projModelOver :=
  TauCeti.isRelativeEffectiveCartier_pow W.isRelativeEffectiveCartier_zeroSectionDivisor n

variable {R' : Type u} [CommRing R'] (f : R →+* R')

/-- **The zero-section divisor commutes with arbitrary base change.** Under the canonical map
`projModel (W.map f) ⟶ projModel W`, the inverse image of `[0]` is the zero-section divisor of the
base-changed Weierstrass curve. -/
@[simp]
theorem zeroSectionDivisor_map :
    (W.map f).zeroSectionDivisor =
      W.zeroSectionDivisor.comap (W.projModelBaseChange f) := by
  have : IsClosedImmersion (W.projModelZero ≫ W.projModelOver) := by
    rw [W.projModelZero_projModelOver]
    infer_instance
  let : IsClosedImmersion W.projModelZero :=
    IsClosedImmersion.of_comp W.projModelZero W.projModelOver
  rw [zeroSectionDivisor_def, zeroSectionDivisor_def]
  exact AlgebraicGeometry.Scheme.IdealSheafData.ker_eq_comap_of_isPullback W.projModelZero
    (W.isPullback_projModelZero_projModelBaseChange f)

/-- **The multiples `n[0]` commute with arbitrary base change.** -/
theorem zeroSectionDivisor_pow_map (n : ℕ) :
    (W.map f).zeroSectionDivisor ^ n =
      (W.zeroSectionDivisor ^ n).comap (W.projModelBaseChange f) := by
  rw [zeroSectionDivisor_map, AlgebraicGeometry.Scheme.IdealSheafData.comap_pow]

end WeierstrassCurve
