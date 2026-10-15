/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.Isogeny.BaseChange.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.FunctionField.Genus
import TauCeti.FieldTheory.FunctionField.Elliptic.Nonsingular
import TauCeti.FieldTheory.FunctionField.Elliptic.Weierstrass.Model

/-!
# The source of an isogeny to an elliptic curve is elliptic

An isogeny `φ : W₁ → W₂` in this development is a coordinate pullback, defined for arbitrary
Weierstrass curves: neither curve is assumed to be nonsingular. This file proves that the source
is nonsingular as soon as the target is. Geometrically, a singular Weierstrass cubic is a rational
curve, and a rational curve dominates no curve of genus one.

Over a perfect field `F` the argument is Lüroth's theorem. If `Δ(W₁) = 0`, then `W₁` has a singular
point `(x₀, y₀)` over `F`, and the slope `(y - y₀) / (x - x₀)` generates the function field `F(W₁)`
(`TauCeti.Place.IsWeierstrassCoordinates.adjoin_div_eq_top_of_isSingular`), so `F(W₁)` is a
rational function field. The pullback `φ^*` embeds `F(W₂)` into it, and by Lüroth's theorem
(`RatFunc.Luroth.algEquiv`) every subfield of a rational function field other than `F` is again
rational. So `F(W₂)` would be rational, of genus zero (`TauCeti.genus_eq_zero_of_algHom_ratFunc`),
while the function field of an elliptic curve has genus one.

Over an arbitrary field a singular point need not be rational, so the general case is reduced to
the perfect one by base change to the algebraic closure `K := AlgebraicClosure F`: the
base-changed isogeny `W₁ ⊗ K → W₂ ⊗ K` (`TauCeti.Isogeny.map`) has elliptic target, hence elliptic
source, and the discriminant of `W₁ ⊗ K` is the image of that of `W₁`.

## Main results

* `TauCeti.Isogeny.isElliptic`: if `W₂` is elliptic, then so is the source of every isogeny
  `W₁ → W₂`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], II.2.5.1 and III.1.4.
* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Proposition 6.1.2.
-/

public section

open scoped IntermediateField

namespace TauCeti

namespace Isogeny

variable {F : Type*} [Field F] {W₁ W₂ : WeierstrassCurve.Affine F}

/-- Over a perfect field, the source of an isogeny to an elliptic curve is elliptic: a singular
source would make its function field rational, and Lüroth's theorem would then make the function
field of the target rational, of genus zero rather than one. -/
private theorem isElliptic_of_perfectField [PerfectField F] [W₂.IsElliptic]
    (φ : Isogeny W₁ W₂) : W₁.IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero]
  intro hΔ
  obtain ⟨x₀, y₀, hs⟩ := WeierstrassCurve.Affine.exists_isSingular_of_Δ_eq_zero W₁ hΔ
  have hW := Place.isWeierstrassCoordinates_infinity (W₁ : WeierstrassCurve F)
  set z : W₁.FunctionField := (W₁.genericY - algebraMap F W₁.FunctionField y₀) /
    (W₁.genericX - algebraMap F W₁.FunctionField x₀)
  -- The slope at the singular point is a transcendental generator of `F(W₁)`.
  let e : RatFunc F ≃ₐ[F] W₁.FunctionField :=
    (RatFunc.algEquivOfTranscendental z
      (hW.transcendental_div_of_isSingular W₁.isFunctionField Place.degree_infinity hs)).trans
      ((IntermediateField.equivOfEq (hW.adjoin_div_eq_top_of_isSingular W₁.isFunctionField
        Place.degree_infinity hs)).trans IntermediateField.topEquiv)
  -- So `φ^*` embeds `F(W₂)` into a rational function field, and by Lüroth's theorem `F(W₂)` has
  -- genus zero, while the function field of an elliptic curve has genus one.
  have : Algebra.Transcendental F W₂.FunctionField :=
    ⟨_, (Place.isWeierstrassCoordinates_infinity (W₂ : WeierstrassCurve F)).transcendental_x⟩
  have hgenus := genus_eq_zero_of_algHom_ratFunc (e.symm.toAlgHom.comp φ.fieldPullback)
  rw [WeierstrassCurve.Affine.genus_functionField] at hgenus
  exact one_ne_zero hgenus

/-- **The source of an isogeny to an elliptic curve is elliptic**, over every field: a Weierstrass
curve admitting an isogeny to an elliptic curve is nonsingular. -/
theorem isElliptic [W₂.IsElliptic] (φ : Isogeny W₁ W₂) : W₁.IsElliptic := by
  have := isElliptic_of_perfectField (φ.map (algebraMap F (AlgebraicClosure F)))
  rw [WeierstrassCurve.isElliptic_iff, isUnit_iff_ne_zero] at this ⊢
  simpa using this

end Isogeny

end TauCeti

end
