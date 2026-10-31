/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Basic
public import TauCeti.RingTheory.FormalGroup.Logarithm.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.Derivation
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.Derivation
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.PairSubst
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.ThirdPoint
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.RingTheory.Derivation.Localization

/-!
# The invariant differential and the logarithm of the formal group of a Weierstrass curve

In the coordinates `z = -x / y`, `w = -1 / y` at the point at infinity, the invariant differential
`ω = dx / (2y + a₁x + a₃)` of a Weierstrass curve becomes

`ω = dz / (1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²)`,

where `w = w(z)` is the `w`-expansion. The denominator is `formalInvariantDifferentialDenom`; it
is minus the partial derivative in `w` of the `w`-equation, and it has constant coefficient `1`.

The main result is that this expansion of `ω` is the normalised invariant differential of the
formal group law `Ê` of the curve
(`invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom`):

`P(z) · (1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²) = 1`,

where `P(T) dT` is the invariant differential of `Ê`, so `P(T) = F_X(0, T)⁻¹`. Equivalently, the
partial derivative of the group law in its first variable at `X = 0` is the denominator
(`subst_pderiv_formalGroup`). The expansion begins `ω = (1 + a₁z + (a₁² + a₂)z² + ⋯) dz`.

Over a `ℚ`-algebra the formal logarithm of `Ê` is therefore the integral of the expansion of `ω`
(`derivative_log_formalGroup_mul_formalInvariantDifferentialDenom`), and it begins
`log(z) = z + (a₁ / 2) z² + ((a₁² + a₂) / 3) z³ + ⋯`. Over a `ℚ`-algebra this logarithm is the
strict isomorphism `FormalGroup.logIso` from `Ê` to the additive formal group law.

## Main definitions

* `WeierstrassCurve.formalInvariantDifferentialDenom`: the series
  `1 - a₁z - a₂z² - 2a₃w(z) - 2a₄zw(z) - 3a₆w(z)²`.

## Main results

* `WeierstrassCurve.inv_evalEval_polynomialY_smul_derivation_div`: for any derivation `D` on a
  field and any solution `(q, w)` of the `w`-equation, `(2y + a₁x + a₃)⁻¹ • D x` at the point
  `(x, y) = (q / w, -1 / w)` is `D q` scaled by the inverse of the denominator at `(q, w)`. This is
  the change of coordinates from `(x, y)` to `(z, w)` in `ω`.
* `WeierstrassCurve.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom`: the
  invariant differential of `Ê` times the denominator is `1`.
* `WeierstrassCurve.subst_pderiv_formalGroup`: `F_X(0, T)` is the denominator.
* `WeierstrassCurve.coeff_one_invariantDifferential_formalGroup` and
  `WeierstrassCurve.coeff_two_invariantDifferential_formalGroup`: the invariant differential
  begins `1 + a₁T + (a₁² + a₂)T²`.
* `WeierstrassCurve.derivative_log_formalGroup_mul_formalInvariantDifferentialDenom`: over a
  `ℚ`-algebra, the derivative of the formal logarithm of `Ê` times the denominator is `1`.
* `WeierstrassCurve.coeff_two_log_formalGroup` and `WeierstrassCurve.coeff_three_log_formalGroup`:
  the logarithm begins `T + (a₁ / 2)T² + ((a₁² + a₂) / 3)T³`.

## Implementation notes

The invariance of `ω` is the additivity of `dx / (2y + a₁x + a₃)` along the addition law, for an
arbitrary derivation (`WeierstrassCurve.Affine.Point.inv_smul_derivation_xCoord_add`). It is
applied to the partial derivative in the first variable, extended to the fraction field of the
two-variable series ring, at the points with parameters `X 0`, `X 1` and `F(X 0, X 1)` of the
universal curve over that field. Their sum relation is the one the associativity proof of the
group law uses. This gives `F_X(X, Y) · G(X) = G(F(X, Y))` for the denominator `G`, and setting
`X = 0` gives `F_X(0, Y) = G(Y)`. The universal curve is used because the argument needs a field
of fractions; the identity is carried to every curve over every commutative ring by
specialisation.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], IV.1, IV.4 and IV.5.
-/

public section

open MvPowerSeries

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

/-! ### The denominator of the invariant differential -/

/-- The series `1 - a₁z - a₂z² - 2a₃w(z) - 2a₄zw(z) - 3a₆w(z)²`, the denominator of the invariant
differential `ω = dz / (1 - a₁z - ⋯)` in the coordinate `z = -x / y` at the point at infinity. It
is minus the partial derivative in `w` of the `w`-equation, evaluated at `w = w(z)`. -/
noncomputable def formalInvariantDifferentialDenom : PowerSeries R :=
  1 - W.a₁ • PowerSeries.X - W.a₂ • PowerSeries.X ^ 2 - (2 * W.a₃) • formalW W -
    (2 * W.a₄) • (PowerSeries.X * formalW W) - (3 * W.a₆) • formalW W ^ 2

/-- The defining formula for `formalInvariantDifferentialDenom`. -/
theorem formalInvariantDifferentialDenom_def :
    W.formalInvariantDifferentialDenom =
      1 - W.a₁ • PowerSeries.X - W.a₂ • PowerSeries.X ^ 2 - (2 * W.a₃) • formalW W -
        (2 * W.a₄) • (PowerSeries.X * formalW W) - (3 * W.a₆) • formalW W ^ 2 :=
  (rfl)

/-- The denominator read at a substitutable series `a`: the same expression in `a` and `w(a)`. -/
theorem subst_formalInvariantDifferentialDenom {τ S : Type*} [CommRing S] [Algebra R S]
    {a : MvPowerSeries τ S} (ha : PowerSeries.HasSubst a) :
    PowerSeries.subst a W.formalInvariantDifferentialDenom =
      1 - W.a₁ • a - W.a₂ • a ^ 2 - (2 * W.a₃) • PowerSeries.subst a (formalW W) -
        (2 * W.a₄) • (a * PowerSeries.subst a (formalW W)) -
        (3 * W.a₆) • PowerSeries.subst a (formalW W) ^ 2 := by
  have h := PowerSeries.subst_X ha (R := R)
  rw [formalInvariantDifferentialDenom, ← PowerSeries.coe_substAlgHom ha] at *
  simp only [map_sub, map_one, map_smul, map_mul, map_pow, h]

/-- The denominator commutes with base change. -/
@[simp]
theorem map_formalInvariantDifferentialDenom {S : Type*} [CommRing S] (φ : R →+* S) :
    (W.map φ).formalInvariantDifferentialDenom =
      PowerSeries.map φ W.formalInvariantDifferentialDenom := by
  simp [formalInvariantDifferentialDenom, map_formalW, PowerSeries.smul_eq_C_mul, map_ofNat]

/-- The denominator below degree three: `w(z)` starts in degree three, so only
`1 - a₁z - a₂z²` contributes there. -/
private theorem coeff_formalInvariantDifferentialDenom_of_lt {n : ℕ} (hn : n < 3) :
    PowerSeries.coeff n W.formalInvariantDifferentialDenom =
      PowerSeries.coeff n
        (1 - W.a₁ • PowerSeries.X - W.a₂ • PowerSeries.X ^ 2 : PowerSeries R) := by
  have hw : formalW W = PowerSeries.X ^ 3 * formalU W := formalW_eq_X_pow_mul_formalU W
  have hzw : PowerSeries.X * formalW W = PowerSeries.X ^ 3 * (PowerSeries.X * formalU W) := by
    rw [hw]; ring
  have hww : formalW W ^ 2 = PowerSeries.X ^ 3 * (PowerSeries.X ^ 3 * formalU W ^ 2) := by
    rw [hw]; ring
  rw [formalInvariantDifferentialDenom, hzw, hww, hw]
  simp [PowerSeries.coeff_X_pow_mul', show ¬3 ≤ n by omega]

/-- The denominator has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_formalInvariantDifferentialDenom :
    PowerSeries.constantCoeff W.formalInvariantDifferentialDenom = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_formalInvariantDifferentialDenom_of_lt W (by norm_num)]
  simp

/-- The linear coefficient of the denominator is `-a₁`. -/
@[simp]
theorem coeff_one_formalInvariantDifferentialDenom :
    PowerSeries.coeff 1 W.formalInvariantDifferentialDenom = -W.a₁ := by
  rw [coeff_formalInvariantDifferentialDenom_of_lt W (by norm_num)]
  simp [PowerSeries.coeff_X_pow]

/-- The quadratic coefficient of the denominator is `-a₂`. -/
@[simp]
theorem coeff_two_formalInvariantDifferentialDenom :
    PowerSeries.coeff 2 W.formalInvariantDifferentialDenom = -W.a₂ := by
  rw [coeff_formalInvariantDifferentialDenom_of_lt W (by norm_num)]
  simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X]

/-! ### The invariant differential in the coordinates `(z, w)` -/

/-- **The invariant differential in the coordinates `z = -x / y`, `w = -1 / y`.** Let `D` be a
derivation over `R` on a field `K`, and let `(q, w)` solve the `w`-equation of `W` with `w ≠ 0`, so
that `(x, y) = (q / w, -1 / w)` is a point of `W⁄K`. If `2y + a₁x + a₃` and the denominator
`1 - a₁q - a₂q² - 2a₃w - 2a₄qw - 3a₆w²` do not vanish, then
`(2y + a₁x + a₃)⁻¹ • D x = (1 - a₁q - a₂q² - 2a₃w - 2a₄qw - 3a₆w²)⁻¹ • D q`. The hypothesis on
`2y + a₁x + a₃` is stated in the cleared form `-2 + a₁q + a₃w ≠ 0`. -/
theorem inv_evalEval_polynomialY_smul_derivation_div {K M : Type*} [Field K] [Algebra R K]
    [AddCommGroup M] [Module R M] [Module K M]
    (D : Derivation R K M) {q w : K} (hw : w ≠ 0) (heq : w = wEquationRHS W q w)
    (hG : 1 - algebraMap R K W.a₁ * q - algebraMap R K W.a₂ * q ^ 2 -
      2 * algebraMap R K W.a₃ * w - 2 * algebraMap R K W.a₄ * (q * w) -
      3 * algebraMap R K W.a₆ * w ^ 2 ≠ 0)
    (hu : -2 + algebraMap R K W.a₁ * q + algebraMap R K W.a₃ * w ≠ 0) :
    ((W⁄K).toAffine.polynomialY.evalEval (q / w) (-1 / w))⁻¹ • D (q / w) =
      (1 - algebraMap R K W.a₁ * q - algebraMap R K W.a₂ * q ^ 2 -
        2 * algebraMap R K W.a₃ * w - 2 * algebraMap R K W.a₄ * (q * w) -
        3 * algebraMap R K W.a₆ * w ^ 2)⁻¹ • D q := by
  rw [wEquationRHS_def] at heq
  have hd := congrArg D heq
  have hD (r : R) : D (algebraMap R K r) = 0 := D.map_algebraMap r
  rw [Affine.evalEval_polynomialY, D.leibniz_div]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃, map_add, Derivation.leibniz,
    Derivation.leibniz_pow, hD, smul_zero, add_zero] at hd ⊢
  generalize algebraMap R K W.a₁ = a₁ at *
  generalize algebraMap R K W.a₂ = a₂ at *
  generalize algebraMap R K W.a₃ = a₃ at *
  generalize algebraMap R K W.a₄ = a₄ at *
  generalize algebraMap R K W.a₆ = a₆ at *
  generalize hg : 1 - a₁ * q - a₂ * q ^ 2 - 2 * a₃ * w - 2 * a₄ * (q * w) - 3 * a₆ * w ^ 2 = g
    at *
  -- differentiating the `w`-equation expresses `D w` through `D q`
  have hDw : D w = ((3 * q ^ 2 + a₁ * w + 2 * a₂ * q * w + a₄ * w ^ 2) / g) • D q := by
    have : g • D w = (3 * q ^ 2 + a₁ * w + 2 * a₂ * q * w + a₄ * w ^ 2) • D q := by
      rw [← hg]
      linear_combination (norm := module) hd
    rw [div_eq_inv_mul, mul_smul, ← this, smul_smul, inv_mul_cancel₀ hG, one_smul]
  have hY : 2 * (-1 / w) + a₁ * (q / w) + a₃ = (-2 + a₁ * q + a₃ * w) / w := by
    field_simp
  rw [hY, hDw, smul_smul, smul_smul, ← sub_smul, smul_smul]
  congr 1
  field_simp
  subst hg
  linear_combination 3 * heq

/-! ### The universal curve

The comparison is made for the universal curve over `ℤ[A₁, ⋯, A₆]`, where the two-variable series
ring is a domain with a fraction field on which the points with series parameters live. -/

section Universal

/-- The two-variable series ring over the universal coefficient ring `ℤ[A₁, ⋯, A₆]`. -/
private abbrev UnivSeries := MvPowerSeries (Fin 2) (MvPolynomial Coeff ℤ)

/-- The fraction field of `UnivSeries`. -/
private abbrev UnivField := FractionRing UnivSeries

/-- The denominator at a parameter `q` has constant coefficient `1`, so it does not vanish. -/
private theorem algebraMap_subst_formalInvariantDifferentialDenom_ne_zero {q : UnivSeries}
    (hq : constantCoeff q = 0) :
    algebraMap UnivSeries UnivField
      (PowerSeries.subst q Universal.curve.formalInvariantDifferentialDenom) ≠ 0 := by
  refine (map_ne_zero_iff _ (IsFractionRing.injective UnivSeries UnivField)).2 fun h ↦ ?_
  have := congrArg constantCoeff h
  rw [PowerSeries.constantCoeff_subst_of_constantCoeff_zero hq] at this
  simp at this

/-- The denominator at a parameter `q`, written out in `UnivField`. -/
private theorem algebraMap_subst_formalInvariantDifferentialDenom {q : UnivSeries}
    (hq : constantCoeff q = 0) :
    algebraMap UnivSeries UnivField
        (PowerSeries.subst q Universal.curve.formalInvariantDifferentialDenom) =
      1 - algebraMap _ UnivField Universal.curve.a₁ * algebraMap UnivSeries UnivField q -
        algebraMap _ UnivField Universal.curve.a₂ * algebraMap UnivSeries UnivField q ^ 2 -
        2 * algebraMap _ UnivField Universal.curve.a₃ *
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) -
        2 * algebraMap _ UnivField Universal.curve.a₄ * (algebraMap UnivSeries UnivField q *
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))) -
        3 * algebraMap _ UnivField Universal.curve.a₆ *
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) ^ 2 := by
  rw [subst_formalInvariantDifferentialDenom _ (PowerSeries.HasSubst.of_constantCoeff_zero hq)]
  simp only [Algebra.smul_def, map_sub, map_one, map_mul, map_pow, map_ofNat,
    ← IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ) UnivSeries UnivField]

/-- `-2 + a₁q + a₃w(q)` has constant coefficient `-2`, so it does not vanish. -/
private theorem neg_two_add_ne_zero {q : UnivSeries} (hq : constantCoeff q = 0) :
    -2 + algebraMap _ UnivField Universal.curve.a₁ * algebraMap UnivSeries UnivField q +
      algebraMap _ UnivField Universal.curve.a₃ *
        algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) ≠ 0 := by
  have hw0 : constantCoeff (PowerSeries.subst q (formalW Universal.curve)) = 0 :=
    PowerSeries.constantCoeff_subst_eq_zero hq _ (constantCoeff_formalW _)
  have h : (-2 + Universal.curve.a₁ • q +
      Universal.curve.a₃ • PowerSeries.subst q (formalW Universal.curve) : UnivSeries) ≠ 0 :=
    fun h ↦ by simpa [hq, hw0, map_ofNat] using congrArg constantCoeff h
  simpa [Algebra.smul_def, ← IsScalarTower.algebraMap_apply (MvPolynomial Coeff ℤ) UnivSeries,
    map_ofNat] using
    (map_ne_zero_iff _ (IsFractionRing.injective UnivSeries UnivField)).2 h

/-- The curve on which the points with series parameters live is the base change of the universal
curve to `UnivField`. -/
private theorem fracCurve_eq_baseChange :
    fracCurve Universal.curve (Fin 2) UnivField = Universal.curve⁄UnivField := by
  rw [fracCurve_def, ← IsScalarTower.algebraMap_eq]
  rfl

/-- `(q, w(q))` solves the `w`-equation in `UnivField`. -/
private theorem algebraMap_subst_formalW_eq_wEquationRHS {q : UnivSeries}
    (hq : constantCoeff q = 0) :
    algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) =
      wEquationRHS Universal.curve (algebraMap UnivSeries UnivField q)
        (algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))) := by
  rw [← algebraMap_wEquationRHS,
    ← subst_formalW_wEquation _ (PowerSeries.HasSubst.of_constantCoeff_zero hq)]

/-- The point with series parameter `q` is the affine point `(q / w(q), -1 / w(q))`. -/
private theorem coords_thetaPoint (hΔ : (fracCurve Universal.curve (Fin 2) UnivField).Δ ≠ 0)
    {q : UnivSeries} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    Universal.curve.thetaPoint hΔ hq hq0 ≠ 0 ∧
      Affine.Point.xCoord (Universal.curve.thetaPoint hΔ hq hq0) =
        algebraMap UnivSeries UnivField q /
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) ∧
      Affine.Point.yCoord (Universal.curve.thetaPoint hΔ hq hq0) =
        -1 / algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)) := by
  have h : (fracCurve Universal.curve (Fin 2) UnivField).toAffine.Nonsingular
      (algebraMap UnivSeries UnivField q /
        algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)))
      (-1 / algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))) := by
    have hΔ' := hΔ
    rw [fracCurve_eq_baseChange] at hΔ' ⊢
    refine chord_point_nonsingular _ ?_
      (algebraMap_subst_formalW_ne_zero Universal.curve hq hq0) hΔ'
    simpa [wEquationRHS_def, WeierstrassCurve.baseChange] using
      algebraMap_subst_formalW_eq_wEquationRHS hq
  rw [thetaPoint_eq_some Universal.curve hΔ hq hq0 h]
  exact ⟨Affine.Point.some_ne_zero h, Affine.Point.xCoord_some h, Affine.Point.yCoord_some h⟩

/-- `2y + a₁x + a₃` does not vanish at the point `(q / w(q), -1 / w(q))`. -/
private theorem evalEval_polynomialY_div_ne_zero {q : UnivSeries} (hq : constantCoeff q = 0)
    (hq0 : q ≠ 0) :
    (Universal.curve⁄UnivField).toAffine.polynomialY.evalEval
        (algebraMap UnivSeries UnivField q /
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)))
        (-1 / algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))) ≠
      0 := by
  have hw := algebraMap_subst_formalW_ne_zero Universal.curve (KK := UnivField) hq hq0
  rw [Affine.evalEval_polynomialY]
  simp only [WeierstrassCurve.baseChange, map_a₁, map_a₃]
  convert div_ne_zero (neg_two_add_ne_zero hq) hw using 1
  field_simp

/-- At the point `(q / w(q), -1 / w(q))`, `(2y + a₁x + a₃)⁻¹ · D x = G(q)⁻¹ · D q`. -/
private theorem inv_mul_derivation_div_formalW
    (D : Derivation (MvPolynomial Coeff ℤ) UnivField UnivField)
    {q : UnivSeries} (hq : constantCoeff q = 0) (hq0 : q ≠ 0) :
    ((Universal.curve⁄UnivField).toAffine.polynomialY.evalEval
        (algebraMap UnivSeries UnivField q /
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve)))
        (-1 / algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))))⁻¹ *
        D (algebraMap UnivSeries UnivField q /
          algebraMap UnivSeries UnivField (PowerSeries.subst q (formalW Universal.curve))) =
      (algebraMap UnivSeries UnivField
        (PowerSeries.subst q Universal.curve.formalInvariantDifferentialDenom))⁻¹ *
        D (algebraMap UnivSeries UnivField q) := by
  have hG0 := algebraMap_subst_formalInvariantDifferentialDenom_ne_zero hq
  rw [algebraMap_subst_formalInvariantDifferentialDenom hq] at hG0 ⊢
  simpa only [smul_eq_mul] using
    Universal.curve.inv_evalEval_polynomialY_smul_derivation_div D
    (algebraMap_subst_formalW_ne_zero Universal.curve hq hq0)
    (algebraMap_subst_formalW_eq_wEquationRHS hq) hG0 (neg_two_add_ne_zero hq)

/-- **The invariance of `ω` for the universal curve**: `F_X(X, Y) · G(X) = G(F(X, Y))`. -/
private theorem pderiv_mul_subst_formalInvariantDifferentialDenom_universal :
    pderiv 0 (formalGroup Universal.curve).toPowerSeries *
        PowerSeries.subst (X 0 : UnivSeries) Universal.curve.formalInvariantDifferentialDenom =
      PowerSeries.subst (formalGroup Universal.curve).toPowerSeries
        Universal.curve.formalInvariantDifferentialDenom := by
  classical
  -- the partial derivative in the first variable, extended to the fraction field
  let D : Derivation (MvPolynomial Coeff ℤ) UnivField UnivField :=
    Derivation.extendOfIsLocalization (nonZeroDivisors UnivSeries)
      ((Algebra.linearMap UnivSeries UnivField).compDer (pderiv 0))
  have hD (a : UnivSeries) : D (algebraMap UnivSeries UnivField a) =
      algebraMap UnivSeries UnivField (pderiv 0 a) := by
    simp [D, Derivation.extendOfIsLocalization_algebraMap]
  have hF : (formalGroup Universal.curve).toPowerSeries =
      subst (pairSubstitution (X 0 : UnivSeries) (X 1)) (formalAdd Universal.curve) := by
    rw [formalGroup_toPowerSeries, rename_eq_subst]
    congr 1
    funext i
    rcases i with ⟨⟨⟩⟩ | ⟨⟨⟩⟩ <;> simp
  rw [hF]
  have hΔ := fracCurve_Δ_ne_zero Universal.curve (σ := Fin 2) (KK := UnivField)
    Universal.curve_Δ_ne_zero
  have hχ := hasSubst_coordSpecialize (O := MvPolynomial Coeff ℤ) (0 : Fin 2)
  have hc₀ : constantCoeff (X 0 : UnivSeries) = 0 := constantCoeff_X _
  have hc₁ : constantCoeff (X 1 : UnivSeries) = 0 := constantCoeff_X _
  have h₀ : (X 0 : UnivSeries) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have h₁ : (X 1 : UnivSeries) ≠ 0 := nonZeroDivisors.ne_zero X_mem_nonZeroDivisors
  have hχ₀ := subst_coordSpecialize_X_self (O := MvPolynomial Coeff ℤ) (0 : Fin 2)
  have hχ₁ := subst_coordSpecialize_X_of_ne (O := MvPolynomial Coeff ℤ) (i := (0 : Fin 2))
    (j := 1) (by simp)
  have hFc := constantCoeff_subst_pair_formalAdd Universal.curve hc₀ hc₁
  have hF0 := subst_pair_formalAdd_ne_zero Universal.curve hχ hc₀ hc₁ hχ₀ hχ₁
  -- the three points with parameters `X 0`, `X 1` and `F(X 0, X 1)`, and their sum relation
  obtain ⟨hP, hPx, hPy⟩ := coords_thetaPoint hΔ hc₀ h₀
  obtain ⟨hQ, hQx, hQy⟩ := coords_thetaPoint hΔ hc₁ h₁
  obtain ⟨hS, hSx, hSy⟩ := coords_thetaPoint hΔ hFc hF0
  have e := thetaPoint_add_of_subst_separates Universal.curve (KK := UnivField) hΔ hχ hc₀ hc₁
    h₀ h₁ hχ₀ hχ₁ hFc hF0
  generalize Universal.curve.thetaPoint hΔ hc₀ h₀ = P at hP hPx hPy e
  generalize Universal.curve.thetaPoint hΔ hc₁ h₁ = Q at hQ hQx hQy e
  generalize Universal.curve.thetaPoint hΔ hFc hF0 = S at hS hSx hSy e
  -- move them to `Universal.curve⁄UnivField`, the curve the derivation lemmas are stated on
  revert P Q S
  rw [fracCurve_eq_baseChange]
  intro P hP hPx hPy Q hQ hQx hQy S hS hSx hSy e
  -- additivity of `dx / (2y + a₁x + a₃)` along `P + Q = S`
  have key := Affine.Point.inv_smul_derivation_xCoord_add D hP hQ (e ▸ hS)
    (fun _ ↦ hPx ▸ hPy ▸ evalEval_polynomialY_div_ne_zero hc₀ h₀)
    (fun _ ↦ hQx ▸ hQy ▸ evalEval_polynomialY_div_ne_zero hc₁ h₁)
    (e ▸ hSx ▸ hSy ▸ evalEval_polynomialY_div_ne_zero hFc hF0)
  rw [e, hPx, hPy, hQx, hQy, hSx, hSy, smul_eq_mul, smul_eq_mul, smul_eq_mul,
    inv_mul_derivation_div_formalW D hc₀ h₀, inv_mul_derivation_div_formalW D hc₁ h₁,
    inv_mul_derivation_div_formalW D hFc hF0] at key
  simp only [hD, pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by simp), map_one,
    _root_.map_zero, mul_one, mul_zero, add_zero] at key
  apply IsFractionRing.injective UnivSeries UnivField
  rw [map_mul, (inv_mul_eq_iff_eq_mul₀
    (algebraMap_subst_formalInvariantDifferentialDenom_ne_zero hFc)).1 key]
  field_simp [algebraMap_subst_formalInvariantDifferentialDenom_ne_zero hc₀]

/-- For the universal curve, `F_X(0, T)` is the denominator: set `X = 0` in the invariance. -/
private theorem subst_pderiv_formalGroup_universal :
    subst ![0, PowerSeries.X] (pderiv 0 (formalGroup Universal.curve).toPowerSeries) =
      Universal.curve.formalInvariantDifferentialDenom := by
  have hF := (formalGroup Universal.curve).zero_constantCoeff
  have ha : HasSubst (![0, PowerSeries.X] : Fin 2 → PowerSeries (MvPolynomial Coeff ℤ)) :=
    HasSubst.zero_X
  have h := congrArg (subst (![0, PowerSeries.X] : Fin 2 → PowerSeries (MvPolynomial Coeff ℤ)))
    pderiv_mul_subst_formalInvariantDifferentialDenom_universal
  rw [subst_mul ha, subst_powerSeriesSubst ha (PowerSeries.HasSubst.X _),
    subst_powerSeriesSubst ha (PowerSeries.HasSubst.of_constantCoeff_zero hF),
    (formalGroup Universal.curve).zero_add PowerSeries.HasSubst.X', PowerSeries.X_subst] at h
  simpa [subst_X ha, PowerSeries.subst_zero_eq_C_constantCoeff] using h

end Universal

/-! ### The invariant differential of the formal group -/

/-- **The invariant differential of the formal group of a Weierstrass curve is the expansion of
`ω = dx / (2y + a₁x + a₃)`** in the coordinate `z` at the point at infinity:
`P(z) · (1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²) = 1`, where `P(T) dT` is the normalised invariant
differential of `Ê` (Silverman IV.4). No ellipticity is needed. -/
theorem invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom :
    (formalGroup W).invariantDifferential * W.formalInvariantDifferentialDenom = 1 := by
  have h := (formalGroup Universal.curve).invariantDifferential_mul_subst_pderiv
  rw [subst_pderiv_formalGroup_universal] at h
  have := congrArg (PowerSeries.map W.specialize) h
  rw [map_mul, map_one, FormalGroup.map_invariantDifferential, ← map_formalGroup,
    ← map_formalInvariantDifferentialDenom] at this
  simpa using this

/-- **The partial derivative of the group law at `X = 0`**: `F_X(0, T)` is the denominator
`1 - a₁T - a₂T² - 2a₃w(T) - 2a₄Tw(T) - 3a₆w(T)²`. -/
theorem subst_pderiv_formalGroup :
    subst ![0, PowerSeries.X] (pderiv 0 (formalGroup W).toPowerSeries) =
      W.formalInvariantDifferentialDenom := by
  have h₁ := (formalGroup W).invariantDifferential_mul_subst_pderiv
  have h₂ := W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  linear_combination W.formalInvariantDifferentialDenom * h₁ -
    subst ![0, PowerSeries.X] (pderiv 0 (formalGroup W).toPowerSeries) * h₂

/-- The invariant differential of `Ê` has linear coefficient `a₁`. -/
@[simp]
theorem coeff_one_invariantDifferential_formalGroup :
    PowerSeries.coeff 1 (formalGroup W).invariantDifferential = W.a₁ := by
  have h := congrArg (PowerSeries.coeff 1)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] at h
  linear_combination h

/-- The invariant differential of `Ê` has quadratic coefficient `a₁² + a₂`. -/
@[simp]
theorem coeff_two_invariantDifferential_formalGroup :
    PowerSeries.coeff 2 (formalGroup W).invariantDifferential = W.a₁ ^ 2 + W.a₂ := by
  have h := congrArg (PowerSeries.coeff 2)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  simp [PowerSeries.coeff_mul, Finset.Nat.antidiagonal_succ] at h
  linear_combination h

/-! ### The formal logarithm -/

section Logarithm

variable [Algebra ℚ R]

/-- **The formal logarithm of `Ê` is the integral of `ω`**: over a `ℚ`-algebra its derivative times
the denominator `1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²` is `1` (Silverman IV.5). -/
theorem derivative_log_formalGroup_mul_formalInvariantDifferentialDenom :
    PowerSeries.derivative (formalGroup W).log * W.formalInvariantDifferentialDenom = 1 := by
  rw [FormalGroup.derivative_log]
  exact W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom

/-- The quadratic coefficient of the formal logarithm of `Ê` is `a₁ / 2`. -/
@[simp]
theorem coeff_two_log_formalGroup :
    PowerSeries.coeff 2 (formalGroup W).log = (2 : ℚ)⁻¹ • W.a₁ := by
  rw [FormalGroup.coeff_log]
  simp

/-- The cubic coefficient of the formal logarithm of `Ê` is `(a₁² + a₂) / 3`. -/
@[simp]
theorem coeff_three_log_formalGroup :
    PowerSeries.coeff 3 (formalGroup W).log = (3 : ℚ)⁻¹ • (W.a₁ ^ 2 + W.a₂) := by
  rw [FormalGroup.coeff_log]
  simp

end Logarithm

end WeierstrassCurve
