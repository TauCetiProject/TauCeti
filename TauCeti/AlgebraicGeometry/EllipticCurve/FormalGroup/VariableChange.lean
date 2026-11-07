/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange
public import TauCeti.RingTheory.FormalGroup.Height.Ideal
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import TauCeti.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.CharP.Algebra
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable

/-!
# Weierstrass changes of variables on the formal parameter

In the chart `z = -x/y`, `w = -1/y`, an admissible change `C = (u,r,s,t)`
from `C • W` to `W` induces the parameter transition

`z ↦ (u²z + r w(z)) / (u³ - su²z - t w(z))`.

The denominator has unit constant coefficient `u³`, so this formula defines an
invertible formal coordinate over every commutative ring, including singular
Weierstrass equations. Its linear coefficient is `u⁻¹`. Substituting the transition
into the old `w`-expansion gives `w(z)` divided by the same denominator. Thus the
transition identifies the two formal neighbourhoods, not just their tangent spaces.
These are the coordinate transitions used to descend the formal neighbourhood of
the marked identity in families of Weierstrass equations.

The transition is also compatible with the formal group laws: it is an isomorphism from the
formal group law of `C • W` to that of `W`, that is
`C.formalCoordinate W • formalGroup (C • W) = formalGroup W`
(`WeierstrassCurve.VariableChange.formalCoordinate_smul_formalGroup`), over every commutative
ring. So the formal group law of a Weierstrass equation descends along changes of variables, and
its height and height ideals do not depend on the chosen equation.

Writing `G` for the denominator `1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²` of the invariant
differential `ω = dz / G(z)` and `φ` for the transition, the denominators satisfy
`u G_(C • W)(z) φ'(z) = G_W(φ(z))`: the pullback of the invariant differential of `W` along the
transition is `u⁻¹` times that of `C • W`, the formal form of `φ_C^* ω_W = u⁻¹ ω_(C • W)`. Over a
`ℚ`-algebra, correspondingly, `log_W(φ(z)) = u⁻¹ log_(C • W)(z)`.

## Main results

All in the namespace `WeierstrassCurve.VariableChange`:

* `formalInvariantDifferentialDenom_mul_derivative_formalCoordinate`: `u G_(C • W) φ' = G_W ∘ φ`
  for the denominators of the invariant differentials.
* `subst_invariantDifferential_formalGroup_mul_derivative_formalCoordinate`: the invariant
  differential of `W` pulls back to `u⁻¹` times that of `C • W`.
* `subst_formalCoordinate_log_formalGroup`: over a `ℚ`-algebra, `log_W ∘ φ = u⁻¹ log_(C • W)`.
* `formalCoordinate_smul_formalGroup`: the transition carries the formal group law of `C • W` to
  that of `W`.
* `formalGroup_variableChange`: the formal group law of `C • W` is that of `W` transported along
  the inverse transition.
* `heightIdeal_formalGroup_variableChange` and `height_formalGroup_variableChange`: the height
  ideals, and over a field the height, are unchanged by a change of variables.

## Implementation notes

The identity `u G_(C • W) φ' = G_W ∘ φ` is a polynomial identity in `z`, `w(z)` and `w'(z)`
modulo the `w`-equation and its derivative. Over a `ℚ`-algebra the logarithms are the integrals
of the invariant differentials, so `φ` is the composite of the homomorphism `u⁻¹ log_(C • W)` to
the additive formal group with the exponential of `W`. The universal Weierstrass curve and the
universal change of variables are defined over the domain `ℤ[a₁, a₂, a₃, a₄, a₆][u, u⁻¹, r, s, t]`
of characteristic zero, which embeds in its fraction field, a `ℚ`-algebra; every other pair is a
specialization of this one.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.1, IV.4 and IV.5.
-/

public section

noncomputable section

namespace WeierstrassCurve.VariableChange

open PowerSeries Matrix

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The denominator `u³ - su²z - t w(z)` of the formal parameter transition
from `C • W` to `W`; here `w` is the expansion of `C • W`. -/
def formalDenom (C : VariableChange R) (W : WeierstrassCurve R) : PowerSeries R :=
  PowerSeries.C (C.u : R) ^ 3 - PowerSeries.C (C.s * (C.u : R) ^ 2) * X -
    PowerSeries.C C.t * formalW (C • W)

/-- The explicit denominator of the formal parameter transition. -/
theorem formalDenom_def (C : VariableChange R) (W : WeierstrassCurve R) :
    C.formalDenom W = PowerSeries.C (C.u : R) ^ 3 -
      PowerSeries.C (C.s * (C.u : R) ^ 2) * X - PowerSeries.C C.t * formalW (C • W) :=
  (rfl)

@[simp]
theorem constantCoeff_formalDenom (C : VariableChange R) (W : WeierstrassCurve R) :
    constantCoeff (C.formalDenom W) = (C.u : R) ^ 3 := by
  simp [formalDenom_def]

/-- The denominator of the transition is a unit. -/
theorem isUnit_formalDenom (C : VariableChange R) (W : WeierstrassCurve R) :
    IsUnit (C.formalDenom W) :=
  isUnit_iff_constantCoeff.mpr (by simp)

/-- The inverse denominator used in the formal parameter transition. -/
private def inverseDenom (C : VariableChange R) (W : WeierstrassCurve R) : PowerSeries R :=
  invOfUnit (C.formalDenom W) (C.u ^ 3)

private theorem inverseDenom_def (C : VariableChange R) (W : WeierstrassCurve R) :
    C.inverseDenom W = invOfUnit (C.formalDenom W) (C.u ^ 3) := (rfl)

private theorem formalDenom_mul_inverseDenom (C : VariableChange R)
    (W : WeierstrassCurve R) : C.formalDenom W * C.inverseDenom W = 1 :=
  mul_invOfUnit _ _ (C.constantCoeff_formalDenom W)

private theorem constantCoeff_inverseDenom (C : VariableChange R)
    (W : WeierstrassCurve R) :
    constantCoeff (C.inverseDenom W) = ↑C.u⁻¹ ^ 3 := by
  simp [inverseDenom_def, constantCoeff_invOfUnit]

private theorem coeff_one_formalNum_mul_inverseDenom (C : VariableChange R)
    (W : WeierstrassCurve R) :
    coeff 1 ((PowerSeries.C (C.u : R) ^ 2 * X +
      PowerSeries.C C.r * formalW (C • W)) * C.inverseDenom W) = (↑(C.u⁻¹) : R) := by
  simp [coeff_mul, Finset.Nat.antidiagonal_succ, constantCoeff_inverseDenom,
    ← map_pow]
  simp only [← Units.val_pow_eq_pow_val, ← Units.val_mul]
  congr 1
  group

/-- The formal coordinate from the parameter of `C • W` to that of `W`, induced
by `(x,y) ↦ (u²x+r, u³y+su²x+t)`. It is not in general strict. -/
def formalCoordinate (C : VariableChange R) (W : WeierstrassCurve R) :
    TauCeti.FormalCoordinate R where
  toPowerSeries :=
    (PowerSeries.C (C.u : R) ^ 2 * X + PowerSeries.C C.r * formalW (C • W)) *
      C.inverseDenom W
  constantCoeff_toPowerSeries := by simp
  isUnit_coeff_one := by
    rw [coeff_one_formalNum_mul_inverseDenom]
    exact (C.u⁻¹).isUnit

/-- The series of the formal coordinate induced by a Weierstrass change. -/
theorem formalCoordinate_toPowerSeries (C : VariableChange R) (W : WeierstrassCurve R) :
    (C.formalCoordinate W).toPowerSeries =
      (PowerSeries.C (C.u : R) ^ 2 * X + PowerSeries.C C.r * formalW (C • W)) *
        invOfUnit (C.formalDenom W) (C.u ^ 3) := by
  rw [← inverseDenom_def]
  rfl

/-- The induced parameter has linear coefficient `u⁻¹`, in the direction from
`C • W` to `W`. -/
@[simp]
theorem coeff_one_formalCoordinate (C : VariableChange R) (W : WeierstrassCurve R) :
    coeff 1 (C.formalCoordinate W).toPowerSeries = ↑C.u⁻¹ :=
  coeff_one_formalNum_mul_inverseDenom C W

/-- The unit character of the formal coordinate transition is `u⁻¹`. -/
@[simp]
theorem linearCoeff_formalCoordinate (C : VariableChange R) (W : WeierstrassCurve R) :
    TauCeti.FormalCoordinate.linearCoeff (C.formalCoordinate W) = C.u⁻¹ := by
  apply Units.ext
  simp [TauCeti.FormalCoordinate.val_linearCoeff]

/-- The identity change induces the identity formal coordinate. -/
@[simp]
theorem formalCoordinate_one (W : WeierstrassCurve R) :
    (1 : VariableChange R).formalCoordinate W = 1 := by
  have h : invOfUnit (1 : PowerSeries R) 1 = 1 := by
    simpa using mul_invOfUnit (1 : PowerSeries R) 1 (by simp)
  apply TauCeti.FormalCoordinate.ext
  simp [formalCoordinate_toPowerSeries, formalDenom_def, one_def, h]

/-- Substitution into the old `w`-expansion gives the new `w`-expansion divided
by `u³ - su²z - t w(z)`. This identifies the formal neighbourhoods in the two
Weierstrass charts. -/
theorem subst_formalCoordinate_formalW (C : VariableChange R) (W : WeierstrassCurve R) :
    subst (C.formalCoordinate W).toPowerSeries (formalW W) =
      formalW (C • W) * invOfUnit (C.formalDenom W) (C.u ^ 3) := by
  let V := (C • W).map (PowerSeries.C : R →+* PowerSeries R)
  let D := C.formalDenom W
  let d := C.inverseDenom W
  let N := PowerSeries.C (C.u : R) ^ 2 * X + PowerSeries.C C.r * formalW (C • W)
  have hDd : D * d = 1 := C.formalDenom_mul_inverseDenom W
  have hpoint : V.toProjective.Equation ![X, -1, formalW (C • W)] :=
    equation_formalW_point (C • W)
  have himage := (Projective.equation_variableChange (W.map PowerSeries.C)
    (C.map PowerSeries.C) _).mp (by simpa [V, map_variableChange] using hpoint)
  have hnormalized := (Projective.equation_smul (W' := (W.map PowerSeries.C).toProjective)
    ((C.map PowerSeries.C).toMatrix *ᵥ ![X, -1, formalW (C • W)])
    (IsUnit.of_mul_eq_one D (mul_comm D d ▸ hDd))).mpr himage
  have hcoord : d • ((C.map PowerSeries.C).toMatrix *ᵥ ![X, -1, formalW (C • W)]) =
      ![N * d, -1, formalW (C • W) * d] := by
    funext i
    simp only [D, formalDenom_def, map_mul, map_pow] at hDd
    fin_cases i <;> simp [toMatrix_def, N, smul_eq_mul]
    · ring
    · linear_combination -hDd
    · ring
  rw [hcoord] at hnormalized
  symm
  refine W.eq_subst_formalW_of_wEquation
    (C.formalCoordinate W).constantCoeff_toPowerSeries (by simp) ?_
  simpa only [formalCoordinate_toPowerSeries, inverseDenom_def, N, d] using
    (W.toProjective.equation_neg_one_iff_wEquation (N * d) (formalW (C • W) * d)).mp
      hnormalized

/-- The transition denominators multiply after substitution. This is the
normalization factor for composing maps in the projective identity chart. -/
theorem subst_formalCoordinate_formalDenom_mul (C C' : VariableChange R)
    (W : WeierstrassCurve R) :
    subst (C.formalCoordinate (C' • W)).toPowerSeries (C'.formalDenom W) *
      C.formalDenom (C' • W) = (C * C').formalDenom W := by
  have hp := (C.formalCoordinate (C' • W)).hasSubst
  have hw := C.subst_formalCoordinate_formalW (C' • W)
  have hd := C.formalDenom_mul_inverseDenom (C' • W)
  simp only [formalDenom_def, ← PowerSeries.coe_substAlgHom hp,
    map_sub, map_mul, map_pow, PowerSeries.substAlgHom_X, PowerSeries.subst_C,
    ← PowerSeries.C_apply, PowerSeries.coe_substAlgHom, hw]
  simp only [formalCoordinate_toPowerSeries, formalDenom_def, mul_smul]
  simp only [mul_def, Units.val_mul, map_add, map_mul, map_pow]
  simp only [inverseDenom_def, formalDenom_def, map_mul, map_pow] at hd
  grind

/-- Formal parameter transitions reverse the native product, just like the
maps of Weierstrass curves: first apply `C` to go to `C' • W`, then `C'` to go
to `W`. This is the cocycle identity for the formal neighbourhood charts. -/
theorem formalCoordinate_mul (C C' : VariableChange R) (W : WeierstrassCurve R) :
    (C * C').formalCoordinate W = C'.formalCoordinate W * C.formalCoordinate (C' • W) := by
  let P := (C.formalCoordinate (C' • W)).toPowerSeries
  let D := C.formalDenom (C' • W)
  let d := C.inverseDenom (C' • W)
  let E := C'.formalDenom W
  let e := C'.inverseDenom W
  let H := (C * C').formalDenom W
  let N := PowerSeries.C ((C * C').u : R) ^ 2 * X +
    PowerSeries.C (C * C').r * formalW ((C * C') • W)
  have hp : HasSubst P := (C.formalCoordinate (C' • W)).hasSubst
  have hd : D * d = 1 := C.formalDenom_mul_inverseDenom (C' • W)
  have he : subst P E * subst P e = 1 := by
    rw [← PowerSeries.coe_substAlgHom hp, ← map_mul, C'.formalDenom_mul_inverseDenom W,
      map_one]
  have hw : subst P (formalW (C' • W)) = formalW ((C * C') • W) * d := by
    simpa only [P, d, inverseDenom_def, mul_smul] using C.subst_formalCoordinate_formalW (C' • W)
  have hE : subst P E * D = H := subst_formalCoordinate_formalDenom_mul C C' W
  have hN : subst P (PowerSeries.C (C'.u : R) ^ 2 * X +
      PowerSeries.C C'.r * formalW (C' • W)) = N * d := by
    simp only [← PowerSeries.coe_substAlgHom hp, map_add, map_mul, map_pow,
      PowerSeries.substAlgHom_X, PowerSeries.subst_C, ← PowerSeries.C_apply,
      PowerSeries.coe_substAlgHom, hw]
    simp only [P, formalCoordinate_toPowerSeries, N, mul_smul]
    simp only [d, inverseDenom_def, mul_def, Units.val_mul, map_add, map_mul, map_pow]
    ring
  have hQ : subst P (C'.formalCoordinate W).toPowerSeries = N * d * subst P e := by
    simp only [formalCoordinate_toPowerSeries, PowerSeries.subst_mul hp, hN,
      e, inverseDenom_def]
  have hH : ((C * C').formalCoordinate W).toPowerSeries * H = N := by
    have h := (C * C').formalDenom_mul_inverseDenom W
    simp only [formalCoordinate_toPowerSeries, N, H, inverseDenom_def] at *
    linear_combination N * h
  apply TauCeti.FormalCoordinate.ext
  apply ((C * C').isUnit_formalDenom W).mul_right_cancel
  rw [hH, TauCeti.FormalCoordinate.toPowerSeries_mul, hQ]
  calc
    N = N * (D * d) * (subst P E * subst P e) := by rw [hd, he]; ring
    _ = N * d * subst P e * (subst P E * D) := by ring
    _ = N * d * subst P e * H := by rw [hE]

/-- The inverse Weierstrass change induces the inverse formal coordinate. -/
@[simp]
theorem formalCoordinate_inv (C : VariableChange R) (W : WeierstrassCurve R) :
    C⁻¹.formalCoordinate (C • W) = (C.formalCoordinate W)⁻¹ := by
  apply mul_left_cancel (a := C.formalCoordinate W)
  simpa using (formalCoordinate_mul C⁻¹ C W).symm

/-- The transition denominator commutes with arbitrary base change. -/
@[simp]
theorem map_formalDenom (C : VariableChange R) (W : WeierstrassCurve R) (f : R →+* S) :
    (C.map f).formalDenom (W.map f) = PowerSeries.map f (C.formalDenom W) := by
  simp [formalDenom_def, map_variableChange, map_formalW]

/-- The formal coordinate transition commutes with arbitrary base change,
including noninjective coefficient maps. -/
@[simp]
theorem map_formalCoordinate (C : VariableChange R) (W : WeierstrassCurve R) (f : R →+* S) :
    (C.map f).formalCoordinate (W.map f) = (C.formalCoordinate W).map f := by
  apply TauCeti.FormalCoordinate.ext
  simp [formalCoordinate_toPowerSeries, TauCeti.FormalCoordinate.toPowerSeries_map,
    map_variableChange, map_formalW]

/-! ### Compatibility with the formal group laws -/

variable (C : VariableChange R) (W : WeierstrassCurve R)

/-- The polynomial identity behind the transformation of the invariant differential. Here `z` is
the parameter of `C • W`, `w` and `w'` are its `w`-expansion and the derivative of that, `G` is its
denominator `1 - A₁z - ⋯`, and `aᵢ` are the coefficients of `W`. With
`N = u²z + rw` and `D = u³ - su²z - tw`, so that the transition is `φ = N / D`, the left side is
`u G (N' D - N D')` and the right side is `D²` times the denominator of `W` at `(N / D, w / D)`. It
holds modulo the `w`-equation and its derivative. -/
private theorem mul_derivative_eq_of_wEquation {T : Type*} [CommRing T]
    {A₁ A₂ A₃ A₄ A₆ a₁ a₂ a₃ a₄ a₆ u r s t z w w' G : T}
    (h₁ : u * A₁ = a₁ + 2 * s) (h₂ : u ^ 2 * A₂ = a₂ - s * a₁ + 3 * r - s ^ 2)
    (h₃ : u ^ 3 * A₃ = a₃ + r * a₁ + 2 * t)
    (h₄ : u ^ 4 * A₄ = a₄ - s * a₃ + 2 * r * a₂ - (t + r * s) * a₁ + 3 * r ^ 2 - 2 * s * t)
    (h₆ : u ^ 6 * A₆ = a₆ + r * a₄ + r ^ 2 * a₂ + r ^ 3 - t * a₃ - t ^ 2 - r * t * a₁)
    (hG : G = 1 - A₁ * z - A₂ * z ^ 2 - 2 * A₃ * w - 2 * A₄ * (z * w) - 3 * A₆ * w ^ 2)
    (hw : w = z ^ 3 + A₁ * z * w + A₂ * z ^ 2 * w + A₃ * w ^ 2 + A₄ * z * w ^ 2 + A₆ * w ^ 3)
    (hw' : w' * G = 3 * z ^ 2 + A₁ * w + 2 * A₂ * z * w + A₄ * w ^ 2) :
    u * G * ((u ^ 2 + r * w') * (u ^ 3 - s * u ^ 2 * z - t * w) -
        (u ^ 2 * z + r * w) * (-(s * u ^ 2) - t * w')) =
      (u ^ 3 - s * u ^ 2 * z - t * w) ^ 2 -
        a₁ * (u ^ 2 * z + r * w) * (u ^ 3 - s * u ^ 2 * z - t * w) -
        a₂ * (u ^ 2 * z + r * w) ^ 2 - 2 * a₃ * w * (u ^ 3 - s * u ^ 2 * z - t * w) -
        2 * a₄ * (u ^ 2 * z + r * w) * w - 3 * a₆ * w ^ 2 := by
  -- solve the coefficient relations for the `aᵢ` and eliminate them
  obtain rfl : a₆ = u ^ 6 * A₆ - r * a₄ - r ^ 2 * a₂ - r ^ 3 + t * a₃ + t ^ 2 + r * t * a₁ := by
    linear_combination -h₆
  obtain rfl :
      a₄ = u ^ 4 * A₄ + s * a₃ - 2 * r * a₂ + (t + r * s) * a₁ - 3 * r ^ 2 + 2 * s * t := by
    linear_combination -h₄
  obtain rfl : a₃ = u ^ 3 * A₃ - r * a₁ - 2 * t := by linear_combination -h₃
  obtain rfl : a₂ = u ^ 2 * A₂ + s * a₁ - 3 * r + s ^ 2 := by linear_combination -h₂
  obtain rfl : a₁ = u * A₁ - 2 * s := by linear_combination -h₁
  subst hG
  linear_combination (u * (r * (u ^ 3 - s * u ^ 2 * z - t * w) + (u ^ 2 * z + r * w) * t)) * hw' +
    3 * u ^ 3 * (r * s - t) * hw

/-- **The denominators of the invariant differentials under a change of variables.** For the
transition `φ` from the parameter of `C • W` to that of `W`, `u G_(C • W)(z) φ'(z) = G_W(φ(z))`,
where `G` is the denominator `1 - a₁z - a₂z² - 2a₃w - 2a₄zw - 3a₆w²` of the invariant differential
`dz / G(z)`. This holds over every commutative ring. -/
theorem formalInvariantDifferentialDenom_mul_derivative_formalCoordinate :
    PowerSeries.C (C.u : R) * ((C • W).formalInvariantDifferentialDenom *
        derivative (C.formalCoordinate W).toPowerSeries) =
      subst (C.formalCoordinate W).toPowerSeries W.formalInvariantDifferentialDenom := by
  -- write both sides in `z`, `w = w_(C • W)(z)`, `w'` and `d = D⁻¹`, where `φ = N d`
  have hsubst := subst_formalInvariantDifferentialDenom W
    (HasSubst.of_constantCoeff_zero' (C.formalCoordinate W).constantCoeff_toPowerSeries)
  rw [subst_formalCoordinate_formalW] at hsubst
  rw [hsubst, formalCoordinate_toPowerSeries]
  have hG := (C • W).formalInvariantDifferentialDenom_def
  have hw := (C • W).formalW_wEquation
  rw [wEquationRHS_def] at hw
  have hw' := (C • W).derivative_formalW_mul_formalInvariantDifferentialDenom
  have hDd : C.formalDenom W * invOfUnit (C.formalDenom W) (C.u ^ 3) = 1 :=
    mul_invOfUnit _ _ (C.constantCoeff_formalDenom W)
  have hD := C.formalDenom_def W
  simp only [smul_eq_C_mul, map_mul, map_pow, map_ofNat, algebraMap_eq] at hG hw hw' hD ⊢
  set w := formalW (C • W)
  set D := C.formalDenom W
  set d := invOfUnit D (C.u ^ 3)
  set N : PowerSeries R := PowerSeries.C (C.u : R) ^ 2 * X + PowerSeries.C C.r * w with hN
  -- the derivative of `d = D⁻¹` is `-D' d²`
  have hd' : derivative d = -derivative D * d ^ 2 := by
    have h := congrArg derivative hDd
    rw [Derivation.leibniz, Derivation.map_one_eq_zero, smul_eq_mul, smul_eq_mul] at h
    linear_combination d * h - derivative d * hDd
  have hφ' : derivative (N * d) =
      (PowerSeries.C (C.u : R) ^ 2 + PowerSeries.C C.r * derivative w) * d -
        N * (-(PowerSeries.C C.s * PowerSeries.C (C.u : R) ^ 2) -
          PowerSeries.C C.t * derivative w) * d ^ 2 := by
    rw [Derivation.leibniz, hd', smul_eq_mul, smul_eq_mul, hD]
    simp only [N, map_add, map_sub, Derivation.leibniz, Derivation.leibniz_pow,
      derivative_C, derivative_X, smul_eq_mul]
    ring
  rw [hφ']
  -- the identity cleared of `d`, then multiplied by `d²` using `D d = 1`
  have hQ := mul_derivative_eq_of_wEquation (z := (X : PowerSeries R)) (w := w) (w' := derivative w)
    (u := PowerSeries.C (C.u : R)) (r := PowerSeries.C C.r) (s := PowerSeries.C C.s)
    (t := PowerSeries.C C.t) (a₁ := PowerSeries.C W.a₁) (a₂ := PowerSeries.C W.a₂)
    (a₃ := PowerSeries.C W.a₃) (a₄ := PowerSeries.C W.a₄) (a₆ := PowerSeries.C W.a₆)
    (by rw [← map_mul, variableChange_a₁, ← mul_assoc, Units.mul_inv, one_mul]
        simp only [map_add, map_mul, map_ofNat])
    (by rw [← map_pow, ← map_mul, variableChange_a₂, ← mul_assoc, ← mul_pow, Units.mul_inv,
          one_pow, one_mul]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat])
    (by rw [← map_pow, ← map_mul, variableChange_a₃, ← mul_assoc, ← mul_pow, Units.mul_inv,
          one_pow, one_mul]
        simp only [map_add, map_mul, map_ofNat])
    (by rw [← map_pow, ← map_mul, variableChange_a₄, ← mul_assoc, ← mul_pow, Units.mul_inv,
          one_pow, one_mul]
        simp only [map_add, map_sub, map_mul, map_pow, map_ofNat])
    (by rw [← map_pow, ← map_mul, variableChange_a₆, ← mul_assoc, ← mul_pow, Units.mul_inv,
          one_pow, one_mul]
        simp only [map_add, map_sub, map_mul, map_pow])
    hG (by linear_combination hw) (by linear_combination hw')
  rw [← hD, ← hN] at hQ
  linear_combination d ^ 2 * hQ -
    (PowerSeries.C (C.u : R) * (C • W).formalInvariantDifferentialDenom *
      (PowerSeries.C (C.u : R) ^ 2 + PowerSeries.C C.r * derivative w) * d - 1 - D * d +
      PowerSeries.C W.a₁ * N * d + 2 * PowerSeries.C W.a₃ * w * d) * hDd

/-- **The invariant differential under a change of variables**: the pullback along the
transition `φ` of the invariant differential of the formal group of `W` is `u⁻¹` times that of
`C • W`, `P_W(φ(z)) φ'(z) = u⁻¹ P_(C • W)(z)`. This is the formal form of
`φ_C^* ω_W = u⁻¹ ω_(C • W)` (Silverman III.1, Table 3.1), over every commutative ring. -/
theorem subst_invariantDifferential_formalGroup_mul_derivative_formalCoordinate :
    subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
        derivative (C.formalCoordinate W).toPowerSeries =
      PowerSeries.C (↑C.u⁻¹ : R) * (formalGroup (C • W)).invariantDifferential := by
  have hφ := HasSubst.of_constantCoeff_zero' (C.formalCoordinate W).constantCoeff_toPowerSeries
  have hP := congrArg (subst (C.formalCoordinate W).toPowerSeries)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  rw [← coe_substAlgHom hφ, map_mul, map_one, coe_substAlgHom] at hP
  have hu : PowerSeries.C (C.u : R) * PowerSeries.C (↑C.u⁻¹ : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  linear_combination
    (-(subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
        derivative (C.formalCoordinate W).toPowerSeries *
        (formalGroup (C • W)).invariantDifferential * (C • W).formalInvariantDifferentialDenom)) *
      hu -
    subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
        derivative (C.formalCoordinate W).toPowerSeries *
      (C • W).invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom +
    PowerSeries.C (↑C.u⁻¹ : R) * (formalGroup (C • W)).invariantDifferential *
        subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
      C.formalInvariantDifferentialDenom_mul_derivative_formalCoordinate W +
    PowerSeries.C (↑C.u⁻¹ : R) * (formalGroup (C • W)).invariantDifferential * hP

section Rat

variable [Algebra ℚ R]

/-- **The logarithm under a change of variables**: over a `ℚ`-algebra, the logarithm of the
formal group of `W` composed with the transition `φ` is `u⁻¹` times the logarithm of the formal
group of `C • W`. -/
theorem subst_formalCoordinate_log_formalGroup :
    subst (C.formalCoordinate W).toPowerSeries (formalGroup W).log =
      (↑C.u⁻¹ : R) • (formalGroup (C • W)).log := by
  have : HasUniqueDiv R := .of_isTorsionFree ℚ R
  have hφ := HasSubst.of_constantCoeff_zero' (C.formalCoordinate W).constantCoeff_toPowerSeries
  refine derivative.ext ?_ ?_
  · rw [derivative_subst hφ, FormalGroup.derivative_log, Derivation.map_smul,
      FormalGroup.derivative_log, smul_eq_C_mul]
    exact C.subst_invariantDifferential_formalGroup_mul_derivative_formalCoordinate W
  · exact (constantCoeff_subst_eq_zero (C.formalCoordinate W).constantCoeff_toPowerSeries _
      (formalGroup W).constantCoeff_log).trans (by simp)

/-- Over a `ℚ`-algebra the transition `φ = exp_W ∘ (u⁻¹ log_(C • W))` is a homomorphism from the
formal group law of `C • W` to that of `W`. -/
private theorem formalCoordinate_smul_formalGroup_of_rat :
    C.formalCoordinate W • formalGroup (C • W) = formalGroup W := by
  have hφ := HasSubst.of_constantCoeff_zero' (C.formalCoordinate W).constantCoeff_toPowerSeries
  let f : TauCeti.FormalGroupHom (formalGroup (C • W)) FormalGroup.𝔾ₐ :=
    { toPowerSeries := (↑C.u⁻¹ : R) • (formalGroup (C • W)).log
      zero_constantCoeff := by simp
      hom := (TauCeti.FormalGroupHom.hom_additive_iff (by simp)).mpr
        ((formalGroup (C • W)).subst_toPowerSeries_eq_add_iff.mpr ⟨_, rfl⟩) }
  refine ((formalGroup W).expHom.comp f).smul_eq ?_
  simp only [f, TauCeti.FormalGroupHom.comp_toPowerSeries, FormalGroup.expHom_toPowerSeries]
  rw [← C.subst_formalCoordinate_log_formalGroup W, FormalGroup.subst_subst_log_exp _ hφ]

end Rat

/-! ### Every ring -/

/-- Transporting the formal group law of `C • W` along the transition commutes with base change. -/
private theorem map_formalCoordinate_smul_formalGroup (f : R →+* S) :
    (C.formalCoordinate W • formalGroup (C • W)).map f =
      (C.map f).formalCoordinate (W.map f) • formalGroup (C.map f • W.map f) := by
  rw [FormalGroup.map_smul, map_variableChange, map_formalGroup, map_formalCoordinate]

open TauCeti.WeierstrassChange in
/-- The ring `ℤ[a₁, a₂, a₃, a₄, a₆][u, u⁻¹, r, s, t]` of the universal Weierstrass curve together
with the universal change of variables. -/
private abbrev UnivRing := ChangeRing (MvPolynomial Coeff ℤ)

/-- The powers of `u` are non-zero-divisors of `ℤ[a₁, a₂, a₃, a₄, a₆][u, r, s, t]`. -/
private theorem powers_le_nonZeroDivisors :
    Submonoid.powers (MvPolynomial.X 0 : MvPolynomial (Fin 4) (MvPolynomial Coeff ℤ)) ≤
      nonZeroDivisors _ :=
  powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero 0)

private instance : IsDomain UnivRing :=
  IsLocalization.isDomain_localization powers_le_nonZeroDivisors

private instance : CharZero UnivRing :=
  charZero_of_injective_algebraMap (IsLocalization.injective _ powers_le_nonZeroDivisors)

open TauCeti.WeierstrassChange in
/-- **A change of variables is an isomorphism of formal groups.** The formal coordinate
transition of `C` is a homomorphism from the formal group law of `C • W` to that of `W`, over every
commutative ring and for every Weierstrass curve, singular or not. -/
theorem formalCoordinate_smul_formalGroup :
    C.formalCoordinate W • formalGroup (C • W) = formalGroup W := by
  let C₀ := ChangeRing.universalChange (MvPolynomial Coeff ℤ)
  let W₀ : WeierstrassCurve UnivRing :=
    Universal.curve.map (algebraMap (MvPolynomial Coeff ℤ) UnivRing)
  have h₀ : C₀.formalCoordinate W₀ • formalGroup (C₀ • W₀) = formalGroup W₀ := by
    let ι := algebraMap UnivRing (FractionRing UnivRing)
    have h := (map_formalCoordinate_smul_formalGroup C₀ W₀ ι).trans
      (formalCoordinate_smul_formalGroup_of_rat _ _)
    rw [map_formalGroup] at h
    refine FormalGroup.ext (MvPowerSeries.ext fun n ↦ IsFractionRing.injective UnivRing
      (FractionRing UnivRing) ?_)
    simpa only [FormalGroup.map_toPowerSeries, MvPowerSeries.coeff_map] using
      congrArg (fun F : FormalGroup _ ↦ MvPowerSeries.coeff n F.toPowerSeries) h
  let k := ChangeRing.lift (W.specialize, C)
  have hC : C₀.map k = C := ChangeRing.map_lift _
  have hW : W₀.map k = W := by
    rw [WeierstrassCurve.map_map, ChangeRing.lift_comp_algebraMap]
    exact WeierstrassCurve.map_specialize W
  have h := map_formalCoordinate_smul_formalGroup C₀ W₀ k
  rwa [h₀, hC, hW, ← map_formalGroup, hW, eq_comm] at h

/-- The formal group law of `C • W` is that of `W` transported along the inverse of the formal
coordinate transition. -/
theorem formalGroup_variableChange :
    formalGroup (C • W) = (C.formalCoordinate W)⁻¹ • formalGroup W := by
  rw [← C.formalCoordinate_smul_formalGroup W, inv_smul_smul]

/-- The height ideals of the formal group of a Weierstrass curve do not depend on the chosen
Weierstrass equation. -/
@[simp]
theorem heightIdeal_formalGroup_variableChange (p n : ℕ) :
    (formalGroup (C • W)).heightIdeal p n = (formalGroup W).heightIdeal p n := by
  conv_rhs => rw [← C.formalCoordinate_smul_formalGroup W]
  rw [FormalGroup.heightIdeal_smul]

/-- Over a field, the height of the formal group of a Weierstrass curve does not depend on the
chosen Weierstrass equation. -/
@[simp]
theorem height_formalGroup_variableChange {K : Type*} [Field K] (C : VariableChange K)
    (W : WeierstrassCurve K) (p : ℕ) :
    (formalGroup (C • W)).height p = (formalGroup W).height p := by
  conv_rhs => rw [← C.formalCoordinate_smul_formalGroup W]
  rw [FormalGroup.height_smul]

end WeierstrassCurve.VariableChange
