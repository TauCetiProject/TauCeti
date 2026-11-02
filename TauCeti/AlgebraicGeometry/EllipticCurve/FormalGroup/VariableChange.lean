/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import TauCeti.RingTheory.MvPowerSeries.Inverse

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
the marked identity in families of Weierstrass equations. Compatibility with the
formal group law is not asserted here.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1 and IV.1.
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

end WeierstrassCurve.VariableChange
