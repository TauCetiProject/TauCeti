/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.InvariantDifferential
public import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.WExpansion
public import TauCeti.AlgebraicGeometry.EllipticCurve.Projective.VariableChange
public import TauCeti.RingTheory.FormalGroup.CoordinateChange.Basic
public import TauCeti.RingTheory.PowerSeries.Coordinate.Basic
public import TauCeti.RingTheory.MvPowerSeries.Inverse
import Mathlib.Algebra.CharP.Algebra
import TauCeti.AlgebraicGeometry.EllipticCurve.FormalGroup.Add.Assoc
import TauCeti.AlgebraicGeometry.EllipticCurve.Universal
import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange.Representable
import TauCeti.RingTheory.Derivation.Localization
import TauCeti.RingTheory.FormalGroup.Logarithm.Naturality
import TauCeti.RingTheory.PowerSeries.Derivative

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

The transition also respects the invariant differential and the group law. The curve
morphism `(x,y) ↦ (u²x+r, u³y+su²x+t)` pulls back `ω = dx / (2y + a₁x + a₃)` on `W` to
`u⁻¹` times the invariant differential of `C • W`. In the formal parameter, with `ψ` the
transition, this reads `P_W(ψ(z)) ψ'(z) = u⁻¹ P_{C • W}(z)` for the normalised invariant
differentials `P` of the formal groups. Over a field, the corresponding statement on function
fields, for the inverse morphism, is
`TauCeti.Isogeny.pullbackDifferential_variableChangeIsogeny_invariantDifferential`;
here it is read in the formal neighbourhood of the identity, over every ring. Consequently
`ψ` is an isomorphism of formal group laws from `Ê_{C • W}` to `Ê_W`: `ψ • Ê_{C • W} = Ê_W`.
All statements hold over every commutative ring, including singular equations,
characteristics two and three and rings with nilpotents.

## Main results

* `WeierstrassCurve.VariableChange.formalCoordinate`: the transition `ψ`, with
  `formalCoordinate_mul` (the cocycle identity) and `map_formalCoordinate` (base change).
* `WeierstrassCurve.VariableChange.subst_formalCoordinate_formalInvariantDifferentialDenom`:
  `G_W(ψ(z)) = u ψ'(z) G_{C • W}(z)` for the denominators `G` of the invariant differentials.
* `WeierstrassCurve.VariableChange.subst_formalCoordinate_invariantDifferential_formalGroup`:
  `ψ*ω_W = u⁻¹ ω_{C • W}`.
* `WeierstrassCurve.VariableChange.formalGroup_smul` and
  `WeierstrassCurve.VariableChange.formalCoordinate_smul_formalGroup`: the formal group law of
  `C • W` is the transport of that of `W` along `ψ⁻¹`.

## Implementation notes

The differential identity is first proved over a domain in which `2 ≠ 0`, by comparing the two
expressions of `ω` at the points with parameters `ψ(z)` and `z` over the fraction field of
the series ring (`WeierstrassCurve.inv_mul_derivation_div_subst_formalW`). It is then carried
to every commutative ring by specialising the universal pair of a Weierstrass equation and a
change of variables over `ℤ[a₁, a₂, a₃, a₄, a₆][u, u⁻¹, r, s, t]`. The comparison of formal
group laws is the uniqueness of the logarithm over a `ℚ`-algebra, transported in the same way.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1, IV.1 and IV.4.
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

/-! ### Compatibility with the invariant differential and the formal group law -/

namespace WeierstrassCurve.VariableChange

open PowerSeries TauCeti.WeierstrassChange

variable {R : Type*} [CommRing R]

/-- The field identity behind the transformation of the invariant differential. Under
`x = U²x' + r` and `y = U³y' + sU²x' + t` with `UV = 1`, the expression `2y + a₁x + a₃` is
`U³(2y' + a₁'x' + a₃')`, where `a₁' = V(a₁ + 2s)` and `a₃' = V³(a₃ + ra₁ + 2t)`. So if `δ` is the
derivative of `x'` and `G₁⁻¹Ψ`, `G₂⁻¹` are the two expressions of the invariant differential,
then `G₁ = UΨG₂`. -/
private theorem eq_mul_mul_of_inv_mul_eq {F : Type*} [Field F]
    {δ x y G₁ G₂ Ψ U V a₁ a₃ r s t : F} (hU : U * V = 1) (hG₁ : G₁ ≠ 0) (hG₂ : G₂ ≠ 0)
    (e₁ : (2 * (U ^ 3 * y + s * U ^ 2 * x + t) + a₁ * (U ^ 2 * x + r) + a₃)⁻¹ * (U ^ 2 * δ) =
      G₁⁻¹ * Ψ)
    (e₂ : (2 * y + V * (a₁ + 2 * s) * x + V ^ 3 * (a₃ + r * a₁ + 2 * t))⁻¹ * δ = G₂⁻¹) :
    G₁ = U * Ψ * G₂ := by
  have hP : 2 * (U ^ 3 * y + s * U ^ 2 * x + t) + a₁ * (U ^ 2 * x + r) + a₃ =
      U ^ 3 * (2 * y + V * (a₁ + 2 * s) * x + V ^ 3 * (a₃ + r * a₁ + 2 * t)) := by
    linear_combination (-(U ^ 2 * x * (a₁ + 2 * s)) -
      (a₃ + r * a₁ + 2 * t) * (1 + U * V + U ^ 2 * V ^ 2)) * hU
  rw [hP] at e₁
  generalize 2 * y + V * (a₁ + 2 * s) * x + V ^ 3 * (a₃ + r * a₁ + 2 * t) = P at e₁ e₂
  have hP0 : P ≠ 0 := by
    rintro rfl
    exact hG₂ (inv_eq_zero.1 (by simpa using e₂.symm))
  have hU0 : U ≠ 0 := left_ne_zero_of_mul_eq_one hU
  field_simp at e₁ e₂
  have hδ : δ ≠ 0 := by
    rintro rfl
    exact hP0 (by simpa using e₂.symm)
  refine mul_left_cancel₀ hδ ?_
  linear_combination e₁ - U * Ψ * e₂

section Domain

variable [IsDomain R]

/- `R⟦X⟧` is `MvPowerSeries Unit R` by definition; the fraction field is taken of the latter
because `inv_mul_derivation_div_subst_formalW` is stated for multivariable series rings. -/
local notation "K" => FractionRing (MvPowerSeries Unit R)
local notation "ι" => algebraMap (MvPowerSeries Unit R) (FractionRing (MvPowerSeries Unit R))

/-- Over a domain in which `2 ≠ 0`, the transition transforms the denominator of the invariant
differential by `G_W(ψ(z)) = u ψ'(z) G_{C • W}(z)`. Both sides are read at the points with
parameters `ψ(z)` on `W` and `z` on `C • W`, which correspond under the curve morphism. -/
private theorem subst_formalCoordinate_formalInvariantDifferentialDenom_of_isDomain
    (h2 : (2 : R) ≠ 0) (C : VariableChange R) (W : WeierstrassCurve R) :
    subst (C.formalCoordinate W).toPowerSeries W.formalInvariantDifferentialDenom =
      PowerSeries.C (C.u : R) * d⁄dX (C.formalCoordinate W).toPowerSeries *
        (C • W).formalInvariantDifferentialDenom := by
  -- the derivative `d/dz`, extended to the fraction field `K` of the series ring
  let D : Derivation R K K :=
    Derivation.extendOfIsLocalization (nonZeroDivisors (MvPowerSeries Unit R))
      ((Algebra.linearMap (MvPowerSeries Unit R) K).compDer (derivative (R := R)))
  have hD (a : R⟦X⟧) : D (ι a) = ι (d⁄dX a) := by
    simp [D, Derivation.extendOfIsLocalization_algebraMap]
  have hDc (r : R) : D (algebraMap R K r) = 0 := D.map_algebraMap r
  have hC (c : R) : ι (PowerSeries.C c) = algebraMap R K c := by
    rw [← PowerSeries.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  have hinj := IsFractionRing.injective (MvPowerSeries Unit R) K
  have hψ : (C.formalCoordinate W).toPowerSeries ≠ 0 := fun h ↦
    (C.u⁻¹).ne_zero (by simpa [h] using (coeff_one_formalCoordinate C W).symm)
  -- `ω` at the point with parameter `ψ(z)` of `W` and at the point with parameter `z` of `C • W`
  have e₁ := W.inv_mul_derivation_div_subst_formalW h2 D
    (C.formalCoordinate W).constantCoeff_toPowerSeries hψ
  have e₂ := (C • W).inv_mul_derivation_div_subst_formalW h2 D constantCoeff_X X_ne_zero
  rw [X_subst, X_subst, hD, derivative_X, map_one, mul_one] at e₂
  rw [hD] at e₁
  -- the coordinates `x = u²x' + r` and `y = u³y' + su²x' + t` of the first point in `K`
  have hDen : ι (C.formalDenom W) = algebraMap R K (C.u : R) ^ 3 -
      algebraMap R K C.s * algebraMap R K (C.u : R) ^ 2 * ι X -
      algebraMap R K C.t * ι (formalW (C • W)) := by
    rw [formalDenom_def]
    simp only [map_sub, map_mul, map_pow, hC]
  have hDe := congrArg ι (mul_invOfUnit (C.formalDenom W) (C.u ^ 3) (by simp))
  rw [map_mul, map_one, hDen] at hDe
  have ha0 : ι (formalW (C • W)) ≠ 0 := by
    simpa [X_subst] using
      algebraMap_subst_formalW_ne_zero (C • W) (σ := Unit) (KK := K) constantCoeff_X X_ne_zero
  have he0 := right_ne_zero_of_mul_eq_one hDe
  have hx : ι (C.formalCoordinate W).toPowerSeries /
      ι (subst (C.formalCoordinate W).toPowerSeries (formalW W)) =
      algebraMap R K (C.u : R) ^ 2 * (ι X / ι (formalW (C • W))) + algebraMap R K C.r := by
    rw [subst_formalCoordinate_formalW, formalCoordinate_toPowerSeries]
    simp only [map_mul, map_add, map_pow, hC]
    field_simp
  have hy : -1 / ι (subst (C.formalCoordinate W).toPowerSeries (formalW W)) =
      algebraMap R K (C.u : R) ^ 3 * (-1 / ι (formalW (C • W))) +
        algebraMap R K C.s * algebraMap R K (C.u : R) ^ 2 * (ι X / ι (formalW (C • W))) +
        algebraMap R K C.t := by
    rw [subst_formalCoordinate_formalW, map_mul]
    field_simp
    linear_combination hDe
  rw [hx, hy] at e₁
  simp only [Affine.evalEval_polynomialY, WeierstrassCurve.baseChange, map_a₁, map_a₃,
    variableChange_a₁, variableChange_a₃, map_mul, map_add, map_pow, map_ofNat,
    Derivation.leibniz, Derivation.leibniz_pow, hDc, mul_zero, smul_zero, add_zero,
    smul_eq_mul] at e₁ e₂
  have hG₁ : ι (subst (C.formalCoordinate W).toPowerSeries
      W.formalInvariantDifferentialDenom) ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 fun h ↦ by
      simpa [(C.formalCoordinate W).constantCoeff_subst_toPowerSeries] using
        congrArg constantCoeff h
  have hG₂ : ι (C • W).formalInvariantDifferentialDenom ≠ 0 :=
    (map_ne_zero_iff _ hinj).2 fun h ↦ by simpa using congrArg constantCoeff h
  have hU : algebraMap R K (C.u : R) * algebraMap R K ↑C.u⁻¹ = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  apply hinj
  rw [map_mul, map_mul, hC]
  exact eq_mul_mul_of_inv_mul_eq hU hG₁ hG₂ e₁ e₂

end Domain

/-- The ring `ℤ[a₁, a₂, a₃, a₄, a₆][u, u⁻¹, r, s, t]` of the universal pair of a Weierstrass
equation and a change of variables. -/
private abbrev UnivRing := ChangeRing (MvPolynomial Coeff ℤ)

private theorem injective_algebraMap_univRing :
    Function.Injective (algebraMap (MvPolynomial (Fin 4) (MvPolynomial Coeff ℤ)) UnivRing) :=
  IsLocalization.injective _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin 4)))

private theorem isDomain_univRing : IsDomain UnivRing :=
  IsLocalization.isDomain_localization
    (powers_le_nonZeroDivisors_of_noZeroDivisors (MvPolynomial.X_ne_zero (0 : Fin 4)))

private theorem charZero_univRing : CharZero UnivRing :=
  charZero_of_injective_algebraMap injective_algebraMap_univRing

/-- Every pair of a Weierstrass equation and a change of variables is a specialization of the
universal pair over `UnivRing`. -/
private theorem exists_map_universal (C : VariableChange R) (W : WeierstrassCurve R) :
    ∃ k : UnivRing →+* R,
      (WeierstrassCurve.map Universal.curve (algebraMap _ UnivRing)).map k = W ∧
        (ChangeRing.universalChange _).map k = C :=
  ⟨ChangeRing.lift (W.specialize, C), by rw [WeierstrassCurve.map_map]; simp,
    ChangeRing.map_lift _⟩

/-- **The transition transforms the denominator of the invariant differential** by
`G_W(ψ(z)) = u ψ'(z) G_{C • W}(z)`, where `G` is `formalInvariantDifferentialDenom` and `ψ` is
the formal parameter transition from `C • W` to `W`. -/
theorem subst_formalCoordinate_formalInvariantDifferentialDenom
    (C : VariableChange R) (W : WeierstrassCurve R) :
    subst (C.formalCoordinate W).toPowerSeries W.formalInvariantDifferentialDenom =
      PowerSeries.C (C.u : R) * d⁄dX (C.formalCoordinate W).toPowerSeries *
        (C • W).formalInvariantDifferentialDenom := by
  have := isDomain_univRing
  have := charZero_univRing
  obtain ⟨k, hW, hC⟩ := exists_map_universal C W
  have h := congrArg (PowerSeries.map k)
    (subst_formalCoordinate_formalInvariantDifferentialDenom_of_isDomain two_ne_zero
      (ChangeRing.universalChange _) (WeierstrassCurve.map Universal.curve (algebraMap _ _)))
  generalize WeierstrassCurve.map Universal.curve (algebraMap _ UnivRing) = W₀ at h hW
  generalize ChangeRing.universalChange (MvPolynomial Coeff ℤ) = C₀ at h hC
  have hs : PowerSeries.map k (subst (C₀.formalCoordinate W₀).toPowerSeries
      W₀.formalInvariantDifferentialDenom) =
      subst (PowerSeries.map k (C₀.formalCoordinate W₀).toPowerSeries)
        (PowerSeries.map k W₀.formalInvariantDifferentialDenom) :=
    PowerSeries.map_subst (TauCeti.FormalCoordinate.hasSubst _) _
  rw [← hW, ← hC, map_formalCoordinate, TauCeti.FormalCoordinate.toPowerSeries_map,
    map_variableChange, map_formalInvariantDifferentialDenom,
    map_formalInvariantDifferentialDenom, derivative_map, ← hs, h, map_mul, map_mul,
    PowerSeries.map_C]
  simp

/-- **The transition pulls back the invariant differential `ω_W` to `u⁻¹ ω_{C • W}`**: in the
formal parameter, `P_W(ψ(z)) ψ'(z) = u⁻¹ P_{C • W}(z)`, where `P` is the normalised invariant
differential of the formal group and `ψ` is the transition from `C • W` to `W`. -/
theorem subst_formalCoordinate_invariantDifferential_formalGroup
    (C : VariableChange R) (W : WeierstrassCurve R) :
    subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
        d⁄dX (C.formalCoordinate W).toPowerSeries =
      PowerSeries.C ((C.u⁻¹ : Rˣ) : R) * (formalGroup (C • W)).invariantDifferential := by
  have hψ := (C.formalCoordinate W).hasSubst
  have hs := congrArg (subst (C.formalCoordinate W).toPowerSeries)
    W.invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  rw [← coe_substAlgHom hψ, map_mul, map_one, coe_substAlgHom hψ,
    subst_formalCoordinate_formalInvariantDifferentialDenom] at hs
  have hP := (C • W).invariantDifferential_formalGroup_mul_formalInvariantDifferentialDenom
  have hu : PowerSeries.C (C.u : R) * PowerSeries.C ((C.u⁻¹ : Rˣ) : R) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  set Q := subst (C.formalCoordinate W).toPowerSeries (formalGroup W).invariantDifferential *
    d⁄dX (C.formalCoordinate W).toPowerSeries
  linear_combination (PowerSeries.C ((C.u⁻¹ : Rˣ) : R) *
      (formalGroup (C • W)).invariantDifferential) * hs -
    (Q * PowerSeries.C (C.u : R) * PowerSeries.C ((C.u⁻¹ : Rˣ) : R)) * hP - Q * hu

/-- Over a `ℚ`-algebra, the formal group laws are compared through their logarithms: the
logarithm of `ψ⁻¹ • Ê_W` is `u log_W(ψ(z))`, whose derivative is the invariant differential
of `Ê_{C • W}`. -/
private theorem formalGroup_smul_of_algebra [Algebra ℚ R] (C : VariableChange R)
    (W : WeierstrassCurve R) :
    formalGroup (C • W) = (C.formalCoordinate W)⁻¹ • formalGroup W := by
  refine FormalGroup.invariantDifferential_injective ?_
  rw [← FormalGroup.derivative_log, ← FormalGroup.derivative_log, FormalGroup.log_smul, inv_inv,
    map_inv, linearCoeff_formalCoordinate, inv_inv, Derivation.map_smul,
    derivative_subst (C.formalCoordinate W).hasSubst, FormalGroup.derivative_log,
    FormalGroup.derivative_log, subst_formalCoordinate_invariantDifferential_formalGroup,
    smul_eq_C_mul, ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]

/-- The transport of the formal group law of `W` along the inverse transition commutes with
base change. -/
private theorem map_inv_formalCoordinate_smul_formalGroup {S : Type*} [CommRing S] (f : R →+* S)
    (C : VariableChange R) (W : WeierstrassCurve R) :
    ((C.map f).formalCoordinate (W.map f))⁻¹ • formalGroup (W.map f) =
      ((C.formalCoordinate W)⁻¹ • formalGroup W).map f := by
  rw [FormalGroup.map_smul, map_inv, map_formalCoordinate, map_formalGroup]

/-- **The formal group law of `C • W` is the transport of that of `W`** along the inverse of the
formal parameter transition `ψ` from `C • W` to `W`. -/
theorem formalGroup_smul (C : VariableChange R) (W : WeierstrassCurve R) :
    formalGroup (C • W) = (C.formalCoordinate W)⁻¹ • formalGroup W := by
  -- prove it for the universal pair after embedding `UnivRing` in its fraction field, a
  -- `ℚ`-algebra, and specialize
  have := isDomain_univRing
  have := charZero_univRing
  have hι := IsFractionRing.injective UnivRing (FractionRing UnivRing)
  have : CharZero (FractionRing UnivRing) := charZero_of_injective_algebraMap hι
  obtain ⟨k, hW, hC⟩ := exists_map_universal C W
  generalize WeierstrassCurve.map Universal.curve (algebraMap _ UnivRing) = W₀ at hW
  generalize ChangeRing.universalChange (MvPolynomial Coeff ℤ) = C₀ at hC
  have h₀ : formalGroup (C₀ • W₀) = (C₀.formalCoordinate W₀)⁻¹ • formalGroup W₀ := by
    refine FormalGroup.map_injective hι ?_
    dsimp only
    rw [← map_inv_formalCoordinate_smul_formalGroup, ← map_formalGroup, ← map_variableChange]
    exact formalGroup_smul_of_algebra _ _
  rw [← hW, ← hC, map_inv_formalCoordinate_smul_formalGroup, ← h₀, ← map_formalGroup,
    map_variableChange]

/-- **The formal parameter transition is an isomorphism of formal group laws**: transporting the
formal group law of `C • W` along the transition `ψ` to `W` gives that of `W`, so
`FormalGroup.smulIso` makes `ψ` an isomorphism from `Ê_{C • W}` to `Ê_W`. -/
theorem formalCoordinate_smul_formalGroup (C : VariableChange R) (W : WeierstrassCurve R) :
    C.formalCoordinate W • formalGroup (C • W) = formalGroup W := by
  rw [formalGroup_smul, smul_inv_smul]

end WeierstrassCurve.VariableChange
