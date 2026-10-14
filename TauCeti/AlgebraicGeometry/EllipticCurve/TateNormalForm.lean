/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic

/-!
# Tate normal form

For `a b : R`, the Weierstrass curve in **Tate normal form** is

`Y² + aXY + bY = X³ + bX²`,

that is, `a₁ = a`, `a₂ = a₃ = b` and `a₄ = a₆ = 0` (`WeierstrassCurve.tateNormalForm`). The point
`(0, 0)` lies on it. Its discriminant is
`b³ (a³ - a⁴ - 8a²b + 36ab - 16b² - 27b)`, so `b` is a unit whenever the curve is elliptic.

Let `W` be a Weierstrass curve over a commutative ring `R` and `(x, y)` a point of `W` with
coordinates in `R`. Suppose that the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃` is a unit at
`(x, y)` and that the `3`-division polynomial `Ψ₃` is a unit at `x`. For an elliptic curve over a
field these say that the point `(x, y)` is killed neither by `2` nor by `3`; over a ring they say
this at every point of `Spec R`. Then exactly one change of variables carries `W` to Tate
normal form and `(x, y)` to `(0, 0)`
(`WeierstrassCurve.existsUnique_variableChange_tateNormalForm`).
It is `WeierstrassCurve.toTateNormalForm`, given by

`u = ψ₂³ / Ψ₃,  r = x,  s = (a₄ + 2a₂x - a₁y + 3x²) / ψ₂,  t = y`,

and the resulting curve has `b = Ψ₃³ / ψ₂⁸`. No hypothesis on `R` is needed. The translation
`(r, t) = (x, y)` moves the point to the origin, `s` makes the tangent line there horizontal
(`a₄ = 0`), and `u` makes `a₂ = a₃`. The identity behind the last step is
`(C • W).b₈ = u⁻⁸ Ψ₃(r)` (`WeierstrassCurve.variableChange_b₈_eq_eval_Ψ₃`): once `a₄ = a₆ = 0`,
the invariant `b₈` is `a₂a₃²`. For an elliptic `W` the two unit conditions are also necessary
(`WeierstrassCurve.exists_variableChange_tateNormalForm_iff`). The construction commutes with base
change (`WeierstrassCurve.toTateNormalForm_map`).

Finally, `WeierstrassCurve.UniversalTate.curve` is the Tate normal form with indeterminate
coefficients over `ℤ[A, B][Δ⁻¹]`. It is elliptic, and every elliptic Tate normal form over a
commutative ring is its base change along exactly one ring homomorphism
(`WeierstrassCurve.UniversalTate.map_lift`, `WeierstrassCurve.UniversalTate.eq_lift`), naturally in
the base ring (`WeierstrassCurve.UniversalTate.comp_lift`).

## Main definitions

* `WeierstrassCurve.tateNormalForm a b`: the curve `Y² + aXY + bY = X³ + bX²`.
* `WeierstrassCurve.toTateNormalForm`: the change of variables to Tate normal form centred at a
  point where `ψ₂` and `Ψ₃` are units.
* `WeierstrassCurve.UniversalTate.Ring`, `WeierstrassCurve.UniversalTate.curve`: the ring
  `ℤ[A, B][Δ⁻¹]` and the universal elliptic Tate normal form over it.
* `WeierstrassCurve.UniversalTate.lift`: the classifying homomorphism `ℤ[A, B][Δ⁻¹] →+* R` of an
  elliptic Tate normal form over `R`.
* `WeierstrassCurve.UniversalTate.curveULift`: the universal elliptic Tate normal form over the copy
  `ULift.{u} ℤ[A, B][Δ⁻¹]` of `ℤ[A, B][Δ⁻¹]` in `Type u`, over which it is read in schemes of
  universe `u`.

## Main results

* `WeierstrassCurve.tateNormalForm_Δ`: the discriminant of the Tate normal form.
* `WeierstrassCurve.toTateNormalForm_smul`: the change of variables produces a Tate normal form,
  with explicit coefficients.
* `WeierstrassCurve.eq_toTateNormalForm`: it is the only change of variables doing so that sends
  `(x, y)` to `(0, 0)`.
* `WeierstrassCurve.existsUnique_variableChange_tateNormalForm`: existence and uniqueness together.
* `WeierstrassCurve.exists_variableChange_tateNormalForm_iff`: for elliptic `W`, such a change of
  variables exists exactly when `(x, y)` lies on `W` and `ψ₂` and `Ψ₃` are units there.

## Provenance

The `UniversalTate` namespace adapts the construction of the universal elliptic Weierstrass curve in
`TauCeti/AlgebraicGeometry/EllipticCurve/Universal.lean` to two coefficients: `UniversalTate.Ring`
is `Localization.Away` of the discriminant as `Universal.EllipticRing` is, `UniversalTate.curve` is
the base change of the polynomial curve as `Universal.ellipticCurve` is, `Ring.ringHom_ext` follows
`Universal.EllipticRing.ringHom_ext`, and `lift`, `lift_comp_algebraMap`, `lift_algebraMap`,
`map_lift`, `comp_lift` and `eq_lift` follow the classifying homomorphism `specializeElliptic` and
its lemmas `specializeElliptic_comp_algebraMap`, `specializeElliptic_algebraMap`,
`map_specializeElliptic`, `specializeElliptic_map` and `specializeElliptic_map_ellipticCurve`.

## References

* [J. H. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Exercise 8.13, where the
  normal form is written `y² + (1 - c)xy - by = x³ - bx²`; it is the present one with
  `a = 1 - c` and `b` replaced by `-b`.
* D. S. Kubert, *Universal bounds on the torsion of elliptic curves*, Proc. London Math. Soc. (3)
  33 (1976), 193–237.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The Tate normal form -/

/-- The Weierstrass curve `Y² + aXY + bY = X³ + bX²` in **Tate normal form**:
`a₁ = a`, `a₂ = a₃ = b` and `a₄ = a₆ = 0`. -/
def tateNormalForm (a b : R) : WeierstrassCurve R where
  a₁ := a
  a₂ := b
  a₃ := b
  a₄ := 0
  a₆ := 0

variable (a b : R)

@[simp] theorem tateNormalForm_a₁ : (tateNormalForm a b).a₁ = a := (rfl)
@[simp] theorem tateNormalForm_a₂ : (tateNormalForm a b).a₂ = b := (rfl)
@[simp] theorem tateNormalForm_a₃ : (tateNormalForm a b).a₃ = b := (rfl)
@[simp] theorem tateNormalForm_a₄ : (tateNormalForm a b).a₄ = 0 := (rfl)
@[simp] theorem tateNormalForm_a₆ : (tateNormalForm a b).a₆ = 0 := (rfl)

@[simp]
theorem tateNormalForm_b₂ : (tateNormalForm a b).b₂ = a ^ 2 + 4 * b := by
  simp [b₂, sq]

@[simp]
theorem tateNormalForm_b₄ : (tateNormalForm a b).b₄ = a * b := by
  simp [b₄]

@[simp]
theorem tateNormalForm_b₆ : (tateNormalForm a b).b₆ = b ^ 2 := by
  simp [b₆, sq]

@[simp]
theorem tateNormalForm_b₈ : (tateNormalForm a b).b₈ = b ^ 3 := by
  simp only [b₈, tateNormalForm_a₁, tateNormalForm_a₂, tateNormalForm_a₃, tateNormalForm_a₄,
    tateNormalForm_a₆]
  ring

/-- The discriminant of the Tate normal form `Y² + aXY + bY = X³ + bX²`. -/
theorem tateNormalForm_Δ :
    (tateNormalForm a b).Δ =
      b ^ 3 * (a ^ 3 - a ^ 4 - 8 * a ^ 2 * b + 36 * a * b - 16 * b ^ 2 - 27 * b) := by
  rw [Δ, tateNormalForm_b₂, tateNormalForm_b₄, tateNormalForm_b₆, tateNormalForm_b₈]
  ring

/-- If the Tate normal form `Y² + aXY + bY = X³ + bX²` is elliptic, then `b` is a unit. -/
theorem isUnit_of_isUnit_tateNormalForm_Δ {a b : R} (h : IsUnit (tateNormalForm a b).Δ) :
    IsUnit b := by
  rw [tateNormalForm_Δ] at h
  exact (isUnit_pow_iff three_ne_zero).mp (isUnit_of_mul_isUnit_left h)

/-- The point `(0, 0)` lies on the Tate normal form. -/
theorem equation_tateNormalForm_zero : (tateNormalForm a b).toAffine.Equation 0 0 :=
  Affine.equation_zero.mpr (tateNormalForm_a₆ a b)

/-- The Tate normal form commutes with base change. -/
@[simp]
theorem map_tateNormalForm {A : Type*} [CommRing A] (φ : R →+* A) :
    (tateNormalForm a b).map φ = tateNormalForm (φ a) (φ b) := by
  ext <;> simp

/-! ### Changes of variables to Tate normal form -/

variable (W : WeierstrassCurve R)

/-- On the Tate normal form, the `2`-division polynomial `ψ₂` takes the value `b` at `(0, 0)`. -/
@[simp]
theorem evalEval_ψ₂_tateNormalForm_zero : (tateNormalForm a b).ψ₂.evalEval 0 0 = b := by
  simp [ψ₂]

/-- On the Tate normal form, the `3`-division polynomial `Ψ₃` takes the value `b³` at `0`. -/
@[simp]
theorem eval_Ψ₃_tateNormalForm_zero : (tateNormalForm a b).Ψ₃.eval 0 = b ^ 3 := by
  simp [eval_Ψ₃]

variable {W} {x y : R}

variable (hψ₂ : IsUnit (W.ψ₂.evalEval x y)) (hΨ₃ : IsUnit (W.Ψ₃.eval x))

/-- The **change of variables to Tate normal form** centred at a point `(x, y)` at which the
`2`-division polynomial `ψ₂` and the `3`-division polynomial `Ψ₃` are units:
`u = ψ₂³ / Ψ₃`, `r = x`, `s = (a₄ + 2a₂x - a₁y + 3x²) / ψ₂` and `t = y`. When `(x, y)` lies on
`W`, it carries `W` to Tate normal form (`toTateNormalForm_smul`) and `(x, y)` to `(0, 0)`, and it
is the only change of variables doing both (`eq_toTateNormalForm`). -/
noncomputable def toTateNormalForm : VariableChange R where
  u := (hΨ₃.unit * hψ₂.unit⁻¹ ^ 3)⁻¹
  r := x
  s := (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * ↑hψ₂.unit⁻¹
  t := y

@[simp]
theorem toTateNormalForm_u : (toTateNormalForm hψ₂ hΨ₃).u = (hΨ₃.unit * hψ₂.unit⁻¹ ^ 3)⁻¹ :=
  (rfl)

@[simp] theorem toTateNormalForm_r : (toTateNormalForm hψ₂ hΨ₃).r = x := (rfl)

@[simp]
theorem toTateNormalForm_s : (toTateNormalForm hψ₂ hΨ₃).s =
    (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * ↑hψ₂.unit⁻¹ :=
  (rfl)

@[simp] theorem toTateNormalForm_t : (toTateNormalForm hψ₂ hΨ₃).t = y := (rfl)

/-- **Existence of Tate normal form.** If `(x, y)` lies on `W`, and `ψ₂` and `Ψ₃` are units there,
then `toTateNormalForm` carries `W` to the Tate normal form with `a = (Ψ₃ / ψ₂³)(a₁ + 2s)` and
`b = Ψ₃³ / ψ₂⁸`. -/
theorem toTateNormalForm_smul (h : W.toAffine.Equation x y) :
    toTateNormalForm hψ₂ hΨ₃ • W =
      tateNormalForm (W.Ψ₃.eval x * ↑hψ₂.unit⁻¹ ^ 3 * (W.a₁ + 2 * (toTateNormalForm hψ₂ hΨ₃).s))
        (W.Ψ₃.eval x ^ 3 * ↑hψ₂.unit⁻¹ ^ 8) := by
  have hψ : (2 * y + W.a₁ * x + W.a₃) * ↑hψ₂.unit⁻¹ = 1 := by
    rw [← Affine.evalEval_polynomialY, ← ψ₂]
    exact hψ₂.mul_val_inv
  have hs : (toTateNormalForm hψ₂ hΨ₃).s * (2 * y + W.a₁ * x + W.a₃) =
      W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2 := by
    rw [toTateNormalForm_s]
    linear_combination (W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2) * hψ
  have hm := a₂_mul_ψ₂_sq_eq_eval_Ψ₃ h hs
  have hu : (↑(toTateNormalForm hψ₂ hΨ₃).u⁻¹ : R) = W.Ψ₃.eval x * ↑hψ₂.unit⁻¹ ^ 3 := by
    simp
  rw [Affine.equation_iff] at h
  ext
  · rw [variableChange_a₁, hu, tateNormalForm_a₁]
  · -- `u⁻²m = (Ψ₃/ψ₂³)²m` equals `Ψ₃³/ψ₂⁸` because `mψ₂² = Ψ₃` (`hm`)
    rw [variableChange_a₂, hu, tateNormalForm_a₂, toTateNormalForm_r]
    linear_combination (-W.Ψ₃.eval x ^ 2 * ↑hψ₂.unit⁻¹ ^ 6 *
      (W.a₂ - (toTateNormalForm hψ₂ hΨ₃).s * W.a₁ + 3 * x - (toTateNormalForm hψ₂ hΨ₃).s ^ 2) *
      (1 + (2 * y + W.a₁ * x + W.a₃) * ↑hψ₂.unit⁻¹)) * hψ +
      W.Ψ₃.eval x ^ 2 * ↑hψ₂.unit⁻¹ ^ 8 * hm
  · rw [variableChange_a₃, hu, tateNormalForm_a₃, toTateNormalForm_r, toTateNormalForm_t]
    linear_combination W.Ψ₃.eval x ^ 3 * ↑hψ₂.unit⁻¹ ^ 8 * hψ
  · rw [variableChange_a₄, hu, tateNormalForm_a₄, toTateNormalForm_r, toTateNormalForm_t]
    linear_combination -(W.Ψ₃.eval x * ↑hψ₂.unit⁻¹ ^ 3) ^ 4 * hs
  · rw [variableChange_a₆, hu, tateNormalForm_a₆, toTateNormalForm_r, toTateNormalForm_t]
    linear_combination -(W.Ψ₃.eval x * ↑hψ₂.unit⁻¹ ^ 3) ^ 6 * h

/-- **Uniqueness of Tate normal form.** A change of variables carrying `W` to a Tate normal form
and `(x, y)` to `(0, 0)` (that is, with `r = x` and `t = y`) is `toTateNormalForm`. -/
theorem eq_toTateNormalForm {C : VariableChange R} (hr : C.r = x) (ht : C.t = y) {a b : R}
    (hC : C • W = tateNormalForm a b) : C = toTateNormalForm hψ₂ hΨ₃ := by
  have h₂ : (C • W).a₂ = (C • W).a₃ := by simp [hC]
  have h₄ : (C • W).a₄ = 0 := by simp [hC]
  have h₆ : (C • W).a₆ = 0 := by simp [hC]
  have hw : IsUnit (↑C.u⁻¹ : R) := Units.isUnit _
  rw [variableChange_a₂, variableChange_a₃, hr, ht] at h₂
  rw [variableChange_a₄, hr, ht, (hw.pow 4).mul_right_eq_zero] at h₄
  rw [variableChange_a₆, hr, ht, (hw.pow 6).mul_right_eq_zero] at h₆
  have h : W.toAffine.Equation x y := by
    rw [Affine.equation_iff]
    linear_combination -h₆
  have hs : C.s * (2 * y + W.a₁ * x + W.a₃) = W.a₄ + 2 * x * W.a₂ - y * W.a₁ + 3 * x ^ 2 := by
    linear_combination -h₄
  have hψ : (2 * y + W.a₁ * x + W.a₃) * ↑hψ₂.unit⁻¹ = 1 := by
    rw [← Affine.evalEval_polynomialY, ← ψ₂]
    exact hψ₂.mul_val_inv
  -- cancelling `u⁻²` in `u⁻² m = u⁻³ ψ₂` gives `m = u⁻¹ ψ₂`, hence `Ψ₃ = m ψ₂² = u⁻¹ ψ₂³`
  have hmw : W.a₂ - C.s * W.a₁ + 3 * x - C.s ^ 2 = ↑C.u⁻¹ * (2 * y + W.a₁ * x + W.a₃) :=
    (hw.pow 2).mul_left_cancel (by linear_combination h₂)
  have hΨ : W.Ψ₃.eval x = ↑C.u⁻¹ * (2 * y + W.a₁ * x + W.a₃) ^ 3 := by
    rw [← a₂_mul_ψ₂_sq_eq_eval_Ψ₃ h hs, hmw]
    ring
  ext : 1
  · -- `u (Ψ₃/ψ₂³) = 1`, using `Ψ₃ = u⁻¹ψ₂³` (`hΨ`)
    rw [toTateNormalForm_u, eq_inv_iff_mul_eq_one, Units.ext_iff]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]
    linear_combination (2 * y + W.a₁ * x + W.a₃) ^ 3 * ↑hψ₂.unit⁻¹ ^ 3 * C.u.inv_mul +
      ↑C.u * ↑hψ₂.unit⁻¹ ^ 3 * hΨ + ((2 * y + W.a₁ * x + W.a₃) ^ 2 * ↑hψ₂.unit⁻¹ ^ 2 +
        (2 * y + W.a₁ * x + W.a₃) * ↑hψ₂.unit⁻¹ + 1) * hψ
  · rw [toTateNormalForm_r, hr]
  · rw [toTateNormalForm_s, ← hs]
    linear_combination -C.s * hψ
  · rw [toTateNormalForm_t, ht]

include hψ₂ hΨ₃ in
/-- **Tate normal form.** If `(x, y)` lies on `W`, and the `2`- and `3`-division polynomials `ψ₂`
and `Ψ₃` are units there, then exactly one change of variables carries `W` to a Tate normal form
`Y² + aXY + bY = X³ + bX²` and `(x, y)` to `(0, 0)`. -/
theorem existsUnique_variableChange_tateNormalForm (h : W.toAffine.Equation x y) :
    ∃! C : VariableChange R, C.r = x ∧ C.t = y ∧ ∃ a b : R, C • W = tateNormalForm a b :=
  ⟨toTateNormalForm hψ₂ hΨ₃,
    ⟨toTateNormalForm_r .., toTateNormalForm_t .., _, _, toTateNormalForm_smul hψ₂ hΨ₃ h⟩,
    fun _ ⟨hr, ht, _, _, hC⟩ ↦ eq_toTateNormalForm hψ₂ hΨ₃ hr ht hC⟩

/-- For an elliptic `W`, a change of variables carrying `W` to a Tate normal form and `(x, y)` to
`(0, 0)` exists exactly when `(x, y)` lies on `W` and the `2`- and `3`-division polynomials `ψ₂`
and `Ψ₃` are units there. -/
theorem exists_variableChange_tateNormalForm_iff [W.IsElliptic] :
    (∃ C : VariableChange R, C.r = x ∧ C.t = y ∧ ∃ a b : R, C • W = tateNormalForm a b) ↔
      W.toAffine.Equation x y ∧ IsUnit (W.ψ₂.evalEval x y) ∧ IsUnit (W.Ψ₃.eval x) := by
  refine ⟨fun ⟨C, hr, ht, a, b, hC⟩ ↦ ?_, fun ⟨h, hψ₂, hΨ₃⟩ ↦
    (existsUnique_variableChange_tateNormalForm hψ₂ hΨ₃ h).exists⟩
  have hb : IsUnit b := isUnit_of_isUnit_tateNormalForm_Δ (hC ▸ (C • W).isUnit_Δ)
  have h₃ : (C • W).a₃ = b := by simp [hC]
  have h₆ : (C • W).a₆ = 0 := by simp [hC]
  have h₈ : (C • W).b₈ = b ^ 3 := by simp [hC]
  have hw : IsUnit (↑C.u⁻¹ : R) := Units.isUnit _
  rw [variableChange_a₃, hr, ht] at h₃
  rw [variableChange_a₆, hr, ht, (hw.pow 6).mul_right_eq_zero] at h₆
  rw [variableChange_b₈_eq_eval_Ψ₃, hr] at h₈
  refine ⟨?_, ?_, isUnit_of_mul_isUnit_right (h₈ ▸ hb.pow 3)⟩
  · rw [Affine.equation_iff]
    linear_combination -h₆
  · -- `h₃` gives `u⁻³ (a₃ + x a₁ + 2y) = b`, a unit; the factor is `ψ₂(x, y)` up to reordering
    rw [ψ₂, Affine.evalEval_polynomialY]
    convert isUnit_of_mul_isUnit_right (h₃ ▸ hb) using 1
    ring

/-- **Tate normal form commutes with base change.** The image of `toTateNormalForm` under a ring
homomorphism `φ` is the change of variables to Tate normal form of `W.map φ` at `(φ x, φ y)`, where
`ψ₂` and `Ψ₃` are again units since they are the images under `φ` of their values on `W`. -/
theorem toTateNormalForm_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (toTateNormalForm hψ₂ hΨ₃).map φ =
      toTateNormalForm (W := W.map φ) (x := φ x) (y := φ y)
        (by rw [map_ψ₂, Polynomial.map_mapRingHom_evalEval]; exact hψ₂.map φ)
        (by rw [map_Ψ₃, Polynomial.eval_map_apply]; exact hΨ₃.map φ) := by
  generalize_proofs hψ₂' hΨ₃'
  have e₂ : Units.map φ hψ₂.unit = hψ₂'.unit :=
    Units.ext <| by simp [map_ψ₂, Polynomial.map_mapRingHom_evalEval]
  have e₃ : Units.map φ hΨ₃.unit = hΨ₃'.unit := Units.ext <| by simp [map_Ψ₃]
  ext : 1
  · simp only [VariableChange.map, toTateNormalForm_u, map_inv, map_mul, map_pow, e₂, e₃]
  · rfl
  · simp only [VariableChange.map, toTateNormalForm_s, ← e₂, Units.coe_map_inv,
      MonoidHom.coe_ofClass, map_add, map_sub, map_mul, map_pow, map_ofNat, map_a₁, map_a₂, map_a₄]
  · rfl

/-! ### The universal Tate normal form over `ℤ[A, B][Δ⁻¹]` -/

namespace UniversalTate

open MvPolynomial (X)

/-- The Tate normal form `Y² + AXY + BY = X³ + BX²` over the polynomial ring `ℤ[A, B]`, with the
indeterminates `A = X 0` and `B = X 1` as coefficients. -/
noncomputable abbrev polyCurve : WeierstrassCurve (MvPolynomial (Fin 2) ℤ) :=
  tateNormalForm (X 0) (X 1)

/-- The ring `ℤ[A, B][Δ⁻¹]`: the polynomial ring `ℤ[A, B]` localised away from the discriminant of
the Tate normal form with coefficients `A` and `B`. -/
abbrev Ring : Type := Localization.Away polyCurve.Δ

/-- The **universal elliptic Tate normal form**, over `ℤ[A, B][Δ⁻¹]`. Every elliptic Tate normal
form over a commutative ring is its base change along exactly one ring homomorphism (`map_lift`,
`eq_lift`). -/
noncomputable abbrev curve : WeierstrassCurve Ring :=
  polyCurve.baseChange Ring

/-- The universal Tate normal form is an elliptic curve. -/
instance : curve.IsElliptic where
  isUnit := by
    simpa only [baseChange, map_Δ] using IsLocalization.Away.algebraMap_isUnit polyCurve.Δ

/-- Two ring homomorphisms out of `ℤ[A, B][Δ⁻¹]` are equal as soon as they agree on the images of
the indeterminates `A` and `B`. -/
-- `high`, as for Mathlib's `Localization.algHom_ext`, so that `ext` tries this lemma before
-- `RingHom.ext`.
@[ext high]
theorem Ring.ringHom_ext {S : Type*} [Semiring S] {f g : Ring →+* S}
    (h₀ : f (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 0)) =
      g (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 0)))
    (h₁ : f (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 1)) =
      g (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 1))) : f = g :=
  IsLocalization.ringHom_ext (.powers polyCurve.Δ) <|
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) <| Fin.forall_fin_two.mpr
      ⟨by simpa only [RingHom.comp_apply] using h₀, by simpa only [RingHom.comp_apply] using h₁⟩

variable {a b}

/-- Substituting `a` and `b` for the indeterminates turns `polyCurve` into the Tate normal form
`Y² + aXY + bY = X³ + bX²`. -/
theorem map_polyCurve (a b : R) :
    polyCurve.map (MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b]) = tateNormalForm a b := by
  simp [polyCurve]

/-- The **classifying homomorphism** `ℤ[A, B][Δ⁻¹] →+* R` of an elliptic Tate normal form
`Y² + aXY + bY = X³ + bX²` over `R`, sending `A` to `a` and `B` to `b`. -/
noncomputable def lift (h : IsUnit (tateNormalForm a b).Δ) : Ring →+* R :=
  IsLocalization.Away.lift polyCurve.Δ
    (g := MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b]) <| by
    rwa [← map_Δ, map_polyCurve]

/-- Restricted to the polynomial ring `ℤ[A, B]`, the classifying homomorphism substitutes `a` and
`b` for the indeterminates. Use this shape when composing ring maps and `lift_algebraMap` when
rewriting underneath an application. -/
theorem lift_comp_algebraMap (h : IsUnit (tateNormalForm a b).Δ) :
    (lift h).comp (algebraMap (MvPolynomial (Fin 2) ℤ) Ring) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b] :=
  IsLocalization.Away.lift_comp ..

/-- The pointwise form of `lift_comp_algebraMap`. -/
theorem lift_algebraMap (h : IsUnit (tateNormalForm a b).Δ) (p : MvPolynomial (Fin 2) ℤ) :
    lift h (algebraMap (MvPolynomial (Fin 2) ℤ) Ring p) =
      MvPolynomial.eval₂Hom (Int.castRingHom R) ![a, b] p :=
  IsLocalization.Away.lift_eq ..

@[simp]
theorem lift_algebraMap_X_zero (h : IsUnit (tateNormalForm a b).Δ) :
    lift h (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 0)) = a := by
  simp [lift]

@[simp]
theorem lift_algebraMap_X_one (h : IsUnit (tateNormalForm a b).Δ) :
    lift h (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 1)) = b := by
  simp [lift]

/-- Every elliptic Tate normal form is the base change of the universal one along its classifying
homomorphism. -/
@[simp]
theorem map_lift (h : IsUnit (tateNormalForm a b).Δ) : curve.map (lift h) = tateNormalForm a b := by
  simp [baseChange]

/-- The classifying homomorphism is natural in the base ring: followed by a ring homomorphism
`φ : R →+* S`, the classifying homomorphism of `Y² + aXY + bY = X³ + bX²` is that of its base change
`Y² + φ(a)XY + φ(b)Y = X³ + φ(b)X²`, whose discriminant is the unit `φ(Δ)`. -/
theorem comp_lift {S : Type*} [CommRing S] (φ : R →+* S) (h : IsUnit (tateNormalForm a b).Δ) :
    φ.comp (lift h) = lift (a := φ a) (b := φ b)
      (by rw [← map_tateNormalForm, map_Δ]; exact h.map φ) := by
  ext <;> simp

/-- The classifying homomorphism is unique: a ring homomorphism out of `ℤ[A, B][Δ⁻¹]` along which
the universal Tate normal form becomes `Y² + aXY + bY = X³ + bX²` is `lift`. -/
theorem eq_lift (h : IsUnit (tateNormalForm a b).Δ) {f : Ring →+* R}
    (hf : curve.map f = tateNormalForm a b) : f = lift h := by
  have h₁ := congr_arg a₁ hf
  have h₃ := congr_arg a₃ hf
  simp only [baseChange, map_map, map_a₁, map_a₃, tateNormalForm_a₁, tateNormalForm_a₃] at h₁ h₃
  ext
  · simpa using h₁
  · simpa using h₃

universe u

/-- The universal elliptic Tate normal form `Y² + AXY + BY = X³ + BX²`, over the copy
`ULift.{u} ℤ[A, B][Δ⁻¹]` of its coefficient ring in `Type u`. -/
noncomputable def curveULift : WeierstrassCurve (ULift.{u} Ring) :=
  tateNormalForm (.up (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 0)))
    (.up (algebraMap (MvPolynomial (Fin 2) ℤ) Ring (X 1)))

/-- The universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` is the base change of the one over
`ℤ[A, B][Δ⁻¹]` along the identification of the two rings. -/
theorem curveULift_eq :
    curveULift.{u} = curve.map (ULift.ringEquiv.symm : Ring ≃+* ULift.{u} Ring).toRingHom := by
  -- `ULift.ringEquiv.symm` is `ULift.up` by definition
  simp only [curve, polyCurve, baseChange, map_tateNormalForm]
  rfl

/-- The universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` is a Tate normal form. -/
theorem curveULift_eq_tateNormalForm :
    curveULift.{u} = tateNormalForm curveULift.a₁ curveULift.a₃ :=
  (rfl)

/-- The coefficient `a₁` of the universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` is that of
the one over `ℤ[A, B][Δ⁻¹]`. -/
@[simp]
theorem curveULift_a₁ : curveULift.{u}.a₁ = .up curve.a₁ :=
  (rfl)

/-- The coefficient `a₃` of the universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` is that of
the one over `ℤ[A, B][Δ⁻¹]`. -/
@[simp]
theorem curveULift_a₃ : curveULift.{u}.a₃ = .up curve.a₃ :=
  (rfl)

/-- The point `(0, 0)` lies on the universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]`. -/
theorem equation_curveULift_zero : curveULift.{u}.toAffine.Equation 0 0 := by
  rw [curveULift_eq_tateNormalForm]
  exact equation_tateNormalForm_zero _ _

/-- The base change of the universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` along a ring
homomorphism `φ` is the Tate normal form with the images of `A` and `B` as coefficients. -/
@[simp]
theorem map_curveULift {S : Type*} [CommRing S] (φ : ULift.{u} Ring →+* S) :
    curveULift.map φ = tateNormalForm (φ curveULift.a₁) (φ curveULift.a₃) := by
  simp [curveULift]

/-- The universal Tate normal form over `ULift.{u} ℤ[A, B][Δ⁻¹]` is elliptic. -/
instance : curveULift.{u}.IsElliptic := by
  rw [curveULift_eq]
  infer_instance

end UniversalTate

end WeierstrassCurve
