/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
public import Mathlib.FieldTheory.Separable
public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.FreyCurve.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange
import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Discriminant
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.SeparableDegree
import Mathlib.FieldTheory.SplittingField.Construction

/-!
# The Legendre form of an elliptic curve

The **Legendre form** of an elliptic curve is `y² = x (x - 1) (x - λ)`: the cubic on the right has
its three roots at `0`, `1` and `λ`. In Tau Ceti it is the curve `TauCeti.freyCurve 1 B` with
`B = -λ`, whose invariants `TauCeti.freyCurve_c₄`, `TauCeti.freyCurve_Δ` and `TauCeti.freyCurve_j`
specialise to

  `c₄ = 16 (B² + B + 1)`, `Δ = 16 B² (B + 1)²`, `j = 256 (B² + B + 1)³ / (B² (B + 1)²)`.

Away from characteristic `2` every elliptic curve takes this form after a finite separable
extension of the base field (Silverman, *AEC*, III.1.7). Over a field `F` with `2 ≠ 0`, suppose
that the `2`-division polynomial `4x³ + b₂x² + 2b₄x + b₆` of `W` factors as
`4 (x - e₁) (x - e₂) (x - e₃)` with `e₁ ≠ e₂`, and that `e₂ - e₁ = u²`. Completing the square in
`y`, moving `e₁` to the origin and scaling by `u` is a change of variables taking `W` to the
Legendre form with `λ = (e₃ - e₁) / (e₂ - e₁)`. A splitting field of the `2`-division polynomial,
followed by a splitting field of `X² - (e₂ - e₁)`, supplies the roots and the square root, and it
is separable because the `2`-division polynomial has nonzero discriminant `16 Δ`.

Since `j` is an explicit rational function of `λ`, the Legendre form ties the reduction of an
elliptic curve to its `j`-invariant: this is how the criterion
`WeierstrassCurve.hasPotentialGoodReduction_of_isInteger_j` for potential good reduction is
proved away from residue characteristic `2`. In residue characteristic `2` the Deuring normal form
of `TauCeti/AlgebraicGeometry/EllipticCurve/DeuringNormalForm.lean` takes its place.

Over an arbitrary commutative ring `R` the Legendre form is reached from two points of order two
rather than from roots of the `2`-division polynomial. Let `(x₁, y₁)` and `(x₂, y₂)` be points of
`W` at which `ψ₂ = 2y + a₁x + a₃` vanishes, and `u` a unit with `x₂ - x₁ = u²`. If `W` is elliptic,
this already forces `2` to be a unit (`WeierstrassCurve.isUnit_two_of_evalEval_ψ₂_eq_zero`).
Exactly one change of variables with scaling `u` then carries `W` to a Legendre form, `(x₁, y₁)`
to `(0, 0)` and `(x₂, y₂)` to `(1, 0)` (`WeierstrassCurve.existsUnique_variableChange_legendre`). It
is `WeierstrassCurve.toLegendre`, with `r = x₁`, `s = -a₁/2` and `t = y₁`. A change of variables
with scaling `u` multiplies the invariant differential by `u`, so fixing `u` amounts to fixing the
differential `ω = u·ω_W`. The ring `ℤ[1/2][λ, 1/λ(λ - 1)]` with the curve `y² = x (x - 1) (x - λ)`
(`WeierstrassCurve.UniversalLegendre.curve`) classifies such data at the level of equations: an
elliptic Weierstrass curve with two such points and such a unit `u` determines exactly one ring
homomorphism out of it and one change of variables with scaling `u` to the base change of the
universal curve carrying `(x₁, y₁)` to `(0, 0)` and `(x₂, y₂)` to `(1, 0)`
(`WeierstrassCurve.UniversalLegendre.existsUnique_legendre`). The parameter `λ`
depends on `u` only through `u²`. This is not yet the representability of the Legendre structures
of Katz and Mazur, an ordered basis of `E[2]` together with a nowhere-vanishing differential: it
models them only once the two points are identified with a basis of the `2`-torsion and `ω` with
the corresponding differential, which needs the `2`-torsion subgroup and invariant differential of
an elliptic curve over a general base.

## Main definitions

* `WeierstrassCurve.toLegendre`: the change of variables to Legendre form with scaling `u`,
  centred at a point of order two; it commutes with base change
  (`WeierstrassCurve.toLegendre_map`).
* `WeierstrassCurve.UniversalLegendre.Ring`, `WeierstrassCurve.UniversalLegendre.curve`: the ring
  `ℤ[1/2][λ, 1/λ(λ - 1)]` and the universal Legendre curve over it.
* `WeierstrassCurve.UniversalLegendre.lift`: the classifying homomorphism
  `ℤ[1/2][λ, 1/λ(λ - 1)] →+* R` of an element `l` with `2l(l - 1)` a unit, along which the
  universal curve becomes `y² = x (x - 1) (x - l)`
  (`WeierstrassCurve.UniversalLegendre.map_lift`), naturally in `R`
  (`WeierstrassCurve.UniversalLegendre.comp_lift`).

## Main results

* `WeierstrassCurve.exists_variableChange_smul_eq_freyCurve_one`: a curve whose `2`-division
  polynomial splits, with `e₂ - e₁` a square, is a change of variables away from Legendre form.
* `WeierstrassCurve.exists_variableChange_smul_baseChange_eq_freyCurve_one`: away from
  characteristic `2`, an elliptic curve takes Legendre form over a finite separable extension.
* `TauCeti.isElliptic_freyCurve_one_neg_iff`: `y² = x (x - 1) (x - l)` is elliptic
  exactly when `2l(l - 1)` is a unit.
* `WeierstrassCurve.toLegendre_smul`: over a ring, `toLegendre` carries `W` to Legendre form, with
  an explicit parameter.
* `WeierstrassCurve.eq_toLegendre`: it is the only change of variables with scaling `u` doing so
  that sends `(x₁, y₁)` to `(0, 0)`.
* `WeierstrassCurve.existsUnique_variableChange_legendre` and
  `WeierstrassCurve.exists_variableChange_legendre_iff`: existence and uniqueness together, and,
  for elliptic `W`, the converse.
* `WeierstrassCurve.UniversalLegendre.existsUnique_legendre`: the equation-level universal
  property of the universal Legendre curve.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.1.7 and VII.5.5.
* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.9 and 4.6.2, for the Legendre structures.

## Provenance

The `WeierstrassCurve.UniversalLegendre` namespace is adapted from Tau Ceti's own
`WeierstrassCurve.UniversalTate` in `TauCeti.AlgebraicGeometry.EllipticCurve.TateNormalForm`: the
ring as a localisation of a polynomial ring over `ℤ`, and `Ring.ringHom_ext`, `lift`,
`lift_comp_algebraMap`, `lift_algebraMap`, `map_lift`, `comp_lift` and `eq_lift`, follow the
declarations of the same names there.
-/

public section

universe u

open Polynomial TauCeti

namespace TauCeti

/-- The Legendre form `y² = x (x - 1) (x - l)` is elliptic exactly when `2l(l - 1)` is a unit. -/
theorem isElliptic_freyCurve_one_neg_iff {R : Type*} [CommRing R] {l : R} :
    (freyCurve 1 (-l)).IsElliptic ↔ IsUnit (2 * l * (l - 1)) := by
  rw [isElliptic_freyCurve_iff, IsUnit.mul_iff, IsUnit.mul_iff, IsUnit.neg_iff,
    ← sub_eq_add_neg, ← neg_sub l, IsUnit.neg_iff]
  simp only [isUnit_one, true_and, and_assoc]

end TauCeti

namespace WeierstrassCurve

/-! ### Legendre form over a ring -/

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) {x₁ y₁ x₂ y₂ : R}

/-- The **change of variables to Legendre form** with scaling `u` and centre `(x₁, y₁)`, defined
when `2` is a unit: `u`, `r = x₁`, `s = -a₁/2` and `t = y₁`. When `(x₁, y₁)` and `(x₂, y₂)` are
points of order two on `W` with `x₂ - x₁ = u²`, it carries `W` to Legendre form, `(x₁, y₁)` to
`(0, 0)` and `(x₂, y₂)` to `(1, 0)` (`toLegendre_smul`), and it is the only change of variables with
scaling `u` doing so (`eq_toLegendre`). -/
noncomputable def toLegendre (h2 : IsUnit (2 : R)) (u : Rˣ) (x₁ y₁ : R) : VariableChange R where
  u := u
  r := x₁
  s := -W.a₁ * ↑h2.unit⁻¹
  t := y₁

variable (h2 : IsUnit (2 : R)) (u : Rˣ)

@[simp] theorem toLegendre_u : (W.toLegendre h2 u x₁ y₁).u = u := (rfl)

@[simp] theorem toLegendre_r : (W.toLegendre h2 u x₁ y₁).r = x₁ := (rfl)

@[simp] theorem toLegendre_s : (W.toLegendre h2 u x₁ y₁).s = -W.a₁ * ↑h2.unit⁻¹ := (rfl)

@[simp] theorem toLegendre_t : (W.toLegendre h2 u x₁ y₁).t = y₁ := (rfl)

/-- **Legendre form commutes with base change.** The image of `toLegendre` under a ring
homomorphism `φ` is the change of variables to Legendre form of `W.map φ` with scaling `φ u` and
centre `(φ x₁, φ y₁)`, where `2` is again a unit since it is the image of `2` under `φ`. -/
theorem toLegendre_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (W.toLegendre h2 u x₁ y₁).map φ =
      (W.map φ).toLegendre (map_ofNat φ 2 ▸ h2.map φ) (Units.map φ u) (φ x₁) (φ y₁) := by
  have e (h : IsUnit (2 : A)) : Units.map (φ : R →* A) h2.unit = h.unit :=
    Units.ext <| by simp [map_ofNat]
  ext : 1
  · rfl
  · rfl
  · simp only [VariableChange.map, toLegendre_s, ← e, Units.coe_map_inv, MonoidHom.coe_ofClass,
      map_mul, map_neg, map_a₁]
  · rfl

variable {W}

/-- **Existence of Legendre form.** Let `(x₁, y₁)` and `(x₂, y₂)` be points of `W` at which `ψ₂`
vanishes, with `x₂ - x₁ = u²`. Then `toLegendre` carries `W` to the Legendre form
`y² = x (x - 1) (x - λ)`, that is `freyCurve 1 (-λ)`, with `λ = -(b₂/4 + 2x₁ + x₂)/u²`. Thus
`u² λ = x₃ - x₁` where `x₃ = -b₂/4 - x₁ - x₂` is the `x`-coordinate of the third point of order
two. -/
theorem toLegendre_smul (h₁ : W.toAffine.Equation x₁ y₁) (h₂ : W.toAffine.Equation x₂ y₂)
    (hψ₁ : W.ψ₂.evalEval x₁ y₁ = 0) (hψ₂ : W.ψ₂.evalEval x₂ y₂ = 0) (hu : x₂ - x₁ = u ^ 2) :
    W.toLegendre h2 u x₁ y₁ • W =
      freyCurve 1 ((W.b₂ * ↑h2.unit⁻¹ ^ 2 + 2 * x₁ + x₂) * ↑u⁻¹ ^ 2) := by
  -- `x₁` and `x₂` are roots of `Ψ₂Sq = 4X³ + b₂X² + 2b₄X + b₆`, since `ψ₂² = Ψ₂Sq` on the curve
  have f₁ : 4 * x₁ ^ 3 + W.b₂ * x₁ ^ 2 + 2 * W.b₄ * x₁ + W.b₆ = 0 := by
    simpa [Ψ₂Sq, hψ₁] using (W.evalEval_ψ₂_sq h₁).symm
  have f₂ : 4 * x₂ ^ 3 + W.b₂ * x₂ ^ 2 + 2 * W.b₄ * x₂ + W.b₆ = 0 := by
    simpa [Ψ₂Sq, hψ₂] using (W.evalEval_ψ₂_sq h₂).symm
  rw [ψ₂, Affine.evalEval_polynomialY] at hψ₁ hψ₂
  rw [Affine.equation_iff] at h₁ h₂
  have hi : 2 * (↑h2.unit⁻¹ : R) = 1 := h2.mul_val_inv
  have hv : (u : R) * ↑u⁻¹ = 1 := u.mul_inv
  have hv2 : (↑u⁻¹ : R) ^ 2 * (x₂ - x₁) = 1 := by
    linear_combination (↑u⁻¹ : R) ^ 2 * hu + ((u : R) * ↑u⁻¹ + 1) * hv
  have hb₂ : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := (rfl)
  have hb₄ : W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ := (rfl)
  have hx : IsUnit (x₁ - x₂) := IsUnit.of_mul_eq_one (-(↑u⁻¹ : R) ^ 2) (by linear_combination hv2)
  -- so the sum of the other two roots is determined by each of them
  have hG : 4 * (x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) + W.b₂ * (x₁ + x₂) + 2 * W.b₄ = 0 :=
    hx.mul_right_eq_zero.mp (by linear_combination f₁ - f₂)
  ext
  · rw [variableChange_a₁, freyCurve_a₁, toLegendre_u, toLegendre_s]
    linear_combination -((↑u⁻¹ : R) * W.a₁) * hi
  · rw [variableChange_a₂, freyCurve_a₂, toLegendre_u, toLegendre_s, toLegendre_r]
    linear_combination (-((↑u⁻¹ : R) ^ 2 * (W.a₂ * (2 * ↑h2.unit⁻¹ + 1) +
      W.a₁ ^ 2 * ↑h2.unit⁻¹))) * hi - hv2 - (↑h2.unit⁻¹ : R) ^ 2 * (↑u⁻¹ : R) ^ 2 * hb₂
  · rw [variableChange_a₃, freyCurve_a₃, toLegendre_u, toLegendre_r, toLegendre_t]
    linear_combination (↑u⁻¹ : R) ^ 3 * hψ₁
  · rw [variableChange_a₄, freyCurve_a₄, toLegendre_u, toLegendre_s, toLegendre_r, toLegendre_t]
    linear_combination (↑u⁻¹ : R) ^ 4 * ((↑h2.unit⁻¹ : R) ^ 2 * hG +
      (-(2 * ↑h2.unit⁻¹ + 1) * (W.a₄ + 2 * W.a₂ * x₁ + x₁ ^ 2 + x₁ * x₂ + x₂ ^ 2) -
        ↑h2.unit⁻¹ * (W.a₁ * W.a₃ + W.a₁ ^ 2 * x₁) + W.a₁ * y₁) * hi -
      2 * (↑h2.unit⁻¹ : R) ^ 2 * x₁ * hb₂ - 2 * (↑h2.unit⁻¹ : R) ^ 2 * hb₄) -
      (W.b₂ * ↑h2.unit⁻¹ ^ 2 + 2 * x₁ + x₂) * (↑u⁻¹ : R) ^ 2 * hv2
  · rw [variableChange_a₆, freyCurve_a₆, toLegendre_u, toLegendre_r, toLegendre_t]
    linear_combination -(↑u⁻¹ : R) ^ 6 * h₁

/-- If `ψ₂` vanishes at the coordinate pairs `(x₁, y₁)` and `(x₂, y₂)` and `x₂ - x₁ = u²`, the
change of variables `toLegendre` with centre `(x₁, y₁)` carries `(x₂, y₂)` to `(1, 0)`:
`u² · 1 + r = x₂` and `u³ · 0 + u² s · 1 + t = y₂`. Neither pair need lie on `W`. -/
theorem toLegendre_one_zero (hψ₁ : W.ψ₂.evalEval x₁ y₁ = 0) (hψ₂ : W.ψ₂.evalEval x₂ y₂ = 0)
    (hu : x₂ - x₁ = u ^ 2) :
    ((W.toLegendre h2 u x₁ y₁).u : R) ^ 2 + (W.toLegendre h2 u x₁ y₁).r = x₂ ∧
      ((W.toLegendre h2 u x₁ y₁).u : R) ^ 2 * (W.toLegendre h2 u x₁ y₁).s +
        (W.toLegendre h2 u x₁ y₁).t = y₂ := by
  rw [ψ₂, Affine.evalEval_polynomialY] at hψ₁ hψ₂
  have hi : 2 * (↑h2.unit⁻¹ : R) = 1 := h2.mul_val_inv
  simp only [toLegendre_u, toLegendre_r, toLegendre_s, toLegendre_t]
  refine ⟨by linear_combination -hu, ?_⟩
  linear_combination -(↑h2.unit⁻¹ : R) * hψ₂ + ↑h2.unit⁻¹ * hψ₁ + W.a₁ * ↑h2.unit⁻¹ * hu +
    (y₂ - y₁) * hi

/-- **Uniqueness of Legendre form.** A change of variables with scaling `u` carrying `W` to a
curve `freyCurve 1 B` and `(x₁, y₁)` to `(0, 0)` (that is, with `r = x₁` and `t = y₁`) is
`toLegendre`. -/
theorem eq_toLegendre {C : VariableChange R} (hu : C.u = u) (hr : C.r = x₁) (ht : C.t = y₁)
    {B : R} (hC : C • W = freyCurve 1 B) : C = W.toLegendre h2 u x₁ y₁ := by
  have h₁ : (C • W).a₁ = 0 := by simp [hC]
  rw [variableChange_a₁, (Units.isUnit _).mul_right_eq_zero] at h₁
  have hi : 2 * (↑h2.unit⁻¹ : R) = 1 := h2.mul_val_inv
  ext : 1
  · rw [toLegendre_u, hu]
  · rw [toLegendre_r, hr]
  · rw [toLegendre_s]
    linear_combination ↑h2.unit⁻¹ * h₁ - C.s * hi
  · rw [toLegendre_t, ht]

include h2 in
/-- **Legendre form.** Let `(x₁, y₁)` and `(x₂, y₂)` be points of `W` at which the `2`-division
polynomial `ψ₂` vanishes, with `x₂ - x₁ = u²` for a unit `u`, over a ring in which `2` is a unit.
Then exactly one change of variables with scaling `u` carries `W` to a Legendre form
`y² = x (x - 1) (x - λ)` (a curve `freyCurve 1 B`, with `B = -λ`), `(x₁, y₁)` to `(0, 0)` and
`(x₂, y₂)` to `(1, 0)`. A change of variables with scaling `u` multiplies the invariant
differential by `u`, so this is the Legendre normalisation of the triple `((x₁, y₁), (x₂, y₂), ω)`,
for the differential `ω` that is `u` times the invariant differential of `W`. -/
theorem existsUnique_variableChange_legendre (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hψ₁ : W.ψ₂.evalEval x₁ y₁ = 0)
    (hψ₂ : W.ψ₂.evalEval x₂ y₂ = 0) (hu : x₂ - x₁ = u ^ 2) :
    ∃! C : VariableChange R, C.u = u ∧ C.r = x₁ ∧ C.t = y₁ ∧ (C.u : R) ^ 2 + C.r = x₂ ∧
      (C.u : R) ^ 2 * C.s + C.t = y₂ ∧ ∃ B : R, C • W = freyCurve 1 B :=
  ⟨W.toLegendre h2 u x₁ y₁, ⟨toLegendre_u .., toLegendre_r .., toLegendre_t ..,
    (toLegendre_one_zero h2 u hψ₁ hψ₂ hu).1, (toLegendre_one_zero h2 u hψ₁ hψ₂ hu).2, _,
      toLegendre_smul h2 u h₁ h₂ hψ₁ hψ₂ hu⟩,
    fun _ ⟨hu, hr, ht, _, _, _, hC⟩ ↦ eq_toLegendre h2 u hu hr ht hC⟩

/-- For an elliptic `W`, a change of variables with scaling `u` carrying `W` to a Legendre form,
`(x₁, y₁)` to `(0, 0)` and `(x₂, y₂)` to `(1, 0)` exists exactly when these are points of `W` at
which `ψ₂` vanishes and `x₂ - x₁ = u²`. The ring is then automatically one in which `2` is a unit
(`isUnit_two_of_evalEval_ψ₂_eq_zero`). -/
theorem exists_variableChange_legendre_iff [W.IsElliptic] :
    (∃ C : VariableChange R, C.u = u ∧ C.r = x₁ ∧ C.t = y₁ ∧ (C.u : R) ^ 2 + C.r = x₂ ∧
      (C.u : R) ^ 2 * C.s + C.t = y₂ ∧ ∃ B : R, C • W = freyCurve 1 B) ↔
      W.toAffine.Equation x₁ y₁ ∧ W.toAffine.Equation x₂ y₂ ∧ W.ψ₂.evalEval x₁ y₁ = 0 ∧
        W.ψ₂.evalEval x₂ y₂ = 0 ∧ x₂ - x₁ = u ^ 2 := by
  refine ⟨fun ⟨C, hu, hr, ht, hx₂, hy₂, B, hC⟩ ↦ ?_, fun ⟨h₁, h₂, hψ₁, hψ₂, hu⟩ ↦ ?_⟩
  · -- `(0, 0)` and `(1, 0)` are points of order two on `freyCurve 1 B`, and `C` carries
    -- `(x₁, y₁)` and `(x₂, y₂)` to them
    have e₀ := (Affine.variableChange_equation W C 0 0).mpr
      (by rw [hC]; exact Affine.equation_zero.mpr (freyCurve_a₆ 1 B))
    have e₁ := (Affine.variableChange_equation W C 1 0).mpr
      (by rw [hC, Affine.equation_iff]; simp)
    have p₀ := Affine.variableChange_evalEval_polynomialY W C 0 0
    have p₁ := Affine.variableChange_evalEval_polynomialY W C 1 0
    simp only [mul_zero, mul_one, zero_add, add_zero, hC] at e₀ e₁ p₀ p₁
    rw [hr, ht] at e₀ p₀
    rw [hx₂, hy₂] at e₁ p₁
    refine ⟨e₀, e₁, ?_, ?_, by rw [← hx₂, hr, hu, add_sub_cancel_right]⟩
    · rw [ψ₂, p₀, Affine.evalEval_polynomialY]
      simp
    · rw [ψ₂, p₁, Affine.evalEval_polynomialY]
      simp
  · have h2 := W.isUnit_two_of_evalEval_ψ₂_eq_zero hψ₁ hψ₂ (hu ▸ (u.isUnit.pow 2))
    exact (existsUnique_variableChange_legendre h2 u h₁ h₂ hψ₁ hψ₂ hu).exists

end CommRing

/-! ### Legendre form over a field -/

section Field

variable {F : Type*} [Field F] {W : WeierstrassCurve F}

/-- **Legendre form.** If `2 ≠ 0`, the `2`-division polynomial of `W` factors as
`4 (X - e₁) (X - e₂) (X - e₃)` with `e₁ ≠ e₂`, and `e₂ - e₁ = u²`, then a change of variables takes
`W` to the Legendre form `y² = x (x - 1) (x - λ)` with `λ = (e₃ - e₁) / (e₂ - e₁)`, that is to
`freyCurve 1 (-λ)`. It completes the square in `y`, moves `e₁` to the origin and scales `x` by
`u²`: it is `toLegendre` centred at the point `(e₁, -(a₁e₁ + a₃)/2)` of order two. -/
theorem exists_variableChange_smul_eq_freyCurve_one (h2 : (2 : F) ≠ 0) {e₁ e₂ e₃ u : F}
    (h : W.twoTorsionPolynomial.toPoly = C 4 * (X - C e₁) * (X - C e₂) * (X - C e₃))
    (he : e₂ ≠ e₁) (hu : u ^ 2 = e₂ - e₁) :
    ∃ C : VariableChange F, C • W = freyCurve 1 ((e₁ - e₃) / (e₂ - e₁)) := by
  -- the coefficients of the `2`-division polynomial are the elementary symmetric functions
  rw [Cubic.C_mul_prod_X_sub_C_eq, Cubic.toPoly_injective, twoTorsionPolynomial] at h
  simp only [Cubic.mk.injEq, true_and] at h
  obtain ⟨hb₂, hb₄, hb₆⟩ := h
  have hα : e₂ - e₁ ≠ 0 := sub_ne_zero.mpr he
  have hu0 : u ≠ 0 := by rintro rfl; exact hα (by rw [← hu]; ring)
  -- `(eᵢ, -(a₁eᵢ + a₃)/2)` is a point of `W` at which `ψ₂` vanishes
  have hψ (e : F) : W.ψ₂.evalEval e (-(W.a₁ * e + W.a₃) / 2) = 0 := by
    rw [ψ₂, Affine.evalEval_polynomialY]
    field_simp
    ring
  have heq (e : F) (he : (e - e₁) * (e - e₂) * (e - e₃) = 0) :
      W.toAffine.Equation e (-(W.a₁ * e + W.a₃) / 2) := by
    rw [Affine.equation_iff]
    field_simp
    have hb₂' : W.b₂ = W.a₁ ^ 2 + 4 * W.a₂ := (rfl)
    have hb₄' : W.b₄ = 2 * W.a₄ + W.a₁ * W.a₃ := (rfl)
    have hb₆' : W.b₆ = W.a₃ ^ 2 + 4 * W.a₆ := (rfl)
    linear_combination -(e ^ 2 * (hb₂ - hb₂') + e * (hb₄ - 2 * hb₄') + hb₆ - hb₆') - 4 * he
  refine ⟨W.toLegendre h2.isUnit (Units.mk0 u hu0) e₁ (-(W.a₁ * e₁ + W.a₃) / 2), ?_⟩
  rw [toLegendre_smul h2.isUnit _ (heq e₁ (by ring)) (heq e₂ (by ring)) (hψ e₁) (hψ e₂)
    (by rw [Units.val_mk0, hu])]
  congr 1
  simp only [hb₂, Units.val_inv_eq_inv_val, Units.val_mk0, IsUnit.unit_spec, inv_pow, hu]
  field_simp
  ring

/-- **Legendre form over a finite separable extension.** Away from characteristic `2`, an
elliptic curve over `K` becomes isomorphic to a curve `y² = x (x - 1) (x + B)` over a finite
separable extension `L` of `K`: one obtained by adjoining the roots `e₁, e₂, e₃` of its
`2`-division polynomial and a square root of `e₂ - e₁`. -/
theorem exists_variableChange_smul_baseChange_eq_freyCurve_one {K : Type u} [Field K]
    (W : WeierstrassCurve K) [W.IsElliptic] (h2 : (2 : K) ≠ 0) :
    ∃ (L : Type u) (_ : Field L) (_ : Algebra K L) (_ : FiniteDimensional K L)
      (_ : Algebra.IsSeparable K L) (C : VariableChange L) (B : L),
      C • W.baseChange L = freyCurve 1 B := by
  set P := W.twoTorsionPolynomial
  have hPa : P.a = 4 := by simp only [P, twoTorsionPolynomial]
  have ha : P.a ≠ 0 := by
    rw [hPa, show (4 : K) = 2 * 2 by norm_num]
    exact mul_ne_zero h2 h2
  -- the roots of the `2`-division polynomial, in its splitting field `L₁`
  let L₁ := SplittingField P.toPoly
  have hsplit : (P.toPoly.map (algebraMap K L₁)).Splits := SplittingField.splits P.toPoly
  obtain ⟨e₁, e₂, e₃, h3⟩ := (Cubic.splits_iff_roots_eq_three ha).mp hsplit
  have hdisc : P.discr ≠ 0 := by
    rw [twoTorsionPolynomial_discr]
    exact mul_ne_zero (by rw [show (16 : K) = 2 ^ 4 by norm_num]; exact pow_ne_zero 4 h2)
      W.isUnit_Δ.ne_zero
  obtain ⟨h12, -, -⟩ := (Cubic.discr_ne_zero_iff_roots_ne ha h3).mp hdisc
  have hsep₁ : P.toPoly.Separable := by
    have hnd := (Cubic.discr_ne_zero_iff_roots_nodup ha hsplit).mp hdisc
    rw [Cubic.roots, Cubic.map_toPoly, nodup_roots_iff_of_splits
      ((Polynomial.map_ne_zero_iff (algebraMap K L₁).injective).mpr
        (Cubic.ne_zero_of_a_ne_zero ha)) hsplit] at hnd
    exact (separable_map _).mp hnd
  have : IsGalois K L₁ := IsGalois.of_separable_splitting_field hsep₁
  -- a square root of `e₂ - e₁`, in the splitting field `L` of `X² - (e₂ - e₁)` over `L₁`
  have h2₁ : ((2 : ℕ) : L₁) ≠ 0 := by
    rw [Nat.cast_ofNat, ← map_ofNat (algebraMap K L₁)]
    exact (_root_.map_ne_zero _).mpr h2
  let L := SplittingField (X ^ 2 - C (e₂ - e₁) : L₁[X])
  have : IsGalois L₁ L := IsGalois.of_separable_splitting_field
    (separable_X_pow_sub_C _ h2₁ (sub_ne_zero.mpr (Ne.symm h12)))
  have : Algebra.IsSeparable K L := Algebra.IsSeparable.trans K L₁ L
  have : FiniteDimensional K L := Module.Finite.trans L₁ L
  obtain ⟨u, hu⟩ := (SplittingField.splits (X ^ 2 - C (e₂ - e₁) : L₁[X])).exists_eval_eq_zero
    (by rw [degree_map, degree_X_pow_sub_C two_pos]; norm_num)
  simp only [Polynomial.map_sub, Polynomial.map_pow, map_X, map_C, eval_sub, eval_pow, eval_X,
    eval_C, sub_eq_zero] at hu
  -- the factorisation of the `2`-division polynomial of the base change to `L`
  set ψ := algebraMap L₁ L
  have hfac : (W.baseChange L).twoTorsionPolynomial.toPoly =
      C 4 * (X - C (ψ e₁)) * (X - C (ψ e₂)) * (X - C (ψ e₃)) := by
    have h := congrArg (Polynomial.map ψ) (Cubic.eq_prod_three_roots ha h3)
    rw [Cubic.map_toPoly, Polynomial.map_map, ← IsScalarTower.algebraMap_eq] at h
    simp only [Polynomial.map_mul, Polynomial.map_sub, map_X, map_C] at h
    rw [hPa, map_ofNat, map_ofNat] at h
    have hmap : (W.baseChange L).twoTorsionPolynomial = Cubic.map (algebraMap K L) P := by
      simp only [twoTorsionPolynomial, Cubic.map, baseChange, map_b₂, map_b₄, map_b₆, map_mul,
        map_ofNat, P]
    rw [hmap, Cubic.map_toPoly, h]
  have he : ψ e₂ ≠ ψ e₁ := fun h ↦ h12 (ψ.injective h).symm
  have h2L : (2 : L) ≠ 0 := by
    rw [← map_ofNat (algebraMap K L) 2]
    exact (_root_.map_ne_zero _).mpr h2
  obtain ⟨C, hC⟩ := exists_variableChange_smul_eq_freyCurve_one h2L hfac he (by rw [hu, map_sub])
  exact ⟨L, _, _, ‹_›, ‹_›, C, _, hC⟩

end Field

/-! ### The universal Legendre curve over `ℤ[1/2][λ, 1/λ(λ - 1)]` -/

namespace UniversalLegendre

/-- The ring `ℤ[1/2][λ, 1/λ(λ - 1)]`: the polynomial ring `ℤ[λ]` localised away from
`2λ(λ - 1)`. -/
abbrev Ring : Type := Localization.Away (2 * X * (X - 1) : ℤ[X])

/-- The parameter `λ` of `ℤ[1/2][λ, 1/λ(λ - 1)]`. -/
noncomputable abbrev param : Ring := algebraMap ℤ[X] Ring X

/-- The **universal Legendre curve** `y² = x (x - 1) (x - λ)`, over `ℤ[1/2][λ, 1/λ(λ - 1)]`, with
its points `(0, 0)` and `(1, 0)` of order two. Let `W` be an elliptic Weierstrass curve with
points `(x₁, y₁)` and `(x₂, y₂)` of order two, and `u` a unit with `x₂ - x₁ = u²`. Then there is
exactly one pair of a ring homomorphism and a change of variables with scaling `u` carrying `W` to
the base change of this curve along it, `(x₁, y₁)` to `(0, 0)` and `(x₂, y₂)` to `(1, 0)`
(`existsUnique_legendre`). -/
-- A `def` rather than an `abbrev`, so that `map_lift` rather than `TauCeti.map_freyCurve` is the
-- simp normal form of its base changes.
noncomputable def curve : WeierstrassCurve Ring := freyCurve 1 (-param)

/-- The universal Legendre curve is the Legendre form `y² = x (x - 1) (x - λ)` with parameter `λ`.
Not `@[simp]`, so that `map_lift` stays the simp normal form of its base changes. -/
theorem curve_def : curve = freyCurve 1 (-param) := (rfl)

variable {R : Type*} [CommRing R]

/-- The universal Legendre curve is an elliptic curve. -/
instance : curve.IsElliptic :=
  (isElliptic_freyCurve_one_neg_iff (l := param)).mpr <| by
    have h := IsLocalization.Away.algebraMap_isUnit (S := Ring) (2 * X * (X - 1) : ℤ[X])
    rwa [map_mul, map_mul, map_sub, map_ofNat, map_one] at h

/-- Two ring homomorphisms out of `ℤ[1/2][λ, 1/λ(λ - 1)]` are equal as soon as they agree on the
parameter `λ`. -/
-- `high`, as for Mathlib's `Localization.algHom_ext`, so that `ext` tries this lemma before
-- `RingHom.ext`.
@[ext high]
theorem Ring.ringHom_ext {S : Type*} [Semiring S] {f g : Ring →+* S} (h : f param = g param) :
    f = g :=
  IsLocalization.ringHom_ext (.powers (2 * X * (X - 1) : ℤ[X])) <|
    Polynomial.ringHom_ext' (RingHom.ext_int _ _) (by simpa using h)

/-- The **classifying homomorphism** `ℤ[1/2][λ, 1/λ(λ - 1)] →+* R` of an element `l` of `R` with
`2l(l - 1)` a unit, sending `λ` to `l`. -/
noncomputable def lift {l : R} (h : IsUnit (2 * l * (l - 1))) : Ring →+* R :=
  IsLocalization.Away.lift (2 * X * (X - 1) : ℤ[X])
    (g := Polynomial.eval₂RingHom (Int.castRingHom R) l) (by simpa using h)

/-- Restricted to the polynomial ring `ℤ[λ]`, the classifying homomorphism substitutes `l` for
`λ`. Use this shape when composing ring maps and `lift_algebraMap` when rewriting underneath an
application. -/
theorem lift_comp_algebraMap {l : R} (h : IsUnit (2 * l * (l - 1))) :
    (lift h).comp (algebraMap ℤ[X] Ring) = Polynomial.eval₂RingHom (Int.castRingHom R) l :=
  IsLocalization.Away.lift_comp ..

/-- The pointwise form of `lift_comp_algebraMap`. -/
theorem lift_algebraMap {l : R} (h : IsUnit (2 * l * (l - 1))) (p : ℤ[X]) :
    lift h (algebraMap ℤ[X] Ring p) = Polynomial.eval₂RingHom (Int.castRingHom R) l p :=
  IsLocalization.Away.lift_eq ..

@[simp]
theorem lift_param {l : R} (h : IsUnit (2 * l * (l - 1))) : lift h param = l := by
  simp [lift]

/-- The classifying homomorphism is natural in the base ring: followed by a ring homomorphism
`φ : R →+* S`, the classifying homomorphism of `l` is that of `φ l`. -/
theorem comp_lift {S : Type*} [CommRing S] (φ : R →+* S) {l : R} (h : IsUnit (2 * l * (l - 1))) :
    φ.comp (lift h) = lift (l := φ l)
      (by rw [← map_ofNat φ 2, ← map_one φ, ← map_sub, ← map_mul, ← map_mul]; exact h.map φ) := by
  ext
  simp

/-- The classifying homomorphism is unique: a ring homomorphism out of `ℤ[1/2][λ, 1/λ(λ - 1)]`
sending `λ` to `l` is `lift`. -/
theorem eq_lift {l : R} (h : IsUnit (2 * l * (l - 1))) {f : Ring →+* R} (hf : f param = l) :
    f = lift h := by
  ext
  rw [hf, lift_param]

/-- Every Legendre form `y² = x (x - 1) (x - l)` with `2l(l - 1)` a unit is the base change of the
universal Legendre curve along its classifying homomorphism. -/
@[simp]
theorem map_lift {l : R} (h : IsUnit (2 * l * (l - 1))) :
    curve.map (lift h) = freyCurve 1 (-l) := by
  simp [curve]

variable {W : WeierstrassCurve R} {x₁ y₁ x₂ y₂ : R} (u : Rˣ)

/-- **The universal Legendre curve classifies Legendre normalisations.** Let `W` be an elliptic
Weierstrass curve, `(x₁, y₁)` and `(x₂, y₂)` points of `W` at which `ψ₂` vanishes, and `u` a unit
with `x₂ - x₁ = u²`. Then there is exactly one pair of a ring homomorphism
`f : ℤ[1/2][λ, 1/λ(λ - 1)] →+* R` and a change of variables `C` with scaling `u` such that `C`
carries `W` to the base change of the universal Legendre curve along `f`, `(x₁, y₁)` to `(0, 0)`
and `(x₂, y₂)` to `(1, 0)`. This is an equation-level statement: it models the Legendre structures
of Katz and Mazur only after identifying the two points with a basis of `E[2]` and `u` with the
differential `u` times the invariant differential of `W`. -/
theorem existsUnique_legendre [W.IsElliptic] (h₁ : W.toAffine.Equation x₁ y₁)
    (h₂ : W.toAffine.Equation x₂ y₂) (hψ₁ : W.ψ₂.evalEval x₁ y₁ = 0)
    (hψ₂ : W.ψ₂.evalEval x₂ y₂ = 0) (hu : x₂ - x₁ = u ^ 2) :
    ∃! p : (Ring →+* R) × VariableChange R, p.2.u = u ∧ p.2.r = x₁ ∧ p.2.t = y₁ ∧
      (p.2.u : R) ^ 2 + p.2.r = x₂ ∧ (p.2.u : R) ^ 2 * p.2.s + p.2.t = y₂ ∧
        p.2 • W = curve.map p.1 := by
  have h2 := W.isUnit_two_of_evalEval_ψ₂_eq_zero hψ₁ hψ₂ (hu ▸ (u.isUnit.pow 2))
  obtain ⟨C, ⟨hCu, hCr, hCt, hCx, hCy, B, hC⟩, hCuniq⟩ :=
    existsUnique_variableChange_legendre h2 u h₁ h₂ hψ₁ hψ₂ hu
  have hB : IsUnit (2 * -B * (-B - 1)) := by
    rw [← isElliptic_freyCurve_one_neg_iff, neg_neg, ← hC]
    infer_instance
  refine ⟨(lift hB, C), ⟨hCu, hCr, hCt, hCx, hCy, ?_⟩,
    fun ⟨f, D⟩ ⟨hDu, hDr, hDt, hDx, hDy, hD⟩ ↦ ?_⟩
  · rw [hC, map_lift, neg_neg]
  rw [curve_def, map_freyCurve, map_one, map_neg] at hD
  obtain rfl : D = C := hCuniq D ⟨hDu, hDr, hDt, hDx, hDy, _, hD⟩
  -- comparing `a₄` of the two Legendre forms gives `f λ = -B`
  have hf : f param = -B := by simpa using congrArg a₄ (hD.symm.trans hC)
  rw [eq_lift hB hf]

end UniversalLegendre

end WeierstrassCurve

end
