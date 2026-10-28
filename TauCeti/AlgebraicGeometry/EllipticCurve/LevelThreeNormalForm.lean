/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.Away.Basic
public import TauCeti.AlgebraicGeometry.EllipticCurve.DivisionPolynomial.Basic
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Formula.VariableChange

/-!
# Elliptic curves with a basis of their `3`-torsion

For `μ : R`, the **level-three normal form** is the Weierstrass curve

`Y² + 3μXY + (μ³ - 1)Y = X³`,

that is, `a₁ = 3μ`, `a₃ = μ³ - 1` and `a₂ = a₄ = a₆ = 0`
(`WeierstrassCurve.levelThreeNormalForm`). Its invariants are

  `c₄ = 9μ (μ³ + 8)`, `Δ = 27 (μ³ - 1)³`, `j = 27μ³ (μ³ + 8)³ / (μ³ - 1)³`,

so it is elliptic exactly when `3` and `μ³ - 1` are units. The point `P = (0, 0)` is a flex with
tangent `Y = 0`, so it has order `3`. If `ζ² + ζ + 1 = 0`, the point

`Q = (-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`

also lies on the curve and has order `3`; since `μ² + μ + 1` divides `μ³ - 1`, its `x`-coordinate
differs from that of `P` in every fibre, so `P` and `Q` form a basis of the `3`-torsion.

Conversely, let `W` be a Weierstrass curve over a commutative ring `R` in which `3` is a unit, and
let `P = (x₁, y₁)` and `Q = (x₂, y₂)` be points of `W` at which the `3`-division polynomial `Ψ₃`
vanishes, the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃` is a unit, and with `x₂ - x₁` a unit.
Over a field these say that `P` and `Q` have order `3` and that `Q` is not `±P`, so that `(P, Q)`
is a basis of the `3`-torsion; over a ring they say this at every point of `Spec R`
(`WeierstrassCurve.IsThreeTorsionBasis`). Then exactly one change of variables,
`WeierstrassCurve.toLevelThreeNormalForm`, carries `W` to a level-three normal form, `P` to
`(0, 0)` and `Q` to the point above
(`WeierstrassCurve.existsUnique_variableChange_levelThreeNormalForm`). The Legendre
form attached to a basis of the `2`-torsion is unique only after the choice of an invariant
differential, because `[-1]` fixes every point of order `2`. No such choice is needed here:
`[-1]` moves a basis of the `3`-torsion, and the scaling `u` is determined by `P` and `Q`.

The construction moves `P` to the origin with horizontal tangent, after which `W` is
`Y² + A₁XY + A₃Y = X³` (`a₂` vanishes because `Ψ₃(x₁) = 0`), and then rescales. In those
coordinates write `Q = (X, Y)` and `v = 3A₃ + A₁X`. The scaling is `u = v / (3X)`, and

`μ = A₁X / v`,  `ζ = (A₁X + 3Y) / v`.

The relation `v² = -3 ψ₂(Q)²` on the curve shows that `v` is a unit, and
`(A₁X + 3Y)² + (A₁X + 3Y) v + v² = 0` gives `ζ² + ζ + 1 = 0`.

Finally, `WeierstrassCurve.UniversalLevelThree.curve` is the level-three normal form over
`ℤ[μ, ζ] / (ζ² + ζ + 1)` localised away from the discriminant, that is over
`ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. It is elliptic, carries the basis `(P, Q)` of its `3`-torsion, and
every Weierstrass curve with such a basis over a ring in which `3` is a unit is isomorphic to its
base change along exactly one ring homomorphism
(`WeierstrassCurve.UniversalLevelThree.classifyingHom`), by exactly one change of variables matching
the bases (`WeierstrassCurve.UniversalLevelThree.existsUnique_lift`).

## Main definitions

* `WeierstrassCurve.levelThreeNormalForm μ`: the curve `Y² + 3μXY + (μ³ - 1)Y = X³`.
* `WeierstrassCurve.IsThreeTorsionBasis W x₁ y₁ x₂ y₂`: `(x₁, y₁)` and `(x₂, y₂)` form a basis of
  the `3`-torsion of `W` in every fibre, over a ring in which `3` is a unit.
* `WeierstrassCurve.toLevelThreeNormalForm h`, `WeierstrassCurve.levelThreeParameter h`,
  `WeierstrassCurve.levelThreeRootOfUnity h`: the change of variables carrying such a basis to
  level-three normal form, and the `μ` and `ζ` it reaches.
* `WeierstrassCurve.UniversalLevelThree.Ring`, `WeierstrassCurve.UniversalLevelThree.curve`: the
  ring `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` and the level-three normal form over it.
* `WeierstrassCurve.UniversalLevelThree.lift`: the classifying homomorphism of a level-three normal
  form with a chosen root of `ζ² + ζ + 1`.
* `WeierstrassCurve.UniversalLevelThree.classifyingHom h`: the classifying homomorphism of a
  Weierstrass curve with a basis of its `3`-torsion.

## Main results

* `WeierstrassCurve.levelThreeNormalForm_Δ`, `WeierstrassCurve.levelThreeNormalForm_j`: its
  discriminant and `j`-invariant.
* `WeierstrassCurve.equation_levelThreeNormalForm_basisPoint`,
  `WeierstrassCurve.eval_Ψ₃_levelThreeNormalForm_basisPoint`: the point `Q` lies on the curve and
  has order `3`.
* `WeierstrassCurve.toLevelThreeNormalForm_smul`, `WeierstrassCurve.eq_toLevelThreeNormalForm`:
  `toLevelThreeNormalForm h` reaches a level-three normal form, and is the only change of variables
  doing so that matches the bases.
* `WeierstrassCurve.existsUnique_variableChange_levelThreeNormalForm`: a curve with a basis of its
  `3`-torsion is a unique change of variables away from a level-three normal form.
* `WeierstrassCurve.toLevelThreeNormalForm_map`: the change of variables commutes with base change.
* `WeierstrassCurve.exists_variableChange_levelThreeNormalForm_iff`: for elliptic `W` the
  hypotheses are also necessary.
* `WeierstrassCurve.isUnit_three_of_eval_Ψ₃_eq_zero`: on an elliptic curve, two roots of `Ψ₃`
  differing by a unit force `3` to be a unit.
* `WeierstrassCurve.UniversalLevelThree.existsUnique_lift`: the universal property of the
  level-three normal form over `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`.
* `WeierstrassCurve.UniversalLevelThree.map_lift`, `WeierstrassCurve.UniversalLevelThree.eq_lift`,
  `WeierstrassCurve.UniversalLevelThree.comp_lift`: the classifying homomorphism of an elliptic
  level-three normal form with a root of `ζ² + ζ + 1`, its uniqueness and its naturality.
* `WeierstrassCurve.UniversalLevelThree.comp_classifyingHom`: the classifying homomorphism of a
  basis of the `3`-torsion is natural in the base ring.

## Implementation notes

`WeierstrassCurve.toLevelThreeNormalForm` and its lemmas follow `WeierstrassCurve.toTateNormalForm`,
and the `UniversalLevelThree` namespace follows the layout of the `UniversalTate` namespace, in
`TauCeti/AlgebraicGeometry/EllipticCurve/TateNormalForm.lean`: the ring is `Localization.Away` of
the discriminant of a polynomial curve, and `Ring.ringHom_ext`, `lift`, `map_lift`, `comp_lift` and
`eq_lift` correspond to the lemmas of the same names there. The polynomial ring is replaced by its
quotient `ℤ[μ, ζ] / (ζ² + ζ + 1)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, 2.2.10 and 2.2.11 (naive level-three structures as
  rigidifiers).
* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], Appendix A, Proposition 1.3,
  for the normal form `Y² + a₁XY + a₃Y = X³` at a point of order `3`.
-/

public section

namespace WeierstrassCurve

variable {R : Type*} [CommRing R]

/-! ### The level-three normal form -/

/-- The Weierstrass curve `Y² + 3μXY + (μ³ - 1)Y = X³` in **level-three normal form**:
`a₁ = 3μ`, `a₃ = μ³ - 1` and `a₂ = a₄ = a₆ = 0`. With a root `ζ` of `ζ² + ζ + 1`, the points
`(0, 0)` and `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` form a basis of its `3`-torsion. -/
def levelThreeNormalForm (μ : R) : WeierstrassCurve R where
  a₁ := 3 * μ
  a₂ := 0
  a₃ := μ ^ 3 - 1
  a₄ := 0
  a₆ := 0

variable (μ : R)

@[simp] theorem levelThreeNormalForm_a₁ : (levelThreeNormalForm μ).a₁ = 3 * μ := (rfl)
@[simp] theorem levelThreeNormalForm_a₂ : (levelThreeNormalForm μ).a₂ = 0 := (rfl)
@[simp] theorem levelThreeNormalForm_a₃ : (levelThreeNormalForm μ).a₃ = μ ^ 3 - 1 := (rfl)
@[simp] theorem levelThreeNormalForm_a₄ : (levelThreeNormalForm μ).a₄ = 0 := (rfl)
@[simp] theorem levelThreeNormalForm_a₆ : (levelThreeNormalForm μ).a₆ = 0 := (rfl)

@[simp]
theorem levelThreeNormalForm_b₂ : (levelThreeNormalForm μ).b₂ = 9 * μ ^ 2 := by
  simp only [b₂, levelThreeNormalForm_a₁, levelThreeNormalForm_a₂]
  ring

@[simp]
theorem levelThreeNormalForm_b₄ : (levelThreeNormalForm μ).b₄ = 3 * μ * (μ ^ 3 - 1) := by
  simp [b₄]

@[simp]
theorem levelThreeNormalForm_b₆ : (levelThreeNormalForm μ).b₆ = (μ ^ 3 - 1) ^ 2 := by
  simp [b₆, sq]

@[simp]
theorem levelThreeNormalForm_b₈ : (levelThreeNormalForm μ).b₈ = 0 := by
  simp [b₈]

@[simp]
theorem levelThreeNormalForm_c₄ : (levelThreeNormalForm μ).c₄ = 9 * μ * (μ ^ 3 + 8) := by
  rw [c₄, levelThreeNormalForm_b₂, levelThreeNormalForm_b₄]
  ring

/-- The discriminant of the level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³` is
`27 (μ³ - 1)³`. -/
@[simp]
theorem levelThreeNormalForm_Δ : (levelThreeNormalForm μ).Δ = 27 * (μ ^ 3 - 1) ^ 3 := by
  rw [Δ, levelThreeNormalForm_b₂, levelThreeNormalForm_b₄, levelThreeNormalForm_b₆,
    levelThreeNormalForm_b₈]
  ring

/-- The level-three normal form is elliptic exactly when `3` and `μ³ - 1` are units. -/
theorem isElliptic_levelThreeNormalForm_iff :
    (levelThreeNormalForm μ).IsElliptic ↔ IsUnit (3 : R) ∧ IsUnit (μ ^ 3 - 1) := by
  rw [isElliptic_iff, levelThreeNormalForm_Δ, show (27 : R) = 3 ^ 3 by norm_num, IsUnit.mul_iff,
    isUnit_pow_iff three_ne_zero, isUnit_pow_iff three_ne_zero]

/-- The `j`-invariant of the level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³` is
`27μ³ (μ³ + 8)³ / (μ³ - 1)³`. -/
theorem levelThreeNormalForm_j {F : Type*} [Field F] (μ : F) [(levelThreeNormalForm μ).IsElliptic] :
    (levelThreeNormalForm μ).j = 27 * μ ^ 3 * (μ ^ 3 + 8) ^ 3 / (μ ^ 3 - 1) ^ 3 := by
  obtain ⟨h3, hμ⟩ := (isElliptic_levelThreeNormalForm_iff μ).mp inferInstance
  have h3 : (3 : F) ≠ 0 := h3.ne_zero
  have hμ : μ ^ 3 - 1 ≠ 0 := hμ.ne_zero
  rw [j_eq, levelThreeNormalForm_c₄, levelThreeNormalForm_Δ, show (27 : F) = 3 ^ 3 by norm_num]
  field_simp
  ring

/-- The point `(0, 0)` lies on the level-three normal form. -/
theorem equation_levelThreeNormalForm_zero : (levelThreeNormalForm μ).toAffine.Equation 0 0 :=
  Affine.equation_zero.mpr (levelThreeNormalForm_a₆ μ)

/-- On the level-three normal form the `3`-division polynomial `Ψ₃` vanishes at `0`: the origin is
a point of order `3`. -/
@[simp]
theorem eval_Ψ₃_levelThreeNormalForm_zero : (levelThreeNormalForm μ).Ψ₃.eval 0 = 0 := by
  simp [eval_Ψ₃]

/-- On the level-three normal form the `2`-division polynomial `ψ₂` takes the value `μ³ - 1` at
`(0, 0)`. -/
@[simp]
theorem evalEval_ψ₂_levelThreeNormalForm_zero :
    (levelThreeNormalForm μ).ψ₂.evalEval 0 0 = μ ^ 3 - 1 := by
  simp [ψ₂]

/-- If `ζ² + ζ + 1 = 0`, the point `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` lies on the level-three
normal form. -/
theorem equation_levelThreeNormalForm_basisPoint {ζ : R} (hζ : ζ ^ 2 + ζ + 1 = 0) :
    (levelThreeNormalForm μ).toAffine.Equation (-(μ ^ 2 + μ + 1))
      ((μ ^ 2 + μ + 1) * (μ - ζ)) := by
  rw [Affine.equation_iff]
  simp only [levelThreeNormalForm_a₁, levelThreeNormalForm_a₂, levelThreeNormalForm_a₃,
    levelThreeNormalForm_a₄, levelThreeNormalForm_a₆]
  linear_combination (μ ^ 2 + μ + 1) ^ 2 * hζ

/-- On the level-three normal form the `3`-division polynomial `Ψ₃` vanishes at `-(μ² + μ + 1)`:
the points above it have order `3`. -/
theorem eval_Ψ₃_levelThreeNormalForm_basisPoint :
    (levelThreeNormalForm μ).Ψ₃.eval (-(μ ^ 2 + μ + 1)) = 0 := by
  rw [eval_Ψ₃, levelThreeNormalForm_b₂, levelThreeNormalForm_b₄, levelThreeNormalForm_b₆,
    levelThreeNormalForm_b₈]
  ring

/-- On the level-three normal form the `2`-division polynomial `ψ₂` takes the value
`-(2ζ + 1)(μ² + μ + 1)` at `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. -/
theorem evalEval_ψ₂_levelThreeNormalForm_basisPoint (ζ : R) :
    (levelThreeNormalForm μ).ψ₂.evalEval (-(μ ^ 2 + μ + 1)) ((μ ^ 2 + μ + 1) * (μ - ζ)) =
      -(2 * ζ + 1) * (μ ^ 2 + μ + 1) := by
  rw [ψ₂, Affine.evalEval_polynomialY, levelThreeNormalForm_a₁, levelThreeNormalForm_a₃]
  ring

/-- The level-three normal form commutes with base change. -/
@[simp]
theorem map_levelThreeNormalForm {A : Type*} [CommRing A] (φ : R →+* A) :
    (levelThreeNormalForm μ).map φ = levelThreeNormalForm (φ μ) := by
  ext <;> simp [map_ofNat]

/-! ### Bases of the `3`-torsion -/

/-- The points `P = (x₁, y₁)` and `Q = (x₂, y₂)` form a **basis of the `3`-torsion** of `W` in every
fibre, over a ring in which `3` is a unit: they lie on `W`, the `3`-division polynomial `Ψ₃`
vanishes at both, the `2`-division polynomial `ψ₂ = 2Y + a₁X + a₃` is a unit at both, and
`x₂ - x₁` is a unit. Over a field these say that `P` and `Q` have order `3` and that `Q` is not
`±P`. -/
structure IsThreeTorsionBasis (W : WeierstrassCurve R) (x₁ y₁ x₂ y₂ : R) : Prop where
  /-- `3` is a unit. -/
  isUnit_three : IsUnit (3 : R)
  /-- `P` lies on `W`. -/
  equation_fst : W.toAffine.Equation x₁ y₁
  /-- `Q` lies on `W`. -/
  equation_snd : W.toAffine.Equation x₂ y₂
  /-- `Ψ₃` vanishes at `P`. -/
  eval_Ψ₃_fst : W.Ψ₃.eval x₁ = 0
  /-- `Ψ₃` vanishes at `Q`. -/
  eval_Ψ₃_snd : W.Ψ₃.eval x₂ = 0
  /-- `ψ₂` is a unit at `P`. -/
  isUnit_ψ₂_fst : IsUnit (W.ψ₂.evalEval x₁ y₁)
  /-- `ψ₂` is a unit at `Q`. -/
  isUnit_ψ₂_snd : IsUnit (W.ψ₂.evalEval x₂ y₂)
  /-- The `x`-coordinates of `P` and `Q` differ by a unit. -/
  isUnit_sub : IsUnit (x₂ - x₁)

variable {W : WeierstrassCurve R} {x₁ y₁ x₂ y₂ : R}

/-- A basis of the `3`-torsion remains one after base change. -/
theorem IsThreeTorsionBasis.map (h : W.IsThreeTorsionBasis x₁ y₁ x₂ y₂) {A : Type*} [CommRing A]
    (φ : R →+* A) : (W.map φ).IsThreeTorsionBasis (φ x₁) (φ y₁) (φ x₂) (φ y₂) where
  isUnit_three := by simpa only [map_ofNat] using h.isUnit_three.map φ
  equation_fst := h.equation_fst.map φ
  equation_snd := h.equation_snd.map φ
  eval_Ψ₃_fst := by rw [map_Ψ₃, Polynomial.eval_map_apply, h.eval_Ψ₃_fst, map_zero]
  eval_Ψ₃_snd := by rw [map_Ψ₃, Polynomial.eval_map_apply, h.eval_Ψ₃_snd, map_zero]
  isUnit_ψ₂_fst := by
    rw [map_ψ₂, Polynomial.map_mapRingHom_evalEval]
    exact h.isUnit_ψ₂_fst.map φ
  isUnit_ψ₂_snd := by
    rw [map_ψ₂, Polynomial.map_mapRingHom_evalEval]
    exact h.isUnit_ψ₂_snd.map φ
  isUnit_sub := by simpa using h.isUnit_sub.map φ

/-- **Roots of `Ψ₃` in characteristic `3`.** On an elliptic curve, if the `3`-division polynomial
`Ψ₃` vanishes at `x₁` and at `x₂` and `x₂ - x₁` is a unit, then `3` is a unit. Over a field of
characteristic `3`, the polynomial `Ψ₃ = b₂X³ + b₈` of a nonsingular curve has at most one root. -/
theorem isUnit_three_of_eval_Ψ₃_eq_zero [W.IsElliptic] (h₁ : W.Ψ₃.eval x₁ = 0)
    (h₂ : W.Ψ₃.eval x₂ = 0) (hx : IsUnit (x₂ - x₁)) : IsUnit (3 : R) := by
  rw [eval_Ψ₃] at h₁ h₂
  -- `b₂ (x₂ - x₁)³ = Ψ₃(x₂) - Ψ₃(x₁)` modulo `3`, so `3` divides `b₂`
  obtain ⟨β, hβ⟩ : (3 : R) ∣ W.b₂ := (hx.pow 3).dvd_mul_right.mp
    ⟨-(x₂ ^ 4 - x₁ ^ 4 + W.b₂ * x₁ * x₂ * (x₂ - x₁) + W.b₄ * (x₂ ^ 2 - x₁ ^ 2) +
      W.b₆ * (x₂ - x₁)), by linear_combination h₂ - h₁⟩
  -- then `b₈ = Ψ₃(x₁)` modulo `3`, then `b₄² = b₂b₆ - 4b₈`, and finally `Δ`
  obtain ⟨γ, hγ⟩ : (3 : R) ∣ W.b₈ :=
    ⟨-(x₁ ^ 4 + β * x₁ ^ 3 + W.b₄ * x₁ ^ 2 + W.b₆ * x₁), by linear_combination h₁ - x₁ ^ 3 * hβ⟩
  obtain ⟨δ, hδ⟩ : (3 : R) ∣ W.b₄ ^ 2 :=
    ⟨β * W.b₆ - 4 * γ, by linear_combination W.b_relation + W.b₆ * hβ - 4 * hγ⟩
  refine isUnit_of_dvd_unit ⟨-9 * β ^ 2 * γ - 8 * W.b₄ * δ - 9 * W.b₆ ^ 2 + 9 * β * W.b₄ * W.b₆,
    ?_⟩ W.isUnit_Δ
  rw [Δ]
  linear_combination -W.b₂ ^ 2 * hγ + (9 * W.b₄ * W.b₆ - 3 * γ * (W.b₂ + 3 * β)) * hβ -
    8 * W.b₄ * hδ

/-! ### Changes of variables to level-three normal form -/

/-- On `Y² + a₁XY + a₃Y = X³`, let `(x, y)` be a point at which `3`, `ψ₂ = 2y + a₁x + a₃` are units
and `3x³ + a₁²x² + 3a₁a₃x + 3a₃² = Ψ₃(x) / x` vanishes. Then `v = 3a₃ + a₁x` is a unit, because
`v² = -3ψ₂²`. -/
private theorem isUnit_scaling {a₁ a₃ x y : R} (h3 : IsUnit (3 : R))
    (hψ : IsUnit (2 * y + a₁ * x + a₃)) (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3)
    (hF : 3 * x ^ 3 + a₁ ^ 2 * x ^ 2 + 3 * a₁ * a₃ * x + 3 * a₃ ^ 2 = 0) :
    IsUnit (3 * a₃ + a₁ * x) := by
  have hv₂ : (3 * a₃ + a₁ * x) ^ 2 = -3 * (2 * y + a₁ * x + a₃) ^ 2 := by
    linear_combination 12 * hE + 4 * hF
  exact (isUnit_pow_iff two_ne_zero).mp (hv₂ ▸ h3.neg.mul (hψ.pow 2))

/-- The scaling step. On `Y² + a₁XY + a₃Y = X³`, let `(x, y)` be a point with `x` a unit at which
`3x³ + a₁²x² + 3a₁a₃x + 3a₃² = Ψ₃(x) / x` vanishes and `v = 3a₃ + a₁x` is a unit. If
`u (3x) = v`, `μ v = a₁x` and `ζ v = a₁x + 3y`, then the scaling by `u` carries the curve to the
level-three normal form with parameter `μ`, and `(x, y)` to `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`.
-/
private theorem scaling_spec {a₁ a₃ x y : R} (h3 : IsUnit (3 : R)) (hx : IsUnit x)
    (hv : IsUnit (3 * a₃ + a₁ * x)) (hE : y ^ 2 + a₁ * x * y + a₃ * y = x ^ 3)
    (hF : 3 * x ^ 3 + a₁ ^ 2 * x ^ 2 + 3 * a₁ * a₃ * x + 3 * a₃ ^ 2 = 0) {u : Rˣ} {μ ζ : R}
    (hu : (u : R) * (3 * x) = 3 * a₃ + a₁ * x) (hμ : μ * (3 * a₃ + a₁ * x) = a₁ * x)
    (hζ : ζ * (3 * a₃ + a₁ * x) = a₁ * x + 3 * y) :
    ζ ^ 2 + ζ + 1 = 0 ∧ a₁ = u * (3 * μ) ∧ a₃ = u ^ 3 * (μ ^ 3 - 1) ∧
      x = u ^ 2 * -(μ ^ 2 + μ + 1) ∧ y = u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) := by
  -- `x = u² x₀`, after multiplying by the unit `(3x)² v²`
  have hx₀ : x = u ^ 2 * -(μ ^ 2 + μ + 1) := by
    refine ((hv.pow 2).mul (h3.mul hx |>.pow 2)).mul_left_cancel ?_
    linear_combination (3 * x) ^ 2 * u ^ 2 * (μ * (3 * a₃ + a₁ * x) + a₁ * x +
        (3 * a₃ + a₁ * x)) * hμ + 3 * (3 * a₃ + a₁ * x) ^ 2 * hF +
      ((a₁ * x) ^ 2 + a₁ * x * (3 * a₃ + a₁ * x) + (3 * a₃ + a₁ * x) ^ 2) *
        (u * (3 * x) + (3 * a₃ + a₁ * x)) * hu
  refine ⟨?_, ?_, ?_, hx₀, ?_⟩
  · -- `v² (ζ² + ζ + 1) = (a₁x + 3y)² + (a₁x + 3y) v + v² = 9E + 3F`
    refine (hv.pow 2).mul_right_eq_zero.mp ?_
    linear_combination (ζ * (3 * a₃ + a₁ * x) + (a₁ * x + 3 * y) + (3 * a₃ + a₁ * x)) * hζ +
      9 * hE + 3 * hF
  · refine hv.mul_left_cancel ?_
    linear_combination (-3 * (u : R)) * hμ - a₁ * hu
  · refine ((hv.pow 3).mul (h3.mul hx |>.pow 3)).mul_left_cancel ?_
    linear_combination 9 * a₃ * (3 * a₃ + a₁ * x) ^ 3 * hF -
      (3 * x) ^ 3 * u ^ 3 * (μ ^ 2 * (3 * a₃ + a₁ * x) ^ 2 +
        μ * (3 * a₃ + a₁ * x) * (a₁ * x) + (a₁ * x) ^ 2) * hμ -
      ((a₁ * x) ^ 3 - (3 * a₃ + a₁ * x) ^ 3) * ((u * (3 * x)) ^ 2 +
        u * (3 * x) * (3 * a₃ + a₁ * x) + (3 * a₃ + a₁ * x) ^ 2) * hu
  · refine hv.mul_left_cancel ?_
    linear_combination (-(3 * a₃ + a₁ * x) * u * (μ - ζ)) * hx₀ - y * hu + u * x * hμ -
      u * x * hζ

namespace IsThreeTorsionBasis

variable (h : W.IsThreeTorsionBasis x₁ y₁ x₂ y₂)

include h in
/-- `ψ₂(P) = 2y₁ + a₁x₁ + a₃` is a unit. -/
private theorem isUnit_ψ₂_fst' : IsUnit (2 * y₁ + W.a₁ * x₁ + W.a₃) := by
  have h₁ := h.isUnit_ψ₂_fst
  rwa [ψ₂, Affine.evalEval_polynomialY] at h₁

include h in
/-- The shear step. If `σ ψ₂(P) = a₄ + 2a₂x₁ - a₁y₁ + 3x₁²`, the change of variables
`(1, x₁, σ, y₁)` carries `W` to `Y² + A₁XY + A₃Y = X³` with `A₁ = a₁ + 2σ` and `A₃ = ψ₂(P)` (`a₂`
vanishes because `Ψ₃(x₁) = 0`), and `Q` to the point `(X, Y) = (x₂ - x₁, y₂ - y₁ - σ (x₂ - x₁))`
of it, at which `3X³ + A₁²X² + 3A₁A₃X + 3A₃² = Ψ₃(X) / X` vanishes. -/
private theorem shear_spec {σ : R}
    (hσ : σ * (2 * y₁ + W.a₁ * x₁ + W.a₃) = W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) :
    W.a₂ - σ * W.a₁ + 3 * x₁ - σ ^ 2 = 0 ∧
      (y₂ - y₁ - σ * (x₂ - x₁)) ^ 2 + (W.a₁ + 2 * σ) * (x₂ - x₁) * (y₂ - y₁ - σ * (x₂ - x₁)) +
        (2 * y₁ + W.a₁ * x₁ + W.a₃) * (y₂ - y₁ - σ * (x₂ - x₁)) = (x₂ - x₁) ^ 3 ∧
      3 * (x₂ - x₁) ^ 3 + (W.a₁ + 2 * σ) ^ 2 * (x₂ - x₁) ^ 2 +
        3 * (W.a₁ + 2 * σ) * (2 * y₁ + W.a₁ * x₁ + W.a₃) * (x₂ - x₁) +
        3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) ^ 2 = 0 := by
  have ha₂ : W.a₂ - σ * W.a₁ + 3 * x₁ - σ ^ 2 = 0 := by
    have h₁ := a₂_mul_ψ₂_sq_eq_eval_Ψ₃ h.equation_fst hσ
    rw [h.eval_Ψ₃_fst] at h₁
    exact (h.isUnit_ψ₂_fst'.pow 2).mul_left_eq_zero.mp h₁
  have hP := h.equation_fst
  rw [Affine.equation_iff] at hP
  set C₁ : VariableChange R := ⟨1, x₁, σ, y₁⟩
  have hC₁ : C₁ • W = ⟨W.a₁ + 2 * σ, 0, 2 * y₁ + W.a₁ * x₁ + W.a₃, 0, 0⟩ := by
    ext <;> simp only [C₁, variableChange_a₁, variableChange_a₂, variableChange_a₃,
      variableChange_a₄, variableChange_a₆, inv_one, Units.val_one, one_pow, one_mul]
    · exact ha₂
    · ring
    · linear_combination -hσ
    · linear_combination -hP
  have hE : (C₁ • W).toAffine.Equation (x₂ - x₁) (y₂ - y₁ - σ * (x₂ - x₁)) := by
    rw [← Affine.variableChange_equation]
    convert h.equation_snd using 1 <;> simp only [C₁, Units.val_one, one_pow, one_mul] <;> ring
  have hΨ : (C₁ • W).Ψ₃.eval (x₂ - x₁) = 0 := by
    rw [eval_variableChange_Ψ₃]
    simp only [C₁, inv_one, Units.val_one, one_pow, one_mul, sub_add_cancel, h.eval_Ψ₃_snd]
  rw [hC₁, Affine.equation_iff] at hE
  rw [hC₁, eval_Ψ₃] at hΨ
  simp only [b₂, b₄, b₆, b₈] at hE hΨ
  exact ⟨ha₂, by linear_combination hE,
    h.isUnit_sub.mul_right_eq_zero.mp (by linear_combination hΨ)⟩

/-- The shear `s = (a₄ + 2a₂x₁ - a₁y₁ + 3x₁²) / ψ₂(P)` makes the tangent at `P` horizontal. -/
private theorem slope_spec :
    (W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) * ↑h.isUnit_ψ₂_fst.unit⁻¹ *
      (2 * y₁ + W.a₁ * x₁ + W.a₃) = W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2 := by
  have hψ : (2 * y₁ + W.a₁ * x₁ + W.a₃) * ↑h.isUnit_ψ₂_fst.unit⁻¹ = 1 := by
    rw [← Affine.evalEval_polynomialY, ← ψ₂]
    exact h.isUnit_ψ₂_fst.mul_val_inv
  linear_combination (W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) * hψ

/-- The numerator `v = 3ψ₂(P) + (a₁ + 2s)(x₂ - x₁)` of the scaling is a unit. -/
private theorem isUnit_scalingNumerator :
    IsUnit (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) + (W.a₁ + 2 *
      ((W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) * ↑h.isUnit_ψ₂_fst.unit⁻¹)) *
        (x₂ - x₁)) := by
  obtain ⟨-, hE, hF⟩ := h.shear_spec h.slope_spec
  refine isUnit_scaling h.isUnit_three ?_ hE hF
  have hψ := h.isUnit_ψ₂_snd
  rw [ψ₂, Affine.evalEval_polynomialY] at hψ
  convert hψ using 1
  ring

end IsThreeTorsionBasis

variable (h : W.IsThreeTorsionBasis x₁ y₁ x₂ y₂)

/-- The **change of variables to level-three normal form** of a basis `(P, Q)` of the `3`-torsion:
`r = x₁`, `s = (a₄ + 2a₂x₁ - a₁y₁ + 3x₁²) / ψ₂(P)`, `t = y₁` and `u = v / (3 (x₂ - x₁))`, where
`v = 3ψ₂(P) + (a₁ + 2s)(x₂ - x₁)`. It carries `W` to the level-three normal form with parameter
`μ = levelThreeParameter h` (`toLevelThreeNormalForm_smul`), `P` to `(0, 0)` and `Q` to
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` with `ζ = levelThreeRootOfUnity h`, and it is the only
change of variables doing so (`eq_toLevelThreeNormalForm`). -/
noncomputable def toLevelThreeNormalForm : VariableChange R where
  u := h.isUnit_scalingNumerator.unit * (h.isUnit_three.mul h.isUnit_sub).unit⁻¹
  r := x₁
  s := (W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) * ↑h.isUnit_ψ₂_fst.unit⁻¹
  t := y₁

@[simp]
theorem toLevelThreeNormalForm_u : ((toLevelThreeNormalForm h).u : R) =
    (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) + (W.a₁ + 2 * (toLevelThreeNormalForm h).s) * (x₂ - x₁)) *
      ↑(h.isUnit_three.mul h.isUnit_sub).unit⁻¹ := by
  simp only [toLevelThreeNormalForm, Units.val_mul, IsUnit.unit_spec]

@[simp] theorem toLevelThreeNormalForm_r : (toLevelThreeNormalForm h).r = x₁ := (rfl)

@[simp]
theorem toLevelThreeNormalForm_s : (toLevelThreeNormalForm h).s =
    (W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2) * ↑h.isUnit_ψ₂_fst.unit⁻¹ :=
  (rfl)

@[simp] theorem toLevelThreeNormalForm_t : (toLevelThreeNormalForm h).t = y₁ := (rfl)

/-- The parameter `μ = (a₁ + 2s) / (3u)` of the level-three normal form reached by
`toLevelThreeNormalForm h`. -/
noncomputable def levelThreeParameter : R :=
  ↑(toLevelThreeNormalForm h).u⁻¹ * (W.a₁ + 2 * (toLevelThreeNormalForm h).s) *
    ↑h.isUnit_three.unit⁻¹

/-- The root `ζ = μ + (y₂ - y₁ - s (x₂ - x₁)) / (u (x₂ - x₁))` of `ζ² + ζ + 1` such that
`toLevelThreeNormalForm h` carries `Q` to `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. -/
noncomputable def levelThreeRootOfUnity : R :=
  levelThreeParameter h + ↑(toLevelThreeNormalForm h).u⁻¹ *
    (y₂ - y₁ - (toLevelThreeNormalForm h).s * (x₂ - x₁)) * ↑h.isUnit_sub.unit⁻¹

/-- The properties of `toLevelThreeNormalForm h`, `levelThreeParameter h` and
`levelThreeRootOfUnity h`. -/
private theorem toLevelThreeNormalForm_spec :
    levelThreeRootOfUnity h ^ 2 + levelThreeRootOfUnity h + 1 = 0 ∧
      toLevelThreeNormalForm h • W = levelThreeNormalForm (levelThreeParameter h) ∧
      x₂ = (toLevelThreeNormalForm h).u ^ 2 *
        -(levelThreeParameter h ^ 2 + levelThreeParameter h + 1) + (toLevelThreeNormalForm h).r ∧
      y₂ = (toLevelThreeNormalForm h).u ^ 3 * ((levelThreeParameter h ^ 2 + levelThreeParameter h +
        1) * (levelThreeParameter h - levelThreeRootOfUnity h)) + (toLevelThreeNormalForm h).u ^ 2 *
          (toLevelThreeNormalForm h).s * -(levelThreeParameter h ^ 2 + levelThreeParameter h + 1) +
        (toLevelThreeNormalForm h).t := by
  have hσ : (toLevelThreeNormalForm h).s * (2 * y₁ + W.a₁ * x₁ + W.a₃) =
      W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2 := h.slope_spec
  have hv : IsUnit (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) +
      (W.a₁ + 2 * (toLevelThreeNormalForm h).s) * (x₂ - x₁)) := h.isUnit_scalingNumerator
  have hu : ((toLevelThreeNormalForm h).u : R) * (3 * (x₂ - x₁)) = 3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) +
      (W.a₁ + 2 * (toLevelThreeNormalForm h).s) * (x₂ - x₁) := by
    rw [toLevelThreeNormalForm_u]
    linear_combination (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) +
      (W.a₁ + 2 * (toLevelThreeNormalForm h).s) * (x₂ - x₁)) *
        (h.isUnit_three.mul h.isUnit_sub).val_inv_mul
  have hμ : levelThreeParameter h = ↑(toLevelThreeNormalForm h).u⁻¹ *
      (W.a₁ + 2 * (toLevelThreeNormalForm h).s) * ↑h.isUnit_three.unit⁻¹ := rfl
  have hζ : levelThreeRootOfUnity h = levelThreeParameter h + ↑(toLevelThreeNormalForm h).u⁻¹ *
      (y₂ - y₁ - (toLevelThreeNormalForm h).s * (x₂ - x₁)) * ↑h.isUnit_sub.unit⁻¹ := rfl
  have hr : (toLevelThreeNormalForm h).r = x₁ := rfl
  have ht : (toLevelThreeNormalForm h).t = y₁ := rfl
  have hw₃ := h.isUnit_three.val_inv_mul
  have hwₓ := h.isUnit_sub.val_inv_mul
  obtain ⟨ha₂, hE, hF⟩ := h.shear_spec hσ
  have hP := h.equation_fst
  rw [Affine.equation_iff] at hP
  rw [hr, ht]
  generalize toLevelThreeNormalForm h = C at *
  generalize levelThreeRootOfUnity h = ζ at *
  generalize levelThreeParameter h = μ at *
  have hu' := C.u.inv_mul
  -- `μ v = a₁x` and `ζ v = a₁x + 3y` in the coordinates of the scaling step, using `u (3x) = v`
  have hμv : μ * (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) + (W.a₁ + 2 * C.s) * (x₂ - x₁)) =
      (W.a₁ + 2 * C.s) * (x₂ - x₁) := by
    rw [hμ]
    linear_combination (-(↑C.u⁻¹ * (W.a₁ + 2 * C.s) * ↑h.isUnit_three.unit⁻¹)) * hu +
      (W.a₁ + 2 * C.s) * (x₂ - x₁) * ↑h.isUnit_three.unit⁻¹ * 3 * hu' +
      (W.a₁ + 2 * C.s) * (x₂ - x₁) * hw₃
  have hζv : ζ * (3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) + (W.a₁ + 2 * C.s) * (x₂ - x₁)) =
      (W.a₁ + 2 * C.s) * (x₂ - x₁) + 3 * (y₂ - y₁ - C.s * (x₂ - x₁)) := by
    rw [hζ]
    linear_combination hμv - ↑C.u⁻¹ * (y₂ - y₁ - C.s * (x₂ - x₁)) * ↑h.isUnit_sub.unit⁻¹ * hu +
      3 * (y₂ - y₁ - C.s * (x₂ - x₁)) * ↑h.isUnit_sub.unit⁻¹ * (x₂ - x₁) * hu' +
      3 * (y₂ - y₁ - C.s * (x₂ - x₁)) * hwₓ
  obtain ⟨hζ₀, ha₁, ha₃, hX, hY⟩ :=
    scaling_spec h.isUnit_three h.isUnit_sub hv hE hF hu hμv hζv
  refine ⟨hζ₀, ?_, by linear_combination hX, by linear_combination hY + C.s * hX⟩
  ext
  · simp only [variableChange_a₁, levelThreeNormalForm_a₁, ha₁, Units.inv_mul_cancel_left]
  · simp only [variableChange_a₂, hr, levelThreeNormalForm_a₂, ha₂, mul_zero]
  · rw [variableChange_a₃, hr, ht, levelThreeNormalForm_a₃]
    linear_combination (↑C.u⁻¹ : R) ^ 3 * ha₃ +
      (μ ^ 3 - 1) * (((↑C.u⁻¹ : R) * C.u) ^ 2 + (↑C.u⁻¹ : R) * C.u + 1) * hu'
  · rw [variableChange_a₄, hr, ht, levelThreeNormalForm_a₄]
    linear_combination -(↑C.u⁻¹ : R) ^ 4 * hσ
  · rw [variableChange_a₆, hr, ht, levelThreeNormalForm_a₆]
    linear_combination -(↑C.u⁻¹ : R) ^ 6 * hP

/-- The root of unity of a basis of the `3`-torsion is a root of `ζ² + ζ + 1`. -/
theorem levelThreeRootOfUnity_sq_add_levelThreeRootOfUnity_add_one :
    levelThreeRootOfUnity h ^ 2 + levelThreeRootOfUnity h + 1 = 0 :=
  (toLevelThreeNormalForm_spec h).1

/-- **Existence of level-three normal form.** The change of variables `toLevelThreeNormalForm h`
carries `W` to the level-three normal form with parameter `levelThreeParameter h`. -/
theorem toLevelThreeNormalForm_smul :
    toLevelThreeNormalForm h • W = levelThreeNormalForm (levelThreeParameter h) :=
  (toLevelThreeNormalForm_spec h).2.1

/-- The change of variables `toLevelThreeNormalForm h` carries `Q = (x₂, y₂)` to a point with
`x`-coordinate `-(μ² + μ + 1)`, where `μ = levelThreeParameter h`. -/
theorem toLevelThreeNormalForm_basisPoint_x :
    x₂ = (toLevelThreeNormalForm h).u ^ 2 *
      -(levelThreeParameter h ^ 2 + levelThreeParameter h + 1) + x₁ :=
  (toLevelThreeNormalForm_spec h).2.2.1

/-- The change of variables `toLevelThreeNormalForm h` carries `Q = (x₂, y₂)` to a point with
`y`-coordinate `(μ² + μ + 1)(μ - ζ)`, where `μ = levelThreeParameter h` and
`ζ = levelThreeRootOfUnity h`. -/
theorem toLevelThreeNormalForm_basisPoint_y :
    y₂ = (toLevelThreeNormalForm h).u ^ 3 * ((levelThreeParameter h ^ 2 + levelThreeParameter h +
      1) * (levelThreeParameter h - levelThreeRootOfUnity h)) + (toLevelThreeNormalForm h).u ^ 2 *
        (toLevelThreeNormalForm h).s * -(levelThreeParameter h ^ 2 + levelThreeParameter h + 1) +
      y₁ :=
  (toLevelThreeNormalForm_spec h).2.2.2

/-- The level-three normal form reached by `toLevelThreeNormalForm h` is elliptic: its parameter
`μ` has `μ³ - 1 = u⁻³ ψ₂(P)` a unit. -/
theorem isElliptic_levelThreeNormalForm_levelThreeParameter :
    (levelThreeNormalForm (levelThreeParameter h)).IsElliptic := by
  refine (isElliptic_levelThreeNormalForm_iff _).mpr ⟨h.isUnit_three, ?_⟩
  have h₃ := congr_arg a₃ (toLevelThreeNormalForm_smul h)
  rw [variableChange_a₃, toLevelThreeNormalForm_r, toLevelThreeNormalForm_t,
    levelThreeNormalForm_a₃] at h₃
  rw [← h₃]
  refine ((Units.isUnit _).pow 3).mul ?_
  convert h.isUnit_ψ₂_fst using 1
  rw [ψ₂, Affine.evalEval_polynomialY]
  ring

/-- The identities satisfied by a change of variables to level-three normal form: they determine
`s`, `u`, `μ` and `ζ` in turn. -/
private theorem variableChange_levelThreeNormalForm_spec {C : VariableChange R} {μ ζ : R}
    (hr : C.r = x₁) (ht : C.t = y₁) (hC : C • W = levelThreeNormalForm μ)
    (hx₂ : x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r)
    (hy₂ : y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t) :
    C.s * (2 * y₁ + W.a₁ * x₁ + W.a₃) = W.a₄ + 2 * x₁ * W.a₂ - y₁ * W.a₁ + 3 * x₁ ^ 2 ∧
      C.u * (3 * (x₂ - x₁)) = 3 * (2 * y₁ + W.a₁ * x₁ + W.a₃) + (W.a₁ + 2 * C.s) * (x₂ - x₁) ∧
      C.u * (3 * μ) = W.a₁ + 2 * C.s ∧
      C.u * (x₂ - x₁) * ζ = y₂ - y₁ - C.s * (x₂ - x₁) + C.u * (x₂ - x₁) * μ := by
  have h₁ : (C • W).a₁ = 3 * μ := by rw [hC, levelThreeNormalForm_a₁]
  have h₃ : (C • W).a₃ = μ ^ 3 - 1 := by rw [hC, levelThreeNormalForm_a₃]
  have h₄ : (C • W).a₄ = 0 := by rw [hC, levelThreeNormalForm_a₄]
  have hw : IsUnit (↑C.u⁻¹ : R) := Units.isUnit _
  have hu := C.u.mul_inv
  rw [variableChange_a₁] at h₁
  rw [variableChange_a₃, hr, ht] at h₃
  rw [variableChange_a₄, hr, ht, (hw.pow 4).mul_right_eq_zero] at h₄
  rw [hr] at hx₂
  rw [ht] at hy₂
  have hu₁ : C.u * (3 * μ) = W.a₁ + 2 * C.s := by
    linear_combination -(C.u : R) * h₁ + (W.a₁ + 2 * C.s) * hu
  have hu₃ : C.u ^ 3 * (μ ^ 3 - 1) = 2 * y₁ + W.a₁ * x₁ + W.a₃ := by
    linear_combination -(C.u : R) ^ 3 * h₃ +
      (W.a₃ + x₁ * W.a₁ + 2 * y₁) * (((C.u : R) * ↑C.u⁻¹) ^ 2 + (C.u : R) * ↑C.u⁻¹ + 1) * hu
  refine ⟨by linear_combination -h₄, ?_, hu₁, ?_⟩
  · linear_combination 3 * hu₃ + (x₂ - x₁) * hu₁ + 3 * C.u * (1 - μ) * hx₂
  · linear_combination -hy₂ + (C.s - C.u * (μ - ζ)) * hx₂

/-- **Uniqueness of level-three normal form.** A change of variables carrying `W` to a level-three
normal form, `P` to `(0, 0)` (that is, with `r = x₁` and `t = y₁`) and `Q` to
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` is `toLevelThreeNormalForm h`. -/
theorem eq_toLevelThreeNormalForm {C : VariableChange R} (hr : C.r = x₁) (ht : C.t = y₁) {μ ζ : R}
    (hC : C • W = levelThreeNormalForm μ) (hx₂ : x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r)
    (hy₂ : y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t) :
    C = toLevelThreeNormalForm h := by
  obtain ⟨-, hC₀, hx₀, hy₀⟩ := toLevelThreeNormalForm_spec h
  obtain ⟨hs, hu, -, -⟩ := variableChange_levelThreeNormalForm_spec hr ht hC hx₂ hy₂
  obtain ⟨hs₀, hu₀, -, -⟩ := variableChange_levelThreeNormalForm_spec
    (toLevelThreeNormalForm_r h) (toLevelThreeNormalForm_t h) hC₀ hx₀ hy₀
  have hss : C.s = (toLevelThreeNormalForm h).s :=
    h.isUnit_ψ₂_fst'.mul_right_cancel (hs.trans hs₀.symm)
  ext : 1
  · exact Units.ext <| (h.isUnit_three.mul h.isUnit_sub).mul_right_cancel <| by rw [hu, hu₀, hss]
  · rw [hr, toLevelThreeNormalForm_r]
  · exact hss
  · rw [ht, toLevelThreeNormalForm_t]

/-- The parameter of the level-three normal form reached in `eq_toLevelThreeNormalForm` is
`levelThreeParameter h`. -/
theorem eq_levelThreeParameter {C : VariableChange R} (hr : C.r = x₁) (ht : C.t = y₁) {μ ζ : R}
    (hC : C • W = levelThreeNormalForm μ) (hx₂ : x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r)
    (hy₂ : y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t) :
    μ = levelThreeParameter h := by
  obtain rfl := eq_toLevelThreeNormalForm h hr ht hC hx₂ hy₂
  obtain ⟨-, hC₀, hx₀, hy₀⟩ := toLevelThreeNormalForm_spec h
  obtain ⟨-, -, hμ, -⟩ := variableChange_levelThreeNormalForm_spec hr ht hC hx₂ hy₂
  obtain ⟨-, -, hμ₀, -⟩ := variableChange_levelThreeNormalForm_spec hr ht hC₀ hx₀ hy₀
  exact ((toLevelThreeNormalForm h).u.isUnit.mul h.isUnit_three).mul_left_cancel
    (by linear_combination hμ - hμ₀)

/-- The root of unity in `eq_toLevelThreeNormalForm` is `levelThreeRootOfUnity h`. -/
theorem eq_levelThreeRootOfUnity {C : VariableChange R} (hr : C.r = x₁) (ht : C.t = y₁) {μ ζ : R}
    (hC : C • W = levelThreeNormalForm μ) (hx₂ : x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r)
    (hy₂ : y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t) :
    ζ = levelThreeRootOfUnity h := by
  obtain rfl := eq_levelThreeParameter h hr ht hC hx₂ hy₂
  obtain rfl := eq_toLevelThreeNormalForm h hr ht hC hx₂ hy₂
  obtain ⟨-, hC₀, hx₀, hy₀⟩ := toLevelThreeNormalForm_spec h
  obtain ⟨-, -, -, hζ⟩ := variableChange_levelThreeNormalForm_spec hr ht hC hx₂ hy₂
  obtain ⟨-, -, -, hζ₀⟩ := variableChange_levelThreeNormalForm_spec hr ht hC₀ hx₀ hy₀
  exact ((toLevelThreeNormalForm h).u.isUnit.mul h.isUnit_sub).mul_left_cancel
    (by linear_combination hζ - hζ₀)

include h in
/-- **Level-three normal form.** Let `(P, Q)` be a basis of the `3`-torsion of `W`, with
`P = (x₁, y₁)` and `Q = (x₂, y₂)`. Then exactly one change of variables carries `W` to a
level-three normal form `Y² + 3μXY + (μ³ - 1)Y = X³`, `P` to `(0, 0)` and `Q` to
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` for a root `ζ` of `ζ² + ζ + 1`. Here a point `(x, y)` of
`C • W` corresponds to the point `(u²x + r, u³y + u²sx + t)` of `W`. -/
theorem existsUnique_variableChange_levelThreeNormalForm :
    ∃! C : VariableChange R, C.r = x₁ ∧ C.t = y₁ ∧ ∃ μ ζ : R, ζ ^ 2 + ζ + 1 = 0 ∧
      C • W = levelThreeNormalForm μ ∧ x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r ∧
      y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t := by
  obtain ⟨hζ, hC, hx₂, hy₂⟩ := toLevelThreeNormalForm_spec h
  exact ⟨toLevelThreeNormalForm h, ⟨rfl, rfl, _, _, hζ, hC, hx₂, hy₂⟩,
    fun _ ⟨hr, ht, _, _, _, hC, hx₂, hy₂⟩ ↦ eq_toLevelThreeNormalForm h hr ht hC hx₂ hy₂⟩

/-- For elliptic `W`, a change of variables carrying `W` to a level-three normal form, `(x₁, y₁)`
to `(0, 0)` and `(x₂, y₂)` to `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))` exists exactly when
`(x₁, y₁)`, `(x₂, y₂)` is a basis of the `3`-torsion of `W`: `3` is a unit, and they are points of
`W` at which `Ψ₃` vanishes and `ψ₂` is a unit, with `x₂ - x₁` a unit. -/
theorem exists_variableChange_levelThreeNormalForm_iff [W.IsElliptic] :
    (∃ C : VariableChange R, C.r = x₁ ∧ C.t = y₁ ∧ ∃ μ ζ : R, ζ ^ 2 + ζ + 1 = 0 ∧
      C • W = levelThreeNormalForm μ ∧ x₂ = C.u ^ 2 * -(μ ^ 2 + μ + 1) + C.r ∧
      y₂ = C.u ^ 3 * ((μ ^ 2 + μ + 1) * (μ - ζ)) + C.u ^ 2 * C.s * -(μ ^ 2 + μ + 1) + C.t) ↔
      W.IsThreeTorsionBasis x₁ y₁ x₂ y₂ := by
  refine ⟨fun ⟨C, hr, ht, μ, ζ, hζ, hC, hx₂, hy₂⟩ ↦ ?_, fun h ↦
    (existsUnique_variableChange_levelThreeNormalForm h).exists⟩
  have : (levelThreeNormalForm μ).IsElliptic := hC ▸ inferInstance
  obtain ⟨h3, hμ⟩ := (isElliptic_levelThreeNormalForm_iff μ).mp this
  -- `μ² + μ + 1` divides the unit `μ³ - 1`, and `(2ζ + 1)² = -3`
  have hμ' : IsUnit (μ ^ 2 + μ + 1) :=
    isUnit_of_mul_isUnit_right (x := μ - 1) (by convert hμ using 1; ring)
  have hζ' : IsUnit (2 * ζ + 1) :=
    (isUnit_pow_iff two_ne_zero).mp (by convert h3.neg using 1; linear_combination 4 * hζ)
  -- the points `(0, 0)` and `Q` of `C • W` correspond to `(x₁, y₁)` and `(x₂, y₂)` on `W`
  have hP₀ : x₁ = C.u ^ 2 * 0 + C.r := by rw [hr]; ring
  have hP₁ : y₁ = C.u ^ 3 * 0 + C.u ^ 2 * C.s * 0 + C.t := by rw [ht]; ring
  have hu := (C.u.isUnit)
  refine ⟨h3, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hP₀, hP₁, Affine.variableChange_equation, hC]
    exact equation_levelThreeNormalForm_zero μ
  · rw [hx₂, hy₂, Affine.variableChange_equation, hC]
    exact equation_levelThreeNormalForm_basisPoint μ hζ
  · have h := eval_variableChange_Ψ₃ W C 0
    rw [hC, eval_Ψ₃_levelThreeNormalForm_zero, ← hP₀] at h
    exact ((Units.isUnit _).pow 8).mul_right_eq_zero.mp h.symm
  · have h := eval_variableChange_Ψ₃ W C (-(μ ^ 2 + μ + 1))
    rw [hC, eval_Ψ₃_levelThreeNormalForm_basisPoint, ← hx₂] at h
    exact ((Units.isUnit _).pow 8).mul_right_eq_zero.mp h.symm
  · rw [ψ₂, hP₀, hP₁, Affine.variableChange_evalEval_polynomialY, ← ψ₂, hC,
      evalEval_ψ₂_levelThreeNormalForm_zero]
    exact (hu.pow 3).mul hμ
  · rw [ψ₂, hx₂, hy₂, Affine.variableChange_evalEval_polynomialY, ← ψ₂, hC,
      evalEval_ψ₂_levelThreeNormalForm_basisPoint]
    exact (hu.pow 3).mul (hζ'.neg.mul hμ')
  · rw [hx₂, hr, add_sub_cancel_right]
    exact (hu.pow 2).mul hμ'.neg

/-- The change of variables to level-three normal form, its parameter and its root of unity commute
with base change. -/
private theorem toLevelThreeNormalForm_map_spec {A : Type*} [CommRing A] (φ : R →+* A) :
    (toLevelThreeNormalForm h).map φ = toLevelThreeNormalForm (h.map φ) ∧
      φ (levelThreeParameter h) = levelThreeParameter (h.map φ) ∧
      φ (levelThreeRootOfUnity h) = levelThreeRootOfUnity (h.map φ) := by
  obtain ⟨-, hC, hx₂, hy₂⟩ := toLevelThreeNormalForm_spec h
  have hC' : (toLevelThreeNormalForm h).map φ • W.map φ =
      levelThreeNormalForm (φ (levelThreeParameter h)) := by
    rw [map_variableChange, hC, map_levelThreeNormalForm]
  replace hx₂ := congr_arg φ hx₂
  replace hy₂ := congr_arg φ hy₂
  simp only [map_add, map_mul, map_pow, map_neg, map_one, map_sub] at hx₂ hy₂
  exact ⟨eq_toLevelThreeNormalForm (h.map φ) rfl rfl hC' hx₂ hy₂,
    eq_levelThreeParameter (h.map φ) rfl rfl hC' hx₂ hy₂,
    eq_levelThreeRootOfUnity (h.map φ) rfl rfl hC' hx₂ hy₂⟩

/-- **Level-three normal form commutes with base change.** The image of `toLevelThreeNormalForm h`
under a ring homomorphism `φ` is the change of variables to level-three normal form of the image
basis of the `3`-torsion of `W.map φ`. -/
theorem toLevelThreeNormalForm_map {A : Type*} [CommRing A] (φ : R →+* A) :
    (toLevelThreeNormalForm h).map φ = toLevelThreeNormalForm (h.map φ) :=
  (toLevelThreeNormalForm_map_spec h φ).1

/-- The parameter of the level-three normal form commutes with base change. -/
theorem levelThreeParameter_map {A : Type*} [CommRing A] (φ : R →+* A) :
    φ (levelThreeParameter h) = levelThreeParameter (h.map φ) :=
  (toLevelThreeNormalForm_map_spec h φ).2.1

/-- The root of unity of a basis of the `3`-torsion commutes with base change. -/
theorem levelThreeRootOfUnity_map {A : Type*} [CommRing A] (φ : R →+* A) :
    φ (levelThreeRootOfUnity h) = levelThreeRootOfUnity (h.map φ) :=
  (toLevelThreeNormalForm_map_spec h φ).2.2

/-! ### The universal curve with a basis of its `3`-torsion -/

namespace UniversalLevelThree

open MvPolynomial (X)

/-- The ring `ℤ[μ, ζ] / (ζ² + ζ + 1)`, with `μ = X 0` and `ζ = X 1`. -/
abbrev PolyRing : Type :=
  MvPolynomial (Fin 2) ℤ ⧸ Ideal.span {(X 1 ^ 2 + X 1 + 1 : MvPolynomial (Fin 2) ℤ)}

/-- The level-three normal form over `ℤ[μ, ζ] / (ζ² + ζ + 1)`, with parameter the class of `μ`. -/
noncomputable abbrev polyCurve : WeierstrassCurve PolyRing :=
  levelThreeNormalForm (Ideal.Quotient.mk _ (X 0))

/-- The ring `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`: the ring `ℤ[μ, ζ] / (ζ² + ζ + 1)` localised away from the
discriminant `27 (μ³ - 1)³` of the level-three normal form with parameter `μ`. -/
abbrev Ring : Type := Localization.Away polyCurve.Δ

/-- The parameter `μ` in `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. -/
noncomputable def parameter : Ring :=
  algebraMap PolyRing Ring (Ideal.Quotient.mk _ (X 0))

/-- The primitive cube root of unity `ζ` in `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`. -/
noncomputable def rootOfUnity : Ring :=
  algebraMap PolyRing Ring (Ideal.Quotient.mk _ (X 1))

/-- The root of unity `ζ` of `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` is a root of `ζ² + ζ + 1`. -/
theorem rootOfUnity_sq_add_rootOfUnity_add_one : rootOfUnity ^ 2 + rootOfUnity + 1 = 0 := by
  simpa only [rootOfUnity, map_add, map_pow, map_one, map_zero] using
    congr_arg (algebraMap PolyRing Ring)
    (Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _))

/-- The **universal curve with a basis of its `3`-torsion**: the level-three normal form over
`ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]`, with the basis `(0, 0)`, `(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`. -/
noncomputable abbrev curve : WeierstrassCurve Ring :=
  polyCurve.baseChange Ring

/-- The universal curve is the level-three normal form with parameter `μ`. -/
theorem curve_eq : curve = levelThreeNormalForm parameter := by
  simp [baseChange, parameter]

/-- The universal curve with a basis of its `3`-torsion is an elliptic curve. -/
instance : curve.IsElliptic where
  isUnit := by
    simpa only [baseChange, map_Δ] using IsLocalization.Away.algebraMap_isUnit polyCurve.Δ

/-- Two ring homomorphisms out of `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` are equal as soon as they agree on
`μ` and `ζ`. -/
-- `high`, as for Mathlib's `Localization.algHom_ext`, so that `ext` tries this lemma before
-- `RingHom.ext`.
@[ext high]
theorem Ring.ringHom_ext {S : Type*} [Semiring S] {f g : Ring →+* S}
    (h₀ : f parameter = g parameter) (h₁ : f rootOfUnity = g rootOfUnity) : f = g :=
  IsLocalization.ringHom_ext (.powers polyCurve.Δ) <| Ideal.Quotient.ringHom_ext <|
    MvPolynomial.ringHom_ext' (RingHom.ext_int _ _) <| Fin.forall_fin_two.mpr
      ⟨by simpa only [RingHom.comp_apply, parameter] using h₀,
        by simpa only [RingHom.comp_apply, rootOfUnity] using h₁⟩

variable {μ ζ : R}

/-- The ring homomorphism `ℤ[μ, ζ] / (ζ² + ζ + 1) →+* R` substituting `μ` and a root `ζ` of
`ζ² + ζ + 1`. -/
private noncomputable def polyLift (hζ : ζ ^ 2 + ζ + 1 = 0) : PolyRing →+* R :=
  Ideal.Quotient.lift _ (MvPolynomial.eval₂Hom (Int.castRingHom R) ![μ, ζ]) fun _ ha ↦ by
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    simp [hζ]

private theorem polyLift_mk_X_zero (hζ : ζ ^ 2 + ζ + 1 = 0) :
    polyLift (μ := μ) hζ (Ideal.Quotient.mk _ (X 0)) = μ := by
  simp [polyLift]

private theorem polyLift_mk_X_one (hζ : ζ ^ 2 + ζ + 1 = 0) :
    polyLift (μ := μ) hζ (Ideal.Quotient.mk _ (X 1)) = ζ := by
  simp [polyLift]

/-- The **classifying homomorphism** `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)] →+* R` of an elliptic level-three
normal form `Y² + 3μXY + (μ³ - 1)Y = X³` over `R` with a root `ζ` of `ζ² + ζ + 1`, sending the
parameter to `μ` and the root of unity to `ζ`. -/
noncomputable def lift (hΔ : IsUnit (levelThreeNormalForm μ).Δ) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    Ring →+* R :=
  IsLocalization.Away.lift polyCurve.Δ (g := polyLift hζ) <| by
    rw [levelThreeNormalForm_Δ] at hΔ ⊢
    simpa only [map_mul, map_pow, map_sub, map_one, map_ofNat, polyLift_mk_X_zero] using hΔ

/-- The classifying homomorphism sends the parameter to `μ`. -/
@[simp]
theorem lift_parameter (hΔ : IsUnit (levelThreeNormalForm μ).Δ) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    lift hΔ hζ parameter = μ := by
  rw [lift, parameter, IsLocalization.Away.lift_eq, polyLift_mk_X_zero]

/-- The classifying homomorphism sends the root of unity to `ζ`. -/
@[simp]
theorem lift_rootOfUnity (hΔ : IsUnit (levelThreeNormalForm μ).Δ) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    lift hΔ hζ rootOfUnity = ζ := by
  rw [lift, rootOfUnity, IsLocalization.Away.lift_eq, polyLift_mk_X_one]

/-- Every elliptic level-three normal form is the base change of the universal one along its
classifying homomorphism. -/
@[simp]
theorem map_lift (hΔ : IsUnit (levelThreeNormalForm μ).Δ) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    curve.map (lift hΔ hζ) = levelThreeNormalForm μ := by
  rw [curve_eq, map_levelThreeNormalForm, lift_parameter]

/-- The classifying homomorphism is unique: a ring homomorphism out of
`ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)]` along which the universal curve becomes the level-three normal form
with parameter `μ`, and which sends the root of unity to `ζ`, is `lift`. -/
theorem eq_lift (hΔ : IsUnit (levelThreeNormalForm μ).Δ) (hζ : ζ ^ 2 + ζ + 1 = 0)
    {f : Ring →+* R} (hf : curve.map f = levelThreeNormalForm μ) (hfζ : f rootOfUnity = ζ) :
    f = lift hΔ hζ := by
  have h3 : IsUnit (3 : R) :=
    ((isElliptic_levelThreeNormalForm_iff μ).mp ⟨hΔ⟩).1
  have h₁ := congr_arg a₁ hf
  rw [curve_eq, map_levelThreeNormalForm, levelThreeNormalForm_a₁, levelThreeNormalForm_a₁] at h₁
  ext
  · rw [lift_parameter]
    exact h3.mul_left_cancel h₁
  · rw [lift_rootOfUnity, hfζ]

/-- The classifying homomorphism is natural in the base ring: followed by a ring homomorphism
`φ : R →+* S`, the classifying homomorphism of `(μ, ζ)` is that of `(φ μ, φ ζ)`. -/
theorem comp_lift {S : Type*} [CommRing S] (φ : R →+* S) (hΔ : IsUnit (levelThreeNormalForm μ).Δ)
    (hζ : ζ ^ 2 + ζ + 1 = 0) :
    φ.comp (lift hΔ hζ) = lift (μ := φ μ) (ζ := φ ζ)
      (by rw [← map_levelThreeNormalForm, map_Δ]; exact hΔ.map φ)
      (by simpa using congr_arg φ hζ) := by
  ext <;> simp

/-- The **classifying homomorphism** `ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)] →+* R` of a basis `(P, Q)` of the
`3`-torsion of `W`: the classifying homomorphism of the level-three normal form reached by
`toLevelThreeNormalForm h`, with the root of unity `levelThreeRootOfUnity h`. -/
noncomputable def classifyingHom : Ring →+* R :=
  lift (isElliptic_levelThreeNormalForm_levelThreeParameter h).isUnit
    (levelThreeRootOfUnity_sq_add_levelThreeRootOfUnity_add_one h)

/-- The classifying homomorphism of a basis of the `3`-torsion sends the parameter to
`levelThreeParameter h`. -/
@[simp]
theorem classifyingHom_parameter : classifyingHom h parameter = levelThreeParameter h :=
  lift_parameter ..

/-- The classifying homomorphism of a basis of the `3`-torsion sends the root of unity to
`levelThreeRootOfUnity h`. -/
@[simp]
theorem classifyingHom_rootOfUnity : classifyingHom h rootOfUnity = levelThreeRootOfUnity h :=
  lift_rootOfUnity ..

/-- The base change of the universal curve along the classifying homomorphism of a basis of the
`3`-torsion of `W` is the level-three normal form reached by `toLevelThreeNormalForm h`. -/
@[simp]
theorem map_classifyingHom :
    curve.map (classifyingHom h) = levelThreeNormalForm (levelThreeParameter h) :=
  map_lift ..

/-- The classifying homomorphism of a basis of the `3`-torsion is natural in the base ring: followed
by a ring homomorphism `φ : R →+* S`, it is the classifying homomorphism of the image basis of the
`3`-torsion of `W.map φ`. -/
theorem comp_classifyingHom {S : Type*} [CommRing S] (φ : R →+* S) :
    φ.comp (classifyingHom h) = classifyingHom (h.map φ) := by
  ext <;> simp [levelThreeParameter_map, levelThreeRootOfUnity_map]

include h in
/-- **The universal property of the curve with a basis of its `3`-torsion.** Let `(P, Q)` be a
basis of the `3`-torsion of `W`, with `P = (x₁, y₁)` and `Q = (x₂, y₂)`. Then there is exactly one
pair of a ring homomorphism `f : ℤ[1/3, ζ₃][μ, 1/(μ³ - 1)] →+* R` and a change of variables `C`
such that `C` carries `W` to the base change of `UniversalLevelThree.curve` along `f`, `P` to
`(0, 0)` and `Q` to the image of the universal second basis point
`(-(μ² + μ + 1), (μ² + μ + 1)(μ - ζ))`, namely `(classifyingHom h, toLevelThreeNormalForm h)`. -/
theorem existsUnique_lift :
    ∃! p : (Ring →+* R) × VariableChange R, p.2.r = x₁ ∧ p.2.t = y₁ ∧ p.2 • W = curve.map p.1 ∧
      x₂ = p.2.u ^ 2 * p.1 (-(parameter ^ 2 + parameter + 1)) + p.2.r ∧
      y₂ = p.2.u ^ 3 * p.1 ((parameter ^ 2 + parameter + 1) * (parameter - rootOfUnity)) +
        p.2.u ^ 2 * p.2.s * p.1 (-(parameter ^ 2 + parameter + 1)) + p.2.t := by
  refine ⟨(classifyingHom h, toLevelThreeNormalForm h), ⟨rfl, rfl, ?_, ?_, ?_⟩, ?_⟩
  · rw [map_classifyingHom, toLevelThreeNormalForm_smul]
  · simpa only [map_neg, map_add, map_mul, map_pow, map_one, classifyingHom_parameter,
      toLevelThreeNormalForm_r] using
      toLevelThreeNormalForm_basisPoint_x h
  · simpa only [map_neg, map_add, map_mul, map_pow, map_one, map_sub, classifyingHom_parameter,
      classifyingHom_rootOfUnity, toLevelThreeNormalForm_t] using
      toLevelThreeNormalForm_basisPoint_y h
  rintro ⟨f, C⟩ ⟨hr, ht, hC, hx₂, hy₂⟩
  simp only [map_neg, map_add, map_mul, map_pow, map_one, map_sub] at hx₂ hy₂
  rw [curve_eq, map_levelThreeNormalForm] at hC
  have hfμ := eq_levelThreeParameter h hr ht hC hx₂ hy₂
  have hfζ := eq_levelThreeRootOfUnity h hr ht hC hx₂ hy₂
  obtain rfl := eq_toLevelThreeNormalForm h hr ht hC hx₂ hy₂
  simp only [Prod.mk.injEq, and_true]
  ext
  · rw [hfμ, classifyingHom_parameter]
  · rw [hfζ, classifyingHom_rootOfUnity]

end UniversalLevelThree

end WeierstrassCurve

end
