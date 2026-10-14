/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.Basic
public import TauCeti.Algebra.Module.Torsion.Int
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.VariableChange
public import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Singular
public import TauCeti.RingTheory.RootsOfUnity.Basic
-- Proof-only: an algebraic closure, over which the singular point has rational tangent slopes.
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
-- Proof-only: points carried along a field homomorphism.
import TauCeti.AlgebraicGeometry.EllipticCurve.Affine.Point.MapAlong

/-!
# The nonsingular points of a singular Weierstrass curve

Let `W` be a Weierstrass curve over a field `F` with a singular point `(x₀, y₀) ∈ F²`. Its
nonsingular points still form a group, Mathlib's `W.toAffine.Point`, and this file identifies that
group with the additive or the multiplicative group of `F` (Silverman III.2.5).

Expanded at the singular point, the equation of `W` reads

`(y - y₀)² + a₁ (x - x₀) (y - y₀) = (x - x₀)³ + (3 x₀ + a₂) (x - x₀)²`

(`WeierstrassCurve.Affine.equation_iff_of_isSingular`), so the two tangent lines at `(x₀, y₀)` have
slopes the roots of the **tangent quadratic** `T² + a₁ T - (3 x₀ + a₂)`. Suppose that `α ∈ F` is a
root; the other root is `β = -a₁ - α`, which is also in `F`.

* At a **cusp**, `α = β`, that is `2 α + a₁ = 0`, and the equation reads `u² = (x - x₀)³` with
  `u = y - y₀ - α (x - x₀)`. The map `(x, y) ↦ (x - x₀) / u`, sending the point at infinity to `0`,
  is an isomorphism `W.toAffine.Point ≃+ F` (`WeierstrassCurve.Affine.Point.cuspAddEquiv`).
* At a **split node**, `α ≠ β`, and the equation reads `u w = (x - x₀)³` with
  `w = y - y₀ - β (x - x₀)`. The map `(x, y) ↦ u / w`, sending the point at infinity to `1`, is an
  isomorphism `W.toAffine.Point ≃+ Additive Fˣ` (`WeierstrassCurve.Affine.Point.nodeAddEquiv`).

In both cases three points add to zero exactly when they lie on a line, and the line
`u = m (x - x₀) + c` meets the curve where the parameter `t = (x - x₀) / u`, respectively
`s = u / w`, satisfies a cubic whose roots sum to `0`, respectively multiply to `1`. The proofs
below verify this on Mathlib's chord-and-tangent formulas after moving the singular point to the
origin by a change of variables.

When the tangent quadratic has no root in `F`, the singular point is a nonsplit node, or, over an
imperfect field of characteristic `2`, a cusp whose tangent is not defined over `F`. The group of
nonsingular points is then a twisted form of `Fˣ` or of `F`, and these cases are not treated here.

As a consequence, for `n` invertible in `F` the number of `n`-torsion points among the nonsingular
points divides `n` (`WeierstrassCurve.Affine.Point.natCard_torsionBy_dvd_of_isSingular`), since `F`
has no such torsion and the `n`-th roots of unity in `Fˣ` form a cyclic group of order dividing
`n`. Passing to an algebraic closure, where every singular point has rational tangent slopes, this
holds for every Weierstrass curve with vanishing discriminant over any field
(`WeierstrassCurve.Affine.Point.natCard_torsionBy_dvd_of_Δ_eq_zero`). In the proof of the criterion
of Néron, Ogg and Shafarevich (Silverman VII.7.1) this bound, applied to the reduced curve,
excludes bad reduction when the torsion of order prime to the residue characteristic is unramified.

## Main definitions

* `WeierstrassCurve.Affine.Point.cuspAddEquiv`: at a cusp with tangent slope `α ∈ F`, the
  isomorphism `W.toAffine.Point ≃+ F`.
* `WeierstrassCurve.Affine.Point.nodeAddEquiv`: at a node with tangent slopes in `F`, the
  isomorphism `W.toAffine.Point ≃+ Additive Fˣ`.

## Main results

* `WeierstrassCurve.Affine.Point.cuspAddEquiv_some` and
  `WeierstrassCurve.Affine.Point.val_toMul_nodeAddEquiv_some`: the coordinate formulas.
* `WeierstrassCurve.Affine.Point.cuspAddEquiv_symm_of_ne_zero` and
  `WeierstrassCurve.Affine.Point.nodeAddEquiv_symm_of_ne_one`: the points with a given parameter.
* `WeierstrassCurve.Affine.Point.natCard_torsionBy_dvd_of_isSingular`: when the tangent slopes at
  a singular point lie in `F`, the number of `n`-torsion points divides `n`, for `n` invertible in
  `F`.
* `WeierstrassCurve.Affine.Point.natCard_torsionBy_dvd_of_Δ_eq_zero`: the same divisibility over
  any field whenever `Δ = 0`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], III.2.5 and VII.7.1.
-/

public section

namespace WeierstrassCurve.Affine

open Polynomial

variable {F : Type*} [Field F] {W : WeierstrassCurve F} {α : F}

/-! ### Models singular at the origin -/

section Origin

/-- The algebraic heart of the cusp group law, on `u² = x³` with `u = y - α x`. Let `m` be the
slope in `(x, u)`-coordinates of the line through the points of parameters `t₁` and `t₂`, that is
of `(1 / tᵢ², 1 / tᵢ³)`, or of the tangent when `t₁ = t₂`. The sum of the two points has
`x = m² - x₁ - x₂` and `u = -m (x - x₁) - u₁`, and the conclusion `x = (t₁ + t₂) u` says that its
parameter is `t₁ + t₂`. -/
private theorem cusp_add_aux {t₁ t₂ m : F} (h₁ : t₁ ≠ 0) (h₂ : t₂ ≠ 0) (h : t₁ + t₂ ≠ 0)
    (hm : m * ((t₁ + t₂) * t₁ * t₂) = t₁ ^ 2 + t₁ * t₂ + t₂ ^ 2) :
    m ^ 2 - 1 / t₁ ^ 2 - 1 / t₂ ^ 2 =
      (t₁ + t₂) * (-(m * (m ^ 2 - 1 / t₁ ^ 2 - 1 / t₂ ^ 2 - 1 / t₁ ^ 2)) - 1 / t₁ ^ 3) := by
  rw [← eq_div_iff (by simp [*])] at hm
  subst hm
  field_simp
  ring

/-- The algebraic heart of the node group law, on `u w = x³` with `u - w = d x`. Let `m` be the
slope in `(x, u)`-coordinates of the line through the points of parameters `s₁` and `s₂`, that is
of `(d² sᵢ / (sᵢ - 1)², d³ sᵢ² / (sᵢ - 1)³)`, or of the tangent when `s₁ = s₂`. The sum of the two
points has `x = m (m - d) - x₁ - x₂`, `u = -(m - d) (x - x₁) - w₁` and `w = u - d x`, and the
conclusion `u = s₁ s₂ w` says that its parameter is `s₁ s₂`. -/
private theorem node_add_aux {s₁ s₂ d m x₁ x₂ w₁ : F} (hd : d ≠ 0) (h₁ : s₁ - 1 ≠ 0)
    (h₂ : s₂ - 1 ≠ 0) (h : 1 - s₁ * s₂ ≠ 0) (hx₁ : x₁ = d ^ 2 * s₁ / (s₁ - 1) ^ 2)
    (hx₂ : x₂ = d ^ 2 * s₂ / (s₂ - 1) ^ 2) (hw₁ : w₁ = d ^ 3 * s₁ / (s₁ - 1) ^ 3)
    (hm : m * ((s₁ - 1) * (s₂ - 1) * (1 - s₁ * s₂)) =
      d * (3 * s₁ * s₂ - s₁ ^ 2 * s₂ ^ 2 - s₁ - s₂)) :
    -(m - d) * (m * (m - d) - x₁ - x₂ - x₁) - w₁ =
      s₁ * s₂ * (-(m - d) * (m * (m - d) - x₁ - x₂ - x₁) - w₁ - d * (m * (m - d) - x₁ - x₂)) := by
  rw [← eq_div_iff (by simp [*])] at hm
  subst hm hx₁ hx₂ hw₁
  field_simp
  ring

/-! #### The cusp -/

section Cusp

variable (h0 : W.toAffine.IsSingular 0 0) (hα : α ^ 2 + W.a₁ * α - W.a₂ = 0)
  (hc : 2 * α + W.a₁ = 0)

include h0 hα hc in
private theorem cusp_coeffs : W.a₁ = -2 * α ∧ W.a₂ = -α ^ 2 ∧ W.a₃ = 0 ∧ W.a₄ = 0 := by
  obtain ⟨-, h4, h3⟩ := (isSingular_zero _).1 h0
  exact ⟨by linear_combination hc, by linear_combination -hα + α * hc, h3, h4⟩

include h0 hα hc in
/-- At a cusp with tangent `y = α x` the equation reads `(y - α x)² = x³`. -/
private theorem equation_iff_cusp {x y : F} :
    W.toAffine.Equation x y ↔ (y - α * x) ^ 2 = x ^ 3 := by
  rw [equation_iff_of_isSingular_zero h0]
  constructor <;> intro h
  · linear_combination h - (x * y - α * x ^ 2) * hc - x ^ 2 * hα
  · linear_combination h + (x * y - α * x ^ 2) * hc + x ^ 2 * hα

include h0 hα hc in
/-- A nonsingular point of a cusp is `(1 / t², 1 / t³ + α / t²)` for `t = x / (y - α x)`. -/
private theorem cusp_param {x y : F} (h : W.toAffine.Nonsingular x y) :
    y - α * x ≠ 0 ∧ x = 1 / (x / (y - α * x)) ^ 2 ∧
      y = 1 / (x / (y - α * x)) ^ 3 + α / (x / (y - α * x)) ^ 2 := by
  have hx := ne_zero_of_isSingular_zero h0 h
  have he := (equation_iff_cusp h0 hα hc).1 h.1
  have hu : y - α * x ≠ 0 := fun hu ↦ hx <| by
    rw [hu, zero_pow two_ne_zero] at he
    exact pow_eq_zero_iff three_ne_zero |>.1 he.symm
  refine ⟨hu, ?_, ?_⟩
  · field_simp
    linear_combination -he
  · field_simp
    linear_combination -y * he

include h0 hα hc in
private theorem cusp_nonsingular {t : F} (ht : t ≠ 0) :
    W.toAffine.Nonsingular (1 / t ^ 2) (1 / t ^ 3 + α / t ^ 2) :=
  nonsingular_of_isSingular_zero h0 ((equation_iff_cusp h0 hα hc).2 (by field_simp; ring))
    (by simpa using ht)

/-- The parameter `t = x / (y - α x)` of a point of a cusp, with the point at infinity at `0`. -/
private def cuspFun (α : F) : W.toAffine.Point → F
  | 0 => 0
  | .some x y _ => x / (y - α * x)

private theorem cuspFun_zero : cuspFun (W := W) α 0 = 0 := rfl

private theorem cuspFun_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    cuspFun α (.some x y h) = x / (y - α * x) := rfl

variable [DecidableEq F]

include h0 hα hc in
/-- The cusp group law along the tangent: doubling a point that is not `2`-torsion doubles its
parameter. The tangent slope in `(x, u)`-coordinates is `3 / (2 t)`. -/
private theorem cuspFun_add_self {x₁ y₁ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    cuspFun α (.some x₁ y₁ h₁ + .some x₁ y₁ h₁) =
      cuspFun α (.some x₁ y₁ h₁) + cuspFun α (.some x₁ y₁ h₁) := by
  obtain ⟨ha₁, ha₂, ha₃, ha₄⟩ := cusp_coeffs h0 hα hc
  obtain ⟨hu₁, hx₁, hy₁⟩ := cusp_param h0 hα hc h₁
  have ht₁ : x₁ / (y₁ - α * x₁) ≠ 0 := div_ne_zero (ne_zero_of_isSingular_zero h0 h₁) hu₁
  have hxy : ¬(x₁ = x₁ ∧ y₁ = W.toAffine.negY x₁ y₁) := fun hxy ↦ hy hxy.2
  rw [Point.add_some hxy, cuspFun_some, cuspFun_some,
    div_eq_iff (cusp_param h0 hα hc (nonsingular_add h₁ h₁ hxy)).1, slope_of_Y_ne rfl hy]
  have hy' : y₁ - W.toAffine.negY x₁ y₁ = 2 * (y₁ - α * x₁) := by
    simp only [negY, ha₁, ha₃]; ring
  have h2 : (2 : F) ≠ 0 := fun h2 ↦ hy (by linear_combination hy' + (y₁ - α * x₁) * h2)
  generalize hℓ : (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) /
    (y₁ - W.toAffine.negY x₁ y₁) = ℓ
  rw [hy', div_eq_iff (mul_ne_zero h2 hu₁)] at hℓ
  generalize x₁ / (y₁ - α * x₁) = t₁ at *
  subst hx₁ hy₁
  simp only [addY, negY, negAddY, addX, ha₁, ha₂, ha₃, ha₄] at hℓ ⊢
  have key := cusp_add_aux (m := ℓ - α) ht₁ ht₁ (by simpa [← two_mul] using ⟨h2, ht₁⟩) (by
    field_simp at hℓ
    linear_combination -t₁ ^ 2 * hℓ)
  linear_combination key

include h0 hα hc in
/-- The cusp group law along a chord: two points with distinct `x`-coordinates add their
parameters. -/
private theorem cuspFun_add_of_X_ne {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    cuspFun α (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) =
      cuspFun α (.some x₁ y₁ h₁) + cuspFun α (.some x₂ y₂ h₂) := by
  obtain ⟨ha₁, ha₂, ha₃, -⟩ := cusp_coeffs h0 hα hc
  obtain ⟨hu₁, hx₁, hy₁⟩ := cusp_param h0 hα hc h₁
  obtain ⟨hu₂, hx₂, hy₂⟩ := cusp_param h0 hα hc h₂
  have ht₁ : x₁ / (y₁ - α * x₁) ≠ 0 := div_ne_zero (ne_zero_of_isSingular_zero h0 h₁) hu₁
  have ht₂ : x₂ / (y₂ - α * x₂) ≠ 0 := div_ne_zero (ne_zero_of_isSingular_zero h0 h₂) hu₂
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun hxy ↦ hx hxy.1
  rw [Point.add_some hxy, cuspFun_some, cuspFun_some, cuspFun_some,
    div_eq_iff (cusp_param h0 hα hc (nonsingular_add h₁ h₂ hxy)).1, slope_of_X_ne hx]
  generalize hℓ : (y₁ - y₂) / (x₁ - x₂) = ℓ
  rw [div_eq_iff (sub_ne_zero.2 hx)] at hℓ
  generalize x₁ / (y₁ - α * x₁) = t₁ at *
  generalize x₂ / (y₂ - α * x₂) = t₂ at *
  subst hx₁ hy₁ hx₂ hy₂
  have hne : t₁ - t₂ ≠ 0 := sub_ne_zero.2 (by rintro rfl; exact hx rfl)
  have hne' : t₁ + t₂ ≠ 0 := fun h ↦ hx (by rw [eq_neg_of_add_eq_zero_left h]; ring)
  simp only [addY, negY, negAddY, addX, ha₁, ha₂, ha₃] at hℓ ⊢
  have key := cusp_add_aux (m := ℓ - α) ht₁ ht₂ hne' (by
    field_simp at hℓ
    refine mul_left_cancel₀ hne ?_
    linear_combination hℓ)
  linear_combination key

include h0 hα hc in
private theorem cuspFun_add (P Q : W.toAffine.Point) :
    cuspFun α (P + Q) = cuspFun α P + cuspFun α Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · simp [← Point.zero_def, cuspFun_zero]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [← Point.zero_def, cuspFun_zero]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · -- `Q = -P`, whose parameter is `-t₁`
    rw [Point.add_of_Y_eq hxy.1 hxy.2, cuspFun_zero, cuspFun_some, cuspFun_some]
    obtain ⟨rfl, rfl⟩ := hxy
    obtain ⟨ha₁, -, ha₃, -⟩ := cusp_coeffs h0 hα hc
    -- negation reverses the sign of `u = y - α x`
    have hu : W.toAffine.negY x₁ y₂ - α * x₁ = -(y₂ - α * x₁) := by
      simp only [negY, ha₁, ha₃]; ring
    rw [hu, div_neg, neg_add_cancel]
  by_cases hx : x₁ = x₂
  · obtain rfl := hx
    obtain rfl := Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun hy ↦ hxy ⟨rfl, hy⟩)
    exact cuspFun_add_self h0 hα hc h₁ (fun hy ↦ hxy ⟨rfl, hy⟩)
  · exact cuspFun_add_of_X_ne h0 hα hc h₁ h₂ hx

/-- The isomorphism `W.toAffine.Point ≃+ F` at a cusp singular at the origin. -/
private def cuspAddEquivOfIsSingularZero : W.toAffine.Point ≃+ F where
  toFun := cuspFun α
  invFun t := if ht : t = 0 then 0 else .some _ _ (cusp_nonsingular h0 hα hc ht)
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · simp [← Point.zero_def, cuspFun_zero]
    · beta_reduce
      obtain ⟨hu, hx, hy⟩ := cusp_param h0 hα hc h
      rw [cuspFun_some, dite_eq_right (div_ne_zero (ne_zero_of_isSingular_zero h0 h) hu),
        Point.some.injEq]
      exact ⟨hx.symm, hy.symm⟩
  right_inv t := by
    beta_reduce
    by_cases ht : t = 0
    · simp [ht, cuspFun_zero]
    · rw [dite_eq_right ht, cuspFun_some]
      field_simp
      ring
  map_add' := cuspFun_add h0 hα hc

private theorem cuspAddEquivOfIsSingularZero_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    cuspAddEquivOfIsSingularZero h0 hα hc (.some x y h) = x / (y - α * x) := rfl

private theorem cuspAddEquivOfIsSingularZero_symm_of_ne_zero {t : F} (ht : t ≠ 0) :
    (cuspAddEquivOfIsSingularZero h0 hα hc).symm t = .some _ _ (cusp_nonsingular h0 hα hc ht) :=
  dite_eq_right ht

end Cusp

/-! #### The split node -/

section Node

variable (h0 : W.toAffine.IsSingular 0 0) (hα : α ^ 2 + W.a₁ * α - W.a₂ = 0)
  (hn : 2 * α + W.a₁ ≠ 0)

include h0 hα in
private theorem node_coeffs : W.a₂ = α ^ 2 + W.a₁ * α ∧ W.a₃ = 0 ∧ W.a₄ = 0 := by
  obtain ⟨-, h4, h3⟩ := (isSingular_zero _).1 h0
  exact ⟨by linear_combination -hα, h3, h4⟩

include h0 hα in
/-- At a node with tangents `y = α x` and `y = -(a₁ + α) x` the equation reads
`(y - α x) (y + (a₁ + α) x) = x³`. -/
private theorem equation_iff_node {x y : F} :
    W.toAffine.Equation x y ↔ (y - α * x) * (y + (W.a₁ + α) * x) = x ^ 3 := by
  rw [equation_iff_of_isSingular_zero h0]
  constructor <;> intro h
  · linear_combination h - x ^ 2 * hα
  · linear_combination h + x ^ 2 * hα

include h0 hα hn in
/-- A nonsingular point of a split node is `(D² s / (s - 1)², -D³ s² / (s - 1)³ + α x)` for
`D = 2 α + a₁` and `s = (y - α x) / (y + (a₁ + α) x) ≠ 1`. -/
private theorem node_param {x y : F} (h : W.toAffine.Nonsingular x y) :
    y - α * x ≠ 0 ∧ y + (W.a₁ + α) * x ≠ 0 ∧
      (y - α * x) / (y + (W.a₁ + α) * x) ≠ 1 ∧
      x = (2 * α + W.a₁) ^ 2 * ((y - α * x) / (y + (W.a₁ + α) * x)) /
        ((y - α * x) / (y + (W.a₁ + α) * x) - 1) ^ 2 ∧
      y = -(2 * α + W.a₁) ^ 3 * ((y - α * x) / (y + (W.a₁ + α) * x)) ^ 2 /
          ((y - α * x) / (y + (W.a₁ + α) * x) - 1) ^ 3 +
        α * ((2 * α + W.a₁) ^ 2 * ((y - α * x) / (y + (W.a₁ + α) * x)) /
          ((y - α * x) / (y + (W.a₁ + α) * x) - 1) ^ 2) := by
  have hx := ne_zero_of_isSingular_zero h0 h
  have he := (equation_iff_node h0 hα).1 h.1
  have hu : y - α * x ≠ 0 := fun hu ↦ hx <| by
    rw [hu, zero_mul] at he
    exact pow_eq_zero_iff three_ne_zero |>.1 he.symm
  have hw : y + (W.a₁ + α) * x ≠ 0 := fun hw ↦ hx <| by
    rw [hw, mul_zero] at he
    exact pow_eq_zero_iff three_ne_zero |>.1 he.symm
  have hs : (y - α * x) / (y + (W.a₁ + α) * x) - 1 =
      -((2 * α + W.a₁) * x) / (y + (W.a₁ + α) * x) := by
    rw [div_sub_one hw]
    ring
  have hs0 : -((2 * α + W.a₁) * x) ≠ 0 := neg_ne_zero.2 (mul_ne_zero hn hx)
  refine ⟨hu, hw, sub_ne_zero.1 (hs ▸ div_ne_zero hs0 hw), ?_, ?_⟩
  · rw [hs]
    field_simp
    linear_combination -he
  · rw [hs]
    field_simp
    linear_combination -y * he

include h0 hα hn in
private theorem node_nonsingular {s : F} (hs₀ : s ≠ 0) (hs : s - 1 ≠ 0) :
    W.toAffine.Nonsingular ((2 * α + W.a₁) ^ 2 * s / (s - 1) ^ 2)
      (-(2 * α + W.a₁) ^ 3 * s ^ 2 / (s - 1) ^ 3 + α * ((2 * α + W.a₁) ^ 2 * s / (s - 1) ^ 2)) :=
  nonsingular_of_isSingular_zero h0 ((equation_iff_node h0 hα).2 (by field_simp; ring))
    (div_ne_zero (mul_ne_zero (pow_ne_zero 2 hn) hs₀) (pow_ne_zero 2 hs))

/-- The parameter `s = (y - α x) / (y + (a₁ + α) x)` of a point of a split node, with the point at
infinity at `1`. -/
private def nodeFun : W.toAffine.Point → Fˣ
  | 0 => 1
  | .some x y h => Units.mk0 ((y - α * x) / (y + (W.a₁ + α) * x))
      (div_ne_zero (node_param h0 hα hn h).1 (node_param h0 hα hn h).2.1)

private theorem nodeFun_zero : nodeFun h0 hα hn 0 = 1 := rfl

private theorem val_nodeFun_some {x y : F} (h : W.toAffine.Nonsingular x y) :
    (nodeFun h0 hα hn (.some x y h) : F) = (y - α * x) / (y + (W.a₁ + α) * x) := rfl

variable [DecidableEq F]

include h0 hα hn in
/-- The node group law along the tangent: doubling a point that is not `2`-torsion squares its
parameter. -/
private theorem val_nodeFun_add_self {x₁ y₁ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (hy : y₁ ≠ W.toAffine.negY x₁ y₁) :
    (nodeFun h0 hα hn (.some x₁ y₁ h₁ + .some x₁ y₁ h₁) : F) =
      nodeFun h0 hα hn (.some x₁ y₁ h₁) * nodeFun h0 hα hn (.some x₁ y₁ h₁) := by
  obtain ⟨ha₂, ha₃, ha₄⟩ := node_coeffs h0 hα
  obtain ⟨-, -, hs₁, hx₁, hy₁⟩ := node_param h0 hα hn h₁
  have hxy : ¬(x₁ = x₁ ∧ y₁ = W.toAffine.negY x₁ y₁) := fun hxy ↦ hy hxy.2
  rw [Point.add_some hxy, val_nodeFun_some, val_nodeFun_some,
    div_eq_iff (node_param h0 hα hn (nonsingular_add h₁ h₁ hxy)).2.1, slope_of_Y_ne rfl hy]
  have hy' : y₁ - W.toAffine.negY x₁ y₁ = (y₁ - α * x₁) + (y₁ + (W.a₁ + α) * x₁) := by
    simp only [negY, ha₃]; ring
  have hsum : (y₁ - α * x₁) + (y₁ + (W.a₁ + α) * x₁) ≠ 0 := hy' ▸ sub_ne_zero.2 hy
  generalize hℓ : (3 * x₁ ^ 2 + 2 * W.a₂ * x₁ + W.a₄ - W.a₁ * y₁) /
    (y₁ - W.toAffine.negY x₁ y₁) = ℓ
  rw [hy', div_eq_iff hsum, ha₂, ha₄] at hℓ
  -- the tangent slope in `(x, u)`-coordinates satisfies `m (u + w) = 3 x² - D u`
  have hm : (ℓ - α) * ((y₁ - α * x₁) + (y₁ + (W.a₁ + α) * x₁)) =
      3 * x₁ ^ 2 - (2 * α + W.a₁) * (y₁ - α * x₁) := by
    linear_combination -hℓ
  generalize (y₁ - α * x₁) / (y₁ + (W.a₁ + α) * x₁) = s₁ at *
  have hs : s₁ - 1 ≠ 0 := sub_ne_zero.2 hs₁
  have hw₁ : y₁ + (W.a₁ + α) * x₁ = (-(2 * α + W.a₁)) ^ 3 * s₁ / (s₁ - 1) ^ 3 := by
    rw [hy₁, hx₁]
    field_simp
    ring
  have hsum' : (y₁ - α * x₁) + (y₁ + (W.a₁ + α) * x₁) =
      -(2 * α + W.a₁) ^ 3 * s₁ * (s₁ + 1) / (s₁ - 1) ^ 3 := by
    rw [hy₁, hx₁]
    field_simp
    ring
  -- the point is not `2`-torsion, so `s₁ ≠ -1`
  have h11 : 1 - s₁ * s₁ ≠ 0 := by
    intro h
    have h' : (1 - s₁) * (s₁ + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.1 h' with h' | h'
    · exact hs (by linear_combination -h')
    · exact hsum (by rw [hsum', h']; simp)
  have key := node_add_aux (x₁ := x₁) (x₂ := x₁) (w₁ := y₁ + (W.a₁ + α) * x₁) (m := ℓ - α)
    (neg_ne_zero.2 hn) hs hs h11 (by rw [hx₁]; ring) (by rw [hx₁]; ring) hw₁ (by
      rw [hsum', hy₁, hx₁] at hm
      field_simp at hm
      have hK : (2 * α + W.a₁) ^ 3 * s₁ ≠ 0 := mul_ne_zero (pow_ne_zero 3 hn) (by
        rintro rfl
        exact hsum (by simpa using hsum'))
      refine mul_left_cancel₀ hK ?_
      linear_combination (s₁ - 1) ^ 2 * hm)
  simp only [addY, negY, negAddY, addX, ha₂, ha₃]
  linear_combination key

include h0 hα hn in
/-- The node group law along a chord: two points with distinct `x`-coordinates multiply their
parameters. -/
private theorem val_nodeFun_add_of_X_ne {x₁ y₁ x₂ y₂ : F} (h₁ : W.toAffine.Nonsingular x₁ y₁)
    (h₂ : W.toAffine.Nonsingular x₂ y₂) (hx : x₁ ≠ x₂) :
    (nodeFun h0 hα hn (.some x₁ y₁ h₁ + .some x₂ y₂ h₂) : F) =
      nodeFun h0 hα hn (.some x₁ y₁ h₁) * nodeFun h0 hα hn (.some x₂ y₂ h₂) := by
  obtain ⟨ha₂, ha₃, -⟩ := node_coeffs h0 hα
  obtain ⟨-, -, hs₁, hx₁, hy₁⟩ := node_param h0 hα hn h₁
  obtain ⟨-, -, hs₂, hx₂, hy₂⟩ := node_param h0 hα hn h₂
  have hxy : ¬(x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂) := fun hxy ↦ hx hxy.1
  rw [Point.add_some hxy, val_nodeFun_some, val_nodeFun_some, val_nodeFun_some,
    div_eq_iff (node_param h0 hα hn (nonsingular_add h₁ h₂ hxy)).2.1, slope_of_X_ne hx]
  generalize hℓ : (y₁ - y₂) / (x₁ - x₂) = ℓ
  rw [div_eq_iff (sub_ne_zero.2 hx)] at hℓ
  generalize (y₁ - α * x₁) / (y₁ + (W.a₁ + α) * x₁) = s₁ at *
  generalize (y₂ - α * x₂) / (y₂ + (W.a₁ + α) * x₂) = s₂ at *
  have hw₁ : y₁ + (W.a₁ + α) * x₁ = (-(2 * α + W.a₁)) ^ 3 * s₁ / (s₁ - 1) ^ 3 := by
    have := sub_ne_zero.2 hs₁
    rw [hy₁, hx₁]
    field_simp
    ring
  have hne : s₁ - s₂ ≠ 0 := sub_ne_zero.2 (by rintro rfl; exact hx (hx₁.trans hx₂.symm))
  -- the two points are not opposite, so `s₁ s₂ ≠ 1`
  have h12 : 1 - s₁ * s₂ ≠ 0 := fun h12 ↦ hx <| by
    rw [hx₁, hx₂, div_eq_div_iff (pow_ne_zero 2 (sub_ne_zero.2 hs₁))
      (pow_ne_zero 2 (sub_ne_zero.2 hs₂))]
    linear_combination (2 * α + W.a₁) ^ 2 * (s₁ - s₂) * h12
  have key := node_add_aux (x₁ := x₁) (x₂ := x₂) (w₁ := y₁ + (W.a₁ + α) * x₁) (m := ℓ - α)
    (neg_ne_zero.2 hn) (sub_ne_zero.2 hs₁) (sub_ne_zero.2 hs₂) h12 (by rw [hx₁]; ring)
    (by rw [hx₂]; ring) hw₁ (by
      rw [hx₁, hx₂, hy₁, hy₂] at hℓ
      field_simp at hℓ
      refine mul_left_cancel₀ hne ?_
      linear_combination -hℓ)
  simp only [addY, negY, negAddY, addX, ha₂, ha₃]
  linear_combination key

private theorem nodeFun_add (P Q : W.toAffine.Point) :
    nodeFun h0 hα hn (P + Q) = nodeFun h0 hα hn P * nodeFun h0 hα hn Q := by
  rcases P with _ | ⟨x₁, y₁, h₁⟩
  · simp [← Point.zero_def, nodeFun_zero]
  rcases Q with _ | ⟨x₂, y₂, h₂⟩
  · simp [← Point.zero_def, nodeFun_zero]
  ext
  rw [Units.val_mul]
  by_cases hxy : x₁ = x₂ ∧ y₁ = W.toAffine.negY x₂ y₂
  · -- `Q = -P`, whose parameter is `s₁⁻¹`
    rw [Point.add_of_Y_eq hxy.1 hxy.2, nodeFun_zero, val_nodeFun_some, val_nodeFun_some,
      Units.val_one]
    obtain ⟨rfl, rfl⟩ := hxy
    obtain ⟨-, ha₃, -⟩ := node_coeffs h0 hα
    obtain ⟨hu₂, hw₂, -⟩ := node_param h0 hα hn h₂
    -- negation swaps `u = y - α x` and `w = y + (a₁ + α) x` up to sign
    have hu : W.toAffine.negY x₁ y₂ - α * x₁ = -(y₂ + (W.a₁ + α) * x₁) := by
      simp only [negY, ha₃]; ring
    have hw : W.toAffine.negY x₁ y₂ + (W.a₁ + α) * x₁ = -(y₂ - α * x₁) := by
      simp only [negY, ha₃]; ring
    rw [hu, hw, neg_div_neg_eq, div_mul_div_comm, mul_comm, div_self (mul_ne_zero hu₂ hw₂)]
  by_cases hx : x₁ = x₂
  · obtain rfl := hx
    obtain rfl := Y_eq_of_Y_ne h₁.1 h₂.1 rfl (fun hy ↦ hxy ⟨rfl, hy⟩)
    exact val_nodeFun_add_self h0 hα hn h₁ (fun hy ↦ hxy ⟨rfl, hy⟩)
  · exact val_nodeFun_add_of_X_ne h0 hα hn h₁ h₂ hx

/-- The isomorphism `W.toAffine.Point ≃+ Additive Fˣ` at a split node singular at the origin. -/
private def nodeAddEquivOfIsSingularZero : W.toAffine.Point ≃+ Additive Fˣ where
  toFun P := .ofMul (nodeFun h0 hα hn P)
  invFun s := if hs : (s.toMul : F) = 1 then 0 else
    .some _ _ (node_nonsingular h0 hα hn s.toMul.ne_zero (sub_ne_zero.2 hs))
  left_inv := by
    rintro (_ | ⟨x, y, h⟩)
    · simp [← Point.zero_def, nodeFun_zero h0 hα hn]
    · beta_reduce
      obtain ⟨-, -, hs, hx, hy⟩ := node_param h0 hα hn h
      rw [toMul_ofMul, dite_eq_right (by rwa [val_nodeFun_some]), Point.some.injEq,
        val_nodeFun_some]
      exact ⟨hx.symm, hy.symm⟩
  right_inv s := by
    beta_reduce
    by_cases hs : (s.toMul : F) = 1
    · rw [dite_eq_left hs, nodeFun_zero, ofMul_one, eq_comm, ← toMul_eq_one]
      exact Units.ext hs
    · rw [dite_eq_right hs]
      apply Additive.toMul.injective
      rw [toMul_ofMul]
      ext
      have hs' := sub_ne_zero.2 hs
      rw [val_nodeFun_some, div_eq_iff (node_param h0 hα hn
        (node_nonsingular h0 hα hn s.toMul.ne_zero hs')).2.1]
      field_simp
      ring
  map_add' P Q := by
    rw [nodeFun_add h0 hα hn]
    rfl

private theorem val_toMul_nodeAddEquivOfIsSingularZero_some {x y : F}
    (h : W.toAffine.Nonsingular x y) :
    ((nodeAddEquivOfIsSingularZero h0 hα hn (.some x y h)).toMul : F) =
      (y - α * x) / (y + (W.a₁ + α) * x) := rfl

private theorem nodeAddEquivOfIsSingularZero_symm_of_ne_one {s : Additive Fˣ}
    (hs : (s.toMul : F) ≠ 1) :
    (nodeAddEquivOfIsSingularZero h0 hα hn).symm s =
      .some _ _ (node_nonsingular h0 hα hn s.toMul.ne_zero (sub_ne_zero.2 hs)) :=
  dite_eq_right hs

end Node

end Origin

/-! ### An arbitrary singular point -/

namespace Point

variable {x₀ y₀ : F}

/-- Translating a singular point `(x₀, y₀)` to the origin keeps `a₁` and changes `a₂` to
`3 x₀ + a₂`, the linear coefficient of the tangent quadratic. -/
private theorem isSingular_zero_translate (h : W.toAffine.IsSingular x₀ y₀) :
    (VariableChange.mk 1 x₀ 0 y₀ • W).toAffine.IsSingular 0 0 ∧
      (VariableChange.mk 1 x₀ 0 y₀ • W).a₁ = W.a₁ ∧
      (VariableChange.mk 1 x₀ 0 y₀ • W).a₂ = 3 * x₀ + W.a₂ :=
  ⟨(isSingular_iff_variableChange _ x₀ y₀).1 h, by simp [variableChange_a₁],
    by simp [variableChange_a₂]; ring⟩

/-- A nonsingular point of the model translated to the origin gives one of `W`. -/
private theorem nonsingular_of_translate {x y : F}
    (h : (VariableChange.mk 1 x₀ 0 y₀ • W).toAffine.Nonsingular x y) :
    W.toAffine.Nonsingular (x₀ + x) (y₀ + y) := by
  have := (variableChange_nonsingular W (VariableChange.mk 1 x₀ 0 y₀) x y).2 h
  simp only [Units.val_one, one_pow, one_mul, zero_mul, add_zero] at this
  rwa [add_comm x₀, add_comm y₀]

variable [DecidableEq F]

private theorem addEquivVariableChange_translate_some {x y : F}
    (hxy : (VariableChange.mk 1 x₀ 0 y₀ • W).toAffine.Nonsingular x y) :
    addEquivVariableChange W (VariableChange.mk 1 x₀ 0 y₀) (.some x y hxy) =
      .some _ _ (nonsingular_of_translate hxy) := by
  rw [coe_addEquivVariableChange, equivVariableChange_some, Point.some.injEq]
  constructor <;> simp <;> ring

private theorem addEquivVariableChange_symm_translate_some {x y : F}
    (hxy : W.toAffine.Nonsingular x y) :
    ∃ h' : (VariableChange.mk 1 x₀ 0 y₀ • W).toAffine.Nonsingular (x - x₀) (y - y₀),
      (addEquivVariableChange W (VariableChange.mk 1 x₀ 0 y₀)).symm (.some x y hxy) =
        .some _ _ h' := by
  refine ⟨(variableChange_nonsingular W _ _ _).1 (by simpa using hxy), ?_⟩
  rw [coe_addEquivVariableChange_symm, equivVariableChange_symm_some, Point.some.injEq]
  constructor <;> simp [VariableChange.inv_def] <;> ring

/-- **The nonsingular points at a cusp form the additive group** (Silverman III.2.5). If
`(x₀, y₀)` is a singular point of `W` whose tangent quadratic `T² + a₁ T - (3 x₀ + a₂)` has the
double root `α ∈ F`, so that `2 α + a₁ = 0`, then `(x, y) ↦ (x - x₀) / (y - y₀ - α (x - x₀))`, with
the point at infinity sent to `0`, is a group isomorphism `W.toAffine.Point ≃+ F`. -/
def cuspAddEquiv (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hc : 2 * α + W.a₁ = 0) :
    W.toAffine.Point ≃+ F :=
  have h' := isSingular_zero_translate h
  (addEquivVariableChange W (VariableChange.mk 1 x₀ 0 y₀)).symm.trans
    (cuspAddEquivOfIsSingularZero h'.1 (by rw [h'.2.1, h'.2.2]; exact hα) (by rwa [h'.2.1]))

/-- The coordinate formula for `cuspAddEquiv`. -/
@[simp]
theorem cuspAddEquiv_some (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hc : 2 * α + W.a₁ = 0) {x y : F}
    (hxy : W.toAffine.Nonsingular x y) :
    cuspAddEquiv h hα hc (.some x y hxy) = (x - x₀) / (y - y₀ - α * (x - x₀)) := by
  obtain ⟨h', e⟩ := addEquivVariableChange_symm_translate_some (x₀ := x₀) (y₀ := y₀) hxy
  rw [cuspAddEquiv, AddEquiv.trans_apply, e, cuspAddEquivOfIsSingularZero_some]

/-- The inverse of `cuspAddEquiv` sends a parameter `t ≠ 0` to the point
`(x₀ + 1 / t², y₀ + (1 / t³ + α / t²))`. -/
@[simp]
theorem cuspAddEquiv_symm_of_ne_zero (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hc : 2 * α + W.a₁ = 0) {t : F} (ht : t ≠ 0) :
    (cuspAddEquiv h hα hc).symm t =
      .some (x₀ + 1 / t ^ 2) (y₀ + (1 / t ^ 3 + α / t ^ 2)) (by
        have h' := isSingular_zero_translate h
        exact nonsingular_of_translate (cusp_nonsingular h'.1
          (by rw [h'.2.1, h'.2.2]; exact hα) (by rwa [h'.2.1]) ht)) := by
  rw [cuspAddEquiv, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    cuspAddEquivOfIsSingularZero_symm_of_ne_zero _ _ _ ht, addEquivVariableChange_translate_some]

/-- **The nonsingular points at a split node form the multiplicative group** (Silverman III.2.5).
If `(x₀, y₀)` is a singular point of `W` whose tangent quadratic `T² + a₁ T - (3 x₀ + a₂)` has the
two distinct roots `α` and `-a₁ - α` in `F`, so that `2 α + a₁ ≠ 0`, then
`(x, y) ↦ (y - y₀ - α (x - x₀)) / (y - y₀ + (a₁ + α) (x - x₀))`, with the point at infinity sent to
`1`, is a group isomorphism `W.toAffine.Point ≃+ Additive Fˣ`. -/
def nodeAddEquiv (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hn : 2 * α + W.a₁ ≠ 0) :
    W.toAffine.Point ≃+ Additive Fˣ :=
  have h' := isSingular_zero_translate h
  (addEquivVariableChange W (VariableChange.mk 1 x₀ 0 y₀)).symm.trans
    (nodeAddEquivOfIsSingularZero h'.1 (by rw [h'.2.1, h'.2.2]; exact hα) (by rwa [h'.2.1]))

/-- The coordinate formula for `nodeAddEquiv`. -/
@[simp]
theorem val_toMul_nodeAddEquiv_some (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hn : 2 * α + W.a₁ ≠ 0) {x y : F}
    (hxy : W.toAffine.Nonsingular x y) :
    ((nodeAddEquiv h hα hn (.some x y hxy)).toMul : F) =
      (y - y₀ - α * (x - x₀)) / (y - y₀ + (W.a₁ + α) * (x - x₀)) := by
  obtain ⟨h', e⟩ := addEquivVariableChange_symm_translate_some (x₀ := x₀) (y₀ := y₀) hxy
  rw [nodeAddEquiv, AddEquiv.trans_apply, e, val_toMul_nodeAddEquivOfIsSingularZero_some,
    (isSingular_zero_translate h).2.1]

/-- The inverse of `nodeAddEquiv` sends a parameter `s ≠ 1` to the point
`(x₀ + D² s / (s - 1)², y₀ + (-D³ s² / (s - 1)³ + α D² s / (s - 1)²))`, where `D = 2 α + a₁`. -/
@[simp]
theorem nodeAddEquiv_symm_of_ne_one (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) (hn : 2 * α + W.a₁ ≠ 0) {s : Additive Fˣ}
    (hs : (s.toMul : F) ≠ 1) :
    (nodeAddEquiv h hα hn).symm s =
      .some (x₀ + (2 * α + W.a₁) ^ 2 * s.toMul / (s.toMul - 1) ^ 2)
        (y₀ + (-(2 * α + W.a₁) ^ 3 * s.toMul ^ 2 / (s.toMul - 1) ^ 3 +
          α * ((2 * α + W.a₁) ^ 2 * s.toMul / (s.toMul - 1) ^ 2))) (by
        have h' := isSingular_zero_translate h
        have := nonsingular_of_translate (node_nonsingular h'.1
          (by rw [h'.2.1, h'.2.2]; exact hα) (by rwa [h'.2.1]) s.toMul.ne_zero (sub_ne_zero.2 hs))
        rwa [h'.2.1] at this) := by
  rw [nodeAddEquiv, AddEquiv.symm_trans_apply, AddEquiv.symm_symm,
    nodeAddEquivOfIsSingularZero_symm_of_ne_one _ _ _ hs, addEquivVariableChange_translate_some,
    Point.some.injEq, (isSingular_zero_translate h).2.1]
  exact ⟨rfl, rfl⟩

/-- **Torsion at a singular point with rational tangents.** If `(x₀, y₀)` is a singular point of
`W` at which the tangent slopes lie in `F`, then for `n` invertible in `F` the number of `n`-torsion
points divides `n`: the `n`-torsion is trivial at a cusp, and a subgroup of the `n`-th roots of
unity at a split node. -/
theorem natCard_torsionBy_dvd_of_isSingular (h : W.toAffine.IsSingular x₀ y₀)
    (hα : α ^ 2 + W.a₁ * α - (3 * x₀ + W.a₂) = 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point n) ∣ n := by
  by_cases hc : 2 * α + W.a₁ = 0
  · rw [Nat.card_congr ((cuspAddEquiv h hα hc).torsionByCongr n).toEquiv]
    have := TauCeti.subsingleton_torsionBy_of_injective_zsmul (V := F) n fun a b hab ↦ by
      simpa [hn] using hab
    rw [Nat.card_of_subsingleton (0 : AddSubgroup.torsionBy F n)]
    exact one_dvd n
  · -- the `n`-torsion of `Additive Fˣ` is the group of `n`-th roots of unity
    calc Nat.card (AddSubgroup.torsionBy W.toAffine.Point n)
        = Nat.card (Submodule.torsionBy ℤ (Additive Fˣ) n) :=
          Nat.card_congr ((nodeAddEquiv h hα hc).torsionByCongr n).toEquiv
      _ = Nat.card (rootsOfUnity n F) :=
          (Nat.card_congr (TauCeti.torsionByUnitsEquivRootsOfUnity n).toEquiv).trans
            (Nat.card_congr Additive.toMul)
      _ ∣ n := TauCeti.card_rootsOfUnity_dvd n

/-- **Torsion of a singular cubic.** If `Δ = 0`, then for `n` invertible in `F` the number of
`n`-torsion points among the nonsingular points divides `n`. In particular the `n`-torsion is not
`(ℤ / n)²` for `n > 1`, unlike the `n`-torsion of an elliptic curve. -/
theorem natCard_torsionBy_dvd_of_Δ_eq_zero (hΔ : W.Δ = 0) {n : ℕ} (hn : (n : F) ≠ 0) :
    Nat.card (AddSubgroup.torsionBy W.toAffine.Point n) ∣ n := by
  classical
  -- over an algebraic closure the curve has a singular point with rational tangent slopes
  let f := algebraMap F (AlgebraicClosure F)
  obtain ⟨x₀, y₀, h⟩ := exists_isSingular_of_Δ_eq_zero (W.map f).toAffine
    (by rw [map_Δ, hΔ, _root_.map_zero])
  obtain ⟨α, hα⟩ := IsAlgClosed.exists_root
    (C 1 * X ^ 2 + C (W.map f).a₁ * X + C (-(3 * x₀ + (W.map f).a₂)))
    (by rw [degree_quadratic one_ne_zero]; decide)
  have hK := natCard_torsionBy_dvd_of_isSingular h (α := α) (by simpa [sub_eq_add_neg] using hα)
    (n := n) (by rwa [← map_natCast f, _root_.map_ne_zero])
  -- and the `n`-torsion over `F` embeds into the `n`-torsion over the closure
  let φ : W.toAffine.Point →+ (W.map f).toAffine.Point :=
    AddMonoidHom.mk' (Point.mapAlong f f.injective) (Point.mapAlong_add f f.injective)
  have hle : (AddSubgroup.torsionBy W.toAffine.Point n).map φ ≤
      AddSubgroup.torsionBy (W.map f).toAffine.Point n := by
    rintro _ ⟨P, hP, rfl⟩
    rw [AddSubgroup.torsionBy.nsmul_iff, ← map_nsmul, AddSubgroup.torsionBy.nsmul_iff.1 hP,
      _root_.map_zero]
  rw [← AddSubgroup.card_map_of_injective (f := φ) (Point.mapAlong_injective f f.injective)]
  exact (AddSubgroup.card_dvd_of_le hle).trans hK

end Point

end WeierstrassCurve.Affine
