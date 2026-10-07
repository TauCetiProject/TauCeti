/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Elliptic and cusp parameters for hyperbolic triangles

A vertex of a finite-area hyperbolic triangle is either elliptic, with a finite order `m ≥ 2`,
or ideal, in which case it is a cusp.  `TriangleOrder` keeps those alternatives distinct instead
of encoding a cusp by an untyped infinity value.  Its reciprocal contribution is `1 / m` at an
elliptic vertex and `0` at a cusp; multiplying by `π` gives the corresponding interior angle.

The predicate `TriangleOrder.IsHyperbolic p q r` is the typed hyperbolic triangle inequality
`p.reciprocal + q.reciprocal + r.reciprocal < 1`.  The main comparison theorem rewrites it as
the geometric angle inequality `p.angle + q.angle + r.angle < π`.

## Main declarations

* `TriangleOrder`: an elliptic order `m ≥ 2` or a cusp.
* `TriangleOrder.reciprocal`: the contribution `1 / m` or `0` to the triangle inequality.
* `TriangleOrder.angle`: the corresponding angle `π / m` or `0`.
* `TriangleOrder.IsHyperbolic`: the typed reciprocal-sum condition for a hyperbolic triple.

## References

S. Katok, *Fuchsian Groups*, Chicago Lectures in Mathematics (1992), §3.1.
-/

public section

noncomputable section

open Real

namespace TauCeti

/-- The order attached to a vertex of a finite-area hyperbolic triangle: either a finite
elliptic order `m ≥ 2`, or a cusp. -/
inductive TriangleOrder where
  /-- An elliptic vertex of order `m ≥ 2`. -/
  | elliptic (m : ℕ) (hm : 2 ≤ m)
  /-- An ideal vertex, with angle zero. -/
  | cusp
  deriving DecidableEq

namespace TriangleOrder

/-- The reciprocal contribution of a triangle vertex: `1 / m` for an elliptic vertex of order
`m`, and `0` for a cusp. -/
def reciprocal : TriangleOrder → ℝ
  | .elliptic m _ => (m : ℝ)⁻¹
  | .cusp => 0

/-- The reciprocal contribution of an elliptic vertex is the inverse of its order. -/
@[simp]
theorem reciprocal_elliptic (m : ℕ) (hm : 2 ≤ m) :
    (elliptic m hm).reciprocal = (m : ℝ)⁻¹ := by
  rw [reciprocal]

/-- A cusp contributes zero to the reciprocal sum. -/
@[simp]
theorem reciprocal_cusp : cusp.reciprocal = 0 := by
  rw [reciprocal]

/-- Reciprocal contributions are nonnegative. -/
theorem reciprocal_nonneg (p : TriangleOrder) : 0 ≤ p.reciprocal := by
  cases p with
  | elliptic m hm =>
      exact inv_nonneg.mpr (Nat.cast_nonneg m)
  | cusp =>
      exact le_rfl

/-- The reciprocal contribution is positive exactly at an elliptic vertex. -/
@[simp]
theorem reciprocal_pos_iff (p : TriangleOrder) : 0 < p.reciprocal ↔ p ≠ cusp := by
  cases p with
  | elliptic m hm =>
      have hm0 : 0 < m := lt_of_lt_of_le (by decide) hm
      simp [reciprocal, inv_pos, Nat.cast_pos, hm0]
  | cusp =>
      simp [reciprocal]

/-- The reciprocal contribution vanishes exactly at a cusp. -/
@[simp]
theorem reciprocal_eq_zero_iff (p : TriangleOrder) : p.reciprocal = 0 ↔ p = cusp := by
  cases p with
  | elliptic m hm =>
      have hm0 : m ≠ 0 := (lt_of_lt_of_le (by decide) hm).ne'
      simp [reciprocal, hm0]
  | cusp =>
      simp [reciprocal]

/-- Every triangle-order reciprocal is strictly less than one. -/
theorem reciprocal_lt_one (p : TriangleOrder) : p.reciprocal < 1 := by
  cases p with
  | elliptic m hm =>
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hm)
      rw [reciprocal_elliptic, inv_lt_one₀ hm0]
      exact_mod_cast (lt_of_lt_of_le (by decide : 1 < 2) hm)
  | cusp =>
      exact zero_lt_one

/-- Every triangle-order reciprocal is at most `1 / 2`; equality is attained only at elliptic
order two. -/
theorem reciprocal_le_half (p : TriangleOrder) : p.reciprocal ≤ (2 : ℝ)⁻¹ := by
  cases p with
  | elliptic m hm =>
      have h2 : (0 : ℝ) < 2 := by norm_num
      have hm0 : (0 : ℝ) < m := Nat.cast_pos.mpr (lt_of_lt_of_le (by decide) hm)
      exact (inv_le_inv₀ hm0 h2).2 (Nat.cast_le.mpr hm)
  | cusp =>
      positivity

/-- Reciprocal contribution is `1 / 2` exactly at an elliptic vertex of order two. -/
@[simp]
theorem reciprocal_eq_inv_two_iff (p : TriangleOrder) :
    p.reciprocal = (2 : ℝ)⁻¹ ↔ p = elliptic 2 (by decide) := by
  cases p with
  | elliptic m hm =>
      rw [reciprocal_elliptic]
      constructor
      · intro h
        have hm2 : m = 2 := by
          exact_mod_cast inv_injective h
        subst m
        rfl
      · intro h
        have hm2 : m = 2 := TriangleOrder.elliptic.inj h
        subst m
        rfl
  | cusp =>
      norm_num

/-- Reciprocal contribution distinguishes triangle orders. -/
theorem reciprocal_injective : Function.Injective reciprocal := by
  intro p q hpq
  cases p with
  | cusp =>
      cases q with
      | cusp => rfl
      | elliptic n hn =>
          rw [reciprocal_cusp, reciprocal_elliptic] at hpq
          exact absurd hpq.symm (inv_ne_zero (Nat.cast_ne_zero.mpr
            (lt_of_lt_of_le (by decide) hn).ne'))
  | elliptic m hm =>
      cases q with
      | cusp =>
          rw [reciprocal_elliptic, reciprocal_cusp] at hpq
          exact absurd hpq (inv_ne_zero (Nat.cast_ne_zero.mpr
            (lt_of_lt_of_le (by decide) hm).ne'))
      | elliptic n hn =>
          rw [reciprocal_elliptic, reciprocal_elliptic] at hpq
          have hmn : m = n := Nat.cast_injective (inv_injective hpq)
          subst n
          rfl

/-- The interior angle attached to a triangle vertex: `π / m` at an elliptic vertex of order
`m`, and `0` at a cusp. -/
def angle (p : TriangleOrder) : ℝ :=
  π * p.reciprocal

/-- A triangle-order angle is `π` times its reciprocal contribution. -/
theorem angle_def (p : TriangleOrder) : p.angle = π * p.reciprocal := by
  rw [angle]

/-- The angle at an elliptic vertex of order `m` is `π / m`. -/
@[simp]
theorem angle_elliptic (m : ℕ) (hm : 2 ≤ m) :
    (elliptic m hm).angle = π / m := by
  rw [angle, reciprocal_elliptic, div_eq_mul_inv]

/-- The angle at a cusp is zero. -/
@[simp]
theorem angle_cusp : cusp.angle = 0 := by
  simp [angle]

/-- Triangle-order angles are nonnegative. -/
theorem angle_nonneg (p : TriangleOrder) : 0 ≤ p.angle :=
  mul_nonneg pi_pos.le p.reciprocal_nonneg

/-- A triangle-order angle is positive exactly at an elliptic vertex. -/
@[simp]
theorem angle_pos_iff (p : TriangleOrder) : 0 < p.angle ↔ p ≠ cusp := by
  rw [angle, mul_pos_iff_of_pos_left pi_pos, reciprocal_pos_iff]

/-- A triangle-order angle vanishes exactly at a cusp. -/
@[simp]
theorem angle_eq_zero_iff (p : TriangleOrder) : p.angle = 0 ↔ p = cusp := by
  rw [angle, mul_eq_zero]
  simp only [pi_ne_zero, false_or, reciprocal_eq_zero_iff]

/-- Every triangle-order angle is at most `π / 2`. -/
theorem angle_le_pi_div_two (p : TriangleOrder) : p.angle ≤ π / 2 := by
  rw [angle, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left p.reciprocal_le_half pi_pos.le

/-- Every triangle-order angle is strictly less than `π`. -/
theorem angle_lt_pi (p : TriangleOrder) : p.angle < π := by
  rw [angle]
  calc
    π * p.reciprocal < π * 1 := mul_lt_mul_of_pos_left p.reciprocal_lt_one pi_pos
    _ = π := mul_one π

/-- The typed hyperbolic triangle condition: the sum of the three reciprocal contributions is
strictly less than one. -/
def IsHyperbolic (p q r : TriangleOrder) : Prop :=
  p.reciprocal + q.reciprocal + r.reciprocal < 1

/-- The typed hyperbolic condition, unfolded as the reciprocal-sum inequality. -/
theorem isHyperbolic_iff (p q r : TriangleOrder) :
    IsHyperbolic p q r ↔ p.reciprocal + q.reciprocal + r.reciprocal < 1 := by
  rw [IsHyperbolic]

/-- The hyperbolic condition is unchanged by swapping the first two vertices. -/
theorem IsHyperbolic.swap {p q r : TriangleOrder} (h : IsHyperbolic p q r) :
    IsHyperbolic q p r := by
  simpa only [IsHyperbolic, add_comm p.reciprocal q.reciprocal] using h

/-- The hyperbolic condition is unchanged by cyclically rotating the vertices. -/
theorem IsHyperbolic.rotate {p q r : TriangleOrder} (h : IsHyperbolic p q r) :
    IsHyperbolic q r p := by
  simpa only [IsHyperbolic, add_assoc, add_comm p.reciprocal,
    add_left_comm p.reciprocal] using h

/-- Three cusps satisfy the typed hyperbolic triangle condition. -/
@[simp]
theorem isHyperbolic_cusp_cusp_cusp : IsHyperbolic cusp cusp cusp := by
  simp [IsHyperbolic]

/-- **The reciprocal and angle forms of the hyperbolic triangle condition agree.** -/
theorem isHyperbolic_iff_angle_sum_lt_pi (p q r : TriangleOrder) :
    IsHyperbolic p q r ↔ p.angle + q.angle + r.angle < π := by
  rw [IsHyperbolic, angle, angle, angle]
  have hfactor :
      π * p.reciprocal + π * q.reciprocal + π * r.reciprocal =
        π * (p.reciprocal + q.reciprocal + r.reciprocal) := by ring
  rw [hfactor]
  constructor
  · intro h
    calc
      π * (p.reciprocal + q.reciprocal + r.reciprocal) < π * 1 :=
        mul_lt_mul_of_pos_left h pi_pos
      _ = π := mul_one π
  · intro h
    have h' : π * (p.reciprocal + q.reciprocal + r.reciprocal) < π * 1 := by
      simpa only [mul_one] using h
    exact lt_of_mul_lt_mul_left h' pi_pos.le

end TriangleOrder

end TauCeti
