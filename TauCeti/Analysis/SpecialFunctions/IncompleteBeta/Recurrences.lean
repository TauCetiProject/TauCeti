/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic
import TauCeti.Analysis.SpecialFunctions.Pow.Real

/-!
# Recurrence relations of the regularized incomplete beta function

The regularized incomplete beta function `I_x(a, b)` satisfies a family of
three-term relations between neighbouring parameter pairs, collected in DLMF §8.17(iv). Writing
`x' = 1 - x` and `c = a + b - 1` (DLMF 8.17.11), they are

* `I_x(a, b) = x I_x(a - 1, b) + x' I_x(a, b - 1)` (8.17.12);
* `(a + b) I_x(a, b) = a I_x(a + 1, b) + b I_x(a, b + 1)` (8.17.13);
* `(a + b x) I_x(a, b) = x b I_x(a - 1, b + 1) + a I_x(a + 1, b)` (8.17.14);
* `(b + a x') I_x(a, b) = a x' I_x(a + 1, b - 1) + b I_x(a, b + 1)` (8.17.15);
* `a I_x(a + 1, b) = (a + c x) I_x(a, b) - c x I_x(a - 1, b)` (8.17.16);
* `b I_x(a, b + 1) = (b + c x') I_x(a, b) - c x' I_x(a, b - 1)` (8.17.17);
* `I_x(a, b) = I_x(a + 1, b - 1) + x ^ a x' ^ (b - 1) / (a Β(a, b))` (8.17.18);
* `I_x(a, b) = I_x(a - 1, b + 1) - x ^ (a - 1) x' ^ b / (b Β(a, b))` (8.17.19).

Each holds for `0 ≤ x ≤ 1` whenever the parameters that occur in it are positive. Several also
hold when one of them vanishes, through the boundary values of
`TauCeti.regularizedIncompleteBeta`: `I_x(0, b) = 1` for `0 < b` and `0 ≤ x` (and
`I_x(0, b) = 0` for `x < 0` or `b ≤ 0`), and `I_x(a, 0) = 0`. Each theorem below assumes only
what its identity needs.
The homogeneous relations 8.17.12–8.17.17 hold for every real `x`. Off `[0, 1)`, at parameter
pairs with `0 ≤ a` and `0 < b`, the clamped function takes one common value, `0` for `x < 0` and
`1` for `1 ≤ x`, and the coefficients balance. In 8.17.13 and 8.17.14 the second parameter may
also be `0`: then the term with second parameter `b + 1` drops out, because its coefficient
contains the factor `b = 0`, and the remaining terms vanish through `I_x(a, 0) = 0`. In 8.17.12,
8.17.15 and 8.17.17 the term with second parameter `b - 1` is `0` at `b = 1`, so there they hold
for `x ≤ 1` only. The inhomogeneous relations 8.17.18 and 8.17.19 need `0 ≤ x ≤ 1`.

The unit steps 8.17.20 and 8.17.21 are `TauCeti.regularizedIncompleteBeta_add_one_left` and
`TauCeti.regularizedIncompleteBeta_add_one_right`; together with the antidiagonal step
`TauCeti.regularizedIncompleteBeta_add_one_right_sub_add_one_left` they give all the relations
above, through the functional equation of the Gamma function. The relations 8.17.15 and
8.17.18 are the reflections `x ↦ 1 - x`, `a ↔ b` of 8.17.14 and 8.17.19 under
`TauCeti.regularizedIncompleteBeta_symm`, at positive parameters, and 8.17.16 and 8.17.17
eliminate the antidiagonal term of 8.17.14 and 8.17.15 with 8.17.13.

## Main results

* `TauCeti.regularizedIncompleteBeta_eq_mul_sub_one_left_add_mul_sub_one_right` — 8.17.12;
* `TauCeti.add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_add_mul_add_one_right` —
  8.17.13;
* `TauCeti.add_mul_regularizedIncompleteBeta_eq_mul_sub_one_left_add_one_right_add` — 8.17.14;
* `TauCeti.add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_sub_one_right_add` — 8.17.15;
* `TauCeti.mul_regularizedIncompleteBeta_add_one_left_eq_mul_sub_mul_sub_one_left` — 8.17.16;
* `TauCeti.mul_regularizedIncompleteBeta_add_one_right_eq_mul_sub_mul_sub_one_right` — 8.17.17;
* `TauCeti.regularizedIncompleteBeta_eq_add_one_left_sub_one_right_add` — 8.17.18;
* `TauCeti.regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub` — 8.17.19.

## References

* [NIST Digital Library of Mathematical Functions, §8.17(iv)](https://dlmf.nist.gov/8.17.iv)
-/

public section

namespace TauCeti

open ProbabilityTheory

variable {a b x : ℝ}

/-- Off `[0, 1)` the regularized incomplete beta function does not depend on the parameters in
the range `0 ≤ a`, `0 < b`: it is `0` to the left of `0` and `1` from `1` on. -/
private lemma exists_forall_regularizedIncompleteBeta_eq_of_notMem_Ico (hx : x ∉ Set.Ico 0 1) :
    ∃ v, ∀ a b, 0 ≤ a → 0 < b → regularizedIncompleteBeta a b x = v := by
  rcases lt_or_ge x 0 with hx0 | hx0
  · exact ⟨0, fun a b _ _ ↦ regularizedIncompleteBeta_eq_zero_of_neg a b hx0⟩
  · have hx1 : 1 ≤ x := le_of_not_gt fun h ↦ hx ⟨hx0, h⟩
    exact ⟨1, fun a b ha hb ↦ regularizedIncompleteBeta_eq_one_of_one_le ha hb hx1⟩

/-- The antidiagonal step in the form `I_x(a, b) = I_x(a - 1, b + 1) - x ^ (a - 1) (1 - x) ^ b /
(b Β(a, b))`, [DLMF 8.17.19](https://dlmf.nist.gov/8.17.E19).

At `a = 1` it reads `I_x(1, b) = 1 - (1 - x) ^ b` for `0 ≤ x ≤ 1`, through the boundary value
`I_x(0, b) = 1`. -/
theorem regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub (ha : 1 ≤ a) (hb : 0 < b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a b x = regularizedIncompleteBeta (a - 1) (b + 1) x -
      x ^ (a - 1) * (1 - x) ^ b / (b * beta a b) := by
  obtain ⟨α, rfl⟩ : ∃ α, a = α + 1 := ⟨a - 1, by ring⟩
  have hα : 0 ≤ α := by linarith
  have hstep := regularizedIncompleteBeta_add_one_right_sub_add_one_left hα hb hx0 hx1
  have hcoef : Real.Gamma (α + b + 1) / (Real.Gamma (α + 1) * Real.Gamma (b + 1)) =
      1 / (b * beta (α + 1) b) := by
    rw [ProbabilityTheory.beta, Real.Gamma_add_one hb.ne', add_right_comm α 1 b]
    have := (Real.Gamma_pos_of_pos (by linarith : 0 < α + 1)).ne'
    have := (Real.Gamma_pos_of_pos hb).ne'
    field_simp
  rw [add_sub_cancel_right]
  rw [hcoef] at hstep
  linear_combination -hstep

/-- The antidiagonal step in the form `I_x(a, b) = I_x(a + 1, b - 1) + x ^ a (1 - x) ^ (b - 1) /
(a Β(a, b))`, [DLMF 8.17.18](https://dlmf.nist.gov/8.17.E18).

At `b = 1` it reads `I_x(a, 1) = x ^ a` for `0 ≤ x ≤ 1`, through the boundary value
`I_x(a + 1, 0) = 0`. -/
theorem regularizedIncompleteBeta_eq_add_one_left_sub_one_right_add (ha : 0 < a) (hb : 1 ≤ b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a b x = regularizedIncompleteBeta (a + 1) (b - 1) x +
      x ^ a * (1 - x) ^ (b - 1) / (a * beta a b) := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [sub_self, Real.rpow_zero, regularizedIncompleteBeta_one_right ha hx0 hx1,
      regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl, zero_add,
      beta_one_right (by positivity)]
    field_simp
  -- The reflection of 8.17.19 at `(b, a, 1 - x)`.
  have h := regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub hb.le ha
    (by linarith : 0 ≤ 1 - x) (by linarith)
  have s1 := regularizedIncompleteBeta_symm ha (by linarith : 0 < b) x
  have s2 := regularizedIncompleteBeta_symm (by linarith : 0 < a + 1) (by linarith : 0 < b - 1) x
  rw [sub_sub_cancel, beta_comm] at h
  linear_combination s1 - s2 - h

/-- The two unit steps weighted by the parameters,
`(a + b) I_x(a, b) = a I_x(a + 1, b) + b I_x(a, b + 1)`,
[DLMF 8.17.13](https://dlmf.nist.gov/8.17.E13), for every real `x`.

It also holds at `a = 0` and at `b = 0`, through the boundary values `I_x(0, b) = 1` for `0 < b`
and `0 ≤ x` (and `0` for `x < 0` or `b = 0`) and `I_x(a, 0) = 0`. -/
theorem add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_add_mul_add_one_right (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (a + b) * regularizedIncompleteBeta a b x =
      a * regularizedIncompleteBeta (a + 1) b x + b * regularizedIncompleteBeta a (b + 1) x := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  by_cases hx : x ∈ Set.Ico 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Ico hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_zero_left hb hx0,
      regularizedIncompleteBeta_zero_left (by linarith) hx0]
    ring
  rw [regularizedIncompleteBeta_add_one_left ha hb hx0 hx1.le,
    regularizedIncompleteBeta_add_one_right ha hb hx0 hx1.le]
  have := (beta_pos ha hb).ne'
  field_simp
  ring

/-- `I_x(a, b) = x I_x(a - 1, b) + (1 - x) I_x(a, b - 1)`,
[DLMF 8.17.12](https://dlmf.nist.gov/8.17.E12), for every real `x` when `1 < b`, and for
`x ≤ 1` when `b = 1`.

At `a = 1` it holds through the boundary values `I_x(0, b) = 1` for `0 ≤ x` and `I_x(0, b) = 0`
for `x < 0`, and at `b = 1` through `I_x(a, 0) = 0`. At `b = 1` and `1 < x` it fails: the left
side is `1` and the right side is `x`. -/
theorem regularizedIncompleteBeta_eq_mul_sub_one_left_add_mul_sub_one_right (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hbx : 1 < b ∨ x ≤ 1) :
    regularizedIncompleteBeta a b x = x * regularizedIncompleteBeta (a - 1) b x +
      (1 - x) * regularizedIncompleteBeta a (b - 1) x := by
  rcases hb.eq_or_lt with rfl | hb
  · have hx1 : x ≤ 1 := hbx.resolve_left (lt_irrefl 1)
    rw [sub_self, regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl, mul_zero, add_zero]
    rcases lt_or_ge x 0 with hx0 | hx0
    · simp [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx0]
    have h' : regularizedIncompleteBeta (a - 1) 1 x = x ^ (a - 1) := by
      rcases ha.eq_or_lt with rfl | ha
      · rw [sub_self, Real.rpow_zero, regularizedIncompleteBeta_zero_left one_pos hx0]
      · exact regularizedIncompleteBeta_one_right (by linarith) hx0 hx1
    rw [regularizedIncompleteBeta_one_right (by linarith) hx0 hx1, h',
      Real.rpow_eq_rpow_sub_one_mul hx0 (by linarith)]
    ring
  by_cases hx : x ∈ Set.Ico 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Ico hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have hright := regularizedIncompleteBeta_add_one_right (b := b - 1) (by linarith : 0 < a)
    (by linarith) hx0 hx1.le
  have hdown := regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub ha
    (by linarith : 0 < b - 1) hx0 hx1.le
  rw [sub_add_cancel] at hright hdown
  rw [hright, Real.rpow_eq_rpow_sub_one_mul hx0 (by linarith : a ≠ 0)]
  linear_combination x * hdown

/-- `(a + b x) I_x(a, b) = x b I_x(a - 1, b + 1) + a I_x(a + 1, b)`,
[DLMF 8.17.14](https://dlmf.nist.gov/8.17.E14), for every real `x`.

At `a = 1` it holds through the boundary values `I_x(0, b + 1) = 1` for `0 ≤ x` and
`I_x(0, b + 1) = 0` for `x < 0`, and at `b = 0` through `I_x(a, 0) = 0`. -/
theorem add_mul_regularizedIncompleteBeta_eq_mul_sub_one_left_add_one_right_add (ha : 1 ≤ a)
    (hb : 0 ≤ b) :
    (a + b * x) * regularizedIncompleteBeta a b x =
      x * b * regularizedIncompleteBeta (a - 1) (b + 1) x +
        a * regularizedIncompleteBeta (a + 1) b x := by
  rcases hb.eq_or_lt with rfl | hb
  · simp
  by_cases hx : x ∈ Set.Ico 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Ico hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have ha0 : 0 < a := by linarith
  have hdown := regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub ha hb hx0 hx1.le
  have hleft := regularizedIncompleteBeta_add_one_left ha0 hb hx0 hx1.le
  rw [Real.rpow_eq_rpow_sub_one_mul hx0 ha0.ne'] at hleft
  have := (beta_pos ha0 hb).ne'
  linear_combination (norm := (field_simp; ring)) b * x * hdown - a * hleft

/-- `(b + a (1 - x)) I_x(a, b) = a (1 - x) I_x(a + 1, b - 1) + b I_x(a, b + 1)`,
[DLMF 8.17.15](https://dlmf.nist.gov/8.17.E15), for every real `x` when `1 < b`, and for
`x ≤ 1` when `b = 1`.

At `a = 0` it holds through the boundary values `I_x(0, b) = 1` for `0 ≤ x` and `I_x(0, b) = 0`
for `x < 0`, and at `b = 1` through `I_x(a + 1, 0) = 0`. At `b = 1`, `0 < a` and `1 < x` it
fails: the left side is `1 + a (1 - x)` and the right side is `1`. -/
theorem add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_sub_one_right_add (ha : 0 ≤ a)
    (hb : 1 ≤ b) (hbx : 1 < b ∨ x ≤ 1) :
    (b + a * (1 - x)) * regularizedIncompleteBeta a b x =
      a * (1 - x) * regularizedIncompleteBeta (a + 1) (b - 1) x +
        b * regularizedIncompleteBeta a (b + 1) x := by
  rcases hb.eq_or_lt with rfl | hb
  · have hx1 : x ≤ 1 := hbx.resolve_left (lt_irrefl 1)
    rw [sub_self, regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl, mul_zero, zero_add]
    rcases lt_or_ge x 0 with hx0 | hx0
    · simp [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx0]
    rcases ha.eq_or_lt with rfl | ha
    · rw [regularizedIncompleteBeta_zero_left one_pos hx0,
        regularizedIncompleteBeta_zero_left (by norm_num) hx0]
      ring
    rw [regularizedIncompleteBeta_add_one_right ha one_pos hx0 hx1,
      regularizedIncompleteBeta_one_right ha hx0 hx1, beta_one_right ha.le, Real.rpow_one]
    field_simp
  rcases ha.eq_or_lt with rfl | ha
  · rcases lt_or_ge x 0 with hx0 | hx0
    · simp [regularizedIncompleteBeta_eq_zero_of_neg _ _ hx0]
    rw [regularizedIncompleteBeta_zero_left (by linarith) hx0,
      regularizedIncompleteBeta_zero_left (by linarith) hx0]
    ring
  -- The reflection of 8.17.14 at `(b, a, 1 - x)`.
  have h := add_mul_regularizedIncompleteBeta_eq_mul_sub_one_left_add_one_right_add
    (x := 1 - x) hb.le ha.le
  have s1 := regularizedIncompleteBeta_symm ha (by linarith : 0 < b) x
  have s2 := regularizedIncompleteBeta_symm (by linarith : 0 < a + 1) (by linarith : 0 < b - 1) x
  have s3 := regularizedIncompleteBeta_symm ha (by linarith : 0 < b + 1) x
  linear_combination (b + a * (1 - x)) * s1 - a * (1 - x) * s2 - b * s3 - h

/-- `a I_x(a + 1, b) = (a + c x) I_x(a, b) - c x I_x(a - 1, b)` with `c = a + b - 1`,
[DLMF 8.17.16](https://dlmf.nist.gov/8.17.E16), for every real `x`.

At `a = 1` it holds through the boundary values `I_x(0, b) = 1` for `0 < b` and `0 ≤ x`, and
`I_x(0, b) = 0` for `x < 0`. No hypothesis on `b` is needed: for `b ≤ 0` every value is `0`. -/
theorem mul_regularizedIncompleteBeta_add_one_left_eq_mul_sub_mul_sub_one_left (ha : 1 ≤ a) :
    a * regularizedIncompleteBeta (a + 1) b x =
      (a + (a + b - 1) * x) * regularizedIncompleteBeta a b x -
        (a + b - 1) * x * regularizedIncompleteBeta (a - 1) b x := by
  rcases lt_or_ge b 0 with hb | hb
  · simp [regularizedIncompleteBeta_eq_zero_of_nonpos_right hb.le]
  -- 8.17.14 at `(a, b)` plus `x` times 8.17.13 at `(a - 1, b)`.
  have h14 := add_mul_regularizedIncompleteBeta_eq_mul_sub_one_left_add_one_right_add
    (x := x) ha hb
  have h13 := add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_add_mul_add_one_right
    (x := x) (by linarith : 0 ≤ a - 1) hb
  rw [sub_add_cancel] at h13
  linear_combination -h14 + x * h13

/-- `b I_x(a, b + 1) = (b + c (1 - x)) I_x(a, b) - c (1 - x) I_x(a, b - 1)` with
`c = a + b - 1`, [DLMF 8.17.17](https://dlmf.nist.gov/8.17.E17), for every real `x` when
`1 < b`, and for `x ≤ 1` when `b = 1`.

No hypothesis on `a` is needed: at `a = 0` it holds through the boundary values `I_x(0, b) = 1`
for `0 ≤ x` and `I_x(0, b) = 0` for `x < 0`, and for `a < 0` every value is `0`. At `b = 1` it
holds through `I_x(a, 0) = 0`. -/
theorem mul_regularizedIncompleteBeta_add_one_right_eq_mul_sub_mul_sub_one_right (hb : 1 ≤ b)
    (hbx : 1 < b ∨ x ≤ 1) :
    b * regularizedIncompleteBeta a (b + 1) x =
      (b + (a + b - 1) * (1 - x)) * regularizedIncompleteBeta a b x -
        (a + b - 1) * (1 - x) * regularizedIncompleteBeta a (b - 1) x := by
  rcases lt_or_ge a 0 with ha | ha
  · simp [regularizedIncompleteBeta_eq_zero_of_neg_left ha]
  -- 8.17.15 at `(a, b)` plus `1 - x` times 8.17.13 at `(a, b - 1)`.
  have h15 := add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_sub_one_right_add ha hb hbx
  have h13 := add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_add_mul_add_one_right
    (x := x) ha (by linarith : 0 ≤ b - 1)
  rw [sub_add_cancel] at h13
  linear_combination -h15 + (1 - x) * h13

end TauCeti
