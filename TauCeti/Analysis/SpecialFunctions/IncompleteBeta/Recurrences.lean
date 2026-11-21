/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.IncompleteBeta.Basic

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

Each holds whenever the parameters that occur in it are positive. Several also hold when one of
them vanishes, through the boundary values of `TauCeti.regularizedIncompleteBeta`: `I_x(0, b) = 1`
for `0 < b` and `0 ≤ x` (and `I_x(0, b) = 0` for `x < 0` or `b ≤ 0`), and `I_x(a, 0) = 0`. Each
theorem below assumes only what its identity needs.
The homogeneous relations 8.17.12–8.17.17 hold for every real `x`, because off `[0, 1]` the clamped
function takes the same value `0` or `1` at all the parameters involved and the coefficients
balance (`TauCeti.exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc`); 8.17.18 and 8.17.19
need `0 ≤ x ≤ 1`.

The unit steps 8.17.20 and 8.17.21 are `TauCeti.regularizedIncompleteBeta_add_one_left` and
`TauCeti.regularizedIncompleteBeta_add_one_right`; together with the antidiagonal step
`TauCeti.regularizedIncompleteBeta_add_one_right_sub_add_one_left` they give all the relations
above, through the functional equation of the Gamma function.

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

/-- The antidiagonal step in the form `I_x(a, b) = I_x(a + 1, b - 1) + x ^ a (1 - x) ^ (b - 1) /
(a Β(a, b))`, [DLMF 8.17.18](https://dlmf.nist.gov/8.17.E18).

At `b = 1` it reads `I_x(a, 1) = x ^ a`, through the boundary value `I_x(a + 1, 0) = 0`. -/
theorem regularizedIncompleteBeta_eq_add_one_left_sub_one_right_add (ha : 0 < a) (hb : 1 ≤ b)
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    regularizedIncompleteBeta a b x = regularizedIncompleteBeta (a + 1) (b - 1) x +
      x ^ a * (1 - x) ^ (b - 1) / (a * beta a b) := by
  rcases hb.eq_or_lt with rfl | hb
  · rw [sub_self, Real.rpow_zero, regularizedIncompleteBeta_one_right ha hx0 hx1,
      regularizedIncompleteBeta_eq_zero_of_nonpos_right le_rfl, zero_add, beta_one_right ha]
    field_simp
  obtain ⟨β, rfl⟩ : ∃ β, b = β + 1 := ⟨b - 1, by ring⟩
  have hβ : 0 < β := by linarith
  have hstep := regularizedIncompleteBeta_add_one_right_sub_add_one_left ha.le hβ hx0 hx1
  have hcoef : Real.Gamma (a + β + 1) / (Real.Gamma (a + 1) * Real.Gamma (β + 1)) =
      1 / (a * beta a (β + 1)) := by
    rw [ProbabilityTheory.beta, Real.Gamma_add_one ha.ne', add_assoc]
    have := (Real.Gamma_pos_of_pos ha).ne'
    have := (Real.Gamma_pos_of_pos (by linarith : 0 < β + 1)).ne'
    field_simp
  rw [add_sub_cancel_right]
  rw [hcoef] at hstep
  linear_combination hstep

/-- The antidiagonal step in the form `I_x(a, b) = I_x(a - 1, b + 1) - x ^ (a - 1) (1 - x) ^ b /
(b Β(a, b))`, [DLMF 8.17.19](https://dlmf.nist.gov/8.17.E19).

At `a = 1` it reads `I_x(1, b) = 1 - (1 - x) ^ b`, through the boundary value `I_x(0, b) = 1`. -/
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
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_zero_left hb hx0,
      regularizedIncompleteBeta_zero_left (by linarith) hx0]
    ring
  rw [regularizedIncompleteBeta_add_one_left ha hb hx0 hx1,
    regularizedIncompleteBeta_add_one_right ha hb hx0 hx1]
  have := (beta_pos ha hb).ne'
  field_simp
  ring

/-- `I_x(a, b) = x I_x(a - 1, b) + (1 - x) I_x(a, b - 1)`,
[DLMF 8.17.12](https://dlmf.nist.gov/8.17.E12), for every real `x`.

At `a = 1` it holds through the boundary values `I_x(0, b) = 1` for `0 ≤ x` and `I_x(0, b) = 0`
for `x < 0`. -/
theorem regularizedIncompleteBeta_eq_mul_sub_one_left_add_mul_sub_one_right (ha : 1 ≤ a)
    (hb : 1 < b) :
    regularizedIncompleteBeta a b x = x * regularizedIncompleteBeta (a - 1) b x +
      (1 - x) * regularizedIncompleteBeta a (b - 1) x := by
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have hright := regularizedIncompleteBeta_add_one_right (b := b - 1) (by linarith : 0 < a)
    (by linarith) hx0 hx1
  have hdown := regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub ha
    (by linarith : 0 < b - 1) hx0 hx1
  have hpow : x ^ a = x ^ (a - 1) * x := by
    rw [← Real.rpow_add_one' hx0 (by linarith), sub_add_cancel]
  rw [sub_add_cancel] at hright hdown
  rw [hright, hpow]
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
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have ha0 : 0 < a := by linarith
  have hdown := regularizedIncompleteBeta_eq_sub_one_left_add_one_right_sub ha hb hx0 hx1
  have hleft := regularizedIncompleteBeta_add_one_left ha0 hb hx0 hx1
  have hpow : x ^ a = x ^ (a - 1) * x := by
    rw [← Real.rpow_add_one' hx0 (by linarith), sub_add_cancel]
  rw [hpow] at hleft
  have := (beta_pos ha0 hb).ne'
  linear_combination (norm := (field_simp; ring)) b * x * hdown - a * hleft

/-- `(b + a (1 - x)) I_x(a, b) = a (1 - x) I_x(a + 1, b - 1) + b I_x(a, b + 1)`,
[DLMF 8.17.15](https://dlmf.nist.gov/8.17.E15), for every real `x`.

At `a = 0` it holds through the boundary values `I_x(0, b) = 1` for `0 ≤ x` and `I_x(0, b) = 0`
for `x < 0`. -/
theorem add_mul_regularizedIncompleteBeta_eq_mul_add_one_left_sub_one_right_add (ha : 0 ≤ a)
    (hb : 1 < b) :
    (b + a * (1 - x)) * regularizedIncompleteBeta a b x =
      a * (1 - x) * regularizedIncompleteBeta (a + 1) (b - 1) x +
        b * regularizedIncompleteBeta a (b + 1) x := by
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have hb0 : 0 < b := by linarith
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_zero_left hb0 hx0,
      regularizedIncompleteBeta_zero_left (by linarith) hx0]
    ring
  have hdown := regularizedIncompleteBeta_eq_add_one_left_sub_one_right_add ha hb.le hx0 hx1
  have hright := regularizedIncompleteBeta_add_one_right ha hb0 hx0 hx1
  have hpow : (1 - x) ^ b = (1 - x) ^ (b - 1) * (1 - x) := by
    rw [← Real.rpow_add_one' (by linarith) (by linarith), sub_add_cancel]
  rw [hpow] at hright
  have := (beta_pos ha hb0).ne'
  linear_combination (norm := (field_simp; ring)) a * (1 - x) * hdown - b * hright

/-- `a I_x(a + 1, b) = (a + c x) I_x(a, b) - c x I_x(a - 1, b)` with `c = a + b - 1`,
[DLMF 8.17.16](https://dlmf.nist.gov/8.17.E16), for every real `x`.

At `a = 1` it holds through the boundary values `I_x(0, b) = 1` for `0 < b` and `0 ≤ x`, and
`I_x(0, b) = 0` for `x < 0`. No hypothesis on `b` is needed: for `b ≤ 0` every value is `0`. -/
theorem mul_regularizedIncompleteBeta_add_one_left_eq_mul_sub_mul_sub_one_left (ha : 1 ≤ a) :
    a * regularizedIncompleteBeta (a + 1) b x =
      (a + (a + b - 1) * x) * regularizedIncompleteBeta a b x -
        (a + b - 1) * x * regularizedIncompleteBeta (a - 1) b x := by
  rcases le_or_gt b 0 with hb | hb
  · simp [regularizedIncompleteBeta_eq_zero_of_nonpos_right hb]
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_add_one_left one_pos hb hx0 hx1, sub_self,
      regularizedIncompleteBeta_zero_left hb hx0, regularizedIncompleteBeta_one_left hb hx0 hx1,
      beta_one_left hb, Real.rpow_one]
    field_simp
    ring
  have ha0 : 0 < a := by linarith
  have ha1 : 0 < a - 1 := by linarith
  have hleft := regularizedIncompleteBeta_add_one_left ha0 hb hx0 hx1
  have hleft' := regularizedIncompleteBeta_add_one_left ha1 hb hx0 hx1
  have hbeta : beta a b = (a - 1) / (a + b - 1) * beta (a - 1) b := by
    have hc : a - 1 + b = a + b - 1 := by ring
    have h := beta_add_one_left ha1.ne' (by linarith : a - 1 + b ≠ 0)
    rwa [sub_add_cancel, hc] at h
  have hpow : x ^ a = x ^ (a - 1) * x := by
    rw [← Real.rpow_add_one' hx0 (by linarith), sub_add_cancel]
  rw [sub_add_cancel] at hleft'
  rw [hpow, hbeta] at hleft
  have := (beta_pos ha1 hb).ne'
  have : a + b - 1 ≠ 0 := by linarith
  linear_combination (norm := (field_simp; ring)) a * hleft - (a + b - 1) * x * hleft'

/-- `b I_x(a, b + 1) = (b + c (1 - x)) I_x(a, b) - c (1 - x) I_x(a, b - 1)` with
`c = a + b - 1`, [DLMF 8.17.17](https://dlmf.nist.gov/8.17.E17), for every real `x`.

No hypothesis on `a` is needed: at `a = 0` it holds through the boundary values `I_x(0, b) = 1`
for `0 ≤ x` and `I_x(0, b) = 0` for `x < 0`, and for `a < 0` every value is `0`. -/
theorem mul_regularizedIncompleteBeta_add_one_right_eq_mul_sub_mul_sub_one_right (hb : 1 < b) :
    b * regularizedIncompleteBeta a (b + 1) x =
      (b + (a + b - 1) * (1 - x)) * regularizedIncompleteBeta a b x -
        (a + b - 1) * (1 - x) * regularizedIncompleteBeta a (b - 1) x := by
  rcases lt_or_ge a 0 with ha | ha
  · simp [regularizedIncompleteBeta_eq_zero_of_neg_left ha]
  by_cases hx : x ∈ Set.Icc 0 1
  swap
  · obtain ⟨v, hv⟩ := exists_forall_regularizedIncompleteBeta_eq_of_notMem_Icc hx
    simp (disch := first | positivity | linarith) only [hv]
    ring
  obtain ⟨hx0, hx1⟩ := hx
  have hb0 : 0 < b := by linarith
  have hb1 : 0 < b - 1 := by linarith
  rcases ha.eq_or_lt with rfl | ha
  · rw [regularizedIncompleteBeta_zero_left hb0 hx0, regularizedIncompleteBeta_zero_left hb1 hx0,
      regularizedIncompleteBeta_zero_left (by linarith) hx0]
    ring
  have hright := regularizedIncompleteBeta_add_one_right ha hb0 hx0 hx1
  have hright' := regularizedIncompleteBeta_add_one_right ha hb1 hx0 hx1
  have hbeta : beta a b = (b - 1) / (a + b - 1) * beta a (b - 1) := by
    have h := beta_add_one_right hb1.ne' (by linarith : a + (b - 1) ≠ 0)
    rwa [sub_add_cancel, ← add_sub_assoc] at h
  have hpow : (1 - x) ^ b = (1 - x) ^ (b - 1) * (1 - x) := by
    rw [← Real.rpow_add_one' (by linarith) (by linarith), sub_add_cancel]
  rw [sub_add_cancel] at hright'
  rw [hpow, hbeta] at hright
  have := (beta_pos ha hb1).ne'
  have : a + b - 1 ≠ 0 := by linarith
  linear_combination (norm := (field_simp; ring)) b * hright - (a + b - 1) * (1 - x) * hright'

end TauCeti
