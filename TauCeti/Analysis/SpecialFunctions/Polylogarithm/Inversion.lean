/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic

/-!
# Inversion of nonpositive-weight polylogarithms

In nonpositive integer weight `n ≤ 0`, the polylogarithm `Li_n(z)` satisfies the rational
inversion relation
`polylog n z + (-1) ^ n * polylog n z⁻¹ = -1` when `n = 0` (`z ∉ {0, 1}`), and `= 0` when `n < 0`
(`z ≠ 1`).

In weight zero this is the elementary identity `z / (1 - z) + z⁻¹ / (1 - z⁻¹) = -1` for
`z ∉ {0, 1}`, matching the Bernoulli-polynomial inversion formula for `n ≥ 1` at `B_0 = 1`.
Because the Euler differential operator `z ↦ z * deriv · z` anticommutes with `z ↦ z⁻¹`
(`mul_deriv_polylog_neg_nat_comp_inv`) and kills the constant `-1`, induction on `-n` shows that
`polylog n z + (-1) ^ n * polylog n z⁻¹ = 0` in every strictly negative weight `n < 0` for all
`z ≠ 1` (including `z = 0`, where `0⁻¹ = 0` and `polylog n 0 = 0`).

## Main declarations

* `TauCeti.Polylog.polylog_zero_weight_add_inv`: `polylog 0 z + polylog 0 z⁻¹ = -1` for
  `z ≠ 0` and `z ≠ 1`.
* `TauCeti.Polylog.polylog_add_zpow_mul_inv_of_neg`: `polylog n z + (-1) ^ n * polylog n z⁻¹ = 0`
  for `n < 0` and `z ≠ 1`.
* `TauCeti.Polylog.polylog_inv_of_neg`: `polylog n z⁻¹ = -(-1) ^ n * polylog n z` for `n < 0`
  and `z ≠ 1`.
* `TauCeti.Polylog.polylog_inversion_of_nonpos`, `TauCeti.Polylog.polylog_inv_of_nonpos`: unified
  nonpositive-weight inversion formulas for `n ≤ 0`, `z ≠ 0`, and `z ≠ 1`.
* `TauCeti.Polylog.polylog_neg_one_inv`: weight `-1` is invariant under `z ↦ z⁻¹` for `z ≠ 1`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762,
  Astérisque 216 (1993), §1.3, `(5)`, p. 51.
* Don Zagier, *The dilogarithm function*, in Frontiers in Number Theory, Physics,
  and Geometry II (2007), Part I, §2, p. 8.
-/

public section

namespace TauCeti.Polylog

/-- In weight zero, `polylog 0 z + polylog 0 z⁻¹ = -1` away from `0` and `1`. -/
theorem polylog_zero_weight_add_inv {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    polylog 0 z + polylog 0 z⁻¹ = -1 := by
  have hz1' : 1 - z ≠ 0 := sub_ne_zero.mpr hz1.symm
  simp only [polylog_zero_weight]
  field_simp
  ring

/-- Solved-for-`z⁻¹` form of weight-zero inversion away from `0` and `1`. -/
theorem polylog_zero_weight_inv {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    polylog 0 z⁻¹ = -1 - polylog 0 z := by
  linear_combination polylog_zero_weight_add_inv hz0 hz1

/-- In strictly negative weights `-(r + 1)`, `polylog (-(r + 1)) z + (-1) ^ (r + 1) *
polylog (-(r + 1)) z⁻¹ = 0` for every `z ≠ 1` (including `z = 0`). -/
theorem polylog_neg_nat_succ_add_pow_mul_inv (r : ℕ) {z : ℂ} (hz1 : z ≠ 1) :
    polylog (-((r + 1 : ℕ) : ℤ)) z + (-1 : ℂ) ^ (r + 1) * polylog (-((r + 1 : ℕ) : ℤ)) z⁻¹ = 0 := by
  induction r generalizing z with
  | zero =>
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hU : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := isOpen_ne.inter isOpen_ne
      have heq :
          (fun w : ℂ => polylog 0 w + polylog 0 w⁻¹) =ᶠ[nhds z] fun _ : ℂ => (-1 : ℂ) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz0, hz1⟩) fun w hw =>
          polylog_zero_weight_add_inv hw.1 hw.2
      have hderiv := congrArg (z * ·) heq.deriv_eq
      have hdiff1 : DifferentiableAt ℂ (polylog 0) z := by
        simpa using (analyticAt_polylog_neg_nat 0 hz1).differentiableAt
      have hdiff2 : DifferentiableAt ℂ (fun w : ℂ => polylog 0 w⁻¹) z := by
        simpa [Function.comp_def] using
          (analyticAt_polylog_neg_nat 0 (inv_ne_one.mpr hz1)).differentiableAt.comp z
            (differentiableAt_inv hz0)
      rw [deriv_const, mul_zero, deriv_fun_add hdiff1 hdiff2, mul_add] at hderiv
      have h1 : z * deriv (polylog 0) z = polylog (-((0 + 1 : ℕ) : ℤ)) z := by
        simpa using (polylog_neg_nat_succ 0 z).symm
      have h2 : z * deriv (fun w : ℂ => polylog 0 w⁻¹) z = -polylog (-((0 + 1 : ℕ) : ℤ)) z⁻¹ := by
        simpa using mul_deriv_polylog_neg_nat_comp_inv 0 hz1
      rw [h1, h2] at hderiv
      simpa [pow_one] using hderiv
  | succ r ih =>
    rcases eq_or_ne z 0 with rfl | hz0
    · simp
    · have hU : IsOpen {w : ℂ | w ≠ 0 ∧ w ≠ 1} := isOpen_ne.inter isOpen_ne
      have heq :
          (fun w : ℂ =>
              polylog (-((r + 1 : ℕ) : ℤ)) w +
                (-1 : ℂ) ^ (r + 1) * polylog (-((r + 1 : ℕ) : ℤ)) w⁻¹) =ᶠ[nhds z]
            fun _ : ℂ => (0 : ℂ) :=
        Filter.eventuallyEq_of_mem (hU.mem_nhds ⟨hz0, hz1⟩) fun w hw => ih hw.2
      have hderiv := congrArg (z * ·) heq.deriv_eq
      have hdiff1 : DifferentiableAt ℂ (polylog (-((r + 1 : ℕ) : ℤ))) z :=
        (analyticAt_polylog_neg_nat (r + 1) hz1).differentiableAt
      have hdiff2 : DifferentiableAt ℂ (fun w : ℂ => polylog (-((r + 1 : ℕ) : ℤ)) w⁻¹) z := by
        simpa only [Function.comp_def] using
          (analyticAt_polylog_neg_nat (r + 1) (inv_ne_one.mpr hz1)).differentiableAt.comp z
            (differentiableAt_inv hz0)
      rw [deriv_const, mul_zero, deriv_fun_add hdiff1 (hdiff2.const_mul _),
        deriv_const_mul _ hdiff2, mul_add, ← mul_assoc, mul_comm z ((-1 : ℂ) ^ (r + 1)),
        mul_assoc, ← polylog_neg_nat_succ (r + 1) z,
        mul_deriv_polylog_neg_nat_comp_inv (r + 1) hz1] at hderiv
      linear_combination (norm := (rw [pow_succ]; ring)) hderiv

/-- In strictly negative integer weight `n < 0`, `polylog n z + (-1) ^ n * polylog n z⁻¹ = 0` for
every `z ≠ 1` (including `z = 0`). -/
theorem polylog_add_zpow_mul_inv_of_neg {n : ℤ} (hn : n < 0) {z : ℂ} (hz1 : z ≠ 1) :
    polylog n z + (-1 : ℂ) ^ n * polylog n z⁻¹ = 0 := by
  lift -n - 1 to ℕ using (by omega) with r hr
  obtain rfl : n = -((r + 1 : ℕ) : ℤ) := by
    push_cast
    omega
  have hsign : (-1 : ℂ) ^ (-((r + 1 : ℕ) : ℤ)) = (-1 : ℂ) ^ (r + 1) := by
    rw [zpow_neg, zpow_natCast, ← inv_pow, inv_neg, inv_one]
  rw [hsign]
  exact polylog_neg_nat_succ_add_pow_mul_inv r hz1

/-- Solved-for-`z⁻¹` form of inversion in strictly negative weight `n < 0` away from `z = 1`. -/
theorem polylog_inv_of_neg {n : ℤ} (hn : n < 0) {z : ℂ} (hz1 : z ≠ 1) :
    polylog n z⁻¹ = -(-1 : ℂ) ^ n * polylog n z := by
  have hsq : (-1 : ℂ) ^ n * (-1 : ℂ) ^ n = 1 := by
    rw [← mul_zpow]
    norm_num
  have h := congrArg ((-1 : ℂ) ^ n * ·) (polylog_add_zpow_mul_inv_of_neg hn hz1)
  rw [mul_zero, mul_add, ← mul_assoc, hsq, one_mul] at h
  linear_combination h

/-- Inversion in nonpositive weight: for `n ≤ 0` and `z ∉ {0, 1}`, the combination
`polylog n z + (-1) ^ n * polylog n z⁻¹` is `-1` in weight zero and `0` below. -/
theorem polylog_inversion_of_nonpos (n : ℤ) (hn : n ≤ 0) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    polylog n z + (-1 : ℂ) ^ n * polylog n z⁻¹ = if n = 0 then -1 else 0 := by
  rcases hn.eq_or_lt with rfl | hn'
  · simpa using polylog_zero_weight_add_inv hz0 hz1
  · simp only [hn'.ne, ↓reduceIte]
    exact polylog_add_zpow_mul_inv_of_neg hn' hz1

/-- Solved-for-`z⁻¹` form of nonpositive-weight inversion away from `0` and `1`. -/
theorem polylog_inv_of_nonpos {n : ℤ} (hn : n ≤ 0) {z : ℂ} (hz0 : z ≠ 0) (hz1 : z ≠ 1) :
    polylog n z⁻¹ = (if n = 0 then -1 else 0) - (-1 : ℂ) ^ n * polylog n z := by
  rcases hn.eq_or_lt with rfl | hn'
  · simpa using polylog_zero_weight_inv hz0 hz1
  · simp only [hn'.ne, ↓reduceIte, zero_sub, ← neg_mul]
    exact polylog_inv_of_neg hn' hz1

/-- Weight `-1` is invariant under `z ↦ z⁻¹` away from `z = 1`. -/
theorem polylog_neg_one_inv {z : ℂ} (hz1 : z ≠ 1) :
    polylog (-1) z⁻¹ = polylog (-1) z := by
  simpa using polylog_inv_of_neg (n := -1) (by omega) hz1

-- Weight-zero inversion at `z = 2`, `z = I`, and `z = -3` gives `-1`.
example : polylog 0 (2 : ℂ) + polylog 0 (2 : ℂ)⁻¹ = -1 ∧
    polylog 0 Complex.I + polylog 0 Complex.I⁻¹ = -1 ∧
    polylog 0 (-3 : ℂ) + polylog 0 (-3 : ℂ)⁻¹ = -1 :=
  ⟨polylog_zero_weight_add_inv (by norm_num) (by norm_num),
    polylog_zero_weight_add_inv Complex.I_ne_zero (by
      intro h
      have := congrArg Complex.im h
      norm_num at this),
    polylog_zero_weight_add_inv (by norm_num) (by norm_num)⟩

-- Neither `z ≠ 0` nor `z ≠ 1` can be omitted from `polylog_inversion_of_nonpos` in weight zero.
example : polylog 0 (0 : ℂ) + (-1 : ℂ) ^ (0 : ℤ) * polylog 0 (0 : ℂ)⁻¹ ≠ -1 ∧
    polylog 0 (1 : ℂ) + (-1 : ℂ) ^ (0 : ℤ) * polylog 0 (1 : ℂ)⁻¹ ≠ -1 := by
  norm_num [polylog_zero_weight]

end TauCeti.Polylog
