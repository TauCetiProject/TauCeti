/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# Lipschitz bounds for first Riesz sums

For coefficients `c : ℕ → 𝕜` the first Riesz sum is `S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`,
written here as `∑ n ∈ Ioc 0 ⌊y⌋₊, c n * (y / n - 1)`, the index set of Mathlib's
`Chebyshev.psi`. Each term is a ramp `c(n) max (y / n - 1) 0`, so `S` is continuous, has right
derivative `∑_{n ≤ y} c(n) / n`, and is Lipschitz in `y` with constant `∑_{n ≤ y} ‖c(n)‖ / n`.
Its weighted form `w · S(a / w) = ∑_n c(n) max (a / n - w) 0` is Lipschitz in the weight `w` with
constant `∑_{n ≤ a / w} ‖c(n)‖`, and antitone in `w` when the coefficients are nonnegative.

## Main results

* `TauCeti.sum_Ioc_floor_mul_div_sub_one_eq_sum_max`: the Riesz sum as a sum of ramps.
* `TauCeti.norm_sum_Ioc_floor_mul_div_sub_one_sub_sum_le`: Lipschitz bound in `y`.
* `TauCeti.norm_mul_sum_Ioc_floor_div_sub_mul_sum_le`: Lipschitz bound in the weight.
* `TauCeti.mul_sum_Ioc_floor_div_le_mul_sum`: antitonicity in the weight.
* `TauCeti.continuous_sum_Ioc_floor_mul_div_sub_one`,
  `TauCeti.hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one`: continuity and the right derivative.

## References

* The ramp decomposition and the Lipschitz bounds in the weight are the ingredients of the bounds
  for the Riesz remainder in the formal proof of the Riemann hypothesis for Dirichlet
  `L`-functions, https://github.com/leanprover-community/riemann-hypothesis.
-/

public section

open Finset

namespace TauCeti

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The Riesz sum `∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` as a sum of ramps: for every `N ≥ ⌊y⌋₊` it equals
`∑_{1 ≤ n ≤ N} c(n) max (y / n - 1) 0`, the ramps of the indices `n > y` vanishing. -/
theorem sum_Ioc_floor_mul_div_sub_one_eq_sum_max (c : ℕ → 𝕜) {y : ℝ} {N : ℕ}
    (hN : ⌊y⌋₊ ≤ N) :
    ∑ n ∈ Ioc 0 ⌊y⌋₊, c n * ((y : 𝕜) / n - 1) =
      ∑ n ∈ Ioc 0 N, c n * ((max (y / n - 1) 0 : ℝ) : 𝕜) := by
  rw [← sum_Ioc_consecutive _ (Nat.zero_le _) hN, sum_eq_zero (s := Ioc ⌊y⌋₊ N), add_zero]
  · refine sum_congr rfl fun n hn ↦ ?_
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Ioc.1 hn).1
    have hny : (n : ℝ) ≤ y := (Nat.le_floor_iff' (mem_Ioc.1 hn).1.ne').1 (mem_Ioc.1 hn).2
    rw [max_eq_left (by rwa [sub_nonneg, one_le_div hn0])]
    push_cast
    ring
  · intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le _).trans_lt (mem_Ioc.1 hn).1
    have hyn : y < n := Nat.lt_of_floor_lt (mem_Ioc.1 hn).1
    rw [max_eq_right (by rw [sub_nonpos, div_le_one hn0]; exact hyn.le)]
    simp

/-- The weighted Riesz sum `w' · S(a / w')` as a sum of ramps in the weight: for `0 < w ≤ w'` it
equals `∑_{1 ≤ n ≤ a / w} c(n) max (a / n - w') 0`. -/
private theorem mul_sum_Ioc_floor_div_eq_sum_max (c : ℕ → 𝕜) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    (w' : 𝕜) * ∑ n ∈ Ioc 0 ⌊a / w'⌋₊, c n * (((a / w' : ℝ) : 𝕜) / n - 1) =
      ∑ n ∈ Ioc 0 ⌊a / w⌋₊, c n * ((max (a / n - w') 0 : ℝ) : 𝕜) := by
  have hw' := hw.trans_le hww'
  have hN : ⌊a / w'⌋₊ ≤ ⌊a / w⌋₊ := by
    rcases le_total a 0 with ha | ha
    · simp [Nat.floor_of_nonpos (div_nonpos_of_nonpos_of_nonneg ha hw'.le)]
    · exact Nat.floor_le_floor (div_le_div_of_nonneg_left ha hw hww')
  rw [sum_Ioc_floor_mul_div_sub_one_eq_sum_max c hN, mul_sum]
  refine sum_congr rfl fun n hn ↦ ?_
  have hn : (n : ℝ) ≠ 0 := by exact_mod_cast (mem_Ioc.1 hn).1.ne'
  have h : w' * (a / w' / n - 1) = a / n - w' := by field_simp
  rw [mul_left_comm, ← RCLike.ofReal_mul, mul_max_of_nonneg _ _ hw'.le, mul_zero, h]

/-- **Lipschitz bound for a Riesz sum.** For `z ≤ y`,
`‖S(y) - S(z)‖ ≤ (∑_{1 ≤ n ≤ y} ‖c(n)‖ / n) (y - z)`, where
`S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`. -/
theorem norm_sum_Ioc_floor_mul_div_sub_one_sub_sum_le (c : ℕ → 𝕜) {y z : ℝ} (hzy : z ≤ y) :
    ‖∑ n ∈ Ioc 0 ⌊y⌋₊, c n * ((y : 𝕜) / n - 1) - ∑ n ∈ Ioc 0 ⌊z⌋₊, c n * ((z : 𝕜) / n - 1)‖ ≤
      (∑ n ∈ Ioc 0 ⌊y⌋₊, ‖c n‖ / n) * (y - z) := by
  rw [sum_Ioc_floor_mul_div_sub_one_eq_sum_max c le_rfl,
    sum_Ioc_floor_mul_div_sub_one_eq_sum_max c (Nat.floor_le_floor hzy), ← sum_sub_distrib,
    sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
  simp only [← mul_sub, norm_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
  have h : |max (y / n - 1) 0 - max (z / n - 1) 0| ≤ (y - z) / n :=
    (abs_max_sub_max_le_abs _ _ _).trans_eq (by
      rw [sub_sub_sub_cancel_right, ← sub_div,
        abs_of_nonneg (div_nonneg (sub_nonneg.2 hzy) n.cast_nonneg)])
  calc _ ≤ ‖c n‖ * ((y - z) / n) := by gcongr
    _ = ‖c n‖ / n * (y - z) := by ring

/-- **Lipschitz bound for a weighted Riesz sum in the weight.** For `0 < w ≤ w'`,
`‖w S(a / w) - w' S(a / w')‖ ≤ (∑_{1 ≤ n ≤ a / w} ‖c(n)‖) (w' - w)`, where
`S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`. -/
theorem norm_mul_sum_Ioc_floor_div_sub_mul_sum_le (c : ℕ → 𝕜) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    ‖(w : 𝕜) * ∑ n ∈ Ioc 0 ⌊a / w⌋₊, c n * (((a / w : ℝ) : 𝕜) / n - 1) -
        (w' : 𝕜) * ∑ n ∈ Ioc 0 ⌊a / w'⌋₊, c n * (((a / w' : ℝ) : 𝕜) / n - 1)‖ ≤
      (∑ n ∈ Ioc 0 ⌊a / w⌋₊, ‖c n‖) * (w' - w) := by
  rw [mul_sum_Ioc_floor_div_eq_sum_max c hw le_rfl, mul_sum_Ioc_floor_div_eq_sum_max c hw hww',
    ← sum_sub_distrib, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ ↦ ?_)
  rw [← mul_sub, norm_mul, ← RCLike.ofReal_sub, RCLike.norm_ofReal]
  gcongr
  calc _ ≤ |(a / n - w) - (a / n - w')| := abs_max_sub_max_le_abs _ _ _
    _ = w' - w := by rw [sub_sub_sub_cancel_left, abs_of_nonneg (sub_nonneg.2 hww')]

end RCLike

/-- **The weighted Riesz sum is antitone in the weight** for nonnegative coefficients: for
`0 < w ≤ w'`, `w' S(a / w') ≤ w S(a / w)`, where `S(y) = ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)`. -/
theorem mul_sum_Ioc_floor_div_le_mul_sum {c : ℕ → ℝ} (hc : ∀ n, 0 ≤ c n) {a w w' : ℝ} (hw : 0 < w)
    (hww' : w ≤ w') :
    w' * ∑ n ∈ Ioc 0 ⌊a / w'⌋₊, c n * (a / w' / n - 1) ≤
      w * ∑ n ∈ Ioc 0 ⌊a / w⌋₊, c n * (a / w / n - 1) := by
  have h₁ := mul_sum_Ioc_floor_div_eq_sum_max c (a := a) hw le_rfl
  have h₂ := mul_sum_Ioc_floor_div_eq_sum_max c (a := a) hw hww'
  simp only [RCLike.ofReal_real_eq_id, id] at h₁ h₂
  rw [h₁, h₂]
  exact sum_le_sum fun n _ ↦ mul_le_mul_of_nonneg_left (by gcongr) (hc n)

/-- **The Riesz sum is continuous**: `y ↦ ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` is continuous on `ℝ`. -/
theorem continuous_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) :
    Continuous fun t : ℝ ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1) := by
  refine continuous_iff_continuousAt.2 fun x ↦ ?_
  have hcont : Continuous fun t : ℝ ↦ ∑ n ∈ Ioc 0 ⌊x + 1⌋₊, c n * max (t / n - 1) 0 := by
    fun_prop
  refine hcont.continuousAt.congr (Filter.eventuallyEq_of_mem (Iic_mem_nhds (lt_add_one x))
    fun t ht ↦ ?_)
  have h := sum_Ioc_floor_mul_div_sub_one_eq_sum_max c (Nat.floor_le_floor (Set.mem_Iic.1 ht))
  simp only [RCLike.ofReal_real_eq_id, id] at h
  exact h.symm

/-- **Right derivative of the Riesz sum.** `y ↦ ∑_{1 ≤ n ≤ y} c(n) (y / n - 1)` has right
derivative `∑_{1 ≤ n ≤ x} c(n) / n` at every `x`. -/
theorem hasDerivWithinAt_sum_Ioc_floor_mul_div_sub_one (c : ℕ → ℝ) (x : ℝ) :
    HasDerivWithinAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊t⌋₊, c n * (t / n - 1))
      (∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (1 / n)) (Set.Ici x) x := by
  have hlin : HasDerivAt (fun t ↦ ∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (t / n - 1))
      (∑ n ∈ Ioc 0 ⌊x⌋₊, c n * (1 / n)) x :=
    HasDerivAt.fun_sum fun n _ ↦ (((hasDerivAt_id' x).div_const (n : ℝ)).sub_const 1).const_mul
      (c n)
  refine hlin.hasDerivWithinAt.congr_of_eventuallyEq ?_ rfl
  filter_upwards [Ico_mem_nhdsGE (Nat.lt_floor_add_one x)] with t ht
  have hlt : ⌊t⌋₊ < ⌊x⌋₊ + 1 :=
    (Nat.floor_lt' (Nat.succ_ne_zero _)).2 (by exact_mod_cast ht.2)
  rw [le_antisymm (Nat.lt_succ_iff.1 hlt) (Nat.floor_le_floor ht.1)]

end TauCeti
