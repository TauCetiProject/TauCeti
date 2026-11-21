/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex

/-!
# Coefficients of the Airy asymptotic expansions

The coefficients `u_k` and `v_k` of the asymptotic expansions of the Airy functions for large
argument, and the Gamma-function multiplier `χ` of their error bounds (DLMF 9.7.2–9.7.4):

* `TauCeti.airyU`: `u_k = (2k + 1)(2k + 3)⋯(6k − 1) / (216^k k!)`, with `u₀ = 1` and the
  recurrence `u_{k+1} = (6k + 1)(6k + 3)(6k + 5) / ((2k + 1) · 216 · (k + 1)) · u_k`
  (`Nat.airyU_succ`);
* `TauCeti.airyV`: `v_k = −(6k + 1)/(6k − 1) · u_k`, with `v₀ = 1` and `v_k < 0` for `k ≥ 1`;
* `Real.airyChi`: `χ(x) = π^{1/2} Γ(x/2 + 1) / Γ(x/2 + ½)`, with `χ(0) = 1`,
  `χ(1) = π/2`, `χ(2) = 2`, strictly increasing on `(-1, ∞)`
  (`Real.strictMonoOn_airyChi`) and `χ(x) ∼ (πx/2)^{1/2}` as `x → ∞`
  (`Real.isEquivalent_airyChi`, DLMF 9.7.4).

The asymptotic form of `χ` and its monotonicity come from Wendel's inequalities and the strict
monotonicity of `Γ(x + c)/Γ(x)`, both consequences of the log-convexity of `Γ`.

The definitions of `u_k`, `v_k` and `χ`, the statement of the recurrence, the values of `χ` and
the asymptotic form of `χ` are adapted from the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), files `DLMF/Airy/Asymptotics/LaplaceSectors.lean` and
`DLMF/Airy/Asymptotics/DerivativeRemainders.lean`. lean-DLMF writes `u_k` with Pochhammer symbols
and obtains the asymptotic form of `χ` from a limit of Gamma ratios; this formalization proves the
recurrence from the product form and derives the asymptotic form from Wendel's inequalities. The
strict monotonicity of `χ` is not in lean-DLMF.

## References

* NIST Digital Library of Mathematical Functions, §9.7(i), <https://dlmf.nist.gov/9.7.i>.
-/

public section

noncomputable section

open Filter Asymptotics Finset
open scoped Nat Real

namespace TauCeti

/-- The coefficients `u_k = (2k + 1)(2k + 3)⋯(6k − 1) / (216^k k!)` (DLMF 9.7.2). -/
def airyU (k : ℕ) : ℝ :=
  (∏ j ∈ range (2 * k), ((2 * k + 1 + 2 * j : ℕ) : ℝ)) / (216 ^ k * (k ! : ℝ))

/-- The defining product formula for `u_k`. -/
theorem _root_.Nat.airyU_def (k : ℕ) :
    airyU k = (∏ j ∈ range (2 * k), ((2 * k + 1 + 2 * j : ℕ) : ℝ)) / (216 ^ k * (k ! : ℝ)) :=
  (rfl)

/-- `u₀ = 1`. -/
@[simp]
theorem airyU_zero : airyU 0 = 1 := by
  simp [Nat.airyU_def]

/-- The coefficients `u_k` are positive. -/
theorem _root_.Nat.airyU_pos (k : ℕ) : 0 < airyU k := by
  rw [Nat.airyU_def]
  positivity

/-- The products `(2k + 1)(2k + 3)⋯(6k − 1)` in the numerators of `u_k` satisfy
`(2k + 1) P_{k+1} = (6k + 1)(6k + 3)(6k + 5) P_k`. -/
private theorem airyU_numerator_succ (k : ℕ) :
    (∏ j ∈ range (2 * (k + 1)), (2 * (k + 1) + 1 + 2 * j)) * (2 * k + 1) =
      (∏ j ∈ range (2 * k), (2 * k + 1 + 2 * j)) * ((6 * k + 1) * (6 * k + 3) * (6 * k + 5)) := by
  have hshift : (∏ j ∈ range (2 * k), (2 * (k + 1) + 1 + 2 * j)) * (2 * k + 1) =
      (∏ j ∈ range (2 * k), (2 * k + 1 + 2 * j)) * (6 * k + 1) := by
    have h := (prod_range_succ' (fun j => 2 * k + 1 + 2 * j) (2 * k)).symm.trans
      (prod_range_succ (fun j => 2 * k + 1 + 2 * j) (2 * k))
    convert h using 2
    · exact prod_congr rfl fun j _ => by ring
    · ring
  -- Peel off the last two factors of the product over `range (2 * (k + 1))`.
  have h2 : 2 * (k + 1) = 2 * k + 1 + 1 := by ring
  rw [h2, prod_range_succ, prod_range_succ, ← h2]
  linear_combination ((2 * (k + 1) + 1 + 2 * (2 * k)) * (2 * (k + 1) + 1 + 2 * (2 * k + 1))) *
    hshift

/-- The recurrence `u_{k+1} = (6k + 1)(6k + 3)(6k + 5) / ((2k + 1) · 216 · (k + 1)) · u_k`
(DLMF 9.7.2). -/
theorem _root_.Nat.airyU_succ (k : ℕ) :
    airyU (k + 1) = (6 * k + 1) * (6 * k + 3) * (6 * k + 5) / ((2 * k + 1) * 216 * (k + 1)) *
      airyU k := by
  have h : ((∏ j ∈ range (2 * (k + 1)), (2 * (k + 1) + 1 + 2 * j) : ℕ) : ℝ) * (2 * k + 1) =
      ((∏ j ∈ range (2 * k), (2 * k + 1 + 2 * j) : ℕ) : ℝ) *
        ((6 * k + 1) * (6 * k + 3) * (6 * k + 5)) := by
    exact_mod_cast airyU_numerator_succ k
  rw [Nat.airyU_def, Nat.airyU_def, ← Nat.cast_prod, ← Nat.cast_prod, Nat.factorial_succ]
  have h2k : (2 * k + 1 : ℝ) ≠ 0 := by positivity
  push_cast at h ⊢
  rw [(eq_div_iff h2k).mpr h]
  field_simp
  ring

/-- The coefficients `v_k = −(6k + 1)/(6k − 1) · u_k` (DLMF 9.7.2). -/
def airyV (k : ℕ) : ℝ := -((6 * k + 1 : ℝ) / (6 * k - 1)) * airyU k

/-- The defining formula for `v_k`. -/
theorem _root_.Nat.airyV_def (k : ℕ) : airyV k = -((6 * k + 1 : ℝ) / (6 * k - 1)) * airyU k :=
  (rfl)

/-- `v₀ = 1`. -/
@[simp]
theorem airyV_zero : airyV 0 = 1 := by
  simp [Nat.airyV_def]

/-- For `k ≥ 1`, `v_k` is negative: its sign is opposite to that of `u_k`. -/
theorem airyV_neg {k : ℕ} (hk : 1 ≤ k) : airyV k < 0 := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [Nat.airyV_def, neg_mul, neg_neg_iff_pos]
  exact mul_pos (div_pos (by linarith) (by linarith)) (Nat.airyU_pos k)

end TauCeti

namespace Real

/-- The multiplier `χ(x) = π^{1/2} Γ(x/2 + 1) / Γ(x/2 + ½)` (DLMF 9.7.3). -/
def airyChi (x : ℝ) : ℝ := √π * Real.Gamma (x / 2 + 1) / Real.Gamma (x / 2 + 1 / 2)

/-- The defining Gamma-ratio formula for `χ`. -/
theorem airyChi_def (x : ℝ) :
    airyChi x = √π * Real.Gamma (x / 2 + 1) / Real.Gamma (x / 2 + 1 / 2) := (rfl)

/-- `χ(0) = 1`. -/
@[simp]
theorem airyChi_zero : airyChi 0 = 1 := by
  have hπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  simp only [airyChi_def, zero_div, zero_add, Real.Gamma_one, Real.Gamma_one_half_eq, mul_one,
    div_self hπ]

/-- `Γ(3/2) = √π / 2`, the Gamma value in `χ(1)` and `χ(2)`. -/
private theorem Gamma_three_halves : Real.Gamma (3 / 2) = √π / 2 := by
  have h : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  rw [h, Real.Gamma_add_one (by norm_num), Real.Gamma_one_half_eq]
  ring

/-- `χ(1) = π/2`. -/
@[simp]
theorem airyChi_one : airyChi 1 = π / 2 := by
  norm_num [airyChi_def, Gamma_three_halves]
  rw [← mul_div_assoc, Real.mul_self_sqrt Real.pi_pos.le]

/-- `χ(2) = 2`. -/
@[simp]
theorem airyChi_two : airyChi 2 = 2 := by
  have hπ : √π ≠ 0 := (Real.sqrt_pos.2 Real.pi_pos).ne'
  norm_num [airyChi_def, Gamma_three_halves]
  field_simp

/-- `χ` is strictly increasing on `(-1, ∞)`, in particular on `(0, ∞)`. -/
theorem strictMonoOn_airyChi : StrictMonoOn airyChi (Set.Ioi (-1)) := by
  intro x hx y hy hxy
  rw [Set.mem_Ioi] at hx hy
  have hx' : x / 2 + 1 / 2 ∈ Set.Ioi 0 := by rw [Set.mem_Ioi]; linarith
  have hy' : y / 2 + 1 / 2 ∈ Set.Ioi 0 := by rw [Set.mem_Ioi]; linarith
  have h := Real.strictMonoOn_Gamma_add_div_Gamma (c := 1 / 2) (by norm_num) hx' hy'
    (by linarith)
  simp only [add_assoc, add_halves] at h
  rw [airyChi_def, airyChi_def, mul_div_assoc, mul_div_assoc]
  exact mul_lt_mul_of_pos_left h (Real.sqrt_pos.2 Real.pi_pos)

/-- `χ(x) ∼ (πx/2)^{1/2}` as `x → ∞` (DLMF 9.7.4). -/
theorem isEquivalent_airyChi : airyChi ~[atTop] fun x => √(π * x / 2) := by
  have h := (Real.isEquivalent_Gamma_add_one_div_Gamma_add (1 / 2)).comp_tendsto
    (tendsto_id.atTop_div_const two_pos)
  refine (((IsEquivalent.refl (u := fun _ : ℝ => √π)).mul h).congr_left ?_).congr_right ?_
  · exact Eventually.of_forall fun x => by
      simp [airyChi_def, mul_div_assoc]
  · refine Eventually.of_forall fun x => ?_
    simp only [Pi.mul_apply, Function.comp_apply, id]
    have hx : π * x / 2 = π * (x / 2) := by ring
    rw [hx, Real.sqrt_mul Real.pi_pos.le, Real.sqrt_eq_rpow (x / 2)]
    norm_num

end Real
