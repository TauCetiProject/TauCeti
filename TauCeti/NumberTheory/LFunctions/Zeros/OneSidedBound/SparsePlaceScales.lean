/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.Parameters
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Choice of scales for sparse cyclotomic places

The Behrend construction of sparse places uses a dimension `n` and a loss scale `W`.
When the order `2 ^ s` of the cyclic subgroup is between `x ^ 11` and `x ^ 12`,
we can take `W = x ^ δ` and one dimension `n` for all sufficiently large `x`.
The coefficient cap `2 * l₀ s` is logarithmic in `x`, so the fixed powers of the cap
and the dimension-dependent cost both fit within the Behrend size budget.

The scale choice follows `New.Parameters.exists_isSparse_of_ranks` in
`grh/src/New/Reduction/Data/Existence.lean` of [lsernau/grh-lean][short-proof].

[short-proof]: https://github.com/lsernau/grh-lean/blob/72fead1/grh/src/New/Reduction/Data/Existence.lean
-/

public section

open Filter Real

namespace TauCeti.OneSidedBound

/-- For a polynomial-sized dyadic tower, a fixed dimension works in the sparse-place
size estimates with loss scale `x ^ δ`. In particular `δ = ε / 6` makes the sixth
power of the loss scale equal to `x ^ ε`. -/
theorem eventually_sparse_place_parameter_bounds {δ : ℝ} (hδ : 0 < δ) (hδle : δ ≤ 11) :
    ∃ n : ℕ, 0 < n ∧ ∀ᶠ x : ℝ in atTop, ∀ s : ℕ,
      x ^ (11 : ℕ) ≤ (2 : ℝ) ^ s → (2 : ℝ) ^ s ≤ x ^ (12 : ℕ) →
        1 ≤ x ^ δ ∧ x ^ δ ≤ (2 : ℝ) ^ s ∧ (2 : ℝ) ^ s ≤ (x ^ δ) ^ n ∧
        (2 * (l₀ s : ℝ)) ^ n ≤ x ^ δ ∧ 3 * (l₀ s : ℝ) * n * 2 ^ n ≤ (x ^ δ) ^ (3 : ℕ) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (12 / δ)
  have hn₀ : 0 < n := Nat.cast_pos.mp ((div_pos (by norm_num) hδ).trans hn)
  have h12 : 12 ≤ δ * n := by
    rw [mul_comm]
    exact ((div_lt_iff₀ hδ).mp hn).le
  let C : ℝ := 81 * (12 / log 2)
  have hlog₂ : 0 < log 2 := log_pos (by norm_num)
  have hC : 0 < C := by dsimp [C]; positivity
  have hcap := ((isLittleO_log_rpow_rpow_atTop n hδ).const_mul_left ((2 * C) ^ n)).eventuallyLE
  have hδ3 : 0 < δ * 3 := by positivity
  have hcost := ((isLittleO_log_rpow_atTop hδ3).const_mul_left (3 * C * n * 2 ^ n)).eventuallyLE
  refine ⟨n, hn₀, ?_⟩
  filter_upwards [eventually_gt_atTop (1 : ℝ), hcap, hcost] with x hx hcapₓ hcostₓ s hlow hupp
  have hx₀ : 0 < x := zero_lt_one.trans hx
  have hlogₓ := log_nonneg hx.le
  have hs₀ : s ≠ 0 := by
    rintro rfl
    exact (one_lt_pow₀ hx (by norm_num : (11 : ℕ) ≠ 0)).not_ge (by simpa using hlow)
  have hslog : (s : ℝ) * log 2 ≤ 12 * log x := by
    simpa [log_pow] using log_le_log (by positivity : 0 < (2 : ℝ) ^ s) hupp
  have hl₀ : (l₀ s : ℝ) ≤ C * log x := by
    have hs : (s : ℝ) ≤ 12 / log 2 * log x := by
      rw [div_mul_eq_mul_div, le_div_iff₀ hlog₂]
      exact hslog
    calc
      (l₀ s : ℝ) ≤ 81 * (s : ℝ) := by exact_mod_cast l₀_le hs₀
      _ ≤ C * log x := by simpa only [C, mul_assoc] using mul_le_mul_of_nonneg_left hs (by norm_num)
  refine ⟨one_le_rpow hx.le hδ.le, ?_, hupp.trans ?_, ?_, ?_⟩
  · exact (rpow_le_rpow_of_exponent_le hx.le hδle).trans (by simpa using hlow)
  · rw [← rpow_mul_natCast hx₀.le, ← rpow_natCast]
    exact rpow_le_rpow_of_exponent_le hx.le (by simpa using h12)
  · have hh : (2 * C * log x) ^ n ≤ x ^ δ := by
      simpa [Real.norm_eq_abs, abs_of_nonneg hlogₓ, abs_of_nonneg hC.le,
        abs_of_nonneg (rpow_nonneg hx₀.le _), rpow_natCast, mul_pow] using hcapₓ
    calc
      _ ≤ (2 * (C * log x)) ^ n := by gcongr
      _ ≤ _ := by simpa only [mul_assoc] using hh
  · rw [← rpow_mul_natCast hx₀.le]
    calc
      _ ≤ 3 * (C * log x) * n * 2 ^ n := by gcongr
      _ = (3 * C * n * 2 ^ n) * log x := by ring
      _ ≤ _ := by
        simpa [Real.norm_eq_abs, abs_of_nonneg hlogₓ, abs_of_nonneg hC.le,
          abs_of_nonneg (rpow_nonneg hx₀.le _)] using hcostₓ

end TauCeti.OneSidedBound
