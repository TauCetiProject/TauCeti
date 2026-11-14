/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.RegularizedHypergeometric
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# A large-parameter limit of the Kummer function

For arbitrary fixed complex `c` and `z`, the ordinary Kummer function
`Γ(2k + c) 𝐌(k, 2k + c, z)` tends to `exp (z / 2)` as the natural number `k` tends to infinity.
The lower parameter eventually has positive real part, so no restriction on `c` is needed.
This asymptotic is used in minimal-solution arguments for the incomplete-gamma continued
fractions; see [DLMF, §8.9](https://dlmf.nist.gov/8.9).
-/

public section

open Filter
open scoped Nat Topology

namespace Complex

private theorem eventually_kummer_parameters (c : ℂ) :
    ∀ᶠ k : ℕ in atTop, 0 < (k : ℝ) ∧ 0 ≤ (k : ℝ) + c.re := by
  filter_upwards [tendsto_natCast_atTop_atTop.eventually
    (eventually_gt_atTop (max 0 (-c.re)))] with k hk
  constructor <;> linarith [le_max_left 0 (-c.re), le_max_right 0 (-c.re)]

private theorem kummer_coeff_succ (c : ℂ) {k : ℕ}
    (hb : 0 < (2 * (k : ℂ) + c).re) (n : ℕ) :
    Gamma (2 * k + c) * regularizedHGFunCoeff {(k : ℂ)} {2 * k + c} (n + 1) =
      (Gamma (2 * k + c) * regularizedHGFunCoeff {(k : ℂ)} {2 * k + c} n) *
        (((k : ℂ) + n) / (2 * k + c + n) / (n + 1)) := by
  rw [regularizedHGFunCoeff_add_one
    (by simpa using ne_neg_natCast_of_re_pos hb n)]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]
  rw [div_mul_eq_div_div]
  ring

private theorem kummer_coeff_bound (c : ℂ) {k : ℕ} (hk : 0 < (k : ℝ))
    (hc : 0 ≤ (k : ℝ) + c.re) (n : ℕ) :
    ‖Gamma (2 * k + c) * regularizedHGFunCoeff {(k : ℂ)} {2 * k + c} n‖ ≤
      1 / (n ! : ℝ) := by
  have hb : 0 < (2 * (k : ℂ) + c).re := by simp; linarith
  induction n with
  | zero => simp [regularizedHGFunCoeff, Gamma_ne_zero_of_re_pos hb]
  | succ n ih =>
    have hratio : ‖((k : ℂ) + n) / (2 * k + c + n)‖ ≤ 1 := by
      rw [norm_div]
      apply (div_le_one (by
        have := re_le_norm (2 * (k : ℂ) + c + n)
        simp at this
        linarith [n.cast_nonneg (α := ℝ)])).2
      calc ‖(k : ℂ) + n‖ = (k : ℝ) + n := by
              rw [← Nat.cast_add, norm_natCast, Nat.cast_add]
        _ ≤ (2 * (k : ℂ) + c + n).re := by simp; linarith
        _ ≤ ‖2 * (k : ℂ) + c + n‖ := re_le_norm _
    rw [kummer_coeff_succ c hb n, norm_mul, norm_div]
    rw [← Nat.cast_add_one, norm_natCast]
    push_cast
    calc _ ≤ (1 / (n ! : ℝ)) * (1 / ((n : ℝ) + 1)) := by gcongr
      _ = 1 / ((n + 1)! : ℝ) := by
          simp [Nat.factorial_succ, div_eq_mul_inv, mul_comm]

private theorem tendsto_kummer_coeff (c : ℂ) (n : ℕ) :
    Tendsto (fun k : ℕ => Gamma (2 * k + c) *
      regularizedHGFunCoeff {(k : ℂ)} {2 * k + c} n)
      atTop (𝓝 ((1 / 2 : ℂ) ^ n / n !)) := by
  have hpos : ∀ᶠ k : ℕ in atTop, 0 < (2 * (k : ℂ) + c).re := by
    filter_upwards [eventually_kummer_parameters c] with k hk
    simp only [mul_re, re_ofNat, natCast_re, im_ofNat, natCast_im, mul_zero,
      sub_zero, add_re]
    linarith [hk.1, hk.2]
  induction n with
  | zero =>
    apply tendsto_const_nhds.congr'
    filter_upwards [hpos] with k hk
    simp [regularizedHGFunCoeff, Gamma_ne_zero_of_re_pos hk]
  | succ n ih =>
    have hratio : Tendsto (fun k : ℕ => ((k : ℂ) + n) / (2 * k + c + n))
        atTop (𝓝 (1 / 2 : ℂ)) := by
      simpa [add_comm, add_left_comm, add_assoc] using
        tendsto_add_mul_div_add_mul_atTop_nhds (n : ℂ) (c + n) 1
          (d := (2 : ℂ)) (by norm_num)
    have hlim := ih.mul (hratio.div_const (n + 1 : ℂ))
    have heq : ((1 / 2 : ℂ) ^ n / n !) * ((1 / 2) / (n + 1)) =
        (1 / 2 : ℂ) ^ (n + 1) / (n + 1)! := by
      rw [pow_succ, Nat.factorial_succ]
      push_cast
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq] at hlim
    apply hlim.congr'
    filter_upwards [hpos] with k hk
    exact (kummer_coeff_succ c hk n).symm

/-- The ordinary Kummer function with upper parameter `k` and lower parameter `2k + c`
converges to `exp (z / 2)` for every fixed pair of complex numbers `c` and `z`. -/
theorem tendsto_Gamma_mul_regularizedHGFun_nhds_exp_div_two (c z : ℂ) :
    Tendsto (fun k : ℕ => Gamma (2 * k + c) *
      regularizedHGFun {(k : ℂ)} {2 * k + c} z) atTop (𝓝 (exp (z / 2))) := by
  have hlim := tendsto_tsum_of_dominated_convergence
    (f := fun (k n : ℕ) => (Gamma (2 * k + c) *
      regularizedHGFunCoeff {(k : ℂ)} {2 * k + c} n) * z ^ n)
    (g := fun n => ((1 / 2 : ℂ) ^ n / n !) * z ^ n)
    (Real.summable_pow_div_factorial ‖z‖)
    (fun n => (tendsto_kummer_coeff c n).mul_const (z ^ n)) ?_
  · have hsum : (∑' n : ℕ, ((1 / 2 : ℂ) ^ n / n !) * z ^ n) = exp (z / 2) := by
      rw [exp_eq_exp_ℂ]
      convert (NormedSpace.expSeries_div_hasSum_exp (z / 2)).tsum_eq using 1
      congr 1
      ext n
      simp only [div_eq_mul_inv]
      ring
    rw [hsum] at hlim
    convert hlim using 1
    ext k
    simpa only [mul_assoc] using ((hasSum_regularizedHGFun (a := {(k : ℂ)})
      (b := {2 * (k : ℂ) + c}) (by simp) z).mul_left (Gamma (2 * k + c))).tsum_eq.symm
  · filter_upwards [eventually_kummer_parameters c] with k hk n
    rw [norm_mul, norm_pow]
    calc _ ≤ (1 / (n ! : ℝ)) * ‖z‖ ^ n := by
          gcongr
          exact kummer_coeff_bound c hk.1 hk.2 n
      _ = ‖z‖ ^ n / n ! := by ring

end Complex
