/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
import TauCeti.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Geometric bounds along large windows

An eventual geometric lower bound constrains an upper bound known only at indices selected on
arbitrarily large windows, even when the upper bound loses a subexponential factor in the window
scale. This is the rate comparison used in the windowed Landau argument.
-/

public section

open Filter

namespace TauCeti

/-- Suppose `a / d^(k+1)` eventually bounds `v k` below, with `a, d > 0`. If at arbitrarily large
scales `U` one can choose an index `k ≥ U` with `v k ≤ C exp(η U) / R^k`, for every `η > 0`
(with `C` allowed to depend on `η`), then `R ≤ d`. -/
theorem le_of_window_exp_div_pow_bound {v : ℕ → ℝ} {a d R : ℝ} (ha : 0 < a) (hd : 0 < d)
    (hlower : ∀ᶠ k in atTop, a / d ^ (k + 1) ≤ v k)
    (hupper : ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧ v k ≤ C * Real.exp (η * U) / R ^ k) : R ≤ d := by
  by_contra! hR
  obtain ⟨r, hdr, hrR⟩ := exists_between hR
  have hr : 0 < r := hd.trans hdr
  have hpos : 0 < R := hr.trans hrR
  have hratio : 1 < R / r := (one_lt_div hr).2 hrR
  let η := Real.log (R / r)
  have hη : 0 < η := Real.log_pos hratio
  obtain ⟨C, hC⟩ := hupper η hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 <| hlower.and
    (eventually_div_pow_le_div_pow |C| (half_pos ha) hd hdr)
  obtain ⟨U, hU, k, hk, hv⟩ := hC N
  have hkN : N ≤ k := by exact_mod_cast hU.trans hk
  have hexp : Real.exp (η * U) ≤ (R / r) ^ k := by
    calc
      Real.exp (η * U) ≤ Real.exp (η * (k : ℝ)) :=
        Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hk hη.le)
      _ = (R / r) ^ k := by
        rw [mul_comm, Real.exp_natCast_mul, Real.exp_log (div_pos hpos hr)]
  have hv' : v k ≤ |C| / r ^ k := calc
    v k ≤ C * Real.exp (η * U) / R ^ k := hv
    _ ≤ |C| * (R / r) ^ k / R ^ k := by gcongr; exact le_abs_self _
    _ = |C| / r ^ k := by rw [div_pow]; field_simp
  obtain ⟨hlo, hhi⟩ := hN k hkN
  have hhalf : a / 2 / d ^ (k + 1) < a / d ^ (k + 1) := by
    gcongr
    linarith
  exact (hlo.trans (hv'.trans hhi)).not_gt hhalf

end TauCeti
