/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.NormalForm
public import TauCeti.Analysis.Complex.Taylor.WindowPoleComparison
import TauCeti.Analysis.Meromorphic.ExpansionDisc

/-!
# Rightmost poles from Taylor bounds on windows

An upper bound on the sum of a Taylor coefficient norm on a vertical line and the real part
of the corresponding reflected coefficient at the real centre excludes the shifted-pole
case of the expansion-disc dichotomy. Thus if there is a pole, the rightmost pole is real
and its leading Laurent coefficient cannot have positive real part. The bound is needed
only at one sufficiently large Taylor degree per selected window, and for each centre the
windows may be chosen separately.

This extends the pole exclusion argument in Levent Alpöge's `Deduction.landau_window`
(<https://github.com/leanprover-community/riemann-hypothesis>) to poles of arbitrary finite order.
-/

public section

open Complex Metric
open scoped Nat

/-- Suppose `F` is in meromorphic normal form on `re z > θ`, with all poles there to the left
of `re z = σ`. At each centre `σ + γ * I`, assume a bound `C * exp (η * U) / (σ - θ)^k` on the sum
of the absolute Taylor coefficient there and the real part of the reflected coefficient at
`σ`, for every `η > 0` and arbitrarily large `U` at some degree `k ≥ U`. If the half-plane
contains a pole, it contains a rightmost real pole whose leading Laurent coefficient has
nonpositive real part. -/
theorem MeromorphicNFOn.exists_rightmost_real_pole_of_window_taylor_bound {F : ℂ → ℂ} {θ σ : ℝ}
    (hF : MeromorphicNFOn F {z | θ < z.re})
    (hσ : ∀ z : ℂ, θ < z.re → meromorphicOrderAt F z < 0 → z.re < σ)
    (hp : ∃ z : ℂ, θ < z.re ∧ meromorphicOrderAt F z < 0)
    (hupper : ∀ (γ η : ℝ), 0 < η → ∃ C : ℝ, ∀ U₀ : ℝ, ∃ U ≥ U₀, ∃ k : ℕ,
      U ≤ (k : ℝ) ∧
        ‖iteratedDeriv k F ((σ : ℂ) + γ * I) / (k ! : ℂ)‖ +
          ((-1) ^ k * (iteratedDeriv k F σ / (k ! : ℂ))).re ≤
          C * Real.exp (η * U) / (σ - θ) ^ k) :
    ∃ β : ℝ, θ < β ∧ meromorphicOrderAt F (β : ℂ) < 0 ∧
      (∀ z : ℂ, meromorphicOrderAt F z < 0 → z.re ≤ β) ∧
      (meromorphicTrailingCoeffAt F β).re ≤ 0 := by
  have horder {z : ℂ} (hz : meromorphicOrderAt F z < 0) :
      ∃ m : ℕ, meromorphicOrderAt F z = (-(↑(m + 1) : ℤ) : WithTop ℤ) := by
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hz.ne_top
    have hn' : n < 0 := WithTop.coe_lt_coe.mp (hn ▸ hz)
    obtain ⟨m, rfl⟩ := Int.eq_negSucc_of_lt_zero hn'
    exact ⟨m, by simpa [Int.negSucc_eq] using hn.symm⟩
  rcases hF.exists_analytic_discs_or_rightmost_real_pole hσ hp with
    ⟨γ, ρ, r, hd, hdr, hr, hpole, hz, hw⟩ | ⟨β, r, hθ, hd, hdr, hr, hpole, hmax, hz⟩
  · rw [dist_eq_norm] at hd hdr
    obtain ⟨m, hm⟩ := horder hpole
    have hne := sub_ne_zero.mp (norm_pos_iff.mp hd)
    have hle := hz.differentiableOn.le_norm_sub_of_window_taylor_bound_of_pole hw.differentiableOn
      (lt_min hdr hdr) hne hm (hupper γ)
    exact (hdr.not_ge (hr.trans hle)).elim
  · refine ⟨β, hθ, hpole, hmax, ?_⟩
    obtain ⟨m, hm⟩ := horder hpole
    refine hz.differentiableOn.meromorphicTrailingCoeffAt_re_nonpos_of_window_taylor_bound
      (sub_pos.mp hd) (lt_min hdr (hdr.trans_le hr)) hm fun η hη ↦ ?_
    obtain ⟨C, hC⟩ := hupper 0 η hη
    refine ⟨C, fun U₀ ↦ ?_⟩
    obtain ⟨U, hU, k, hk, hb⟩ := hC U₀
    exact ⟨U, hU, k, hk, (le_add_of_nonneg_left (norm_nonneg _)).trans hb⟩
