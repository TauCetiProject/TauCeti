/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import TauCeti.Analysis.Calculus.Deriv.Complex
import TauCeti.Analysis.Calculus.Deriv.ZPow

/-!
# Real-parameter smoothness and higher derivatives of `Complex.log`

This file records the smoothness and higher derivatives along the real parameter `t : ℝ` of the
shifted principal complex logarithm `t ↦ Complex.log ((t : ℂ) + z)` whenever `(u : ℂ) + z` lies in
`Complex.slitPlane`.

## Main results

* `Complex.contDiffAt_log_ofReal_add`: arbitrary-order real smoothness of `t ↦ Complex.log (t + z)`
  at `u : ℝ` when `(u : ℂ) + z ∈ Complex.slitPlane`.
* `Complex.iteratedDeriv_log_ofReal_add`: for `k ≥ 1` and `(u : ℂ) + z ∈ Complex.slitPlane`,
  `iteratedDeriv k (fun t : ℝ ↦ Complex.log ((t : ℂ) + z)) u = (-1)^(k - 1) * (k - 1)! / (u + z)^k`.
-/

public section

open Filter Topology
open scoped ContDiff Nat

namespace Complex

/-- For `(u : ℂ) + z ∈ Complex.slitPlane`, the shifted principal logarithm `t ↦ log (t + z)` is
smooth of arbitrary order at `u : ℝ`. -/
theorem contDiffAt_log_ofReal_add {u : ℝ} {z : ℂ} (h : (u : ℂ) + z ∈ slitPlane)
    (n : WithTop ℕ∞) :
    ContDiffAt ℝ n (fun t : ℝ ↦ log ((t : ℂ) + z)) u := by
  have hlin : ContDiffAt ℝ n (fun t : ℝ ↦ (t : ℂ) + z) u :=
    ofRealCLM.contDiff.contDiffAt.add contDiffAt_const
  exact ((contDiffAt_log h).restrict_scalars ℝ).comp u hlin

/-- For `k ≥ 1` and `(u : ℂ) + z ∈ Complex.slitPlane`, the `k`-th derivative of `t ↦ log (t + z)`
at `u : ℝ` is `(-1) ^ (k - 1) * (k - 1)! / (u + z) ^ k`. -/
theorem iteratedDeriv_log_ofReal_add {k : ℕ} (hk : 1 ≤ k) {u : ℝ} {z : ℂ}
    (h : (u : ℂ) + z ∈ slitPlane) :
    iteratedDeriv k (fun t : ℝ ↦ log ((t : ℂ) + z)) u =
      (-1 : ℂ) ^ (k - 1) * ((k - 1)! : ℂ) / ((u : ℂ) + z) ^ k := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
  clear hk
  induction m generalizing u with
  | zero =>
    have hd := (TauCeti.hasDerivAt_ofReal_add u z).clog_real h
    rw [zero_add, iteratedDeriv_one, hd.deriv]
    simp [one_div]
  | succ m ih =>
    have hs : {t : ℝ | (t : ℂ) + z ∈ slitPlane} ∈ 𝓝 u :=
      (isOpen_slitPlane.preimage (continuous_ofReal.add continuous_const)).mem_nhds h
    have hev : iteratedDeriv (m + 1) (fun t : ℝ ↦ log ((t : ℂ) + z)) =ᶠ[𝓝 u]
        fun t : ℝ ↦ (-1 : ℂ) ^ m * (m ! : ℂ) / ((t : ℂ) + z) ^ (m + 1) :=
      Filter.eventually_of_mem hs fun _ ht ↦ ih ht
    have hpow := (TauCeti.hasDerivAt_ofReal_add u z).const_div_pow (slitPlane_ne_zero h)
      ((-1 : ℂ) ^ m * (m ! : ℂ)) (m + 1)
    rw [iteratedDeriv_succ, hev.deriv_eq, hpow.deriv]
    simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, pow_succ]
    ring

end Complex
