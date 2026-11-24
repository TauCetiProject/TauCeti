/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import TauCeti.Analysis.Complex.IteratedDeriv

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
  have hU : IsOpen {w : ℂ | w + z ∈ slitPlane} :=
    isOpen_slitPlane.preimage (continuous_id.add continuous_const)
  have hf : DifferentiableOn ℂ (fun w : ℂ ↦ log (w + z)) {w : ℂ | w + z ∈ slitPlane} :=
    fun w hw ↦ ((hasDerivAt_log hw).comp_add_const w z).differentiableAt.differentiableWithinAt
  simp only [hf.iteratedDeriv_comp_ofReal hU (m + 1) h, iteratedDeriv_comp_add_const,
    _root_.iteratedDeriv_succ_log h, Nat.add_sub_cancel]
  have hexp : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
  rw [hexp, zpow_neg, zpow_natCast, div_eq_mul_inv]

end Complex
