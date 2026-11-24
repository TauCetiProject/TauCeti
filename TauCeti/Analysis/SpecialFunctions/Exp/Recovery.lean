/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Recovering a function from one of its exponentials

`Real.exp` is a smooth bijection onto `(0, ∞)` whose inverse `Real.log` is smooth there, so for
`c ≠ 0` and any order `n`, a real-valued function `g` is `C^n` within a set at a point exactly
when `t ↦ e^{c g(t)}` is.  Mathlib supplies the easy direction (`ContDiffWithinAt.exp`); the
converse recovers `g` as `c⁻¹ log (e^{c g})`.  This file packages both directions as
equivalences, pointwise and on a set.

The analogous statement for continuity needs no lemma of its own: `t ↦ e^{c t}` is an
embedding, so `Topology.IsInducing.continuousWithinAt_iff` and
`Topology.IsInducing.continuousOn_iff` applied to
`Real.isOpenEmbedding_exp.comp (Homeomorph.mulLeft₀ c hc).isOpenEmbedding` give it.

## Main declarations

* `TauCeti.contDiffWithinAt_exp_const_mul_iff`: for `c ≠ 0`, `t ↦ e^{c g(t)}` is `C^n` within a
  set at a point exactly when `g` is.
* `TauCeti.contDiffOn_exp_const_mul_iff`: the same on a set.
-/

public section

namespace TauCeti

/-- For `c ≠ 0`, the exponential `t ↦ e^{c g(t)}` of a real-valued function is `C^n` within a
set at a point exactly when `g` is. -/
@[simp]
theorem contDiffWithinAt_exp_const_mul_iff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {n : WithTop ℕ∞} {c : ℝ} (hc : c ≠ 0) {g : E → ℝ} {s : Set E} {x : E} :
    ContDiffWithinAt ℝ n (fun t => Real.exp (c * g t)) s x ↔ ContDiffWithinAt ℝ n g s x := by
  refine ⟨fun h => ?_, fun h => (contDiffWithinAt_const.mul h).exp⟩
  have hlog : ContDiffWithinAt ℝ n (fun t => c⁻¹ * Real.log (Real.exp (c * g t))) s x :=
    contDiffWithinAt_const.mul (h.log (Real.exp_pos _).ne')
  exact hlog.congr (fun t _ => by simp only [Real.log_exp, inv_mul_cancel_left₀ hc])
    (by simp only [Real.log_exp, inv_mul_cancel_left₀ hc])

/-- For `c ≠ 0`, the exponential `t ↦ e^{c g(t)}` of a real-valued function is `C^n` on a set
exactly when `g` is. -/
@[simp]
theorem contDiffOn_exp_const_mul_iff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : WithTop ℕ∞} {c : ℝ} (hc : c ≠ 0) {g : E → ℝ} {s : Set E} :
    ContDiffOn ℝ n (fun t => Real.exp (c * g t)) s ↔ ContDiffOn ℝ n g s :=
  forall₂_congr fun _ _ => contDiffWithinAt_exp_const_mul_iff hc

end TauCeti
