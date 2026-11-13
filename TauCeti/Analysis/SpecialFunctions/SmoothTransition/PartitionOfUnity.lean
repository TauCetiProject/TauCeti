/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.SmoothTransition

/-!
# A three-piece smooth partition of unity of the line

For `R ≥ 0`, translates of the smooth transition function `ψ = Real.smoothTransition` split the
constant function `1` on `ℝ` into three smooth pieces `βm + β₀ + βp = 1`. The positive piece
`βp(s) = ψ(s - R)` vanishes on `(-∞, R]` and equals one on `[R + 1, ∞)`, its reflection
`βm(s) = βp(-s)` does the same on the negative side, and the middle piece `β₀ = 1 - βm - βp` is
supported in `(-(R + 1), R + 1)`. All three pieces are bounded by one in absolute value, and
their derivatives are bounded by a common constant and vanish outside `[-(R + 1), R + 1]`.

This is the decomposition that patches estimates on the two ends of a cylinder `ℝ × S¹` with an
estimate on a compact core, the cutoffs contributing only terms supported in the core.

## Main declarations

* `TauCeti.exists_contDiff_partition_of_unity_three` -- the three-piece partition of unity
  subordinate to `(-∞, -R)`, `(-(R + 1), R + 1)` and `(R, ∞)`.
-/

public section

open Set
open scoped ContDiff

namespace TauCeti

/-- **A three-piece smooth partition of unity of the line.** For `R ≥ 0` there are smooth
functions `βm`, `β₀`, `βp` with `βm + β₀ + βp = 1`, each of absolute value at most one, with
derivatives bounded by a common constant `L` and vanishing outside `[-(R + 1), R + 1]`, such that
`βm` vanishes on `[-R, ∞)`, `β₀` outside `(-(R + 1), R + 1)` and `βp` on `(-∞, R]`. -/
theorem exists_contDiff_partition_of_unity_three {R : ℝ} (hR : 0 ≤ R) :
    ∃ L, ∃ βm β₀ βp : ℝ → ℝ, ContDiff ℝ ∞ βm ∧ ContDiff ℝ ∞ β₀ ∧ ContDiff ℝ ∞ βp ∧
      (∀ s, βm s + β₀ s + βp s = 1) ∧
      (∀ s, |βm s| ≤ 1 ∧ |β₀ s| ≤ 1 ∧ |βp s| ≤ 1) ∧
      (∀ s, |deriv βm s| ≤ L ∧ |deriv β₀ s| ≤ L ∧ |deriv βp s| ≤ L) ∧
      (∀ s ∉ Icc (-(R + 1)) (R + 1), deriv βm s = 0 ∧ deriv β₀ s = 0 ∧ deriv βp s = 0) ∧
      (∀ s, -R ≤ s → βm s = 0) ∧ (∀ s ∉ Ioo (-(R + 1)) (R + 1), β₀ s = 0) ∧
      ∀ s ≤ R, βp s = 0 := by
  obtain ⟨L, hL⟩ := Real.smoothTransition.exists_forall_norm_deriv_le
  -- The positive piece `βp(s) = ψ(s - R)`; the negative piece is its reflection.
  set βp : ℝ → ℝ := fun s ↦ Real.smoothTransition (s - R)
  have hβpc : ContDiff ℝ ∞ βp :=
    Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)
  have hβmc : ContDiff ℝ ∞ fun s ↦ βp (-s) := hβpc.comp contDiff_neg
  have hdp (s : ℝ) : deriv βp s = deriv Real.smoothTransition (s - R) := by
    simpa using (((hasDerivAt_id s).sub_const R).smoothTransition).deriv
  have hdm (s : ℝ) : deriv (fun s ↦ βp (-s)) s = -deriv βp (-s) := deriv_comp_neg ..
  have hd₀ (s : ℝ) : deriv (fun s ↦ 1 - βp (-s) - βp s) s = deriv βp (-s) - deriv βp s := by
    rw [(((hasDerivAt_const s (1 : ℝ)).fun_sub (hβmc.differentiable (by simp) s).hasDerivAt).fun_sub
      (hβpc.differentiable (by simp) s).hasDerivAt).deriv, hdm]
    ring
  have hpL (s : ℝ) : |deriv βp s| ≤ L := by rw [hdp, ← Real.norm_eq_abs]; exact hL _
  have hpz (s : ℝ) (hs : s ∉ Icc (-(R + 1)) (R + 1)) : deriv βp s = 0 := by
    rw [hdp]
    rcases not_and_or.1 hs with hs | hs
    · exact Real.smoothTransition.deriv_of_neg (by linarith [not_le.1 hs])
    · exact Real.smoothTransition.deriv_of_one_lt (by linarith [not_le.1 hs])
  have hneg {s : ℝ} (hs : s ∉ Icc (-(R + 1)) (R + 1)) : -s ∉ Icc (-(R + 1)) (R + 1) :=
    fun h ↦ hs ⟨by linarith [h.2], by linarith [h.1]⟩
  have hp0 {s : ℝ} (hs : s ≤ R) : βp s = 0 := Real.smoothTransition.zero_of_nonpos (by linarith)
  have hp1 {s : ℝ} (hs : R + 1 ≤ s) : βp s = 1 :=
    Real.smoothTransition.one_of_one_le (by linarith)
  have hpI (s : ℝ) : 0 ≤ βp s ∧ βp s ≤ 1 :=
    ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩
  refine ⟨2 * L, fun s ↦ βp (-s), fun s ↦ 1 - βp (-s) - βp s, βp, hβmc,
    (contDiff_const.sub hβmc).sub hβpc, hβpc, fun s ↦ by ring,
    fun s ↦ ⟨Real.smoothTransition.abs_le_one _, ?_, Real.smoothTransition.abs_le_one _⟩,
    fun s ↦ ⟨?_, ?_, ?_⟩, fun s hs ↦ ⟨?_, ?_, hpz s hs⟩, fun s hs ↦ hp0 (by linarith),
    fun s hs ↦ ?_, fun s hs ↦ hp0 hs⟩
  · -- At most one of `βp (-s)` and `βp s` is nonzero.
    rw [abs_le]
    rcases le_or_gt s 0 with h | h
    · have := hp0 (h.trans hR)
      constructor <;> linarith [hpI (-s), hpI s]
    · have := hp0 (show -s ≤ R by linarith)
      constructor <;> linarith [hpI (-s), hpI s]
  · rw [hdm, abs_neg]
    linarith [hpL (-s), abs_nonneg (deriv βp (-s))]
  · rw [hd₀, abs_le]
    have h₁ := abs_le.1 (hpL (-s))
    have h₂ := abs_le.1 (hpL s)
    constructor <;> linarith [h₁.1, h₁.2, h₂.1, h₂.2]
  · linarith [hpL s, abs_nonneg (deriv βp s)]
  · rw [hdm, hpz _ (hneg hs), neg_zero]
  · rw [hd₀, hpz _ (hneg hs), hpz s hs, sub_zero]
  · rcases not_and_or.1 hs with hs | hs
    · simp only [hp1 (show R + 1 ≤ -s by linarith [not_lt.1 hs]),
        hp0 (show s ≤ R by linarith [not_lt.1 hs])]
      ring
    · simp only [hp0 (show -s ≤ R by linarith [not_lt.1 hs]), hp1 (not_lt.1 hs)]
      ring

end TauCeti
