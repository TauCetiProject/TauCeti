/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Frequency cutoffs

A *frequency cutoff* on a real normed space `E` is a smooth function `χ : E → ℝ` with values in
`[0, 1]` that vanishes on the closed unit ball `‖ξ‖ ≤ 1` and equals `1` for `‖ξ‖ ≥ 2`.

Classical symbols `a ∼ ∑ⱼ χ(ξ) aₘ₋ⱼ(x, ξ)` use such a cutoff to turn the homogeneous terms
`aₘ₋ⱼ`, which are only smooth away from `ξ = 0`, into smooth functions on the whole frequency
space. This file provides the carrier `TauCeti.FrequencyCutoff E` and the facts about it that
the symbol calculus needs:

* `FrequencyCutoff.ofContDiffBump`: `1 - f` is a frequency cutoff for a smooth bump `f` with
  `1 ≤ f.rIn` and `f.rOut ≤ 2`, so frequency cutoffs exist whenever `E` has smooth bump functions
  (for instance in every inner product space and every finite-dimensional space);
* every iterated derivative of a cutoff vanishes on the closed unit ball, and every iterated
  derivative of positive order also vanishes for `‖ξ‖ ≥ 2`, so it is supported in the closed
  annulus `1 ≤ ‖ξ‖ ≤ 2`;
* on a proper space every iterated derivative of a cutoff is bounded, and the difference of two
  cutoffs, as well as `1 - χ`, has compact support.

## References

* M. Taylor, *Pseudodifferential Operators: Four Lectures at MSRI* (2008), Lecture I, (1.17).
* L. Hörmander, *The Analysis of Linear Partial Differential Operators III*, §18.1.
-/

public section

open Metric Filter Set
open scoped ContDiff Topology

namespace TauCeti

/-- A frequency cutoff on `E`: a smooth function with values in `[0, 1]` that vanishes on the
closed unit ball and equals `1` outside the open ball of radius `2`. -/
structure FrequencyCutoff (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] where
  /-- The underlying function. Use the coercion to a function instead. -/
  toFun : E → ℝ
  contDiff' : ContDiff ℝ ∞ toFun
  eq_zero_of_norm_le_one' : ∀ ξ, ‖ξ‖ ≤ 1 → toFun ξ = 0
  eq_one_of_two_le_norm' : ∀ ξ, 2 ≤ ‖ξ‖ → toFun ξ = 1
  nonneg' : ∀ ξ, 0 ≤ toFun ξ
  le_one' : ∀ ξ, toFun ξ ≤ 1

namespace FrequencyCutoff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

instance : FunLike (FrequencyCutoff E) E ℝ where
  coe := toFun
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; congr

@[simp]
theorem toFun_eq_coe (χ : FrequencyCutoff E) : χ.toFun = χ :=
  rfl

@[ext]
theorem ext {χ₁ χ₂ : FrequencyCutoff E} (h : ∀ ξ, χ₁ ξ = χ₂ ξ) : χ₁ = χ₂ :=
  DFunLike.ext _ _ h

variable (χ : FrequencyCutoff E)

theorem contDiff {n : ℕ∞} : ContDiff ℝ n χ :=
  χ.contDiff'.of_le (mod_cast le_top)

theorem continuous : Continuous χ :=
  (χ.contDiff (n := 0)).continuous

theorem apply_eq_zero_of_norm_le_one {ξ : E} (hξ : ‖ξ‖ ≤ 1) : χ ξ = 0 :=
  χ.eq_zero_of_norm_le_one' ξ hξ

theorem apply_eq_one_of_two_le_norm {ξ : E} (hξ : 2 ≤ ‖ξ‖) : χ ξ = 1 :=
  χ.eq_one_of_two_le_norm' ξ hξ

@[simp]
theorem apply_zero : χ 0 = 0 :=
  χ.apply_eq_zero_of_norm_le_one (by simp)

theorem nonneg (ξ : E) : 0 ≤ χ ξ :=
  χ.nonneg' ξ

theorem le_one (ξ : E) : χ ξ ≤ 1 :=
  χ.le_one' ξ

theorem norm_le_one (ξ : E) : ‖χ ξ‖ ≤ 1 := by
  rw [Real.norm_of_nonneg (χ.nonneg ξ)]
  exact χ.le_one ξ

/-- A frequency cutoff vanishes near every point of the open unit ball. -/
theorem eventuallyEq_zero_of_norm_lt_one {ξ : E} (hξ : ‖ξ‖ < 1) : (χ : E → ℝ) =ᶠ[𝓝 ξ] 0 := by
  filter_upwards [isOpen_ball.mem_nhds (mem_ball_zero_iff.2 hξ)] with η hη
  exact χ.apply_eq_zero_of_norm_le_one (mem_ball_zero_iff.1 hη).le

/-- A frequency cutoff equals `1` near every point outside the closed ball of radius `2`. -/
theorem eventuallyEq_one_of_two_lt_norm {ξ : E} (hξ : 2 < ‖ξ‖) : (χ : E → ℝ) =ᶠ[𝓝 ξ] 1 := by
  have : (closedBall (0 : E) 2)ᶜ ∈ 𝓝 ξ :=
    isClosed_closedBall.isOpen_compl.mem_nhds (by simpa using hξ)
  filter_upwards [this] with η hη
  exact χ.apply_eq_one_of_two_le_norm (by simpa using hη : 2 < ‖η‖).le

/-- Every iterated derivative of a frequency cutoff, including its value, vanishes on the closed
unit ball. -/
theorem iteratedFDeriv_eq_zero_of_norm_le_one (k : ℕ) {ξ : E} (hξ : ‖ξ‖ ≤ 1) :
    iteratedFDeriv ℝ k χ ξ = 0 := by
  have hon : EqOn (iteratedFDeriv ℝ k χ) 0 (ball 0 1) := fun η hη ↦ by
    simpa using ((χ.eventuallyEq_zero_of_norm_lt_one (mem_ball_zero_iff.1 hη)).iteratedFDeriv
      ℝ k).eq_of_nhds
  have hcl := hon.closure (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top))
    continuous_const
  rw [closure_ball _ one_ne_zero] at hcl
  exact hcl (mem_closedBall_zero_iff.2 hξ)

/-- Every iterated derivative of positive order of a frequency cutoff vanishes for `‖ξ‖ ≥ 2`. -/
theorem iteratedFDeriv_eq_zero_of_two_le_norm {k : ℕ} (hk : k ≠ 0) {ξ : E} (hξ : 2 ≤ ‖ξ‖) :
    iteratedFDeriv ℝ k χ ξ = 0 := by
  have hon : EqOn (iteratedFDeriv ℝ k χ) 0 (closedBall 0 2)ᶜ := fun η hη ↦ by
    have h := ((χ.eventuallyEq_one_of_two_lt_norm (by simpa using hη)).iteratedFDeriv
      ℝ k).eq_of_nhds
    rw [h]
    exact congrFun (iteratedFDeriv_const_of_ne hk 1) η
  have hcl := hon.closure (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top))
    continuous_const
  rw [closure_compl, interior_closedBall _ two_ne_zero] at hcl
  exact hcl (by simpa using hξ)

/-- The iterated derivatives of positive order of a frequency cutoff are supported in the closed
annulus `1 ≤ ‖ξ‖ ≤ 2`. -/
theorem support_iteratedFDeriv_subset {k : ℕ} (hk : k ≠ 0) :
    Function.support (iteratedFDeriv ℝ k χ) ⊆ {ξ | 1 ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ 2} := by
  intro ξ hξ
  by_contra h
  rcases not_and_or.1 h with h | h
  · exact hξ (χ.iteratedFDeriv_eq_zero_of_norm_le_one k (not_le.1 h).le)
  · exact hξ (χ.iteratedFDeriv_eq_zero_of_two_le_norm hk (not_le.1 h).le)

/-- The function `1 - χ` is supported in the closed ball of radius `2`, hence compactly supported
in a proper space. -/
theorem hasCompactSupport_one_sub [ProperSpace E] : HasCompactSupport (1 - ⇑χ) :=
  HasCompactSupport.intro (isCompact_closedBall 0 2) fun ξ hξ ↦ by
    simp [χ.apply_eq_one_of_two_le_norm (by simpa using hξ : 2 < ‖ξ‖).le]

/-- Two frequency cutoffs agree outside the open ball of radius `2`, so their difference is
compactly supported in a proper space. -/
theorem hasCompactSupport_sub [ProperSpace E] (χ' : FrequencyCutoff E) :
    HasCompactSupport (⇑χ - ⇑χ') :=
  HasCompactSupport.intro (isCompact_closedBall 0 2) fun ξ hξ ↦ by
    have hξ : 2 ≤ ‖ξ‖ := (by simpa using hξ : 2 < ‖ξ‖).le
    simp [χ.apply_eq_one_of_two_le_norm hξ, χ'.apply_eq_one_of_two_le_norm hξ]

/-- Every iterated derivative of a frequency cutoff on a proper space is bounded. -/
theorem exists_bound_iteratedFDeriv [ProperSpace E] (k : ℕ) :
    ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ C := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact ⟨1, fun ξ ↦ by simpa using χ.norm_le_one ξ⟩
  refine (χ.contDiff.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
    (HasCompactSupport.intro (isCompact_closedBall 0 2) fun ξ hξ ↦ ?_)
  exact χ.iteratedFDeriv_eq_zero_of_two_le_norm hk (by simpa using hξ : 2 < ‖ξ‖).le

/-- If `f` is a smooth bump function centred at `0` with `1 ≤ f.rIn` and `f.rOut ≤ 2`, then
`1 - f` is a frequency cutoff. -/
noncomputable def ofContDiffBump [HasContDiffBump E] (f : ContDiffBump (0 : E))
    (h₁ : 1 ≤ f.rIn) (h₂ : f.rOut ≤ 2) : FrequencyCutoff E where
  toFun ξ := 1 - f ξ
  contDiff' := contDiff_const.sub f.contDiff
  eq_zero_of_norm_le_one' ξ hξ := by
    rw [f.one_of_mem_closedBall (mem_closedBall_zero_iff.2 (hξ.trans h₁)), sub_self]
  eq_one_of_two_le_norm' ξ hξ := by
    rw [f.zero_of_le_dist (by simpa using h₂.trans hξ), sub_zero]
  nonneg' _ := sub_nonneg.2 f.le_one
  le_one' _ := sub_le_self _ f.nonneg

@[simp]
theorem ofContDiffBump_apply [HasContDiffBump E] (f : ContDiffBump (0 : E)) (h₁ : 1 ≤ f.rIn)
    (h₂ : f.rOut ≤ 2) (ξ : E) : ofContDiffBump f h₁ h₂ ξ = 1 - f ξ :=
  (rfl)

/-- Frequency cutoffs exist on every space with smooth bump functions. -/
noncomputable instance [HasContDiffBump E] : Inhabited (FrequencyCutoff E) :=
  ⟨ofContDiffBump ⟨1, 2, one_pos, one_lt_two⟩ le_rfl le_rfl⟩

end FrequencyCutoff

end TauCeti
