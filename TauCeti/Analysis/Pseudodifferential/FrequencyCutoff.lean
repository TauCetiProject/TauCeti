/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import TauCeti.Analysis.Calculus.CoordinateDeriv
import TauCeti.Analysis.SpecialFunctions.Pow.Bounds
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
  cutoffs, as well as `1 - χ`, has compact support;
* on `ℝⁿ`, the rescaled cutoff `(x, ξ) ↦ χ(ξ / R)` on phase space is smooth
  (`FrequencyCutoff.contDiff_comp_inv_smul_snd`), multiplying by it gives a function vanishing
  near `‖ξ / R‖ < 1` (`FrequencyCutoff.comp_inv_smul_snd_smul_eventuallyEq_zero`), and it
  satisfies the symbol estimates of order `0`
  (`FrequencyCutoff.exists_bound_mixedDeriv_comp_inv_smul_snd`), for every radius `R`.

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

@[simp]
theorem coe_mk (f : E → ℝ) (h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : FrequencyCutoff E) = f :=
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

/-! ### The rescaled cutoff on phase space -/

section Rescaled

variable {n : ℕ} (χ : FrequencyCutoff (CoordinateSpace n)) (R : ℝ)

/-- The rescaled cutoff `(x, ξ) ↦ χ(ξ / R)` on phase space is smooth. -/
theorem contDiff_comp_inv_smul_snd :
    ContDiff ℝ ∞ fun p : CoordinateSpace n × CoordinateSpace n => χ (R⁻¹ • p.2) :=
  χ.contDiff.comp (contDiff_snd.const_smul R⁻¹)

/-- A function on phase space multiplied by the rescaled cutoff `χ(ξ / R)` vanishes near every
point with `‖ξ / R‖ < 1`. -/
theorem comp_inv_smul_snd_smul_eventuallyEq_zero {A : Type*} [NormedAddCommGroup A]
    [NormedSpace ℝ A] (f : CoordinateSpace n × CoordinateSpace n → A)
    {p : CoordinateSpace n × CoordinateSpace n} (hp : ‖R⁻¹ • p.2‖ < 1) :
    (fun q => χ (R⁻¹ • q.2) • f q) =ᶠ[𝓝 p] 0 := by
  have hc : Continuous fun q : CoordinateSpace n × CoordinateSpace n => R⁻¹ • q.2 :=
    continuous_snd.const_smul R⁻¹
  filter_upwards [(χ.eventuallyEq_zero_of_norm_lt_one hp).comp_tendsto hc.continuousAt]
    with q hq
  simp only [Function.comp_apply, Pi.zero_apply] at hq
  simp [hq]

/-- If `k = 0` or `‖ξ / R‖ < 2`, then `|R⁻¹|^k ≤ |R⁻¹|^k ⟨2R⟩^k ⟨ξ⟩^(-k)`: below the radius
`2 |R|` the weight `⟨ξ⟩^(-k)` is bounded below by `⟨2R⟩^(-k)`, and for `R = 0` both sides vanish. -/
private theorem abs_inv_pow_le_mul_weight {R : ℝ} {k : ℕ} {ξ : CoordinateSpace n}
    (h : k = 0 ∨ ‖R⁻¹ • ξ‖ < 2) : |R⁻¹| ^ k ≤ |R⁻¹| ^ k *
      ((1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - k) / 2)) := by
  rcases eq_or_ne k 0 with hk | hk
  · simp [hk]
  rcases eq_or_ne R 0 with hR | hR
  · simp [hR, zero_pow hk]
  refine le_mul_of_one_le_right (by positivity) ?_
  have hlt := h.resolve_left hk
  rw [norm_smul, norm_inv, Real.norm_eq_abs] at hlt
  have hξ : ‖ξ‖ < 2 * |R| := by
    have := (inv_mul_lt_iff₀ (abs_pos.2 hR)).1 hlt
    linarith
  have hw := one_add_sq_rpow_neg_abs_le_one_add_norm_sq_rpow hξ.le ((0 : ℝ) - k)
  rw [zero_sub, abs_neg, Nat.abs_cast, mul_pow, sq_abs, ← zero_sub] at hw
  norm_num only at hw
  calc (1 : ℝ) = (1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) * (1 + 4 * R ^ 2) ^ (((0 : ℝ) - k) / 2) := by
        rw [← Real.rpow_add (by positivity), show (k : ℝ) / 2 + (0 - k) / 2 = 0 by ring,
          Real.rpow_zero]
    _ ≤ _ := mul_le_mul_of_nonneg_left hw (by positivity)

/-- The rescaled cutoff `(x, ξ) ↦ χ(ξ / R)` satisfies the symbol estimates of order `0`: every
mixed derivative `∂_x^α ∂_ξ^β` is bounded by a multiple of `⟨ξ⟩^(-|β|)`. -/
theorem exists_bound_mixedDeriv_comp_inv_smul_snd (α β : List (Fin n)) :
    ∃ C, ∀ x ξ : CoordinateSpace n,
      ‖mixedDeriv α β (fun p : CoordinateSpace n × CoordinateSpace n => χ (R⁻¹ • p.2)) x ξ‖ ≤
        C * (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - β.length) / 2) := by
  rcases eq_or_ne α [] with rfl | hα
  swap
  · refine ⟨0, fun x ξ => ?_⟩
    simp only [mixedDeriv_def]
    rw [coordinateDeriv_const _ hα]
    simp
  obtain ⟨B, hB⟩ := χ.exists_bound_iteratedFDeriv β.length
  have hval : ∀ x ξ, ‖mixedDeriv [] β (fun p : CoordinateSpace n × CoordinateSpace n =>
      χ (R⁻¹ • p.2)) x ξ‖ ≤ |R⁻¹| ^ β.length * ‖iteratedFDeriv ℝ β.length χ (R⁻¹ • ξ)‖ := by
    intro x ξ
    have hk : ContDiff ℝ β.length χ := χ.contDiff.of_le (by exact_mod_cast le_top)
    have hk' : ContDiff ℝ β.length fun z => χ (R⁻¹ • z) := hk.comp (contDiff_const_smul R⁻¹)
    simp only [mixedDeriv_def, coordinateDeriv_nil]
    refine (norm_coordinateDeriv_le β hk' ξ).trans ?_
    rw [iteratedFDeriv_comp_const_smul R⁻¹ hk, norm_smul, norm_pow, Real.norm_eq_abs]
  set k := β.length
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  refine ⟨|R⁻¹| ^ k * B * (1 + 4 * R ^ 2) ^ ((k : ℝ) / 2), fun x ξ => (hval x ξ).trans ?_⟩
  by_cases hz : k ≠ 0 ∧ 2 ≤ ‖R⁻¹ • ξ‖
  · rw [χ.iteratedFDeriv_eq_zero_of_two_le_norm hz.1 hz.2, norm_zero, mul_zero]
    positivity
  have key := abs_inv_pow_le_mul_weight ((not_and_or.1 hz).imp not_not.1 not_le.1)
  calc |R⁻¹| ^ k * ‖iteratedFDeriv ℝ k χ (R⁻¹ • ξ)‖ ≤ |R⁻¹| ^ k * B :=
        mul_le_mul_of_nonneg_left (hB _) (by positivity)
    _ ≤ |R⁻¹| ^ k * ((1 + 4 * R ^ 2) ^ ((k : ℝ) / 2) *
          (1 + ‖ξ‖ ^ 2) ^ (((0 : ℝ) - k) / 2)) * B := mul_le_mul_of_nonneg_right key hB0
    _ = _ := by ring

end Rescaled

end FrequencyCutoff

end TauCeti
