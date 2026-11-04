/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Frequency cutoffs

A frequency cutoff on a real normed space `E` is a smooth function `χ : E → ℝ` with values in
`[0, 1]` that vanishes on the closed unit ball and is identically `1` outside the open ball of
radius `2`. In the classical symbol calculus a homogeneous term `a(x, ξ)`, which is smooth only
away from `ξ = 0`, is turned into a globally smooth symbol `χ(ξ) a(x, ξ)`; the cutoff removes the
singularity at the zero frequency without changing `a` at large frequencies.

Cutoffs exist on every space with smooth bump functions: `1 - φ` is one, for a bump `φ` that
is `1` on the unit ball and supported in the ball of radius `2`. Their derivatives of positive
order vanish outside the transition annulus `1 ≤ ‖ξ‖ ≤ 2`, so on a proper space they have compact
support and every derivative is bounded. Two cutoffs agree outside the ball of radius `2`, so
their difference is compactly supported.

## Main declarations

* `TauCeti.FrequencyCutoff E`: the frequency cutoffs on `E`.
* `TauCeti.FrequencyCutoff.ofContDiffBump`: the cutoff `1 - φ` built from a smooth bump `φ`.
* `TauCeti.FrequencyCutoff.iteratedFDeriv_eq_zero_of_norm_lt_one`,
  `TauCeti.FrequencyCutoff.iteratedFDeriv_eq_zero_of_two_lt_norm`: derivatives of positive order
  vanish off the transition annulus.
* `TauCeti.FrequencyCutoff.exists_norm_iteratedFDeriv_le`: every derivative is bounded.
* `TauCeti.FrequencyCutoff.hasCompactSupport_sub`: two cutoffs differ by a compactly supported
  function.

## References

* M. E. Taylor, *Pseudodifferential Operators*, Lecture I, (1.17).
* R. B. Melrose, *Introduction to Microlocal Analysis*, Chapter 2.
-/

public section

noncomputable section

open Filter Metric Set
open scoped ContDiff Topology

namespace TauCeti

variable (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A frequency cutoff on `E`: a smooth function with values in `[0, 1]` which vanishes for
`‖ξ‖ ≤ 1` and equals `1` for `2 ≤ ‖ξ‖`. -/
structure FrequencyCutoff where
  /-- The underlying function. Use the coercion to functions instead. -/
  toFun : E → ℝ
  /-- A cutoff is smooth. -/
  contDiff' : ContDiff ℝ ∞ toFun
  /-- A cutoff vanishes on the closed unit ball. -/
  eq_zero_of_norm_le_one' : ∀ ξ, ‖ξ‖ ≤ 1 → toFun ξ = 0
  /-- A cutoff equals `1` outside the open ball of radius `2`. -/
  eq_one_of_two_le_norm' : ∀ ξ, 2 ≤ ‖ξ‖ → toFun ξ = 1
  /-- A cutoff is nonnegative. -/
  nonneg' : ∀ ξ, 0 ≤ toFun ξ
  /-- A cutoff is at most `1`. -/
  le_one' : ∀ ξ, toFun ξ ≤ 1

namespace FrequencyCutoff

variable {E}

instance : FunLike (FrequencyCutoff E) E ℝ where
  coe := toFun
  coe_injective χ₁ χ₂ h := by cases χ₁; cases χ₂; congr

@[ext]
theorem ext {χ₁ χ₂ : FrequencyCutoff E} (h : ∀ ξ, χ₁ ξ = χ₂ ξ) : χ₁ = χ₂ :=
  DFunLike.ext _ _ h

@[simp]
theorem toFun_eq_coe (χ : FrequencyCutoff E) : χ.toFun = χ := (rfl)

@[simp]
theorem coe_mk (f : E → ℝ) (h₁ h₂ h₃ h₄ h₅) :
    ⇑(⟨f, h₁, h₂, h₃, h₄, h₅⟩ : FrequencyCutoff E) = f :=
  (rfl)

variable (χ : FrequencyCutoff E) {ξ : E}

theorem contDiff {n : ℕ∞} : ContDiff ℝ n χ :=
  χ.contDiff'.of_le (mod_cast le_top)

theorem continuous : Continuous χ :=
  χ.contDiff'.continuous

theorem apply_eq_zero (hξ : ‖ξ‖ ≤ 1) : χ ξ = 0 :=
  χ.eq_zero_of_norm_le_one' ξ hξ

theorem apply_eq_one (hξ : 2 ≤ ‖ξ‖) : χ ξ = 1 :=
  χ.eq_one_of_two_le_norm' ξ hξ

theorem nonneg (ξ : E) : 0 ≤ χ ξ :=
  χ.nonneg' ξ

theorem le_one (ξ : E) : χ ξ ≤ 1 :=
  χ.le_one' ξ

@[simp]
theorem apply_zero : χ 0 = 0 :=
  χ.apply_eq_zero (by simp)

/-- A cutoff vanishes near every frequency of norm less than `1`. -/
theorem eventuallyEq_zero (hξ : ‖ξ‖ < 1) : χ =ᶠ[𝓝 ξ] 0 := by
  filter_upwards [isOpen_lt continuous_norm continuous_const |>.mem_nhds hξ] with η hη
  exact χ.apply_eq_zero hη.le

/-- A cutoff equals `1` near every frequency of norm greater than `2`. -/
theorem eventuallyEq_one (hξ : 2 < ‖ξ‖) : χ =ᶠ[𝓝 ξ] 1 := by
  filter_upwards [isOpen_lt continuous_const continuous_norm |>.mem_nhds hξ] with η hη
  exact χ.apply_eq_one hη.le

/-- The derivatives of positive order of a cutoff vanish inside the unit ball. -/
theorem iteratedFDeriv_eq_zero_of_norm_lt_one {k : ℕ} (hξ : ‖ξ‖ < 1) :
    iteratedFDeriv ℝ k χ ξ = 0 := by
  rw [(χ.eventuallyEq_zero hξ).iteratedFDeriv ℝ k |>.eq_of_nhds, iteratedFDeriv_zero,
    Pi.zero_apply]

/-- The derivatives of positive order of a cutoff vanish outside the closed ball of radius `2`. -/
theorem iteratedFDeriv_eq_zero_of_two_lt_norm {k : ℕ} (hk : k ≠ 0) (hξ : 2 < ‖ξ‖) :
    iteratedFDeriv ℝ k χ ξ = 0 := by
  rw [(χ.eventuallyEq_one hξ).iteratedFDeriv ℝ k |>.eq_of_nhds]
  exact congr_fun (iteratedFDeriv_const_of_ne hk (1 : ℝ)) ξ

/-- A derivative of positive order of a cutoff is supported in the closed ball of radius `2`. -/
theorem hasCompactSupport_iteratedFDeriv [ProperSpace E] {k : ℕ} (hk : k ≠ 0) :
    HasCompactSupport (iteratedFDeriv ℝ k χ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) 2) fun ξ hξ =>
    χ.iteratedFDeriv_eq_zero_of_two_lt_norm hk (by simpa using hξ)

/-- Every derivative of a cutoff is bounded. -/
theorem exists_norm_iteratedFDeriv_le [ProperSpace E] (k : ℕ) :
    ∃ C, ∀ ξ, ‖iteratedFDeriv ℝ k χ ξ‖ ≤ C := by
  rcases eq_or_ne k 0 with rfl | hk
  · refine ⟨1, fun ξ => ?_⟩
    rw [norm_iteratedFDeriv_zero, Real.norm_of_nonneg (χ.nonneg ξ)]
    exact χ.le_one ξ
  · exact (χ.contDiff'.continuous_iteratedFDeriv (mod_cast le_top)).bounded_above_of_compact_support
      (χ.hasCompactSupport_iteratedFDeriv hk)

/-- The function `1 - χ` is supported in the closed ball of radius `2`. -/
theorem hasCompactSupport_one_sub [ProperSpace E] : HasCompactSupport (1 - ⇑χ) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) 2) fun ξ hξ => by
    simp [χ.apply_eq_one (by simpa using hξ : 2 < ‖ξ‖).le]

/-- Two cutoffs differ by a compactly supported function. -/
theorem hasCompactSupport_sub [ProperSpace E] (χ₁ χ₂ : FrequencyCutoff E) :
    HasCompactSupport (⇑χ₁ - ⇑χ₂) :=
  HasCompactSupport.intro (isCompact_closedBall (0 : E) 2) fun ξ hξ => by
    have hξ : 2 ≤ ‖ξ‖ := (by simpa using hξ : 2 < ‖ξ‖).le
    simp [χ₁.apply_eq_one hξ, χ₂.apply_eq_one hξ]

section ContDiffBump

variable [HasContDiffBump E]

/-- The frequency cutoff `1 - φ` built from a smooth bump function `φ` centered at `0` which is
`1` on the closed unit ball and supported in the open ball of radius `2`. -/
def ofContDiffBump (φ : ContDiffBump (0 : E)) (hφ₁ : φ.rIn = 1) (hφ₂ : φ.rOut = 2) :
    FrequencyCutoff E where
  toFun ξ := 1 - φ ξ
  contDiff' := contDiff_const.sub φ.contDiff
  eq_zero_of_norm_le_one' ξ hξ := by
    rw [φ.one_of_mem_closedBall (by simpa [hφ₁] using hξ), sub_self]
  eq_one_of_two_le_norm' ξ hξ := by
    rw [φ.zero_of_le_dist (by simpa [hφ₂] using hξ), sub_zero]
  nonneg' ξ := sub_nonneg.mpr φ.le_one
  le_one' ξ := sub_le_self _ φ.nonneg

@[simp]
theorem ofContDiffBump_apply (φ : ContDiffBump (0 : E)) (hφ₁ : φ.rIn = 1) (hφ₂ : φ.rOut = 2)
    (ξ : E) : ofContDiffBump φ hφ₁ hφ₂ ξ = 1 - φ ξ := (rfl)

/-- Every space with smooth bump functions carries a frequency cutoff. -/
instance : Inhabited (FrequencyCutoff E) :=
  ⟨ofContDiffBump ⟨1, 2, one_pos, one_lt_two⟩ rfl rfl⟩

end ContDiffBump

end FrequencyCutoff

end TauCeti
