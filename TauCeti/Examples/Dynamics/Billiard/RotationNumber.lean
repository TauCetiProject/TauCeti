/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Dynamics.Billiard.Circle
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse
import Mathlib.NumberTheory.Real.Irrational

/-!
# Strict comparison of rotation numbers and periodic orbits: checks

Checks for `CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_left` and for the
periodic orbits on invariant graphs of the billiard map
(`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.rotationNumber_eq_div_iff`,
`TauCeti.StrictConvexBilliardTable.IsInvariantGraph.iterate_nextCollision_ne_of_irrational`).

* The translations `g₁(x) = x + α` and `g₂(x) = x + α + 1/10`, with `α = √2/2`: `q = 7`, `p = 5`
  is one admissible choice of the `q`, `p` given by `Irrational.exists_int_sub_nat_mul_mem_Ioo`
  for `ε = 1/10`, that is `0 < p - q α < 1/10`, and the translation number of `g₂` is larger
  than `α`.
* On the circular table of radius `R`, the constant graph `v = 0` (angle `δ = π / 2`) has
  rotation number `1/2` and carries a periodic orbit of type `(1, 2)`; the constant graph
  `v = cos (π √2/2)` (angle `δ = π √2/2`) has rotation number `√2/2` and carries no periodic orbit.
-/

public section

noncomputable section

open Real Set

namespace TauCeti.Examples.BilliardRotationNumber

/-- An admissible choice `q = 7`, `p = 5` for `α = √2/2` and `ε = 1/10`: `0 < 5 - 7 α < 1/10`. -/
theorem five_sub_seven_mul_mem_Ioo : (5 : ℝ) - 7 * (√2 / 2) ∈ Ioo 0 (1 / 10) := by
  have h₁ : √2 < 1.4143 := by
    rw [sqrt_lt' (by norm_num)]
    norm_num
  have h₂ : 1.4142 < √2 := by
    rw [lt_sqrt (by norm_num)]
    norm_num
  constructor <;> linarith

/-- Strict comparison at the irrational value `α = √2/2`: the translation by `α + 1/10` has
translation number larger than `α`. -/
theorem translationNumber_lt_translate :
    (√2 / 2 : ℝ) <
      (CircleDeg1Lift.translate (Multiplicative.ofAdd (√2 / 2 + 1 / 10)) :
        CircleDeg1Lift).translationNumber := by
  have h := CircleDeg1Lift.translationNumber_lt_of_forall_lt_of_irrational_left
    (f := (CircleDeg1Lift.translate (Multiplicative.ofAdd (√2 / 2)) : CircleDeg1Lift))
    (g := (CircleDeg1Lift.translate (Multiplicative.ofAdd (√2 / 2 + 1 / 10)) : CircleDeg1Lift))
    (CircleDeg1Lift.continuous_translate _) (CircleDeg1Lift.continuous_translate _)
    (fun x ↦ by simp only [CircleDeg1Lift.translate_apply]; linarith)
    (by
      rw [CircleDeg1Lift.translationNumber_translate]
      exact irrational_sqrt_two.div_natCast two_ne_zero)
  rwa [CircleDeg1Lift.translationNumber_translate] at h

attribute [local instance] Complex.finrank_real_complex_fact

variable {R : ℝ} (hR : 0 < R)

open StrictConvexBilliardTable

/-- The angle `δ = π / 2` of the circular table: the graph `v = 0` has rotation number `1/2` and
carries a periodic orbit of type `(1, 2)`. -/
theorem exists_periodic_circle_zero :
    ∃ s, (circle hR).nextCollision^[2] (s, 0) = (s + (circle hR).period, 0) := by
  have hc : (0 : ℝ) ∈ Ioo (-1) 1 := by norm_num
  have hρ := rotationNumber_circle hR hc
  rw [arccos_zero, div_div_cancel_left₀ pi_ne_zero] at hρ
  obtain ⟨s, hs⟩ := ((isInvariantGraph_circle hR hc).rotationNumber_eq_div_iff contDiff_circle
    (p := 1) (q := 2) two_pos).1 (by rw [hρ]; norm_num)
  exact ⟨s, by simpa using hs⟩

/-- The angle `δ = π √2/2` of the circular table: the graph `v = cos (π √2/2)` has rotation
number `√2/2`, which is irrational, and carries no periodic orbit. -/
theorem iterate_nextCollision_ne_circle_sqrt_two {q : ℕ} (hq : 0 < q) (p : ℤ) (s : ℝ) :
    (circle hR).nextCollision^[q] (s, cos (π * (√2 / 2))) ≠
      (s + p * (circle hR).period, cos (π * (√2 / 2))) := by
  have hα₀ : 0 < √2 / 2 := by positivity
  have hα₁ : √2 / 2 < 1 := by
    rw [div_lt_one two_pos, sqrt_lt' two_pos]
    norm_num
  have hx₀ : 0 < π * (√2 / 2) := mul_pos pi_pos hα₀
  have hx₁ : π * (√2 / 2) < π := mul_lt_of_lt_one_right pi_pos hα₁
  have hc : cos (π * (√2 / 2)) ∈ Ioo (-1) 1 := by
    constructor
    · rw [← cos_pi]
      exact strictAntiOn_cos ⟨hx₀.le, hx₁.le⟩ ⟨pi_pos.le, le_rfl⟩ hx₁
    · rw [← cos_zero]
      exact strictAntiOn_cos ⟨le_rfl, pi_pos.le⟩ ⟨hx₀.le, hx₁.le⟩ hx₀
  refine (isInvariantGraph_circle hR hc).iterate_nextCollision_ne_of_irrational contDiff_circle
    ?_ hq p s
  rw [rotationNumber_circle hR hc, arccos_cos hx₀.le hx₁.le, mul_div_cancel_left₀ _ pi_ne_zero]
  exact irrational_sqrt_two.div_natCast two_ne_zero

end TauCeti.Examples.BilliardRotationNumber
