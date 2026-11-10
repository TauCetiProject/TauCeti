/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Torsion.Field
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Commuting endomorphisms with the cubics `N³ = 4 N` and `P³ = -4 P`

Let `N`, `P` be commuting endomorphisms of a vector space over a field of characteristic other
than two, with `N³ = 4 N` and `P³ = -4 P`. Then a vector killed by some power of `N + P` is
killed by `N` and by `P`: the generalized kernel of `N + P` is the joint kernel of `N` and `P`.

These are the cubics satisfied by `ad x` and `ad y` for `x * x = 1` and `y * y = -1` in an
associative algebra (`LieAlgebra.ad_pow_three_eq_smul_ad`), which is how the Engel subalgebra of
`x + y` is computed in `LieSubalgebra.lie_eq_zero_and_lie_eq_zero_of_mem_engel_add`.

## Main results

* `Module.End.apply_eq_zero_and_apply_eq_zero_of_pow_add_apply_eq_zero`: for commuting `N`, `P`
  with `N³ = 4 N` and `P³ = -4 P`, every vector killed by a power of `N + P` is killed by `N` and
  by `P`.
-/

public section

namespace Module.End

variable {R M : Type*} [Field R] [NeZero (2 : R)] [AddCommGroup M] [Module R M]
  {N P : Module.End R M}

/-- For commuting endomorphisms `N`, `P` with `N³ = 4 N` and `P³ = -4 P`, if `N` and `P` both kill
`u = N w + P w`, then they both kill `w`. -/
private theorem eq_zero_of_apply_add_apply_eq_zero (hN : N ^ 3 = (4 : R) • N)
    (hP : P ^ 3 = -((4 : R) • P)) (hNP : Commute N P) {w : M} (h₁ : N (N w + P w) = 0)
    (h₂ : P (N w + P w) = 0) : N w = 0 ∧ P w = 0 := by
  have comm : ∀ u, N (P u) = P (N u) := fun u ↦ by
    simpa only [mul_apply_eq_comp] using LinearMap.congr_fun hNP.eq u
  have hN3 : ∀ u, N (N (N u)) = (4 : R) • N u := fun u ↦ by
    simpa only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp, LinearMap.smul_apply] using
      LinearMap.congr_fun hN u
  have hP3 : ∀ u, P (P (P u)) = -((4 : R) • P u) := fun u ↦ by
    simpa only [pow_succ, pow_zero, one_mul, mul_apply_eq_comp, LinearMap.smul_apply,
      LinearMap.neg_apply] using LinearMap.congr_fun hP u
  have h4 : (4 : R) ≠ 0 := by
    rw [show (4 : R) = 2 * 2 by norm_num]
    exact mul_ne_zero two_ne_zero two_ne_zero
  rw [map_add] at h₁ h₂
  have e₁ := congrArg N h₁
  rw [map_add, map_zero] at e₁
  -- `P (P w) = -N (P w)`, so `P³ w = N (N (P w)) = -N³ w`; with the two cubics, `P w = N w`.
  have hPP : P (P w) = -N (P w) := by
    rw [← comm] at h₂
    linear_combination (norm := module) h₂
  have hP3' : P (P (P w)) = -N (N (N w)) := by
    rw [hPP, map_neg, ← comm, hPP, map_neg, neg_neg]
    linear_combination (norm := module) e₁
  have hPN : (4 : R) • (P w - N w) = 0 := by
    linear_combination (norm := module) hP3 w - hP3' + hN3 w
  have hPN' : P w = N w := sub_eq_zero.1 ((smul_eq_zero.1 hPN).resolve_left h4)
  -- Then `N (N w) = 0`, so `4 N w = N³ w = 0`.
  have hNN : (2 : R) • N (N w) = 0 := by
    rw [hPN'] at h₁
    linear_combination (norm := module) h₁
  have hNN' : N (N w) = 0 := (smul_eq_zero.1 hNN).resolve_left two_ne_zero
  have hNw : (4 : R) • N w = 0 := by rw [← hN3, hNN', map_zero]
  have hNw' : N w = 0 := (smul_eq_zero.1 hNw).resolve_left h4
  exact ⟨hNw', hPN'.trans hNw'⟩

/-- For commuting endomorphisms `N`, `P` with `N³ = 4 N` and `P³ = -4 P`, every vector killed by a
power of `N + P` is killed by `N` and by `P`. -/
theorem apply_eq_zero_and_apply_eq_zero_of_pow_add_apply_eq_zero (hN : N ^ 3 = (4 : R) • N)
    (hP : P ^ 3 = -((4 : R) • P)) (hNP : Commute N P) (n : ℕ) {w : M}
    (hw : ((N + P) ^ n) w = 0) : N w = 0 ∧ P w = 0 := by
  induction n generalizing w with
  | zero =>
    rw [pow_zero, one_apply_eq_self] at hw
    simp [hw]
  | succ n ih =>
    rw [pow_succ, mul_apply_eq_comp] at hw
    obtain ⟨h₁, h₂⟩ := ih hw
    rw [LinearMap.add_apply] at h₁ h₂
    exact eq_zero_of_apply_add_apply_eq_zero hN hP hNP h₁ h₂

end Module.End
