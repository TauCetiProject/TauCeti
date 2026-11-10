/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero

/-!
# Scalar-multiplication towers

The composite transitions of the tower `Q ←f Q ←f ⋯` are multiplication by powers of `f`.
Consequently this tower is pro-zero precisely when one power of `f` annihilates all of `Q`.
This uniform bound, unlike elementwise power torsion, makes the tower invisible to inverse
limits and their first derived functor. It applies in particular to cohomological obstruction
modules annihilated by a fixed power of a defining equation.
-/

public section

open CategoryTheory Opposite

universe u v

namespace TauCeti.ModuleTower

variable {R : Type u} [CommRing R]
variable {Q : Type v} [AddCommGroup Q] [Module R Q]

/-- A composite transition in the scalar-multiplication tower is multiplication by the
corresponding power of the scalar. -/
@[simp]
theorem smulTower_transitionOfLE (f : R) {n m : ℕ} (h : n ≤ m) :
    (smulTower Q f).transitionOfLE h = (f ^ (m - n)) • LinearMap.id := by
  induction m, h using Nat.le_induction with
  | base => simp
  | succ m h ih =>
    -- State scalar identities on `Q`, rather than on the carrier of a tower term.
    have key : (f ^ (m - n) • (LinearMap.id : Q →ₗ[R] Q)) ∘ₗ (f • LinearMap.id) =
        f ^ (m + 1 - n) • LinearMap.id := by
      ext x
      simp [Nat.succ_sub h, pow_succ, mul_smul]
    rw [← transitionOfLE_comp_transitionOfLE _ h (Nat.le_succ m), ih,
      transitionOfLE_succ, smulTower_transition]
    exact key

/-- A scalar-multiplication tower is pro-zero exactly when a uniform power of the scalar
annihilates the module. Elementwise power torsion alone is not sufficient. -/
theorem isProZero_smulTower_iff (f : R) :
    (smulTower Q f).IsProZero ↔ ∃ k : ℕ, ∀ x : Q, f ^ k • x = 0 := by
  rw [isProZero_iff_exists_transitionOfLE_eq_zero]
  constructor
  · intro h
    obtain ⟨k, _, hk⟩ := h 0
    -- The tower's terms are `Q`; use this typed identity to evaluate the linear map.
    have hk' : f ^ k • (LinearMap.id : Q →ₗ[R] Q) = 0 := by
      rw [smulTower_transitionOfLE, Nat.sub_zero] at hk
      exact hk
    exact ⟨k, fun x ↦ by simpa using LinearMap.congr_fun hk' x⟩
  · rintro ⟨k, hk⟩ n
    refine ⟨n + k, Nat.le_add_right _ _, ?_⟩
    have hk' : f ^ k • (LinearMap.id : Q →ₗ[R] Q) = 0 := by
      ext x
      simpa using hk x
    rw [smulTower_transitionOfLE, Nat.add_sub_cancel_left]
    exact hk'

end TauCeti.ModuleTower
