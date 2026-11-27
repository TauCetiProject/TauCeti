/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Semiconj.Defs
import Mathlib.Tactic.Group

/-!
# Iterated semiconjugation onto a power

If `F * T ^ q = T * F` in a monoid (so `F` conjugates `T ^ q` to `T` when `F` is invertible), then
iterating gives `F ^ k * T ^ q ^ k = T * F ^ k`. In a group with `F = φ⁻¹` this is the familiar
consequence `φ ^ k τ φ⁻ᵏ = τ ^ q ^ k` of the relation `φ τ φ⁻¹ = τ ^ q` between a Frobenius
element and a tame inertia generator.

## Main results

* `SemiconjBy.pow_left_pow_pow`: if `F` semiconjugates `T ^ q` to `T`, then `F ^ k`
  semiconjugates `T ^ q ^ k` to `T`.
* `MonoidHom.semiconjBy_map_inv_of_map_conj_eq_pow`: if `u (φ τ φ⁻¹) = u τ ^ q` for a monoid
  hom `u` out of a group, then `u φ⁻¹` semiconjugates `u τ ^ q` to `u τ`.
-/

public section

/-- **Iterated semiconjugation onto a power.** If `F * T ^ q = T * F`, then
`F ^ k * T ^ q ^ k = T * F ^ k` for every `k`. -/
theorem SemiconjBy.pow_left_pow_pow {M : Type*} [Monoid M] {T F : M} {q : ℕ}
    (h : SemiconjBy F (T ^ q) T) (k : ℕ) : SemiconjBy (F ^ k) (T ^ q ^ k) T := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ' F, Nat.pow_succ, pow_mul]
    exact h.mul_left (ih.pow_right q)

/-- If a monoid hom `u` out of a group satisfies `u (φ τ φ⁻¹) = u τ ^ q`, then `u φ⁻¹`
semiconjugates `u τ ^ q` to `u τ`, that is `u φ⁻¹ * u τ ^ q = u τ * u φ⁻¹`. Combined with
`SemiconjBy.pow_left_pow_pow` this gives `u φ⁻ᵏ * u τ ^ q ^ k = u τ * u φ⁻ᵏ`. -/
theorem MonoidHom.semiconjBy_map_inv_of_map_conj_eq_pow {G M : Type*} [Group G] [Monoid M]
    {u : G →* M} {τ φ : G} {q : ℕ} (h : u (φ * τ * φ⁻¹) = u τ ^ q) :
    SemiconjBy (u φ⁻¹) (u τ ^ q) (u τ) := by
  rw [SemiconjBy, ← h, ← map_mul, ← map_mul]
  congr 1
  group
