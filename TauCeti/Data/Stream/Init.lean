/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.Stream.Init

/-!
# Interleaving sequences on `ℕ`

`TauCeti.interleave s₁ s₂` is Mathlib's `Stream'.interleave s₁ s₂` (`s₁ ⋈ s₂`), typed on `ℕ → α`
rather than the semireducible type synonym `Stream' α`.

Direct use of `Stream'.interleave` on plain sequences `ℕ → α` suffers two obstacles:
1. Mathlib's `Stream'.get_interleave_left` and `Stream'.get_interleave_right` rewrite through
   `Stream'.get`, which does not match bare function application `(s₁ ⋈ s₂) n`.
2. Because `Stream' α := ℕ → α` is a semireducible `def` (not an `abbrev`), applying
   `Stream'.interleave` directly to arguments of type `ℕ → α` fails `implicit`-transparency
   typechecking during `simp` and `rw`.

Wrapping `Stream'.interleave` with type `(ℕ → α) → (ℕ → α) → ℕ → α` mirrors the design of
`PiNat.prependWord` in `TauCeti.Topology.Instances.CantorSpace`: it reuses Mathlib's definition
and lemmas without duplicating the implementation while making `simp` and `rw` work directly on
plain sequences `ℕ → α`.

## Main results

* `TauCeti.interleave`: interleave two sequences `s₁, s₂ : ℕ → α` as `s₁ 0, s₂ 0, s₁ 1, s₂ 1, …`.
* `TauCeti.interleave_zero`: `interleave s₁ s₂ 0 = s₁ 0`.
* `TauCeti.interleave_two_mul`: `interleave s₁ s₂ (2 * n) = s₁ n`.
* `TauCeti.interleave_two_mul_add_one`: `interleave s₁ s₂ (2 * n + 1) = s₂ n`.
* `TauCeti.interleave_apply`:
  `interleave s₁ s₂ n = if n % 2 = 0 then s₁ (n / 2) else s₂ (n / 2)`.
* `TauCeti.forall_interleave_iff`: reduce a universal property at `(j, interleave s₁ s₂ j)` to its
  even and odd cases `(2 * i, s₁ i)` and `(2 * i + 1, s₂ i)`.
* `TauCeti.forall_lt_two_mul_interleave_iff`: bounded version for `j < 2 * n`.
* `TauCeti.forall_lt_two_mul_interleave_succ_iff`: consecutive-pair version for `j < 2 * n`.
-/

public section

namespace TauCeti

variable {α : Type*}

/-- Interleave two sequences `s₁, s₂ : ℕ → α` as `s₁ 0, s₂ 0, s₁ 1, s₂ 1, …`.

This is Mathlib's `Stream'.interleave s₁ s₂`, typed on `ℕ → α` rather than the semireducible
type synonym `Stream' α` so that `simp` and `rw` can rewrite applications at `0`, `2 * n`, and
`2 * n + 1` directly without unfolding `Stream'`. -/
def interleave (s₁ s₂ : ℕ → α) : ℕ → α :=
  Stream'.interleave s₁ s₂

/-- Evaluating `interleave s₁ s₂` at `0` gives `s₁ 0`. -/
@[simp]
theorem interleave_zero (s₁ s₂ : ℕ → α) : interleave s₁ s₂ 0 = s₁ 0 :=
  Stream'.get_interleave_left 0 s₁ s₂

/-- Evaluating `interleave s₁ s₂` at an even index `2 * n` gives `s₁ n`. -/
@[simp]
theorem interleave_two_mul (s₁ s₂ : ℕ → α) (n : ℕ) : interleave s₁ s₂ (2 * n) = s₁ n :=
  Stream'.get_interleave_left n s₁ s₂

/-- Evaluating `interleave s₁ s₂` at an odd index `2 * n + 1` gives `s₂ n`. -/
@[simp]
theorem interleave_two_mul_add_one (s₁ s₂ : ℕ → α) (n : ℕ) :
    interleave s₁ s₂ (2 * n + 1) = s₂ n :=
  Stream'.get_interleave_right n s₁ s₂

/-- A predicate holds at `(j, interleave s₁ s₂ j)` for every `j` iff it holds at `(2 * i, s₁ i)`
and `(2 * i + 1, s₂ i)` for every `i`. -/
theorem forall_interleave_iff {s₁ s₂ : ℕ → α} {P : ℕ → α → Prop} :
    (∀ j, P j (interleave s₁ s₂ j)) ↔ ∀ i, P (2 * i) (s₁ i) ∧ P (2 * i + 1) (s₂ i) := by
  refine ⟨fun h i ↦ ⟨by simpa using h (2 * i), by simpa using h (2 * i + 1)⟩, fun h j ↦ ?_⟩
  by_cases hmod : j % 2 = 0
  · have hj : j = 2 * (j / 2) := by omega
    rw [hj]
    simpa using (h (j / 2)).1
  · have hj : j = 2 * (j / 2) + 1 := by omega
    rw [hj]
    simpa using (h (j / 2)).2

/-- A predicate holds at `(j, interleave s₁ s₂ j)` for every `j < 2 * n` iff it holds at
`(2 * i, s₁ i)` and `(2 * i + 1, s₂ i)` for every `i < n`. -/
theorem forall_lt_two_mul_interleave_iff {s₁ s₂ : ℕ → α} {n : ℕ} {P : ℕ → α → Prop} :
    (∀ j < 2 * n, P j (interleave s₁ s₂ j)) ↔
      ∀ i < n, P (2 * i) (s₁ i) ∧ P (2 * i + 1) (s₂ i) := by
  rw [forall_interleave_iff (P := fun j x ↦ j < 2 * n → P j x)]
  exact ⟨fun h i hi ↦ ⟨(h i).1 (by omega), (h i).2 (by omega)⟩,
    fun h i ↦ ⟨fun hi ↦ (h i (by omega)).1, fun hi ↦ (h i (by omega)).2⟩⟩

/-- A relation holds on consecutive entries `interleave s₁ s₂ j` and `interleave s₁ s₂ (j + 1)` for
every `j < 2 * n` iff it holds on `(2 * i, s₁ i, s₂ i)` and `(2 * i + 1, s₂ i, s₁ (i + 1))` for
every `i < n`. -/
theorem forall_lt_two_mul_interleave_succ_iff {s₁ s₂ : ℕ → α} {n : ℕ} {R : ℕ → α → α → Prop} :
    (∀ j < 2 * n, R j (interleave s₁ s₂ j) (interleave s₁ s₂ (j + 1))) ↔
      ∀ i < n, R (2 * i) (s₁ i) (s₂ i) ∧ R (2 * i + 1) (s₂ i) (s₁ (i + 1)) := by
  rw [forall_lt_two_mul_interleave_iff (P := fun j x ↦ R j x (interleave s₁ s₂ (j + 1)))]
  refine forall₂_congr fun i _ ↦ ?_
  have hsucc : 2 * i + 1 + 1 = 2 * (i + 1) := by omega
  rw [hsucc, interleave_two_mul, interleave_two_mul_add_one]

/-- Evaluating `interleave s₁ s₂` at `n` yields `s₁ (n / 2)` for even `n` and `s₂ (n / 2)` for
odd `n`. -/
theorem interleave_apply (s₁ s₂ : ℕ → α) (n : ℕ) :
    interleave s₁ s₂ n = if n % 2 = 0 then s₁ (n / 2) else s₂ (n / 2) :=
  (forall_interleave_iff (s₁ := s₁) (s₂ := s₂)
    (P := fun k x ↦ x = if k % 2 = 0 then s₁ (k / 2) else s₂ (k / 2))).2 (fun i ↦ by
      have heven : (2 * i) % 2 = 0 := Nat.mul_mod_right 2 i
      have hdiv₀ : (2 * i) / 2 = i := Nat.mul_div_cancel_left i Nat.two_pos
      have hdiv₁ : (2 * i + 1) / 2 = i := by omega
      exact ⟨by simp [heven, hdiv₀], by simp [hdiv₁]⟩) n

end TauCeti
