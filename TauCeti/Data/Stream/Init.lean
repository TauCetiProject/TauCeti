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

/-- Evaluating `interleave s₁ s₂` at `n` yields `s₁ (n / 2)` for even `n` and `s₂ (n / 2)` for
odd `n`. -/
theorem interleave_apply (s₁ s₂ : ℕ → α) (n : ℕ) :
    interleave s₁ s₂ n = if n % 2 = 0 then s₁ (n / 2) else s₂ (n / 2) := by
  by_cases h : n % 2 = 0
  · conv_lhs => rw [show n = 2 * (n / 2) by omega]
    simp [h]
  · conv_lhs => rw [show n = 2 * (n / 2) + 1 by omega]
    simp [h]

end TauCeti
