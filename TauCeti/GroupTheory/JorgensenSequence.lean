/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Defs

/-!
# Jørgensen's sequence

For elements `A` and `B` of a group, **Jørgensen's sequence** is the iteration
`B₀ = B`, `Bₙ₊₁ = Bₙ A Bₙ⁻¹` of conjugates of `A`. It stays in any subgroup containing `A` and `B`
(`TauCeti.jorgensenSeq_mem`). In `PSL(2, ℝ)` it drives the discreteness arguments behind
Shimizu's lemma, for a parabolic `A`, and Jørgensen's inequality, for a hyperbolic `A`: when the
starting point is close enough to normalising `⟨A⟩` the sequence (or, for a hyperbolic `A`,
suitable conjugates of it by powers of `A`) converges, and discreteness forces a term to reach
the limit.

## Main declarations

* `TauCeti.jorgensenSeq`: the sequence `B₀ = B`, `Bₙ₊₁ = Bₙ A Bₙ⁻¹`.
* `TauCeti.jorgensenSeq_mem`: it lies in every subgroup containing `A` and `B`.
* `TauCeti.map_jorgensenSeq`: group homomorphisms map it to the sequence of the images.

## References

* Troels Jørgensen, *On discrete groups of Möbius transformations*, American Journal of
  Mathematics 98 (1976), 739–749.
-/

public section

namespace TauCeti

variable {G : Type*} [Group G]

/-- **Jørgensen's sequence** `B₀ = B`, `Bₙ₊₁ = Bₙ A Bₙ⁻¹` of conjugates of `A`. -/
def jorgensenSeq (A B : G) : ℕ → G
  | 0 => B
  | n + 1 => jorgensenSeq A B n * A * (jorgensenSeq A B n)⁻¹

/-- Jørgensen's sequence starts at `B`. -/
@[simp]
theorem jorgensenSeq_zero (A B : G) : jorgensenSeq A B 0 = B := (rfl)

/-- Each term of Jørgensen's sequence conjugates `A` by the previous term. -/
theorem jorgensenSeq_succ (A B : G) (n : ℕ) :
    jorgensenSeq A B (n + 1) = jorgensenSeq A B n * A * (jorgensenSeq A B n)⁻¹ := (rfl)

/-- Jørgensen's sequence stays in every subgroup containing `A` and `B`. -/
theorem jorgensenSeq_mem {H : Subgroup G} {A B : G} (hA : A ∈ H) (hB : B ∈ H) (n : ℕ) :
    jorgensenSeq A B n ∈ H := by
  induction n with
  | zero => exact hB
  | succ n ih => exact H.mul_mem (H.mul_mem ih hA) (H.inv_mem ih)

/-- A group homomorphism maps Jørgensen's sequence of `A` and `B` to that of their images. -/
@[simp]
theorem map_jorgensenSeq {H F : Type*} [Group H] [FunLike F G H] [MonoidHomClass F G H] (f : F)
    (A B : G) (n : ℕ) : f (jorgensenSeq A B n) = jorgensenSeq (f A) (f B) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [jorgensenSeq_succ, jorgensenSeq_succ, map_mul, map_mul, map_inv, ih]

end TauCeti
