/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Norm.Basic
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Data.ZMod.Basic

/-!
# Congruences of integer norms

In a possibly noncommutative ring that is free of finite rank over `ℤ`, elements congruent
modulo `(m)` have norms congruent modulo `m`. These are the determinants of left multiplication.
This supplies congruences for absolute norms of principal ideals when the integer norms have
nonnegative product.

## Main results

* `Algebra.intCast_norm_eq_of_sub_mem_span_natCast`: congruent elements have congruent norms.
* `Ideal.span_singleton_natCast_eq_top_iff`: in a nontrivial finite free `ℤ`-algebra,
  the ideal `(m)` is the unit ideal exactly when `m = 1`.
-/

public section

section Congruence

variable {S : Type*} [Ring S] [Module.Free ℤ S] [Module.Finite ℤ S]

/-- **Congruent elements have congruent norms.** If `a ≡ b` modulo the ideal `(m)` of a ring `S`
that is free of finite rank over `ℤ`, then `N(a) ≡ N(b)` modulo `m`. Commutativity of `S`
is not required: the norm is the determinant of left multiplication. -/
theorem Algebra.intCast_norm_eq_of_sub_mem_span_natCast {m : ℕ} {a b : S}
    (h : a - b ∈ Ideal.span {(m : S)}) :
    ((Algebra.norm ℤ a : ℤ) : ZMod m) = ((Algebra.norm ℤ b : ℤ) : ZMod m) := by
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp h
  let B := Module.Free.chooseBasis ℤ S
  rw [Algebra.norm_eq_matrix_det B, Algebra.norm_eq_matrix_det B,
    ← eq_intCast (Int.castRingHom (ZMod m)) _,
    ← eq_intCast (Int.castRingHom (ZMod m)) _, RingHom.map_det, RingHom.map_det,
    sub_eq_iff_eq_add.mp hc.symm]
  simp [map_add, map_mul, ← Matrix.diagonal_natCast]

/-- **The ideal `(m)` is the unit ideal only for `m = 1`**, in a nontrivial ring that is free of
finite rank over `ℤ`. The ring need not be commutative. -/
theorem Ideal.span_singleton_natCast_eq_top_iff [Nontrivial S] {m : ℕ} :
    Ideal.span {(m : S)} = ⊤ ↔ m = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp ((Ideal.eq_top_iff_one _).mp h)
  have hnorm := congrArg (Algebra.norm ℤ (S := S)) hc
  rw [map_mul, map_one] at hnorm
  -- A left inverse makes the integer norm of `m` a unit.
  have hu := Int.isUnit_iff_natAbs_eq.mp (IsUnit.of_mul_eq_one_right _ hnorm)
  rw [Algebra.norm_natCast, Int.natAbs_pow, Int.natAbs_natCast] at hu
  exact (Nat.pow_eq_one.mp hu).resolve_right Module.finrank_pos.ne'

end Congruence
