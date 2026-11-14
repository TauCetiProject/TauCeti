/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.RingTheory.Coprime.Lemmas

/-!
# Coprimality of linear factors, their powers, and polynomial translates

Mathlib's `Polynomial.isCoprime_X_sub_C_of_isUnit_sub` states that `X - C a` and `X - C b` are
coprime when `a - b` is a unit. Evaluating a Bézout relation at `a` gives the converse, so
coprimality of `X - C a` and `X - C b` is equivalent to `IsUnit (a - b)`, and coprimality of
`(X - C a) ^ m` and `(X - C b) ^ n` holds if and only if `m = 0`, `n = 0`, or `IsUnit (a - b)`.
Substituting any polynomial `p` for `X` also shows that `p - C a` and `p - C b` are coprime
whenever `a - b` is a unit (`Polynomial.isCoprime_sub_C_of_isUnit_sub`), for example the binomials
`X ^ n - C a` and `X ^ n - C b`.
-/

public section

namespace Polynomial

section CommRing

variable {R : Type*} [CommRing R]

/-- Linear factors `X - C a` and `X - C b` over a commutative ring are coprime if and only if
`a - b` is a unit. -/
theorem isCoprime_X_sub_C_iff {a b : R} :
    IsCoprime (X - C a) (X - C b) ↔ IsUnit (a - b) := by
  refine ⟨fun ⟨u, v, huv⟩ => isUnit_iff_exists_inv.mpr ⟨v.eval a, ?_⟩,
    isCoprime_X_sub_C_of_isUnit_sub⟩
  have h := congrArg (eval a) huv
  simp only [eval_add, eval_mul, eval_sub, eval_X, eval_C, sub_self, mul_zero, zero_add,
    eval_one] at h
  rwa [mul_comm] at h

/-- Powers `(X - C a) ^ m` and `(X - C b) ^ n` are coprime if and only if at least one exponent
is zero or `a - b` is a unit. -/
theorem isCoprime_X_sub_C_pow_iff {a b : R} {m n : ℕ} :
    IsCoprime ((X - C a) ^ m) ((X - C b) ^ n) ↔ m = 0 ∨ n = 0 ∨ IsUnit (a - b) := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp [isCoprime_one_left]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [isCoprime_one_right]
  simp [hm, hn, IsCoprime.pow_iff (Nat.pos_of_ne_zero hm) (Nat.pos_of_ne_zero hn),
    isCoprime_X_sub_C_iff]

/-- A family of powers `(X - C (a i)) ^ m i` is pairwise coprime if and only if `a i - a j` is a
unit whenever `i ≠ j` and both `m i` and `m j` are nonzero. In particular, repeated nodes of
multiplicity zero are permitted. -/
theorem pairwise_isCoprime_X_sub_C_pow_iff {ι : Type*} (a : ι → R) (m : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime fun i => (X - C (a i)) ^ m i) ↔
      ∀ ⦃i j⦄, i ≠ j → m i ≠ 0 → m j ≠ 0 → IsUnit (a i - a j) := by
  refine ⟨fun h i j hij hmi hmj => ?_, fun h i j hij => ?_⟩
  · rcases isCoprime_X_sub_C_pow_iff.mp (h hij) with h0 | h0 | hu
    · exact absurd h0 hmi
    · exact absurd h0 hmj
    · exact hu
  · rw [Function.onFun_apply, isCoprime_X_sub_C_pow_iff]
    by_cases hmi : m i = 0
    · exact Or.inl hmi
    by_cases hmj : m j = 0
    · exact Or.inr (Or.inl hmj)
    exact Or.inr (Or.inr (h hij hmi hmj))

/-- If `a - b` is a unit, the translates `p - C a` and `p - C b` of a polynomial are coprime. -/
theorem isCoprime_sub_C_of_isUnit_sub (p : R[X]) {a b : R} (h : IsUnit (a - b)) :
    IsCoprime (p - C a) (p - C b) := by
  simpa using (isCoprime_X_sub_C_of_isUnit_sub h).map (aeval p).toRingHom

end CommRing

/-- Over a field, powers `(X - C (a i)) ^ m i` at injective nodes are pairwise coprime for every
multiplicity function `m`. -/
theorem pairwise_coprime_X_sub_C_pow {K : Type*} [Field K] {ι : Type*} {a : ι → K}
    (ha : Function.Injective a) (m : ι → ℕ) :
    Pairwise (Function.onFun IsCoprime fun i => (X - C (a i)) ^ m i) :=
  fun _ _ hij => (pairwise_coprime_X_sub_C ha hij).pow

end Polynomial
