/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.ForwardDiff
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Abel
import TauCeti.Algebra.Group.ForwardDiff

/-!
# The backward difference operator

The backward difference with step `h` of a function `f` from an additive group to an additive
commutative group is `∇_h f (x) = f x - f (x - h)`. With `h = 1` it is the operator `∇` of the
theory of classical orthogonal polynomials of a discrete variable (Koekoek, Lesky and
Swarttouw, *Hypergeometric orthogonal polynomials and their q-analogues*, (1.16.2); DLMF §18.1(i)).
Mathlib's `fwdDiff h f (x) = f (x + h) - f x` is the forward difference `Δ_h`.

Over an additive commutative group, the backward difference is the forward difference
evaluated one step back, and also the negative of the forward difference with step `-h`. Through
these two identities, Mathlib's Newton formulae and its polynomial results for `fwdDiff` give
their backward counterparts. Newton's formulae hold over any additive group: along the line
`x + ℤ h`, the backward difference with step `h` is the backward difference with step `1` of a
function on `ℤ`, where the commutative case applies.

## Main declarations

* `TauCeti.bwdDiff`: the backward difference `∇_h f (x) = f x - f (x - h)`.
* `TauCeti.bwdDiff_iter_apply_add_zsmul`: the iterated backward difference along `x + ℤ h` as
  an iterated backward difference on `ℤ`.
* `TauCeti.bwdDiff_eq_fwdDiff_sub`: `∇_h f (x) = Δ_h f (x - h)`.
* `TauCeti.bwdDiff_eq_neg_fwdDiff_neg`: `∇_h = -Δ_{-h}`.
* `TauCeti.bwdDiff_iter_eq_fwdDiff_iter_sub`: `∇_hⁿ f (x) = Δ_hⁿ f (x - n h)`.
* `TauCeti.bwdDiff_iter_eq_neg_one_pow_smul_fwdDiff_iter`: `∇_hⁿ = (-1)ⁿ Δ_{-h}ⁿ`.
* `TauCeti.bwdDiff_iter_eq_sum`: Newton's formula
  `∇_hⁿ f (x) = ∑_{k ≤ n} (-1)ᵏ C(n, k) f (x - k h)`.
* `TauCeti.shift_sub_eq_sum_bwdDiff_iter`: its inverse
  `f (x - n h) = ∑_{k ≤ n} (-1)ᵏ C(n, k) ∇_hᵏ f (x)`.
* `Polynomial.bwdDiff_iter_degree_eq_factorial`: the `d`-th backward difference of a polynomial
  of degree `d` is the constant `d!` times its leading coefficient.
* `Polynomial.bwdDiff_iter_eq_zero_of_degree_lt`,
  `Polynomial.bwdDiff_iter_degree_add_one_eq_zero`: a backward difference of order greater than
  the degree of a polynomial vanishes.
* `TauCeti.bwdDiff_ascPochhammer_succ_eval`: `∇ (x)_{n+1} = (n + 1) (x)_n` for the rising
  factorial `(x)_n`.
* `TauCeti.bwdDiff_iter_ascPochhammer_eval`: the `k`-th backward difference of a rising
  factorial.
* `TauCeti.sum_range_smul_bwdDiff`: summation by parts for the backward difference on
  `{0, …, N}`.
-/

public section

open Finset Polynomial
open scoped fwdDiff Nat

namespace TauCeti

section AddGroup

variable {M G : Type*} [AddGroup M] [AddCommGroup G]

/-- The backward difference `∇_h f (x) = f x - f (x - h)` with step `h`. With `h = 1` it is the
operator `∇` of DLMF §18.1(i). The forward difference is Mathlib's `fwdDiff h f`. -/
def bwdDiff (h : M) (f : M → G) : M → G :=
  fun x ↦ f x - f (x - h)

/-- The value of the backward difference at a point. -/
theorem bwdDiff_apply (h : M) (f : M → G) (x : M) : bwdDiff h f x = f x - f (x - h) :=
  (rfl)

/-- The backward difference is additive. -/
@[simp]
theorem bwdDiff_add (h : M) (f g : M → G) : bwdDiff h (f + g) = bwdDiff h f + bwdDiff h g :=
  funext fun _ ↦ add_sub_add_comm ..

/-- The backward difference of a constant function is zero. -/
@[simp]
theorem bwdDiff_const (h : M) (g : G) : bwdDiff h (fun _ ↦ g : M → G) = fun _ ↦ 0 :=
  funext fun _ ↦ sub_self g

/-- The backward difference commutes with scalar multiplication by a constant. -/
@[simp]
theorem bwdDiff_const_smul {R : Type*} [DistribSMul R G] (h : M) (r : R)
    (f : M → G) : bwdDiff h (r • f) = r • bwdDiff h f :=
  funext fun _ ↦ (smul_sub ..).symm

/-- The iterated backward difference is additive. -/
@[simp]
theorem bwdDiff_iter_add (h : M) (f g : M → G) (n : ℕ) :
    (bwdDiff h)^[n] (f + g) = (bwdDiff h)^[n] f + (bwdDiff h)^[n] g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, bwdDiff_add, ih]

/-- The iterated backward difference commutes with scalar multiplication by a constant. -/
@[simp]
theorem bwdDiff_iter_const_smul {R : Type*} [DistribSMul R G] (h : M) (r : R)
    (f : M → G) (n : ℕ) : (bwdDiff h)^[n] (r • f) = r • (bwdDiff h)^[n] f := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, bwdDiff_const_smul, ih]

/-- The backward difference commutes with finite sums. -/
@[simp]
theorem bwdDiff_finsetSum {α : Type*} (h : M) (s : Finset α) (f : α → M → G) :
    bwdDiff h (∑ k ∈ s, f k) = ∑ k ∈ s, bwdDiff h (f k) :=
  funext fun x ↦ by simp only [bwdDiff_apply, Finset.sum_apply, Finset.sum_sub_distrib]

/-- The iterated backward difference commutes with finite sums. -/
@[simp]
theorem bwdDiff_iter_finsetSum {α : Type*} (h : M) (s : Finset α) (f : α → M → G) (n : ℕ) :
    (bwdDiff h)^[n] (∑ k ∈ s, f k) = ∑ k ∈ s, (bwdDiff h)^[n] (f k) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply, bwdDiff_finsetSum, ih]

/-- Along the line `x + ℤ h`, the iterated backward difference with step `h` is the iterated
backward difference with step `1` of the function `j ↦ f (x + j • h)` on `ℤ`. -/
theorem bwdDiff_iter_apply_add_zsmul (h : M) (f : M → G) (n : ℕ) (x : M) (m : ℤ) :
    (bwdDiff h)^[n] f (x + m • h) = (bwdDiff (1 : ℤ))^[n] (fun j : ℤ ↦ f (x + j • h)) m := by
  induction n generalizing m with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', bwdDiff_apply, bwdDiff_apply,
      ← ih m, ← ih (m - 1), sub_one_zsmul, add_sub_assoc, ← sub_eq_add_neg]

end AddGroup

section AddCommGroup

variable {M G : Type*} [AddCommGroup M] [AddCommGroup G]

/-- The backward difference is the forward difference one step back:
`∇_h f (x) = Δ_h f (x - h)`. -/
theorem bwdDiff_eq_fwdDiff_sub (h : M) (f : M → G) (x : M) :
    bwdDiff h f x = Δ_[h] f (x - h) := by
  rw [bwdDiff_apply, fwdDiff, sub_add_cancel]

/-- The backward difference with step `h` is the negative of the forward difference with step
`-h`. -/
theorem bwdDiff_eq_neg_fwdDiff_neg (h : M) (f : M → G) : bwdDiff h f = -Δ_[-h] f := by
  funext x
  rw [bwdDiff_apply, Pi.neg_apply, fwdDiff, neg_sub, ← sub_eq_add_neg]

/-- The iterated backward difference is the iterated forward difference `n` steps back:
`∇_hⁿ f (x) = Δ_hⁿ f (x - n h)`. -/
theorem bwdDiff_iter_eq_fwdDiff_iter_sub (h : M) (f : M → G) (n : ℕ) (x : M) :
    (bwdDiff h)^[n] f x = Δ_[h]^[n] f (x - n • h) := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    have hf : bwdDiff h f = fun y ↦ Δ_[h] f (y + -h) :=
      funext fun y ↦ by rw [bwdDiff_eq_fwdDiff_sub, sub_eq_add_neg]
    rw [Function.iterate_succ_apply, ih, hf, fwdDiff_iter_comp_add,
      ← Function.iterate_succ_apply, succ_nsmul, sub_add_eq_sub_sub, sub_eq_add_neg _ h]

/-- The iterated backward difference with step `h` is `(-1) ^ n` times the iterated forward
difference with step `-h`. -/
theorem bwdDiff_iter_eq_neg_one_pow_smul_fwdDiff_iter (h : M) (f : M → G) (n : ℕ) :
    (bwdDiff h)^[n] f = (-1 : ℤ) ^ n • Δ_[-h]^[n] f := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih, bwdDiff_eq_neg_fwdDiff_neg, fwdDiff_const_smul,
      Function.iterate_succ_apply', pow_succ, mul_comm, mul_smul, neg_one_smul]

end AddCommGroup

section Newton

variable {M G : Type*} [AddGroup M] [AddCommGroup G]

/-- **Newton's formula for the backward difference.** The `n`-th backward difference of `f` at
`x` in terms of the values `f (x - k h)`, `0 ≤ k ≤ n`. -/
theorem bwdDiff_iter_eq_sum (h : M) (f : M → G) (n : ℕ) (x : M) :
    (bwdDiff h)^[n] f x =
      ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (n.choose k : ℤ)) • f (x - k • h) := by
  -- reduce to the backward difference with step `1` on `ℤ`, which is commutative
  have hx := bwdDiff_iter_apply_add_zsmul h f n x 0
  rw [zero_zsmul, add_zero] at hx
  rw [hx, bwdDiff_iter_eq_neg_one_pow_smul_fwdDiff_iter, Pi.smul_apply,
    neg_one_pow_smul_fwdDiff_iter_eq_alternating_sum]
  simp only [smul_neg, nsmul_one, zero_sub, neg_zsmul, natCast_zsmul, ← sub_eq_add_neg]

/-- **Inverse of Newton's formula for the backward difference.** The value `f (x - n h)` in
terms of the iterated backward differences of `f` at `x`. -/
theorem shift_sub_eq_sum_bwdDiff_iter (h : M) (f : M → G) (n : ℕ) (x : M) :
    f (x - n • h) =
      ∑ k ∈ range (n + 1), ((-1 : ℤ) ^ k * (n.choose k : ℤ)) • (bwdDiff h)^[k] f x := by
  -- reduce to the backward difference with step `1` on `ℤ`, which is commutative
  have hx (k : ℕ) := bwdDiff_iter_apply_add_zsmul h f k x 0
  simp only [zero_zsmul, add_zero] at hx
  have hshift := shift_eq_sum_fwdDiff_iter (-1 : ℤ) (fun j : ℤ ↦ f (x + j • h)) n 0
  simp only [smul_neg, nsmul_one, zero_sub, neg_zsmul, natCast_zsmul, ← sub_eq_add_neg]
    at hshift
  rw [hshift]
  refine sum_congr rfl fun k _ ↦ ?_
  rw [hx, bwdDiff_iter_eq_neg_one_pow_smul_fwdDiff_iter, Pi.smul_apply, smul_smul,
    mul_right_comm, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul, natCast_zsmul]

end Newton

/-! ### Rising factorials -/

section Pochhammer

variable {R : Type*} [Ring R]

/-- **One backward difference of a rising factorial.** The backward difference of the rising
factorial `(x)_{n+1} = x (x + 1) ⋯ (x + n)` is `n + 1` times the rising factorial `(x)_n`. -/
theorem bwdDiff_ascPochhammer_succ_eval (n : ℕ) :
    bwdDiff 1 (fun x : R ↦ (ascPochhammer R (n + 1)).eval x) =
      fun x ↦ ((n + 1 : ℕ) : R) * (ascPochhammer R n).eval x := by
  funext x
  -- evaluate the integral identity `(X + 1)_{n+1} = (X)_{n+1} + (n + 1) (X + 1)_n` at `x - 1`
  have hev (k : ℕ) (r : R) : (ascPochhammer R k).eval r = aeval r (ascPochhammer ℤ k) := by
    rw [← ascPochhammer_map (Int.castRingHom R), eval_map, ← algebraMap_int_eq, ← aeval_def]
  have h := congrArg (aeval (x - 1)) (ascPochhammer_succ_comp_X_add_one ℤ n)
  simp only [aeval_comp, map_add, map_nsmul, aeval_X, map_one, sub_add_cancel] at h
  rw [bwdDiff_apply, hev, hev, hev, h, add_sub_cancel_left, nsmul_eq_mul]

/-- **Backward differences of rising factorials.** The `k`-th backward difference of the rising
factorial `x (x + 1) ⋯ (x + j - 1)` of degree `j` is `j (j - 1) ⋯ (j - k + 1)` times the rising
factorial of degree `j - k`. In particular it vanishes for `k > j`. -/
theorem bwdDiff_iter_ascPochhammer_eval (j k : ℕ) :
    (bwdDiff (1 : R))^[k] (fun x : R ↦ (ascPochhammer R j).eval x) =
      fun x ↦ (j.descFactorial k : R) * (ascPochhammer R (j - k)).eval x := by
  induction k generalizing j with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply]
    cases j with
    | zero => simp [Function.iterate_fixed]
    | succ i =>
      simp_rw [bwdDiff_ascPochhammer_succ_eval, ← smul_eq_mul, ← Pi.smul_def]
      rw [bwdDiff_iter_const_smul, ih, Nat.succ_descFactorial_succ, Nat.add_sub_add_right]
      funext x
      simp [mul_assoc]

end Pochhammer

/-! ### Summation by parts -/

/-- **Summation by parts for the backward difference** on `{0, …, N}`:
`∑_{x=0}^{N} f(x) ∇g(x) = f(N) g(N) - f(-1) g(-1) - ∑_{x=0}^{N} ∇f(x) g(x - 1)`. -/
theorem sum_range_smul_bwdDiff {R G : Type*} [Ring R] [AddCommGroup G] [Module R G]
    (f : ℤ → R) (g : ℤ → G) (N : ℕ) :
    ∑ x ∈ range (N + 1), f x • bwdDiff 1 g x =
      f N • g N - f (-1) • g (-1) - ∑ x ∈ range (N + 1), bwdDiff 1 f x • g (x - 1) := by
  have h := sum_range_sub (fun k : ℕ ↦ f ((k : ℤ) - 1) • g ((k : ℤ) - 1)) (N + 1)
  simp only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right, Nat.cast_zero, zero_sub] at h
  rw [eq_sub_iff_add_eq, ← sum_add_distrib, ← h]
  refine sum_congr rfl fun x _ ↦ ?_
  simp only [bwdDiff_apply, smul_sub, sub_smul]
  abel

end TauCeti

/-! ### Polynomials -/

namespace Polynomial

open TauCeti

variable {R : Type*} [CommRing R]

/-- The `d`-th backward difference of a polynomial of degree `d` is the constant `d!` times its
leading coefficient. This is the backward analogue of
`Polynomial.fwdDiff_iter_degree_eq_factorial`. -/
theorem bwdDiff_iter_degree_eq_factorial (P : R[X]) :
    (bwdDiff 1)^[P.natDegree] P.eval = P.leadingCoeff • P.natDegree ! := funext fun x ↦ by
  rw [bwdDiff_iter_eq_fwdDiff_iter_sub, P.fwdDiff_iter_degree_eq_factorial, Pi.smul_apply,
    Pi.smul_apply, Pi.natCast_apply, Pi.natCast_apply]

/-- A backward difference of order greater than the degree of a polynomial vanishes. This is the
backward analogue of `Polynomial.fwdDiff_iter_eq_zero_of_degree_lt`. -/
theorem bwdDiff_iter_eq_zero_of_degree_lt {P : R[X]} {n : ℕ} (hP : P.natDegree < n) :
    (bwdDiff 1)^[n] P.eval = 0 := funext fun x ↦ by
  rw [bwdDiff_iter_eq_fwdDiff_iter_sub, fwdDiff_iter_eq_zero_of_degree_lt hP, Pi.zero_apply,
    Pi.zero_apply]

/-- The `(d + 1)`-th backward difference of a polynomial of degree `d` vanishes. This is the
backward analogue of `Polynomial.fwdDiff_iter_degree_add_one_eq_zero`. -/
theorem bwdDiff_iter_degree_add_one_eq_zero (P : R[X]) :
    (bwdDiff 1)^[P.natDegree + 1] P.eval = 0 :=
  bwdDiff_iter_eq_zero_of_degree_lt (Nat.lt_succ_self _)

end Polynomial
