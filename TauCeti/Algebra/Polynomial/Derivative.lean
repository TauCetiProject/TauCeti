/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Polynomial.Derivation
public import Mathlib.Algebra.Polynomial.Reverse
public import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.FieldDivision
import TauCeti.Data.Nat.Factorial.NatCast

/-!
# Polynomial derivatives

This file records auxiliary results relating Mathlib's polynomial derivative APIs, computing
iterated derivatives and their values after a linear change of variables, and controlling degrees
of derivatives under coefficient maps.
The derivative of a cubic `a (X - e₁)(X - e₂)(X - e₃)` at the root `e₁` is
`a (e₁ - e₂)(e₁ - e₃)`.
The roots of all nonzero iterated derivatives of a polynomial form a finite set.
If `p.derivative ≠ 0` (always the case for nonconstant `p` in characteristic zero), then at a
root of `p` of multiplicity `m` the root multiplicity of `p.derivative` is at least `m - 1`, so a
simple root of `p` need not be a root of `p.derivative`; together with the roots of
`p.derivative` that are not roots of `p`, this bounds `p.roots` as a multiset in terms of
`p.derivative.roots` and the distinct roots of `p`.

The derivation `Polynomial.derivative'` has `Polynomial.derivative` as its underlying function,
and every scalar multiple of it is locally nilpotent.

For a polynomial `p` with coefficients in an `R`-algebra `S`, possibly noncommutative, evaluating
`p′` at the central element `algebraMap R S t` expands as a sum of the coefficients of `p`
weighted by scalars depending on `t`.

A coefficient map can lower the degree of a polynomial, and in positive characteristic it can
lower the degree of a derivative even when it preserves the degree of the polynomial itself.
Over an additively torsion-free target the second phenomenon cannot occur: preserving the degree
of `p` preserves the degree of `p.derivative`.

A self-reciprocal polynomial `p` of even degree bound `2 g`, one with `X ^ (2 g) p (1 / X) = p (X)`,
satisfies `p' (1) = g p (1)`: the coefficients in degrees `i` and `2 g - i` agree and their
weights `i - g` and `g - i` cancel. The characteristic polynomial of a symplectic matrix is the
basic example.

For `δ ≠ 0` over a semiring without zero divisors, the operator `q ↦ q' + δ q` and all of its
iterates preserve the degree of a polynomial and have trivial kernel.

Over any commutative ring, the quotient of `p` by `X - a` takes the value `p' (a)` at `a`.

Over any semiring, the coefficient of `p q'` in degree `deg p + deg q - 1` is
`leadingCoeff p · leadingCoeff q · deg q`.

Over a possibly noncommutative semiring, the derivative of `f ^ n` is the sum of the `n` products
`f ^ k * f′ * f ^ (n - 1 - k)` (`Polynomial.derivative_pow_eq_sum`), the form of `derivative_pow`
that does not move `f′` past powers of `f`.

In positive characteristic `p`, every iterated derivative `derivative^[k] f` of order `k ≥ p`
vanishes identically (`Polynomial.iterate_derivative_eq_zero_of_charP`), since `p` divides `k !`.

Over a `ℚ≥0`-algebra, such as a division ring of characteristic zero, the derivative is surjective
(`Polynomial.derivative_surjective`): every polynomial has an antiderivative. In positive
characteristic `p` it is not (`Polynomial.derivative_not_surjective_of_charP`), as `X ^ (p - 1)`
has no antiderivative.

As linear endomorphisms of `R[X]`, the derivative and multiplication by `X` satisfy the Weyl
relation `d x = x d + 1` (`Polynomial.derivative_mul_mulLeft_X`).
-/

public section

namespace Polynomial

open Set

variable {R : Type*} [CommRing R] [IsDomain R]

/-- The roots of the nonzero derivatives of `p`, of every order, form a finite set. -/
theorem finite_setOfPred_isRoot_iterate_derivative (p : R[X]) :
    {z | ∃ k, derivative^[k] p ≠ 0 ∧ (derivative^[k] p).IsRoot z}.Finite := by
  have hk : {k | derivative^[k] p ≠ 0}.Finite := (finite_Iic p.natDegree).subset
    fun k hk ↦ not_lt.1 fun h ↦ hk (iterate_derivative_eq_zero h)
  exact (hk.biUnion fun k hk ↦ finite_setOfPred_isRoot hk).subset
    fun z ⟨k, hk, hz⟩ ↦ mem_biUnion hk hz

/-- If `p.derivative ≠ 0`, then at each root of `p` of multiplicity `m` the root multiplicity of
`p.derivative` is at least `m - 1`, in any characteristic (so a simple root of `p` need not be a
root of `p.derivative`); the distinct roots of `p.derivative` that are not roots of `p` come on
top. Counted with multiplicity, `p.roots` together with those extra roots is therefore bounded
by `p.derivative.roots` together with one copy of each distinct root of `p`. The hypothesis is
needed: over `ZMod 2`, `X ^ 2` has roots `{0, 0}` and derivative `0`. -/
theorem roots_add_roots_derivative_sdiff_roots_le_roots_derivative_add_roots_toFinset_of_ne_zero
    [DecidableEq R] {p : R[X]} (hp : p.derivative ≠ 0) :
    p.roots + (p.derivative.roots.toFinset \ p.roots.toFinset).val ≤
      p.derivative.roots + p.roots.toFinset.val := by
  refine Multiset.le_iff_count.2 fun x ↦ ?_
  simp only [Multiset.count_add, Multiset.count_eq_of_nodup (Finset.nodup _), Finset.mem_val,
    Finset.mem_sdiff, Multiset.mem_toFinset]
  by_cases hx : x ∈ p.roots
  · have := rootMultiplicity_sub_one_le_derivative_rootMultiplicity_of_ne_zero p x hp
    simp only [hx, count_roots, ite_true, not_true_eq_false, and_false, ite_false]
    omega
  · simp only [hx, Multiset.count_eq_zero.2 hx, ite_false, not_false_eq_true, and_true,
      zero_add, add_zero]
    split_ifs with hx'
    exacts [Multiset.count_pos.2 hx', Nat.zero_le _]

/-- In characteristic zero, the bound of
`roots_add_roots_derivative_sdiff_roots_le_roots_derivative_add_roots_toFinset_of_ne_zero` holds
for every `p`: if `p.derivative = 0`, then `p` is constant and both sides are `0`. -/
theorem roots_add_roots_derivative_sdiff_roots_le_roots_derivative_add_roots_toFinset
    [CharZero R] [DecidableEq R] (p : R[X]) :
    p.roots + (p.derivative.roots.toFinset \ p.roots.toFinset).val ≤
      p.derivative.roots + p.roots.toFinset.val := by
  rcases eq_or_ne p.derivative 0 with hp | hp
  · rw [eq_C_of_derivative_eq_zero hp]
    simp
  · exact
      roots_add_roots_derivative_sdiff_roots_le_roots_derivative_add_roots_toFinset_of_ne_zero hp

end Polynomial

namespace TauCeti

open Polynomial

variable {R S : Type*}

/-- The derivation `derivative'` has the ordinary polynomial derivative as its underlying
function. -/
theorem _root_.Polynomial.coe_derivative' [CommSemiring R] :
    ⇑(derivative' : Derivation R R[X] R[X]) = derivative :=
  _root_.funext derivative'_apply

/-- The scaled derivative `r • d / dX` is locally nilpotent: some iterate of it kills each
polynomial. -/
theorem _root_.Polynomial.exists_iterate_smul_derivative'_apply_eq_zero [CommSemiring R] (r : R)
    (p : R[X]) : ∃ n, (r • derivative' : Derivation R R[X] R[X])^[n] p = 0 := by
  refine ⟨p.natDegree + 1, ?_⟩
  rw [← Derivation.coeFn_coe, ← FunLike.coe_pow_eq_iterate, Derivation.coe_smul_linearMap, smul_pow,
    LinearMap.smul_apply, _root_.pow_apply_eq_iterate, Derivation.coeFn_coe, coe_derivative',
    iterate_derivative_eq_zero (Nat.lt_succ_self _), smul_zero]

/-- The `k`-th derivative of `p (a X + b)` is `a ^ k p⁽ᵏ⁾ (a X + b)`. -/
theorem _root_.Polynomial.iterate_derivative_comp_C_mul_X_add_C [CommSemiring R] (p : R[X])
    (a b : R) (k : ℕ) :
    derivative^[k] (p.comp (C a * X + C b)) =
      C (a ^ k) * (derivative^[k] p).comp (C a * X + C b) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp [Function.iterate_succ_apply', ih, derivative_comp, derivative_pow, pow_succ, C_mul]
    ring

/-- The `k`-th derivative of `p (a X)` is `a ^ k p⁽ᵏ⁾ (a X)`. -/
theorem _root_.Polynomial.iterate_derivative_comp_C_mul_X [CommSemiring R] (p : R[X]) (a : R)
    (k : ℕ) :
    derivative^[k] (p.comp (C a * X)) = C (a ^ k) * (derivative^[k] p).comp (C a * X) := by
  simpa using p.iterate_derivative_comp_C_mul_X_add_C a 0 k

/-- The `k`-th derivative of `p (a X + b)` at `x` is `a ^ k` times the `k`-th derivative of `p`
at `a x + b`. -/
theorem _root_.Polynomial.eval_iterate_derivative_comp_C_mul_X_add_C [CommSemiring R]
    (p : R[X]) (a b x : R) (k : ℕ) :
    (derivative^[k] (p.comp (C a * X + C b))).eval x =
      a ^ k * (derivative^[k] p).eval (a * x + b) := by
  simp only [iterate_derivative_comp_C_mul_X_add_C, eval_mul, eval_C, eval_comp, eval_add, eval_X]

/-- The `k`-th derivative of `p (a X)` at `x` is `a ^ k` times the `k`-th derivative of `p` at
`a x`. -/
theorem _root_.Polynomial.eval_iterate_derivative_comp_C_mul_X [CommSemiring R] (p : R[X])
    (a x : R) (k : ℕ) :
    (derivative^[k] (p.comp (C a * X))).eval x = a ^ k * (derivative^[k] p).eval (a * x) := by
  simpa using p.eval_iterate_derivative_comp_C_mul_X_add_C a 0 x k

/-- The derivative of the cubic `a (X - e₁)(X - e₂)(X - e₃)` at its root `e₁` is
`a (e₁ - e₂)(e₁ - e₃)`. -/
theorem _root_.Polynomial.eval_derivative_C_mul_X_sub_C_mul_X_sub_C_mul_X_sub_C [CommRing R]
    (a e₁ e₂ e₃ : R) :
    (C a * (X - C e₁) * (X - C e₂) * (X - C e₃)).derivative.eval e₁ =
      a * (e₁ - e₂) * (e₁ - e₃) := by
  simp only [derivative_mul, derivative_C, derivative_sub, derivative_X, eval_add, eval_mul,
    eval_sub, eval_C, eval_X, eval_one, eval_zero]
  ring

/-- **Reciprocal-polynomial identity.** A polynomial `p` of degree at most `2 g` which is its own
reflection at `2 g`, that is `X ^ (2 g) p (1 / X) = p (X)`, satisfies `p' (1) = g p (1)`. -/
theorem _root_.Polynomial.derivative_eval_one_of_reflect_eq [CommRing R] {p : R[X]} {g : ℕ}
    (hp : p.natDegree ≤ 2 * g) (h : p.reflect (2 * g) = p) :
    p.derivative.eval 1 = g * p.eval 1 := by
  have hlt : p.natDegree < 2 * g + 1 := Nat.lt_succ_of_le hp
  rw [derivative_eval, sum_over_range' _ (fun _ ↦ by simp) _ hlt, eval_eq_sum_range' hlt,
    Finset.mul_sum, ← sub_eq_zero, ← Finset.sum_sub_distrib]
  -- The terms in degrees `i` and `2 g - i` cancel, and the term in degree `g` vanishes.
  refine Finset.sum_involution (fun i _ ↦ 2 * g - i) (fun i hi ↦ ?_) (fun i hi hne ↦ ?_)
    (fun i hi ↦ ?_) (fun i hi ↦ ?_) <;>
    have hi : i ≤ 2 * g := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
  · have hc : p.coeff (2 * g - i) = p.coeff i := by
      conv_rhs => rw [← h]
      rw [coeff_reflect, revAt_le hi]
    rw [hc, Nat.cast_sub hi]
    push_cast
    ring
  · intro heq
    obtain rfl : i = g := by omega
    simp [mul_comm] at hne
  · simp only [Finset.mem_range]
    omega
  · omega

section AlgebraMap

variable [CommSemiring R] [Semiring S] [Algebra R S]

/-- Evaluating the derivative of a polynomial at the image of a scalar `t`, with the same range of
coefficients as `Polynomial.eval_algebraMap_eq_sum_range`. -/
theorem _root_.Polynomial.derivative_eval_algebraMap_eq_sum_range (p : S[X]) (t : R) :
    p.derivative.eval (algebraMap R S t) =
      ∑ i ∈ Finset.range (p.natDegree + 1), ((i : R) * t ^ (i - 1)) • p.coeff i := by
  rw [derivative_eval, sum_over_range _ fun n ↦ by simp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [Algebra.smul_def, Algebra.commutes]
  simp [mul_assoc]

end AlgebraMap

variable [Semiring R] [Semiring S] [HasUniqueDiv S]

/-- A coefficient map into an additively torsion-free semiring which preserves the degree of a
polynomial also preserves the degree of its derivative. -/
theorem _root_.Polynomial.natDegree_map_derivative_eq_of_natDegree_map_eq {f : R →+* S}
    {p : R[X]} (h : (p.map f).natDegree = p.natDegree) :
    (p.derivative.map f).natDegree = p.derivative.natDegree := by
  refine Nat.le_antisymm natDegree_map_le ?_
  rw [← derivative_map, natDegree_derivative (p.map f), h]
  exact natDegree_derivative_le p

section ShiftedDerivative

variable [NoZeroDivisors R] {δ : R} {q : R[X]}

/-- For `δ ≠ 0`, the coefficient of `X ^ deg q` in `q' + δ q` is `δ` times the leading coefficient
of `q`, so this polynomial is nonzero when `q` is. -/
private theorem coeff_natDegree_derivative_add_C_mul_ne_zero (hδ : δ ≠ 0) (hq : q ≠ 0) :
    (derivative q + C δ * q).coeff q.natDegree ≠ 0 := by
  rw [coeff_add, coeff_derivative, coeff_natDegree_succ_eq_zero, zero_mul, zero_add, coeff_C_mul]
  exact mul_ne_zero hδ (leadingCoeff_ne_zero.2 hq)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` (the derivative of `x ↦ q(x) e^(δ x)`, divided by
`e^(δ x)`) preserves the degree of a polynomial. -/
@[simp]
theorem _root_.Polynomial.natDegree_derivative_add_C_mul (hδ : δ ≠ 0) :
    (derivative q + C δ * q).natDegree = q.natDegree := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine natDegree_eq_of_le_of_coeff_ne_zero ?_
    (coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq)
  exact natDegree_add_le_of_degree_le (natDegree_derivative_le q |>.trans (Nat.sub_le _ _))
    (natDegree_C_mul_le δ q)

/-- For `δ ≠ 0`, the operator `q ↦ q' + δ q` has trivial kernel. -/
@[simp]
theorem _root_.Polynomial.derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) :
    derivative q + C δ * q = 0 ↔ q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  by_contra hq
  exact coeff_natDegree_derivative_add_C_mul_ne_zero hδ hq (by rw [h, coeff_zero])

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` preserves the degree of a
polynomial. -/
@[simp]
theorem _root_.Polynomial.natDegree_iterate_derivative_add_C_mul (hδ : δ ≠ 0) (n : ℕ) :
    ((fun r ↦ derivative r + C δ * r)^[n] q).natDegree = q.natDegree := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', natDegree_derivative_add_C_mul hδ, ih]

/-- For `δ ≠ 0`, every iterate of the operator `q ↦ q' + δ q` has trivial kernel. -/
@[simp]
theorem _root_.Polynomial.iterate_derivative_add_C_mul_eq_zero_iff (hδ : δ ≠ 0) (n : ℕ) :
    (fun r ↦ derivative r + C δ * r)^[n] q = 0 ↔ q = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', derivative_add_C_mul_eq_zero_iff hδ, ih]

end ShiftedDerivative

end TauCeti

namespace Polynomial

/-- The quotient of `p` by `X - a` takes the value `p' (a)` at `a`, over any commutative ring.
Note that `a` need not be a root of `p`. -/
@[simp]
theorem eval_divByMonic_X_sub_C_self {R : Type*} [CommRing R] (p : R[X]) (a : R) :
    (p /ₘ (X - C a)).eval a = p.derivative.eval a := by
  simpa using congrArg (eval a) (divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p a)

/-- The coefficient of `p * q'` in degree `deg p + deg q - 1` is
`leadingCoeff p · leadingCoeff q · deg q`, that is, `leadingCoeff p` times the coefficient of
`q'` in degree `deg q - 1`. That coefficient of `q'` need not be its leading coefficient: it
vanishes when the characteristic of `R` divides `deg q`, even if `q' ≠ 0`. If `q` is constant,
both sides are `0`, as `q' = 0`; this includes `q = 0`. If `p = 0`, both sides are `0` too. -/
theorem coeff_mul_derivative_natDegree_add_natDegree_sub_one {R : Type*} [Semiring R]
    (p q : R[X]) :
    (p * derivative q).coeff (p.natDegree + q.natDegree - 1) =
      p.leadingCoeff * q.leadingCoeff * q.natDegree := by
  rcases hq : q.natDegree with _ | n
  · simp [derivative_of_natDegree_zero hq]
  · rw [Nat.add_succ_sub_one, coeff_mul_add_eq_of_natDegree_le le_rfl
      ((natDegree_derivative_le q).trans_eq (by omega)), coeff_derivative, leadingCoeff,
      leadingCoeff, hq, Nat.cast_add_one, mul_assoc]

/-- The `(deg q - 1)`-th coefficient of `q'` is `q.leadingCoeff * q.natDegree`. If `q` is
constant (including `q = 0`), both sides are `0`. -/
theorem coeff_derivative_natDegree_sub_one {R : Type*} [Semiring R] (q : R[X]) :
    (derivative q).coeff (q.natDegree - 1) = q.leadingCoeff * q.natDegree := by
  simpa using coeff_mul_derivative_natDegree_add_natDegree_sub_one 1 q

/-- In positive characteristic `p`, every iterated ordinary derivative of order `k ≥ p` vanishes
identically, since `p` divides `k !`. -/
theorem iterate_derivative_eq_zero_of_charP {R : Type*} [Semiring R] {p : ℕ} [CharP R p]
    (hp : 0 < p) {k : ℕ} (hk : p ≤ k) (f : R[X]) :
    derivative^[k] f = 0 := by
  rw [iterate_derivative_eq_factorial_smul_sum, ← Nat.cast_smul_eq_nsmul R,
    Nat.cast_factorial_eq_zero_of_le hp (CharP.cast_eq_zero R p) hk, zero_smul]

/-- Over a `ℚ≥0`-algebra every polynomial is a derivative: the monomial `a X ^ n` is the
derivative of `(n + 1)⁻¹ a X ^ (n + 1)`. -/
theorem derivative_surjective {R : Type*} [Semiring R] [Algebra ℚ≥0 R] :
    Function.Surjective (derivative (R := R)) := by
  intro p
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨p', rfl⟩ := hp
    obtain ⟨q', rfl⟩ := hq
    exact ⟨p' + q', derivative_add⟩
  | monomial n a =>
    refine ⟨monomial (n + 1) (((n + 1 : ℚ≥0)⁻¹ • a)), ?_⟩
    rw [derivative_monomial, smul_mul_assoc, ← nsmul_eq_mul']
    simp [← Nat.cast_smul_eq_nsmul ℚ≥0, smul_smul]

/-- In characteristic `p`, the monomial `X ^ (p - 1)` is not a derivative: the coefficient of
`X ^ (p - 1)` in the derivative of `q` is `p` times a coefficient of `q`. -/
theorem derivative_not_surjective_of_charP {R : Type*} [Semiring R] [Nontrivial R] (p : ℕ)
    [CharP R p] [NeZero p] : ¬Function.Surjective (derivative (R := R)) := fun h ↦ by
  obtain ⟨q, hq⟩ := h (X ^ (p - 1))
  have := congrArg (fun r : R[X] ↦ r.coeff (p - 1)) hq
  simp only [coeff_derivative, coeff_X_pow_self] at this
  rw [← Nat.cast_add_one, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr (NeZero.ne p)),
    CharP.cast_eq_zero, mul_zero] at this
  exact zero_ne_one this

/-- **The derivative of a power, without commutativity.**  Over any semiring, the derivative of
`f ^ n` is the sum over the `n` positions of the factor that is differentiated. Over a commutative
semiring this is `Polynomial.derivative_pow`. -/
theorem derivative_pow_eq_sum {R : Type*} [Semiring R] (f : R[X]) (n : ℕ) :
    derivative (f ^ n) = ∑ k ∈ Finset.range n, f ^ k * derivative f * f ^ (n - 1 - k) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, derivative_mul, ih, Finset.sum_mul, Finset.sum_range_succ, Nat.add_sub_cancel,
      Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [mul_assoc, ← pow_succ, show n - 1 - k + 1 = n - k by grind]

/-- **The Weyl relation** `d x = x d + 1` between the derivative and multiplication by `X`, as
linear endomorphisms of `R[X]`. -/
theorem derivative_mul_mulLeft_X {R : Type*} [CommSemiring R] :
    (derivative : Module.End R R[X]) * LinearMap.mulLeft R X =
      LinearMap.mulLeft R X * derivative + 1 := by
  refine LinearMap.ext fun p ↦ ?_
  simp [derivative_mul, add_comm]

end Polynomial
