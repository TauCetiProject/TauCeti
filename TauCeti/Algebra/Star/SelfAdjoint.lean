/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.SelfAdjoint

/-!
# Nilpotent self-adjoint elements, anticommutation and star transposition

In a star monoid with zero whose star is proper (`IsProperStar`: `star x * x = 0` forces
`x = 0`), such as a matrix ring over a star-ordered ring like `ℝ` or `ℂ`, a self-adjoint element
`x` with `x * x = star x * x = 0` is zero. Since the powers of a self-adjoint element are
self-adjoint, peeling off squares shows that a nilpotent self-adjoint element is zero. This is
what rules out nonzero nilpotent ideals in an algebra of matrices closed under conjugate
transposition.

In a star ring, taking adjoints shows that an element anticommuting with a self-adjoint `γ` has an
adjoint anticommuting with `γ`, as needed for gradings. Similarly, taking stars transposes
one-sided relations with a self-adjoint element: `x * q = x` becomes `q * x = x` for self-adjoint
`x`, and `q * u = 0` becomes `star u * q = 0`. For a self-adjoint `p`, the
element `2 p - 1` is again self-adjoint, and its commutator `ξ p - p ξ` with a skew-adjoint `ξ`
is self-adjoint. For a self-adjoint `x` in an additive group with a star-additive involution,
`Fact (IsSelfAdjoint (-x))` is packaged from `Fact (IsSelfAdjoint x)`.

Preservation of self-adjoint squares by an additive homomorphism also implies preservation
of anticommutators on the self-adjoint part when the codomain has cancellative addition.

## Main results

* `IsSelfAdjoint.eq_zero_of_isNilpotent`: a nilpotent self-adjoint element is zero.
* `IsSelfAdjoint.mul_star_eq_neg_star_mul`: if `γ * x = -(x * γ)` for a self-adjoint `γ`, then
  `γ * star x = -(star x * γ)`.
* `IsSelfAdjoint.mul_eq_right_of_mul_eq_left`: for self-adjoint `x` and `q`, `x * q = x` implies
  `q * x = x`.
* `IsSelfAdjoint.star_mul_eq_zero_of_mul_eq_zero`: for self-adjoint `q`, `q * u = 0` implies
  `star u * q = 0`.
* `IsSelfAdjoint.two_mul_sub_one`: `2 p - 1` is self-adjoint for a self-adjoint `p`.
* `IsSelfAdjoint.of_mul_eq_one`: a right inverse of a self-adjoint element is self-adjoint.
* `IsSelfAdjoint.mul_sub_mul_of_mem_skewAdjoint`: the commutator `ξ H - H ξ` of a skew-adjoint
  `ξ` with a self-adjoint `H` is self-adjoint.
* `IsSelfAdjoint.eq_zero_of_mem_skewAdjoint`: if `2` is invertible in the scalars, an element
  that is both self-adjoint and skew-adjoint is zero.
* `Units.inv_mem_skewAdjoint`: the inverse of a skew-adjoint unit is skew-adjoint.
* `IsSelfAdjoint.eq_of_mul_eq_right`: uniqueness from mutual multiplication identities.
* `TauCeti.isSelfAdjoint_neg_fact`: packages `Fact (IsSelfAdjoint (-x))` from
  `Fact (IsSelfAdjoint x)`.
* `AddMonoidHom.map_mul_add_mul_of_isSelfAdjoint`: polarization of the self-adjoint square law.
-/

public section

section Nilpotent

variable {R : Type*} [MonoidWithZero R] [StarMul R] [IsProperStar R]

/-- **A nilpotent self-adjoint element is zero** when the star is proper. Some such hypothesis is
needed: over `ZMod 2` the symmetric matrix `!![1, 1; 1, 1]` squares to zero. -/
theorem IsSelfAdjoint.eq_zero_of_isNilpotent {x : R} (hx : IsSelfAdjoint x)
    (hnil : IsNilpotent x) : x = 0 := by
  obtain ⟨m, hm⟩ := hnil
  -- `x ^ 2 ^ (j + 1) = star (x ^ 2 ^ j) * x ^ 2 ^ j`, so each vanishing power of the form `2 ^ j`
  -- forces the previous one to vanish
  have key (j : ℕ) (hj : x ^ 2 ^ j = 0) : x = 0 := by
    induction j with
    | zero => simpa using hj
    | succ j ih =>
      refine ih (star_mul_self_eq_zero.mp ?_)
      rwa [(hx.pow (2 ^ j)).star_eq, ← pow_add, ← two_mul, ← pow_succ']
  exact key m (pow_eq_zero_of_le m.lt_two_pow_self.le hm)

end Nilpotent

/-- An element anticommuting with a self-adjoint `γ` has an adjoint anticommuting with `γ`. -/
theorem IsSelfAdjoint.mul_star_eq_neg_star_mul {R : Type*} [NonUnitalNonAssocRing R]
    [StarRing R] {γ x : R} (hγ : IsSelfAdjoint γ) (h : γ * x = -(x * γ)) :
    γ * star x = -(star x * γ) := by
  have h' := congrArg star h
  rw [star_mul, star_neg, star_mul, hγ.star_eq] at h'
  rw [h', neg_neg]

/-- For self-adjoint `x` and `q`, taking stars turns `x * q = x` into `q * x = x`. -/
theorem IsSelfAdjoint.mul_eq_right_of_mul_eq_left {R : Type*} [Mul R] [StarMul R] {x q : R}
    (hx : IsSelfAdjoint x) (hq : IsSelfAdjoint q) (h : x * q = x) : q * x = x := by
  simpa only [star_mul, hq.star_eq, hx.star_eq] using congrArg star h

/-- For self-adjoint `q`, taking stars turns `q * u = 0` into `star u * q = 0`. -/
theorem IsSelfAdjoint.star_mul_eq_zero_of_mul_eq_zero {R : Type*} [NonUnitalNonAssocSemiring R]
    [StarRing R] {q u : R} (hq : IsSelfAdjoint q) (h : q * u = 0) : star u * q = 0 := by
  simpa only [star_mul, hq.star_eq, star_zero] using congrArg star h

/-- For a self-adjoint `p`, `2 p - 1` is self-adjoint. -/
theorem IsSelfAdjoint.two_mul_sub_one {R : Type*} [Ring R] [StarRing R] {p : R}
    (hp : IsSelfAdjoint p) : IsSelfAdjoint (2 * p - 1) := by
  rw [two_mul]
  exact (hp.add hp).sub (.one _)

/-- A right inverse of a self-adjoint element is self-adjoint. -/
theorem IsSelfAdjoint.of_mul_eq_one {A : Type*} [Monoid A] [StarMul A] {R Rinv : A}
    (hR : IsSelfAdjoint R) (hRRinv : R * Rinv = 1) : IsSelfAdjoint Rinv := by
  have hstar : star Rinv * R = 1 := by
    simpa only [star_mul, hR.star_eq, star_one] using congrArg star hRRinv
  exact left_inv_eq_right_inv hstar hRRinv

/-- The commutator `ξ H - H ξ` of a skew-adjoint `ξ` with a self-adjoint `H` is self-adjoint. -/
theorem IsSelfAdjoint.mul_sub_mul_of_mem_skewAdjoint {R : Type*} [NonUnitalRing R] [StarRing R]
    {ξ H : R} (hH : IsSelfAdjoint H) (hξ : ξ ∈ skewAdjoint R) : IsSelfAdjoint (ξ * H - H * ξ) := by
  simp [IsSelfAdjoint, hH.star_eq, skewAdjoint.mem_iff.mp hξ, neg_add_eq_sub]

/-- If `2` is invertible in a ring of scalars, an element that is both self-adjoint and
skew-adjoint is zero. -/
theorem IsSelfAdjoint.eq_zero_of_mem_skewAdjoint (R : Type*) {A : Type*} [Semiring R]
    [Invertible (2 : R)] [AddCommGroup A] [Module R A] [StarAddMonoid A] {x : A}
    (hx : IsSelfAdjoint x) (h : x ∈ skewAdjoint A) : x = 0 := by
  have hxx : x + x = 0 := by
    rw [skewAdjoint.mem_iff, hx.star_eq, eq_neg_iff_add_eq_zero] at h
    exact h
  rw [← one_smul R x, ← invOf_mul_self (2 : R), mul_smul, two_smul, hxx, smul_zero]

/-- The inverse of a skew-adjoint unit is skew-adjoint. -/
theorem Units.inv_mem_skewAdjoint {R : Type*} [Ring R] [StarRing R] {u : Rˣ}
    (hu : (u : R) ∈ skewAdjoint R) : ((u⁻¹ : Rˣ) : R) ∈ skewAdjoint R := by
  rw [skewAdjoint.mem_iff] at hu ⊢
  rw [← neg_eq_iff_eq_neg]
  refine Units.eq_inv_of_mul_eq_one_left ?_
  rw [mul_neg, ← neg_mul, ← hu, ← star_mul, Units.inv_mul, star_one]

/-- Two self-adjoint elements agreeing in range with an element `e` are equal.
For idempotents in a ring, the equations express equality of their principal right ideals. -/
theorem IsSelfAdjoint.eq_of_mul_eq_right {A : Type*} [Semigroup A] [StarMul A] {e p q : A}
    (hp : IsSelfAdjoint p) (hq : IsSelfAdjoint q)
    (hep : e * p = p) (hpe : p * e = e) (heq : e * q = q) (hqe : q * e = e) :
    p = q := by
  have hpq : p * q = q := by rw [← heq, ← mul_assoc, hpe, heq]
  have hqp : q * p = p := by rw [← hep, ← mul_assoc, hqe, hep]
  have hpq' : q * p = q := by
    simpa only [star_mul, hp.star_eq, hq.star_eq] using congrArg star hpq
  exact hqp.symm.trans hpq'

namespace TauCeti

/-- Package `IsSelfAdjoint (-x)` as a `Fact` from `Fact (IsSelfAdjoint x)`. Kept as a theorem
rather than a global instance (for use via `have` or `attribute [local instance]`) so
`Fact (IsSelfAdjoint ?x)` cannot loop on `-?y`. -/
theorem isSelfAdjoint_neg_fact {R : Type*} [AddGroup R] [StarAddMonoid R] (x : R)
    [h : Fact (IsSelfAdjoint x)] : Fact (IsSelfAdjoint (-x)) :=
  ⟨h.out.neg⟩

end TauCeti

namespace AddMonoidHom

/-- An additive homomorphism preserving self-adjoint squares preserves anticommutators of
self-adjoint elements when addition in the codomain is cancellative. -/
theorem map_mul_add_mul_of_isSelfAdjoint
    {A B : Type*} [NonUnitalNonAssocSemiring A] [StarAddMonoid A]
    [NonUnitalNonAssocSemiring B] [IsCancelAdd B] (f : A →+ B)
    (hf : ∀ x, IsSelfAdjoint x → f (x * x) = f x * f x)
    {x y : A} (hx : IsSelfAdjoint x) (hy : IsSelfAdjoint y) :
    f (x * y + y * x) = f x * f y + f y * f x := by
  have h := hf (x + y) (hx.add hy)
  simp only [add_mul, mul_add, map_add, hf x hx, hf y hy] at h
  rw [map_add]
  -- Collect the two common square terms on the left before cancelling them.
  apply add_left_cancel (a := f x * f x + f y * f y)
  convert h using 1 <;> ac_rfl

end AddMonoidHom
