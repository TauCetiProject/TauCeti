/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import Mathlib.Algebra.Module.LinearMap.Defs

import Mathlib.Tactic.LinearCombination

/-!
# Jordan algebras from a cubic minimal polynomial

Let `J` be a commutative, not necessarily associative, unital `R`-algebra, with a linear trace
`T : J →ₗ[R] R` and two functions `S, N : J → R`, the spur and the determinant (McCrimmon's
cubic norm). Suppose that

* every element is a root of the **generic minimal polynomial** `t³ - T(A) t² + S(A) t - N(A)`,
  that is, `A ∘ (A ∘ A) = T(A) A² - S(A) A + N(A) 1`;
* twice the spur is `T(A)² - T(A ∘ A)`;
* the **gradient of the determinant** at `A` in the direction `B` is `T(A^# ∘ B)`, where
  `A^# = A² - T(A) A + S(A) 1` is the adjoint of `A`, in the polarized form
  `N(A + B) - N(A - B) - 2 N(B) = 2 T(A^# ∘ B)`;
* the **trace form is associative**: `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`.

These are the conditions bundled by `TauCeti.Jordan.IsCubicMinimalPolynomial`. Both Albert
algebras, the split one of `TauCeti/Algebra/AlbertAlgebra/Determinant.lean` and the compact one of
`TauCeti/Algebra/AlbertAlgebra/Compact/Determinant.lean`, satisfy them with `S` the spur and `N`
the determinant. Everything else this file proves about them is derived from these four facts,
together with these side conditions: `2` invertible in `R` for the formulas for the spur, the
linearized cubic equation and the Jordan identity; `T(1) = 3` for Newton's formula, whose solved
form for `N(A)` also needs `2` and `3` invertible; and the scalars acting compatibly with the
product (`SMulCommClass R J J` and `IsScalarTower R J J`) for the Jordan identity.

Polarizing the cubic equation, comparing it at `A + B`, `A - B` and `B`, gives the **linearized
cubic equation** (`TauCeti.Jordan.IsCubicMinimalPolynomial.mul_mul_self_add_two_smul_mul_mul`)

`B ∘ A² + 2 A ∘ (A ∘ B) = T(B) A² + 2 T(A) A ∘ B - (T(A) T(B) - T(A ∘ B)) A - S(A) B
  + T(A^# ∘ B) 1`.

Solving it for `B ∘ A²` writes the multiplication operator `L_{A²}` as a polynomial in `L_A` plus
an operator with values in the span of `1`, `A` and `A²`. The commutator `⁅L_A, L_{A²}⁆` therefore
takes values in that span, and its three coefficients vanish by the cubic equation and the
associativity of the trace form: `J` satisfies the **Jordan identity**
(`TauCeti.Jordan.IsCubicMinimalPolynomial.isCommJordan`).

## Main definitions

* `TauCeti.Jordan.IsCubicMinimalPolynomial T S N`: the trace `T`, the spur `S` and the determinant
  `N` satisfy the cubic equation, the spur formula, the gradient formula and trace associativity.

## Main results

* `TauCeti.Jordan.IsCubicMinimalPolynomial.spur_add` and
  `TauCeti.Jordan.IsCubicMinimalPolynomial.spur_sub`: the polarization of the spur.
* `TauCeti.Jordan.IsCubicMinimalPolynomial.mul_mul_self_add_two_smul_mul_mul`: the linearized
  cubic equation.
* `TauCeti.Jordan.IsCubicMinimalPolynomial.six_mul_det`: **Newton's formula**
  `6 N(A) = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))` when `T(1) = 3`.
* `TauCeti.Jordan.IsCubicMinimalPolynomial.isCommJordan`: **the Jordan identity**.

## References

* K. McCrimmon, *A Taste of Jordan Algebras*, Springer (2004), the chapter on Jordan algebras of
  cubic forms, for the generic minimal polynomial `t³ - T t² + S t - N`, the trace form and the
  adjoint `A^#`, and the derivation of the Jordan identity from the cubic equation.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), Chapter 5.
-/

public section

namespace TauCeti

namespace Jordan

variable {R J : Type*} [CommRing R] [NonAssocCommRing J] [Module R J]

/-- The trace `T`, the spur `S` and the determinant `N` of a commutative unital `R`-algebra `J`
make `J` a **Jordan algebra of a cubic minimal polynomial**: every element satisfies the cubic
equation `A ∘ (A ∘ A) = T(A) A² - S(A) A + N(A) 1`, twice the spur is `T(A)² - T(A ∘ A)`, the
gradient of the determinant at `A` is `B ↦ T(A^# ∘ B)` with `A^# = A² - T(A) A + S(A) 1`, and the
trace form is associative. -/
structure IsCubicMinimalPolynomial (T : J →ₗ[R] R) (S N : J → R) : Prop where
  /-- Twice the spur is `T(A)² - T(A ∘ A)`. -/
  two_mul_spur (A : J) : 2 * S A = T A ^ 2 - T (A * A)
  /-- The cubic equation `A ∘ (A ∘ A) = T(A) A² - S(A) A + N(A) 1`. -/
  mul_mul_self (A : J) : A * (A * A) = T A • (A * A) - S A • A + N A • 1
  /-- The gradient of the determinant, in polarized form. -/
  det_add_sub_det_sub (A B : J) :
    N (A + B) - N (A - B) - 2 * N B = 2 * (T (A * A * B) - T A * T (A * B) + S A * T B)
  /-- The trace form is associative. -/
  trace_mul_assoc (A B C : J) : T (A * B * C) = T (A * (B * C))

namespace IsCubicMinimalPolynomial

variable {T : J →ₗ[R] R} {S N : J → R}

/-- **Newton's formula for the determinant**, without division: when `T(1) = 3`,
`6 N(A) = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))`. -/
theorem six_mul_det (h : IsCubicMinimalPolynomial T S N) (h1 : T 1 = 3) (A : J) :
    6 * N A = T A ^ 3 - 3 * T A * T (A * A) + 2 * T (A * (A * A)) := by
  have h' := congrArg T (h.mul_mul_self A)
  rw [map_add, map_sub, map_smul, map_smul, map_smul, h1, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at h'
  linear_combination (-2) * h' + T A * h.two_mul_spur A

variable [Invertible (2 : R)]

/-- **The spur is half of `T(A)² - T(A ∘ A)`**. -/
theorem spur_eq_invOf_two_mul (h : IsCubicMinimalPolynomial T S N) (A : J) :
    S A = ⅟2 * (T A ^ 2 - T (A * A)) := by
  rw [← h.two_mul_spur, invOf_mul_cancel_left]

/-- **The polarization of the spur**: `S(A + B) = S(A) + S(B) + T(A) T(B) - T(A ∘ B)`. -/
theorem spur_add (h : IsCubicMinimalPolynomial T S N) (A B : J) :
    S (A + B) = S A + S B + (T A * T B - T (A * B)) := by
  apply (isUnit_of_invertible (2 : R)).mul_left_cancel
  have h' := h.two_mul_spur (A + B)
  simp only [add_mul, mul_add, map_add, mul_comm B A] at h'
  linear_combination h' - h.two_mul_spur A - h.two_mul_spur B

/-- The spur is even: `S(-A) = S(A)`. -/
theorem spur_neg (h : IsCubicMinimalPolynomial T S N) (A : J) : S (-A) = S A := by
  apply (isUnit_of_invertible (2 : R)).mul_left_cancel
  rw [h.two_mul_spur, h.two_mul_spur, neg_mul_neg, map_neg, neg_sq]

/-- The polarization of the spur at a difference:
`S(A - B) = S(A) + S(B) - (T(A) T(B) - T(A ∘ B))`. -/
theorem spur_sub (h : IsCubicMinimalPolynomial T S N) (A B : J) :
    S (A - B) = S A + S B - (T A * T B - T (A * B)) := by
  rw [sub_eq_add_neg, h.spur_add, h.spur_neg, map_neg, mul_neg, mul_neg, map_neg]
  ring

/-- **Newton's formula for the determinant**: when `T(1) = 3` and `2` and `3` are invertible,
`N(A) = (T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))) / 6`. -/
theorem det_eq_invOf_two_mul_invOf_three_mul [Invertible (3 : R)]
    (h : IsCubicMinimalPolynomial T S N) (h1 : T 1 = 3) (A : J) :
    N A = ⅟2 * ⅟3 * (T A ^ 3 - 3 * T A * T (A * A) + 2 * T (A * (A * A))) := by
  rw [← h.six_mul_det h1]
  linear_combination
    (-(3 * ⅟3 * N A)) * mul_invOf_self (2 : R) - N A * mul_invOf_self (3 : R)

/-- **The linearized cubic equation**: the part linear in `B` of the cubic equation at `A + B`,
`B ∘ A² + 2 A ∘ (A ∘ B) = T(B) A² + 2 T(A) A ∘ B - (T(A) T(B) - T(A ∘ B)) A - S(A) B
  + T(A^# ∘ B) 1`, with `T(A^# ∘ B) = T(A² ∘ B) - T(A) T(A ∘ B) + S(A) T(B)`. -/
theorem mul_mul_self_add_two_smul_mul_mul (h : IsCubicMinimalPolynomial T S N) (A B : J) :
    B * (A * A) + (2 : R) • (A * (A * B)) =
      T B • (A * A) + (2 * T A) • (A * B) - (T A * T B - T (A * B)) • A
        - S A • B + (T (A * A * B) - T A * T (A * B) + S A * T B) • 1 := by
  -- The cubic equation at `A + B`, minus the one at `A - B`, minus twice the one at `B`, is twice
  -- the claimed identity.
  have h₁ := h.mul_mul_self (A + B)
  have h₂ := h.mul_mul_self (A - B)
  rw [h.spur_add] at h₁
  rw [h.spur_sub] at h₂
  simp only [add_mul, mul_add, sub_mul, mul_sub, mul_comm B A, map_add, map_sub] at h₁ h₂
  apply (isUnit_of_invertible (2 : R)).smul_left_cancel.mp
  linear_combination (norm := module)
    h₁ - h₂ - (2 : R) • h.mul_mul_self B + h.det_add_sub_det_sub A B • (1 : J)

section ScalarTower

variable [SMulCommClass R J J] [IsScalarTower R J J]

/-- **The Jordan identity**: a Jordan algebra of a cubic minimal polynomial satisfies
`(A ∘ B) ∘ A² = A ∘ (B ∘ A²)`. -/
theorem isCommJordan (h : IsCubicMinimalPolynomial T S N) : IsCommJordan J where
  lmul_comm_rmul_rmul A B := by
    -- The linearized cubic equation at `(A, A ∘ B)`, and `A` times the one at `(A, B)`, express
    -- the two sides through `A ∘ (A ∘ (A ∘ B))`, which cancels. What is left is a combination of
    -- `A²`, `A` and `1`. Its `A²`-coefficient vanishes identically, and its `A`- and
    -- `1`-coefficients vanish by the cubic equation and the associativity of the trace form.
    have hL := h.mul_mul_self_add_two_smul_mul_mul A (A * B)
    have hM := congrArg (A * ·) (h.mul_mul_self_add_two_smul_mul_mul A B)
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one] at hM
    have hC := h.mul_mul_self A
    have hT := congrArg (fun C => T (C * B)) hC
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, map_add, map_sub, map_smul,
      smul_eq_mul] at hT
    have hA₁ := h.trace_mul_assoc A A B
    have hA₂ := h.trace_mul_assoc (A * A) A B
    rw [mul_comm (A * A) A] at hA₂
    linear_combination (norm := module)
      hL - hM - T B • hC - hA₁ • A + (hT - hA₂ + T A * hA₁) • (1 : J)

end ScalarTower

end IsCubicMinimalPolynomial

end Jordan

end TauCeti
