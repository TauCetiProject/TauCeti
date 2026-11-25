/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Compact
public import TauCeti.Algebra.Jordan.CubicMinimalPolynomial

import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# The determinant of the compact Albert algebra and its cubic equation

A Hermitian matrix

`⟦a, x⟧ = [[a 0, x 2, star (x 1)], [star (x 2), a 1, x 0], [x 1, star (x 0), a 2]]`

of the compact Albert algebra `TauCeti.CompactAlbertAlgebra R`, whose octonion entries lie in the
Cayley–Dickson double `CayleyDickson ℍ[R]` of the quaternions, has a **determinant**, the cubic
form

`det A = a 0 * a 1 * a 2 - a 0 * N (x 0) - a 1 * N (x 1) - a 2 * N (x 2)
  + T ((x 0 * x 1) * x 2)`,

where `N` and `T` are the octonion norm `TauCeti.CayleyDickson.normSq` and trace
`TauCeti.CayleyDickson.trace`. The octonion entry `x i` sits opposite the diagonal entry `a i`, so
each diagonal entry is paired with the norm of the octonion entry it shares no row or column with;
the last term is the trace of the product of the three octonion entries taken around the matrix.
That trace depends neither on the bracketing nor on which entry the cycle starts from
(`TauCeti.CayleyDickson.trace_mul_assoc` and `TauCeti.CayleyDickson.trace_mul_cycle`), so the
determinant can be read off starting from any diagonal entry
(`TauCeti.CompactAlbertAlgebra.det_eq_rotate`).

Together with the trace `T` and the quadratic **spur** `S`, the sum of the principal `2 × 2` minors

`spur A = a 0 * a 1 + a 1 * a 2 + a 2 * a 0 - N (x 0) - N (x 1) - N (x 2)`,

the determinant is, up to sign, the constant term of the **generic minimal polynomial**
`t³ - T(A) t² + S(A) t - det A`, and every element satisfies the **cubic equation**

`A ∘ (A ∘ A) = T(A) • (A ∘ A) - S(A) • A + det A • 1`

(`TauCeti.CompactAlbertAlgebra.mul_mul_self`), with powers taken in the Jordan product. Its
polarization, the linearized cubic equation, is what proves the Jordan identity in
`TauCeti/Algebra/AlbertAlgebra/Compact/Jordan.lean`. Taking traces in the cubic equation gives
Newton's formula `6 det A = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))`.

For a diagonal matrix with entries `aᵢ` all octonion entries vanish, so over every commutative ring
the determinant reduces to `a 0 * a 1 * a 2`, the spur to `a 0 * a 1 + a 1 * a 2 + a 2 * a 0`, and
the generic minimal polynomial factors as `(t - a 0) (t - a 1) (t - a 2)`. The determinant and
the spur are defined over every commutative ring; the cubic equation needs `2` to be invertible,
because the Jordan product does.

## Main definitions

* `TauCeti.CompactAlbertAlgebra.det`: the determinant, the cubic norm form.
* `TauCeti.CompactAlbertAlgebra.spur`: the spur, a quadratic form in `A` and the coefficient of
  `t` in the generic minimal polynomial.

## Main results

* `TauCeti.CompactAlbertAlgebra.det_smul` and `TauCeti.CompactAlbertAlgebra.spur_smul`: the
  determinant is homogeneous of degree three and the spur homogeneous of degree two.
* `TauCeti.CompactAlbertAlgebra.two_mul_spur` and
  `TauCeti.CompactAlbertAlgebra.spur_eq_invOf_two_mul`: the spur is `(T(A)² - T(A ∘ A)) / 2`.
* `TauCeti.CompactAlbertAlgebra.spur_add` and `TauCeti.CompactAlbertAlgebra.spur_sub`: the
  polarization of the spur, `S(A + B) = S(A) + S(B) + T(A) T(B) - T(A ∘ B)`.
* `TauCeti.CompactAlbertAlgebra.det_add_sub_det_sub`: the gradient of the determinant, in
  polarized form.
* `TauCeti.CompactAlbertAlgebra.mul_mul_self`: **the cubic equation** satisfied by every element.
* `TauCeti.CompactAlbertAlgebra.isCubicMinimalPolynomial`: the trace, the spur and the determinant
  satisfy the hypotheses of `TauCeti.Jordan.IsCubicMinimalPolynomial`.
* `TauCeti.CompactAlbertAlgebra.mul_mul_self_add_two_smul_mul_mul`: the linearized cubic equation.
* `TauCeti.CompactAlbertAlgebra.six_mul_det` and
  `TauCeti.CompactAlbertAlgebra.det_eq_invOf_two_mul_invOf_three_mul`: **Newton's formula** for
  the determinant in terms of the traces of the powers.

## Implementation notes

The statements and proofs follow those for the split Albert algebra in
`TauCeti/Algebra/AlbertAlgebra/Determinant.lean`. The two carriers differ in their octonions: here
the symmetric bilinear form of the norm is written through the octonion trace, as
`N (x + y) = N x + N y + T (x * star y)` (`TauCeti.CayleyDickson.normSq_add_eq_add_trace_mul_star`),
and the octonion products that occur cancel to norms by the inverse properties
`TauCeti.CayleyDickson.mul_star_mul_left` and `TauCeti.CayleyDickson.mul_star_mul_right`.

Only the coordinate facts, the spur formula, the cubic equation, the gradient of the determinant
and the associativity of the trace form, are proved here. The polarization of the spur, the
linearized cubic equation and Newton's formula are specializations of the carrier-independent
results of `TauCeti/Algebra/Jordan/CubicMinimalPolynomial.lean`, shared with the split carrier.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. **39** (2002), 145–205, §3.4, for the
  coordinate formula of the determinant.
* K. McCrimmon, *A Taste of Jordan Algebras*, Springer (2004), the chapter on Jordan algebras of
  cubic forms, for the generic minimal polynomial `t³ - T t² + S t - N` and the cubic equation.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), Chapter 5.
-/

public section

namespace TauCeti

namespace CompactAlbertAlgebra

variable {R : Type*} [CommRing R]

/-- **The determinant** of a Hermitian octonion matrix, the cubic norm form of the compact Albert
algebra: `a₀ a₁ a₂ - a₀ N(x₀) - a₁ N(x₁) - a₂ N(x₂) + T ((x₀ x₁) x₂)`, with `aᵢ` the diagonal
entries and `xᵢ` the octonion entry in position `(i + 1, i + 2)`. -/
def det (A : CompactAlbertAlgebra R) : R :=
  A.diag 0 * A.diag 1 * A.diag 2 - A.diag 0 * CayleyDickson.normSq (A.offDiag 0)
    - A.diag 1 * CayleyDickson.normSq (A.offDiag 1)
    - A.diag 2 * CayleyDickson.normSq (A.offDiag 2)
    + CayleyDickson.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2)

theorem det_def (A : CompactAlbertAlgebra R) :
    det A = A.diag 0 * A.diag 1 * A.diag 2 - A.diag 0 * CayleyDickson.normSq (A.offDiag 0)
      - A.diag 1 * CayleyDickson.normSq (A.offDiag 1)
      - A.diag 2 * CayleyDickson.normSq (A.offDiag 2)
      + CayleyDickson.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2) :=
  (rfl)

/-- **The triple-product term of the determinant does not depend on where the cycle starts**:
the octonion entries can be multiplied in any cyclic order, `xᵢ xᵢ₊₁ xᵢ₊₂`. -/
theorem trace_offDiag_mul_offDiag_mul_offDiag (A : CompactAlbertAlgebra R) (i : Fin 3) :
    CayleyDickson.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) =
      CayleyDickson.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2) := by
  fin_cases i
  · rfl
  · exact CayleyDickson.trace_mul_cycle _ _ _
  · exact (CayleyDickson.trace_mul_cycle _ _ _).symm

/-- The determinant, read off starting from an arbitrary diagonal entry. -/
theorem det_eq_rotate (A : CompactAlbertAlgebra R) (i : Fin 3) :
    det A = A.diag i * A.diag (i + 1) * A.diag (i + 2)
      - A.diag i * CayleyDickson.normSq (A.offDiag i)
      - A.diag (i + 1) * CayleyDickson.normSq (A.offDiag (i + 1))
      - A.diag (i + 2) * CayleyDickson.normSq (A.offDiag (i + 2))
      + CayleyDickson.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
  rw [trace_offDiag_mul_offDiag_mul_offDiag, det_def]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd, zero_add] <;>
    ring

@[simp] theorem det_zero : det (0 : CompactAlbertAlgebra R) = 0 := by simp [det_def]

@[simp] theorem det_one : det (1 : CompactAlbertAlgebra R) = 1 := by simp [det_def]

/-- **The determinant is homogeneous of degree three**: `det (r • A) = r ^ 3 * det A`. -/
@[simp] theorem det_smul (r : R) (A : CompactAlbertAlgebra R) : det (r • A) = r ^ 3 * det A := by
  simp only [det_def, smul_diag, smul_offDiag, Pi.smul_apply, smul_eq_mul,
    CayleyDickson.normSq_smul, smul_mul_assoc, mul_smul_comm, smul_smul, map_smul]
  ring

@[simp] theorem det_neg (A : CompactAlbertAlgebra R) : det (-A) = -det A := by
  rw [← neg_one_smul R A, det_smul]
  ring

/-- **The spur** of a Hermitian octonion matrix, the sum of its three principal `2 × 2` minors:
`a₀ a₁ + a₁ a₂ + a₂ a₀ - N(x₀) - N(x₁) - N(x₂)`. It is a quadratic form in `A` and the coefficient
of `t` in the generic minimal polynomial of the compact Albert algebra
(`TauCeti.CompactAlbertAlgebra.mul_mul_self`), and twice it is `T(A)² - T(A ∘ A)` when `2` is
invertible (`TauCeti.CompactAlbertAlgebra.two_mul_spur`). -/
def spur (A : CompactAlbertAlgebra R) : R :=
  A.diag 0 * A.diag 1 + A.diag 1 * A.diag 2 + A.diag 2 * A.diag 0
    - CayleyDickson.normSq (A.offDiag 0) - CayleyDickson.normSq (A.offDiag 1)
    - CayleyDickson.normSq (A.offDiag 2)

theorem spur_def (A : CompactAlbertAlgebra R) :
    spur A = A.diag 0 * A.diag 1 + A.diag 1 * A.diag 2 + A.diag 2 * A.diag 0
      - CayleyDickson.normSq (A.offDiag 0) - CayleyDickson.normSq (A.offDiag 1)
      - CayleyDickson.normSq (A.offDiag 2) :=
  (rfl)

/-- The spur, read off starting from an arbitrary diagonal entry. -/
theorem spur_eq_rotate (A : CompactAlbertAlgebra R) (i : Fin 3) :
    spur A = A.diag i * A.diag (i + 1) + A.diag (i + 1) * A.diag (i + 2)
      + A.diag (i + 2) * A.diag i - CayleyDickson.normSq (A.offDiag i)
      - CayleyDickson.normSq (A.offDiag (i + 1)) - CayleyDickson.normSq (A.offDiag (i + 2)) := by
  rw [spur_def]
  fin_cases i <;>
    simp only [Fin.isValue, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.reduceAdd, zero_add] <;>
    ring

@[simp] theorem spur_zero : spur (0 : CompactAlbertAlgebra R) = 0 := by simp [spur_def]

/-- The spur of the identity matrix is `3`, one for each principal `2 × 2` minor. -/
@[simp] theorem spur_one : spur (1 : CompactAlbertAlgebra R) = 3 := by
  norm_num [spur_def]

/-- **The spur is homogeneous of degree two**: `spur (r • A) = r ^ 2 * spur A`. -/
@[simp] theorem spur_smul (r : R) (A : CompactAlbertAlgebra R) :
    spur (r • A) = r ^ 2 * spur A := by
  simp only [spur_def, smul_diag, smul_offDiag, Pi.smul_apply, smul_eq_mul,
    CayleyDickson.normSq_smul]
  ring

@[simp] theorem spur_neg (A : CompactAlbertAlgebra R) : spur (-A) = spur A := by
  rw [← neg_one_smul R A, spur_smul]
  ring

/-! ### The Jordan square and the cubic equation -/

section Invertible

variable [Invertible (2 : R)]

/-- **Twice the spur** is `T(A)² - T(A ∘ A)`. -/
theorem two_mul_spur (A : CompactAlbertAlgebra R) :
    2 * spur A = trace A ^ 2 - trace (A * A) := by
  rw [trace_mul_self, spur_def, trace_apply]
  simp only [Fin.sum_univ_three]
  ring

/-- **The gradient of the determinant**, in polarized form: the part of `det (A + B)` linear in
`B` is `T(A^# ∘ B) = T(A² ∘ B) - T(A) T(A ∘ B) + S(A) T(B)`, where `A^# = A² - T(A) A + S(A) 1`
is the adjoint of `A`. -/
theorem det_add_sub_det_sub (A B : CompactAlbertAlgebra R) :
    det (A + B) - det (A - B) - 2 * det B =
      2 * (trace (A * A * B) - trace A * trace (A * B) + spur A * trace B) := by
  -- In coordinates, after rotating every octonion triple product to begin with an entry in
  -- slot `0`, both sides are the same polynomial.
  rw [trace_mul, trace_mul]
  simp only [det_def, spur_def, trace_apply, mul_self_diag, mul_self_offDiag, add_diag, sub_diag,
    add_offDiag, sub_offDiag, Pi.add_apply, Pi.sub_apply,
    CayleyDickson.normSq_add_eq_add_trace_mul_star,
    CayleyDickson.normSq_sub_eq_add_sub_trace_mul_star, Fin.sum_univ_three, Fin.reduceAdd,
    smul_eq_mul, add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, map_add, map_sub, map_smul,
    ← star_mul, CayleyDickson.trace_star, ← CayleyDickson.trace_mul_assoc,
    CayleyDickson.trace_mul_cycle _ _ (A.offDiag 0),
    fun x y => (CayleyDickson.trace_mul_cycle (A.offDiag 0) y x).symm]
  ring

/-- **The cubic equation of the compact Albert algebra.** Every Hermitian octonion matrix is a root
of its generic minimal polynomial `t³ - T(A) t² + S(A) t - det A`, with powers taken in the Jordan
product: `A ∘ (A ∘ A) = T(A) • (A ∘ A) - S(A) • A + det A • 1`. -/
theorem mul_mul_self (A : CompactAlbertAlgebra R) :
    A * (A * A) = trace A • (A * A) - spur A • A + det A • 1 := by
  -- The products of the octonion entries that occur cancel to norms by the inverse properties,
  -- and the two triple products on the diagonal are the triple-product term of the determinant.
  -- What is left in each entry is a polynomial identity in the entries and in the half `⅟2` of
  -- the Jordan product; `linear_combination` closes it from `⅟2 + ⅟2 = 1`.
  have h2 : (⅟2 : R) + ⅟2 = 1 := invOf_two_add_invOf_two
  refine CompactAlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
  · have ht₁ : CayleyDickson.trace (A.offDiag (i + 1) * (A.offDiag (i + 2) * A.offDiag i)) =
        CayleyDickson.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
      rw [← CayleyDickson.trace_mul_assoc, CayleyDickson.trace_mul_cycle]
    have ht₂ : CayleyDickson.trace (A.offDiag (i + 2) * (A.offDiag i * A.offDiag (i + 1))) =
        CayleyDickson.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
      rw [CayleyDickson.trace_mul_comm]
    rw [mul_diag, mul_self_diag, mul_self_offDiag, mul_self_offDiag]
    simp only [add_one_add_one_fin_three, add_one_add_two_fin_three, add_two_add_one_fin_three,
      add_two_add_two_fin_three, star_add, star_star, CayleyDickson.star_smul, mul_add,
      mul_smul_comm, map_add, map_smul, smul_eq_mul, CayleyDickson.trace_mul_star_self, ht₁, ht₂,
      add_diag, sub_diag, smul_diag, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, one_diag,
      Pi.one_apply, mul_one, mul_self_diag, trace_apply, sum_fin_three_rotate _ i]
    rw [spur_eq_rotate A i, det_eq_rotate A i]
    linear_combination
      (CayleyDickson.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2))
        + (A.diag i + A.diag (i + 2)) * CayleyDickson.normSq (A.offDiag (i + 1))
        + (A.diag i + A.diag (i + 1)) * CayleyDickson.normSq (A.offDiag (i + 2))) * h2
  · rw [mul_offDiag, mul_self_diag, mul_self_diag, mul_self_offDiag, mul_self_offDiag,
      mul_self_offDiag]
    simp only [add_one_add_one_fin_three, add_one_add_two_fin_three, add_two_add_one_fin_three,
      add_two_add_two_fin_three, mul_add, add_mul, smul_mul_assoc, mul_smul_comm, star_mul,
      star_add, star_star, CayleyDickson.star_smul, CayleyDickson.mul_star_mul_left,
      CayleyDickson.mul_star_mul_right, add_offDiag, sub_offDiag, smul_offDiag, one_offDiag,
      Pi.add_apply, Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_zero, add_zero,
      trace_apply, sum_fin_three_rotate _ i, mul_self_offDiag]
    rw [spur_eq_rotate A i]
    linear_combination (norm := module)
      (A.diag (i + 1) ^ 2 + A.diag (i + 1) * A.diag (i + 2) + A.diag (i + 2) ^ 2
        + CayleyDickson.normSq (A.offDiag i) + CayleyDickson.normSq (A.offDiag (i + 1))
        + CayleyDickson.normSq (A.offDiag (i + 2))) • h2 • A.offDiag i
      + (A.diag i + A.diag (i + 1) + A.diag (i + 2)) • h2 •
        (star (A.offDiag (i + 2)) * star (A.offDiag (i + 1)))

/-- The trace, the spur and the determinant of the compact Albert algebra satisfy the hypotheses of
`TauCeti.Jordan.IsCubicMinimalPolynomial`: the spur formula, the cubic equation, the gradient of the
determinant and the associativity of the trace form. -/
theorem isCubicMinimalPolynomial :
    Jordan.IsCubicMinimalPolynomial (trace : CompactAlbertAlgebra R →ₗ[R] R) spur det where
  two_mul_spur := two_mul_spur
  mul_mul_self := mul_mul_self
  det_add_sub_det_sub := det_add_sub_det_sub
  trace_mul_assoc := trace_mul_assoc

/-- **The spur is half of `T(A)² - T(A ∘ A)`**, the usual coefficient of a characteristic
polynomial in terms of traces of powers. -/
theorem spur_eq_invOf_two_mul (A : CompactAlbertAlgebra R) :
    spur A = ⅟2 * (trace A ^ 2 - trace (A * A)) :=
  isCubicMinimalPolynomial.spur_eq_invOf_two_mul A

/-- **The polarization of the spur**: `S(A + B) = S(A) + S(B) + T(A) T(B) - T(A ∘ B)`. -/
theorem spur_add (A B : CompactAlbertAlgebra R) :
    spur (A + B) = spur A + spur B + (trace A * trace B - trace (A * B)) :=
  isCubicMinimalPolynomial.spur_add A B

/-- The polarization of the spur at a difference:
`S(A - B) = S(A) + S(B) - (T(A) T(B) - T(A ∘ B))`. -/
theorem spur_sub (A B : CompactAlbertAlgebra R) :
    spur (A - B) = spur A + spur B - (trace A * trace B - trace (A * B)) :=
  isCubicMinimalPolynomial.spur_sub A B

/-- **The linearized cubic equation** of the compact Albert algebra: the part linear in `B` of the
cubic equation `TauCeti.CompactAlbertAlgebra.mul_mul_self` at `A + B`,
`B ∘ A² + 2 A ∘ (A ∘ B) = T(B) A² + 2 T(A) A ∘ B - (T(A) T(B) - T(A ∘ B)) A - S(A) B
  + T(A^# ∘ B) 1`, with `T(A^# ∘ B) = T(A² ∘ B) - T(A) T(A ∘ B) + S(A) T(B)`. -/
theorem mul_mul_self_add_two_smul_mul_mul (A B : CompactAlbertAlgebra R) :
    B * (A * A) + (2 : R) • (A * (A * B)) =
      trace B • (A * A) + (2 * trace A) • (A * B) - (trace A * trace B - trace (A * B)) • A
        - spur A • B + (trace (A * A * B) - trace A * trace (A * B) + spur A * trace B) • 1 :=
  isCubicMinimalPolynomial.mul_mul_self_add_two_smul_mul_mul A B

/-- **Newton's formula for the determinant**, without division:
`6 det A = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))`. -/
theorem six_mul_det (A : CompactAlbertAlgebra R) :
    6 * det A = trace A ^ 3 - 3 * trace A * trace (A * A) + 2 * trace (A * (A * A)) :=
  isCubicMinimalPolynomial.six_mul_det trace_one A

/-- **Newton's formula for the determinant**: when `2` and `3` are invertible,
`det A = (T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))) / 6`. -/
theorem det_eq_invOf_two_mul_invOf_three_mul [Invertible (3 : R)] (A : CompactAlbertAlgebra R) :
    det A = ⅟2 * ⅟3 *
      (trace A ^ 3 - 3 * trace A * trace (A * A) + 2 * trace (A * (A * A))) :=
  isCubicMinimalPolynomial.det_eq_invOf_two_mul_invOf_three_mul trace_one A

end Invertible

end CompactAlbertAlgebra

end TauCeti
