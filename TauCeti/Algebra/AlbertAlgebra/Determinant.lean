/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Basic

import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# The determinant of the split Albert algebra and its cubic equation

A Hermitian octonion matrix

`⟦a, x⟧ = [[a 0, x 2, conj (x 1)], [conj (x 2), a 1, x 0], [x 1, conj (x 0), a 2]]`

of the split Albert algebra `H₃(𝕆)` has a **determinant**, the cubic form

`det A = a 0 * a 1 * a 2 - a 0 * N (x 0) - a 1 * N (x 1) - a 2 * N (x 2)
  + trace ((x 0 * x 1) * x 2)`,

where `N` and `trace` are the norm and the trace of the split octonions. The octonion entry `x i`
sits opposite the diagonal entry `a i`, in position `(i + 1, i + 2)`, so each diagonal entry is
paired with the norm of the octonion entry it does not share a row or column with; the last term is
the trace of the product of the three octonion entries taken around the matrix. That trace does
not depend on the bracketing of the triple product nor on which entry the cycle starts from
(`TauCeti.Octonion.trace_mul_assoc` and `TauCeti.Octonion.trace_mul_cycle`), so the determinant
can be read off starting from any diagonal entry (`TauCeti.AlbertAlgebra.det_eq_rotate`).

Together with the trace `T` and the quadratic **spur** `S`, the sum of the principal `2 × 2` minors

`spur A = a 0 * a 1 + a 1 * a 2 + a 2 * a 0 - N (x 0) - N (x 1) - N (x 2)`,

the determinant is, up to sign, the constant term of the **generic minimal polynomial**
`t³ - T(A) t² + S(A) t - det A` of `H₃(𝕆)`, and the spur is its coefficient of `t`: every element
satisfies the cubic equation

`A ∘ (A ∘ A) = T(A) • (A ∘ A) - S(A) • A + det A • 1`

(`TauCeti.AlbertAlgebra.mul_mul_self`), the Albert-algebra analogue of the rank-two equation
`TauCeti.Octonion.mul_self` of the octonions, with powers taken in the Jordan product. Taking
traces in it, and using `2 S(A) = T(A)² - T(A ∘ A)`, gives Newton's formula for the determinant in
terms of the traces of powers, `6 det A = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))`.

The determinant and the spur are defined over every commutative ring; only the Jordan product, and
so the cubic equation, needs `2` to be invertible, and dividing Newton's formula by `6` needs `3`
to be invertible as well.

## Main definitions

* `TauCeti.AlbertAlgebra.det`: the determinant, the cubic norm form of `H₃(𝕆)`.
* `TauCeti.AlbertAlgebra.spur`: the spur, a quadratic form in `A` and the coefficient of `t` in
  the generic minimal polynomial.

## Main results

* `TauCeti.AlbertAlgebra.det_smul` and `TauCeti.AlbertAlgebra.spur_smul`: the determinant is a
  cubic and the spur a quadratic form.
* `TauCeti.AlbertAlgebra.two_mul_spur` and `TauCeti.AlbertAlgebra.spur_eq_invOf_two_mul`: the
  spur is `(T(A)² - T(A ∘ A)) / 2`.
* `TauCeti.AlbertAlgebra.mul_mul_self`: **the cubic equation** satisfied by every element.
* `TauCeti.AlbertAlgebra.six_mul_det` and
  `TauCeti.AlbertAlgebra.det_eq_invOf_two_mul_invOf_three_mul`: **Newton's formula** for the
  determinant in terms of the traces of the powers.

## References

* J. C. Baez, *The octonions*, Bull. Amer. Math. Soc. 39 (2002), §3.4, for the coordinate formula
  of the determinant and the trace formula for it.
* K. McCrimmon, *A Taste of Jordan Algebras*, Springer (2004), the chapter on Jordan algebras of
  cubic forms, for the generic minimal polynomial `t³ - T t² + S t - N` of a cubic Jordan algebra,
  its spur form `S`, and the cubic equation.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), Chapter 5.
-/

public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*}

section CommRing

variable [CommRing R]

/-- **The determinant** of a Hermitian octonion matrix, the cubic norm form of the split Albert
algebra: `a₀ a₁ a₂ - a₀ N(x₀) - a₁ N(x₁) - a₂ N(x₂) + trace ((x₀ x₁) x₂)`, with `aᵢ` the diagonal
entries and `xᵢ` the octonion entry in position `(i + 1, i + 2)`. -/
def det (A : AlbertAlgebra R) : R :=
  A.diag 0 * A.diag 1 * A.diag 2 - A.diag 0 * Octonion.norm (A.offDiag 0)
    - A.diag 1 * Octonion.norm (A.offDiag 1) - A.diag 2 * Octonion.norm (A.offDiag 2)
    + Octonion.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2)

theorem det_def (A : AlbertAlgebra R) :
    det A = A.diag 0 * A.diag 1 * A.diag 2 - A.diag 0 * Octonion.norm (A.offDiag 0)
      - A.diag 1 * Octonion.norm (A.offDiag 1) - A.diag 2 * Octonion.norm (A.offDiag 2)
      + Octonion.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2) :=
  (rfl)

/-- **The triple-product term of the determinant does not depend on where the cycle starts**:
the octonion entries can be multiplied in any cyclic order, `xᵢ xᵢ₊₁ xᵢ₊₂`. -/
theorem trace_offDiag_mul_offDiag_mul_offDiag (A : AlbertAlgebra R) (i : Fin 3) :
    Octonion.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) =
      Octonion.trace (A.offDiag 0 * A.offDiag 1 * A.offDiag 2) := by
  fin_cases i
  · rfl
  · exact Octonion.trace_mul_cycle _ _ _
  · exact (Octonion.trace_mul_cycle _ _ _).symm

/-- The determinant, read off starting from an arbitrary diagonal entry. -/
theorem det_eq_rotate (A : AlbertAlgebra R) (i : Fin 3) :
    det A = A.diag i * A.diag (i + 1) * A.diag (i + 2) - A.diag i * Octonion.norm (A.offDiag i)
      - A.diag (i + 1) * Octonion.norm (A.offDiag (i + 1))
      - A.diag (i + 2) * Octonion.norm (A.offDiag (i + 2))
      + Octonion.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
  rw [trace_offDiag_mul_offDiag_mul_offDiag, det_def]
  fin_cases i <;> simp <;> ring

@[simp] theorem det_zero : det (0 : AlbertAlgebra R) = 0 := by simp [det_def]

@[simp] theorem det_one : det (1 : AlbertAlgebra R) = 1 := by simp [det_def]

/-- **The determinant is a cubic form**: `det (r • A) = r ^ 3 * det A`. -/
@[simp] theorem det_smul (r : R) (A : AlbertAlgebra R) : det (r • A) = r ^ 3 * det A := by
  simp only [det_def, smul_diag, smul_offDiag, Pi.smul_apply, smul_eq_mul, Octonion.norm_smul,
    smul_mul_assoc, mul_smul_comm, smul_smul, map_smul]
  ring

@[simp] theorem det_neg (A : AlbertAlgebra R) : det (-A) = -det A := by
  rw [← neg_one_smul R A, det_smul]
  ring

/-- **The spur** of a Hermitian octonion matrix, the sum of its three principal `2 × 2` minors:
`a₀ a₁ + a₁ a₂ + a₂ a₀ - N(x₀) - N(x₁) - N(x₂)`. It is a quadratic form in `A` and the coefficient
of `t` in the generic minimal polynomial of the split Albert algebra
(`TauCeti.AlbertAlgebra.mul_mul_self`), and equals `(T(A)² - T(A ∘ A)) / 2` when `2` is invertible
(`TauCeti.AlbertAlgebra.spur_eq_invOf_two_mul`). -/
def spur (A : AlbertAlgebra R) : R :=
  A.diag 0 * A.diag 1 + A.diag 1 * A.diag 2 + A.diag 2 * A.diag 0
    - Octonion.norm (A.offDiag 0) - Octonion.norm (A.offDiag 1) - Octonion.norm (A.offDiag 2)

theorem spur_def (A : AlbertAlgebra R) :
    spur A = A.diag 0 * A.diag 1 + A.diag 1 * A.diag 2 + A.diag 2 * A.diag 0
      - Octonion.norm (A.offDiag 0) - Octonion.norm (A.offDiag 1)
      - Octonion.norm (A.offDiag 2) :=
  (rfl)

/-- The spur, read off starting from an arbitrary diagonal entry. -/
theorem spur_eq_rotate (A : AlbertAlgebra R) (i : Fin 3) :
    spur A = A.diag i * A.diag (i + 1) + A.diag (i + 1) * A.diag (i + 2)
      + A.diag (i + 2) * A.diag i - Octonion.norm (A.offDiag i)
      - Octonion.norm (A.offDiag (i + 1)) - Octonion.norm (A.offDiag (i + 2)) := by
  rw [spur_def]
  fin_cases i <;> simp <;> ring

@[simp] theorem spur_zero : spur (0 : AlbertAlgebra R) = 0 := by simp [spur_def]

/-- The spur of the identity matrix is `3`, one for each principal `2 × 2` minor. -/
@[simp] theorem spur_one : spur (1 : AlbertAlgebra R) = 3 := by
  norm_num [spur_def]

/-- **The spur is a quadratic form**: `spur (r • A) = r ^ 2 * spur A`. -/
@[simp] theorem spur_smul (r : R) (A : AlbertAlgebra R) : spur (r • A) = r ^ 2 * spur A := by
  simp only [spur_def, smul_diag, smul_offDiag, Pi.smul_apply, smul_eq_mul, Octonion.norm_smul]
  ring

@[simp] theorem spur_neg (A : AlbertAlgebra R) : spur (-A) = spur A := by
  rw [← neg_one_smul R A, spur_smul]
  ring

end CommRing

/-! ### The Jordan square and the cubic equation -/

section Invertible

variable [CommRing R] [Invertible (2 : R)]

/-- **Twice the spur** is `T(A)² - T(A ∘ A)`. -/
theorem two_mul_spur (A : AlbertAlgebra R) : 2 * spur A = trace A ^ 2 - trace (A * A) := by
  rw [trace_mul_self, spur_def, trace_apply]
  simp only [Fin.sum_univ_three]
  ring

/-- **The spur is half of `T(A)² - T(A ∘ A)`**, the usual coefficient of a characteristic
polynomial in terms of traces of powers. -/
theorem spur_eq_invOf_two_mul (A : AlbertAlgebra R) :
    spur A = ⅟2 * (trace A ^ 2 - trace (A * A)) := by
  rw [← two_mul_spur, invOf_mul_cancel_left]

/-- **The cubic equation of the split Albert algebra.** Every Hermitian octonion matrix is a root
of its generic minimal polynomial `t³ - T(A) t² + S(A) t - det A`, with powers taken in the Jordan
product: `A ∘ (A ∘ A) = T(A) • (A ∘ A) - S(A) • A + det A • 1`. -/
theorem mul_mul_self (A : AlbertAlgebra R) :
    A * (A * A) = trace A • (A * A) - spur A • A + det A • 1 := by
  -- The products of the octonion entries that occur cancel to norms by conjugate cancellation, and
  -- the two triple products on the diagonal are the triple-product term of the determinant. What
  -- is left in each entry is a polynomial identity in the entries and in the half `⅟2` of the
  -- Jordan product; `linear_combination` closes it from `⅟2 + ⅟2 = 1`, the coefficient of `h2`
  -- being the total weight of the halved terms.
  have h2 : (⅟2 : R) + ⅟2 = 1 := invOf_two_add_invOf_two
  refine AlbertAlgebra.ext (funext fun i => ?_) (funext fun i => ?_)
  · have ht₁ : Octonion.trace (A.offDiag (i + 1) * (A.offDiag (i + 2) * A.offDiag i)) =
        Octonion.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
      rw [← Octonion.trace_mul_assoc, Octonion.trace_mul_cycle]
    have ht₂ : Octonion.trace (A.offDiag (i + 2) * (A.offDiag i * A.offDiag (i + 1))) =
        Octonion.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) := by
      rw [Octonion.trace_mul_comm]
    rw [mul_diag, mul_self_diag, mul_self_offDiag, mul_self_offDiag]
    simp only [add_one_add_one_fin_three, add_one_add_two_fin_three, add_two_add_one_fin_three,
      add_two_add_two_fin_three, map_add, map_smul, smul_eq_mul,
      QuadraticMap.associated_eq_self_apply, Octonion.normQuadraticForm_apply,
      Octonion.associated_normQuadraticForm_apply, Octonion.conj_conj, ht₁, ht₂, add_diag,
      sub_diag, smul_diag, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, one_diag, Pi.one_apply,
      mul_one, mul_self_diag, trace_apply, sum_fin_three_rotate _ i]
    rw [spur_eq_rotate A i, det_eq_rotate A i]
    linear_combination
      Octonion.trace (A.offDiag i * A.offDiag (i + 1) * A.offDiag (i + 2)) * h2
  · rw [mul_offDiag, mul_self_diag, mul_self_diag, mul_self_offDiag, mul_self_offDiag,
      mul_self_offDiag]
    simp only [add_one_add_one_fin_three, add_one_add_two_fin_three, add_two_add_one_fin_three,
      add_two_add_two_fin_three, mul_add, add_mul, smul_mul_assoc, mul_smul_comm,
      Octonion.mul_conj_mul_self, Octonion.conj_mul_mul_self, map_add, map_smul,
      Octonion.conj_conj, add_offDiag, sub_offDiag, smul_offDiag, one_offDiag, Pi.add_apply,
      Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_zero, add_zero,
      trace_apply, sum_fin_three_rotate _ i, mul_self_offDiag]
    rw [spur_eq_rotate A i]
    linear_combination (norm := module)
      (A.diag (i + 1) ^ 2 + A.diag (i + 1) * A.diag (i + 2) + A.diag (i + 2) ^ 2
        + Octonion.norm (A.offDiag i) + Octonion.norm (A.offDiag (i + 1))
        + Octonion.norm (A.offDiag (i + 2))) • h2 • A.offDiag i
      + (A.diag i + A.diag (i + 1) + A.diag (i + 2)) • h2 •
        Octonion.conj (A.offDiag (i + 1) * A.offDiag (i + 2))

/-- **Newton's formula for the determinant**, without division:
`6 det A = T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))`. -/
theorem six_mul_det (A : AlbertAlgebra R) :
    6 * det A = trace A ^ 3 - 3 * trace A * trace (A * A) + 2 * trace (A * (A * A)) := by
  have h := congrArg trace (mul_mul_self A)
  rw [map_add, map_sub, map_smul, map_smul, map_smul, trace_one, smul_eq_mul, smul_eq_mul,
    smul_eq_mul] at h
  linear_combination (-2) * h + trace A * two_mul_spur A

/-- **Newton's formula for the determinant**: when `2` and `3` are invertible,
`det A = (T(A)³ - 3 T(A) T(A ∘ A) + 2 T(A ∘ (A ∘ A))) / 6`. -/
theorem det_eq_invOf_two_mul_invOf_three_mul [Invertible (3 : R)] (A : AlbertAlgebra R) :
    det A = ⅟2 * ⅟3 *
      (trace A ^ 3 - 3 * trace A * trace (A * A) + 2 * trace (A * (A * A))) := by
  rw [← six_mul_det]
  linear_combination
    (-(3 * ⅟3 * det A)) * mul_invOf_self (2 : R) - det A * mul_invOf_self (3 : R)

end Invertible

end AlbertAlgebra

end TauCeti
