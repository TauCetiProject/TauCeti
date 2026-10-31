/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import TauCeti.Algebra.AlbertAlgebra.Determinant

import Mathlib.Tactic.LinearCombination

/-!
# The Jordan identity of the split Albert algebra

The split Albert algebra `J = H₃(𝕆)` of `TauCeti/Algebra/AlbertAlgebra/Basic.lean` is commutative,
and this file proves that it satisfies the **Jordan identity**

`(A ∘ B) ∘ A² = A ∘ (B ∘ A²)`,

that is, `IsCommJordan (AlbertAlgebra R)`, over every commutative ring `R` in which `2` is
invertible. So `H₃(𝕆)` is a Jordan algebra, the exceptional one, and Mathlib's Jordan-algebra
API (`IsJordan`, `commute_lmul_lmul_sq` and the linearized Jordan identities) applies to it. In a
Jordan algebra the commutator `⁅L_A, L_B⁆` of two multiplication operators is a derivation, so the
Jordan identity is what produces derivations of `J` beyond those induced from the octonions.

No coordinate computation of the identity itself is needed. Everything comes from three facts:

* the **cubic equation** `A³ = T(A) A² - S(A) A + det A · 1` of
  `TauCeti/Algebra/AlbertAlgebra/Determinant.lean` (`TauCeti.AlbertAlgebra.mul_mul_self`), with
  `T` the trace, `S` the spur and `A³ = A ∘ A²`;
* the **associativity of the trace form**, `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`
  (`TauCeti.AlbertAlgebra.trace_mul_assoc`);
* the **gradient of the determinant**: its derivative at `A` in the direction `B` is
  `T(A^# ∘ B)`, where `A^# = A² - T(A) A + S(A) 1` is the adjoint of `A`.

The cubic equation holds for every element, so it can be polarized: comparing it at `A + B`,
`A - B` and `B` gives the **linearized cubic equation**
(`TauCeti.AlbertAlgebra.mul_mul_self_add_two_smul_mul_mul`)

`B ∘ A² + 2 A ∘ (A ∘ B) = T(B) A² + 2 T(A) A ∘ B - (T(A) T(B) - T(A ∘ B)) A - S(A) B
  + T(A^# ∘ B) 1`.

Solving it for `B ∘ A²` writes the multiplication operator `L_{A²}` as a polynomial in `L_A`
plus an operator with values in the span of `1`, `A` and `A²`. The commutator `⁅L_A, L_{A²}⁆`
therefore takes values in that span, and its three coefficients vanish by the cubic equation and
the associativity of the trace form.

## Main results

* `TauCeti.AlbertAlgebra.mul_mul_self_add_two_smul_mul_mul`: the linearized cubic equation.
* the `IsCommJordan (AlbertAlgebra R)` instance: the Jordan identity.

## References

* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), Chapter 5, for `H₃(𝕆)` as a Jordan algebra.
* K. McCrimmon, *A Taste of Jordan Algebras*, Springer (2004), the chapter on Jordan algebras of
  cubic forms, for the generic minimal polynomial, the trace form and the adjoint `A^#`.
-/

public section

namespace TauCeti

namespace AlbertAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- **The gradient of the determinant**, in polarized form: the part of `det (A + B)` linear in
`B` is `T(A^# ∘ B) = T(A² ∘ B) - T(A) T(A ∘ B) + S(A) T(B)`. -/
private theorem det_add_sub_det_sub (A B : AlbertAlgebra R) :
    det (A + B) - det (A - B) - 2 * det B =
      2 * (trace (A * A * B) - trace A * trace (A * B) + spur A * trace B) := by
  have hadd (x y : Octonion R) : Octonion.norm (x + y) = Octonion.norm x + Octonion.norm y
      + QuadraticMap.polar (Octonion.normQuadraticForm R) x y := by
    simpa only [Octonion.normQuadraticForm_apply] using
      QuadraticMap.map_add (Octonion.normQuadraticForm R) x y
  have hsub (x y : Octonion R) : Octonion.norm (x - y) = Octonion.norm x + Octonion.norm y
      - QuadraticMap.polar (Octonion.normQuadraticForm R) x y := by
    rw [sub_eq_add_neg, hadd, Octonion.norm_neg, QuadraticMap.polar_neg_right, sub_eq_add_neg]
  -- In coordinates, after rotating every octonion triple product to begin with an entry in
  -- slot `0`, both sides are the same polynomial.
  rw [trace_mul, trace_mul]
  simp only [det_def, spur_def, trace_apply, mul_self_diag, mul_self_offDiag, add_diag, sub_diag,
    add_offDiag, sub_offDiag, Pi.add_apply, Pi.sub_apply, hadd, hsub, Fin.sum_univ_three,
    Fin.reduceAdd, QuadraticMap.polar_add_left, QuadraticMap.polar_smul_left, smul_eq_mul,
    Octonion.polar_normQuadraticForm_conj_left, add_mul, mul_add, sub_mul, mul_sub, map_add,
    map_sub, ← Octonion.trace_mul_assoc, Octonion.trace_mul_cycle _ _ (A.offDiag 0),
    fun x y => (Octonion.trace_mul_cycle (A.offDiag 0) y x).symm]
  ring

/-- **The linearized cubic equation** of the split Albert algebra: the part linear in `B` of the
cubic equation `TauCeti.AlbertAlgebra.mul_mul_self` at `A + B`,
`B ∘ A² + 2 A ∘ (A ∘ B) = T(B) A² + 2 T(A) A ∘ B - (T(A) T(B) - T(A ∘ B)) A - S(A) B
  + T(A^# ∘ B) 1`, with `T(A^# ∘ B) = T(A² ∘ B) - T(A) T(A ∘ B) + S(A) T(B)`. -/
theorem mul_mul_self_add_two_smul_mul_mul (A B : AlbertAlgebra R) :
    B * (A * A) + (2 : R) • (A * (A * B)) =
      trace B • (A * A) + (2 * trace A) • (A * B) - (trace A * trace B - trace (A * B)) • A
        - spur A • B + (trace (A * A * B) - trace A * trace (A * B) + spur A * trace B) • 1 := by
  -- The cubic equation at `A + B`, minus the one at `A - B`, minus twice the one at `B`, is twice
  -- the claimed identity.
  have h₁ := mul_mul_self (A + B)
  have h₂ := mul_mul_self (A - B)
  rw [spur_add] at h₁
  rw [spur_sub] at h₂
  simp only [add_mul, mul_add, sub_mul, mul_sub, mul_comm B A, map_add, map_sub] at h₁ h₂
  apply (isUnit_of_invertible (2 : R)).smul_left_cancel.mp
  linear_combination (norm := module)
    h₁ - h₂ - (2 : R) • mul_mul_self B + det_add_sub_det_sub A B • (1 : AlbertAlgebra R)

/-- **The split Albert algebra is a Jordan algebra**: `(A ∘ B) ∘ A² = A ∘ (B ∘ A²)`. -/
instance : IsCommJordan (AlbertAlgebra R) where
  lmul_comm_rmul_rmul A B := by
    -- The linearized cubic equation at `(A, A ∘ B)`, and `A` times the one at `(A, B)`, express
    -- the two sides through `A ∘ (A ∘ (A ∘ B))`, which cancels. What is left is a combination of
    -- `A²`, `A` and `1`. Its `A²`-coefficient vanishes identically, and its `A`- and
    -- `1`-coefficients vanish by the cubic equation and the associativity of the trace form.
    have hL := mul_mul_self_add_two_smul_mul_mul A (A * B)
    have hM := congrArg (A * ·) (mul_mul_self_add_two_smul_mul_mul A B)
    simp only [mul_add, mul_sub, mul_smul_comm, mul_one] at hM
    have hC := mul_mul_self A
    have hT := congrArg (fun C => trace (C * B)) hC
    simp only [add_mul, sub_mul, smul_mul_assoc, one_mul, map_add, map_sub, map_smul,
      smul_eq_mul] at hT
    have hA₁ := trace_mul_assoc A A B
    have hA₂ := trace_mul_assoc (A * A) A B
    rw [mul_comm (A * A) A] at hA₂
    linear_combination (norm := module)
      hL - hM - trace B • hC - hA₁ • A + (hT - hA₂ + trace A * hA₁) • (1 : AlbertAlgebra R)

end AlbertAlgebra

end TauCeti
