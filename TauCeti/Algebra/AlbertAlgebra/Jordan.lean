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
  `T(A^# ∘ B)`, where `A^# = A² - T(A) A + S(A) 1` is the adjoint of `A`
  (`TauCeti.AlbertAlgebra.det_add_sub_det_sub`).

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
