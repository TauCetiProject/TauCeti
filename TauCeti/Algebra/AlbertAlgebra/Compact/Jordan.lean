/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Jordan.Basic
public import TauCeti.Algebra.AlbertAlgebra.Compact.Determinant

import Mathlib.Tactic.LinearCombination

/-!
# The Jordan identity of the compact Albert algebra

The compact Albert algebra `J = H₃(𝕆)` of `TauCeti/Algebra/AlbertAlgebra/Compact.lean`, the
Hermitian `3 × 3` matrices over the Cayley–Dickson double of the quaternions under the symmetrized
product, is commutative, and this file proves that it satisfies the **Jordan identity**

`(A ∘ B) ∘ A² = A ∘ (B ∘ A²)`,

that is, `IsCommJordan (CompactAlbertAlgebra R)`, over every commutative ring `R` in which `2` is
invertible. Over `ℝ` this makes `CompactAlbertAlgebra ℝ` the exceptional formally real Jordan
algebra of Jordan, von Neumann and Wigner, and Mathlib's Jordan-algebra API (`IsJordan`,
`commute_lmul_lmul_sq` and the linearized Jordan identities) applies to it.

As for the split Albert algebra in `TauCeti/Algebra/AlbertAlgebra/Jordan.lean`, no coordinate
computation of the identity itself is needed. It follows from three facts of
`TauCeti/Algebra/AlbertAlgebra/Compact/Determinant.lean` and
`TauCeti/Algebra/AlbertAlgebra/Compact.lean`:

* the **cubic equation** `A³ = T(A) A² - S(A) A + det A · 1`
  (`TauCeti.CompactAlbertAlgebra.mul_mul_self`), with `T` the trace, `S` the spur and `A³ = A ∘ A²`;
* its polarization, the **linearized cubic equation**
  (`TauCeti.CompactAlbertAlgebra.mul_mul_self_add_two_smul_mul_mul`), which writes the
  multiplication operator `L_{A²}` as a polynomial in `L_A` plus an operator with values in the
  span of `1`, `A` and `A²`;
* the **associativity of the trace form**, `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`
  (`TauCeti.CompactAlbertAlgebra.trace_mul_assoc`).

The commutator `⁅L_A, L_{A²}⁆` therefore takes values in the span of `1`, `A` and `A²`, and its
three coefficients vanish by the cubic equation and the associativity of the trace form.

## Main results

* the `IsCommJordan (CompactAlbertAlgebra R)` instance: the Jordan identity.

## References

* P. Jordan, J. von Neumann and E. Wigner, *On an algebraic generalization of the quantum
  mechanical formalism*, Ann. of Math. **35** (1934), 29–64.
* K. McCrimmon, *A Taste of Jordan Algebras*, Springer (2004), the chapter on Jordan algebras of
  cubic forms, for the derivation of the Jordan identity from the cubic equation.
* T. A. Springer and F. D. Veldkamp, *Octonions, Jordan Algebras and Exceptional Groups*,
  Springer (2000), Chapter 5.
-/

public section

namespace TauCeti

namespace CompactAlbertAlgebra

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- **The compact Albert algebra is a Jordan algebra**: `(A ∘ B) ∘ A² = A ∘ (B ∘ A²)`. -/
instance : IsCommJordan (CompactAlbertAlgebra R) where
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
      hL - hM - trace B • hC - hA₁ • A + (hT - hA₂ + trace A * hA₁) • (1 : CompactAlbertAlgebra R)

end CompactAlbertAlgebra

end TauCeti
