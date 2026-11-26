/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlbertAlgebra.Compact.Determinant

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
computation of the identity itself is needed. The instance is
`TauCeti.Jordan.IsCubicMinimalPolynomial.isCommJordan` of
`TauCeti/Algebra/Jordan/CubicMinimalPolynomial.lean`, applied to
`TauCeti.CompactAlbertAlgebra.isCubicMinimalPolynomial`, and so follows from four facts of
`TauCeti/Algebra/AlbertAlgebra/Compact/Determinant.lean` and
`TauCeti/Algebra/AlbertAlgebra/Compact.lean`:

* the **cubic equation** `A³ = T(A) A² - S(A) A + det A · 1`
  (`TauCeti.CompactAlbertAlgebra.mul_mul_self`), with `T` the trace, `S` the spur and `A³ = A ∘ A²`;
* the **spur formula** `2 S(A) = T(A)² - T(A ∘ A)` (`TauCeti.CompactAlbertAlgebra.two_mul_spur`);
* the **associativity of the trace form**, `T((A ∘ B) ∘ C) = T(A ∘ (B ∘ C))`
  (`TauCeti.CompactAlbertAlgebra.trace_mul_assoc`);
* the **gradient of the determinant**: its derivative at `A` in the direction `B` is
  `T(A^# ∘ B)`, where `A^# = A² - T(A) A + S(A) 1` is the adjoint of `A`
  (`TauCeti.CompactAlbertAlgebra.det_add_sub_det_sub`).

The cubic equation holds for every element, so it can be polarized, and the gradient of the
determinant identifies the coefficient of `1`; this gives the **linearized cubic equation**
(`TauCeti.CompactAlbertAlgebra.mul_mul_self_add_two_smul_mul_mul`). Solving it for `B ∘ A²` writes
the multiplication operator `L_{A²}` as a polynomial in `L_A` plus an operator with values in the
span of `1`, `A` and `A²`. The commutator `⁅L_A, L_{A²}⁆` therefore takes values in that span, and
its three coefficients vanish by the cubic equation and the associativity of the trace form.

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
instance : IsCommJordan (CompactAlbertAlgebra R) :=
  isCubicMinimalPolynomial.isCommJordan

end CompactAlbertAlgebra

end TauCeti
