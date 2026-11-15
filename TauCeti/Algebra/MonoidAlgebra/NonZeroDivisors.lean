/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GroupWithZero.NonZeroDivisors
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Monomial nonzerodivisors in cancellative monoid algebras

Over any semiring `R`, every coefficient-one monomial in the algebra of a cancellative monoid `M`
is a two-sided nonzerodivisor, because left and right multiplication by `single m 1` shift
coefficients injectively along `m * ·` and `· * m`. Consequently, the multiplicative range of
`MonoidAlgebra.of R M` (and of `AddMonoidAlgebra.of R M` for a cancellative additive monoid)
consists of nonzerodivisors, with no commutativity or domain assumption on `R` or `M`.

## Main results

* `TauCeti.MonoidAlgebra.single_one_mem_nonZeroDivisors` and
  `TauCeti.AddMonoidAlgebra.single_one_mem_nonZeroDivisors`: in the algebra of a cancellative
  (additive) monoid over any semiring, every coefficient-one monomial is a nonzerodivisor.
* `TauCeti.MonoidAlgebra.mrange_of_le_nonZeroDivisors` and
  `TauCeti.AddMonoidAlgebra.mrange_of_le_nonZeroDivisors`: the multiplicative range of `of R M` is
  contained in `nonZeroDivisors` whenever `M` is cancellative.
-/

public section

namespace TauCeti

/-- Over any semiring `R`, every coefficient-one monomial in the algebra of a cancellative monoid
`M` is a two-sided nonzerodivisor. -/
@[to_additive (dont_translate := R) TauCeti.AddMonoidAlgebra.single_one_mem_nonZeroDivisors
/-- Over any semiring `R`, every coefficient-one monomial in the algebra of a cancellative additive
monoid `M` is a two-sided nonzerodivisor. -/]
theorem MonoidAlgebra.single_one_mem_nonZeroDivisors (R : Type*) [Semiring R] {M : Type*}
    [Monoid M] [IsCancelMul M] (m : M) :
    _root_.MonoidAlgebra.single m (1 : R) ∈ nonZeroDivisors (_root_.MonoidAlgebra R M) := by
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · ext b
    simpa [_root_.MonoidAlgebra.coeff_single_mul_mul] using congr(($hx).coeff (m * b))
  · ext b
    simpa [_root_.MonoidAlgebra.coeff_mul_single_mul] using congr(($hx).coeff (b * m))

/-- Over any semiring `R`, the multiplicative range of `MonoidAlgebra.of R M` consists of
nonzerodivisors whenever `M` is cancellative. -/
theorem MonoidAlgebra.mrange_of_le_nonZeroDivisors (R M : Type*) [Semiring R] [Monoid M]
    [IsCancelMul M] :
    MonoidHom.mrange (_root_.MonoidAlgebra.of R M) ≤
      nonZeroDivisors (_root_.MonoidAlgebra R M) := by
  rintro _ ⟨m, rfl⟩
  exact single_one_mem_nonZeroDivisors R m

/-- Over any semiring `R`, the multiplicative range of `AddMonoidAlgebra.of R M` consists of
nonzerodivisors whenever `M` is cancellative. -/
theorem AddMonoidAlgebra.mrange_of_le_nonZeroDivisors (R M : Type*) [Semiring R] [AddMonoid M]
    [IsCancelAdd M] :
    MonoidHom.mrange (_root_.AddMonoidAlgebra.of R M) ≤
      nonZeroDivisors (_root_.AddMonoidAlgebra R M) := by
  rintro _ ⟨m, rfl⟩
  exact single_one_mem_nonZeroDivisors R (Multiplicative.toAdd m)

end TauCeti
