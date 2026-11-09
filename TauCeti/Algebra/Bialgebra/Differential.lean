/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: pi
-/
module

public import TauCeti.Algebra.Bialgebra.Primitive
public import Mathlib.RingTheory.Bialgebra.Primitive
public import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The obstruction to an ordinary differential bialgebra

A nonzero square-zero primitive element in a bialgebra over a field forces
characteristic two. Thus a square-zero differential cannot be modeled by an
ordinary primitive Hopf-algebra generator in other characteristics: its tensor
product differential needs a sign, rather than the ordinary tensor multiplication.
Neither an antipode nor finite dimensionality is needed for the obstruction.

The calculation uses `TauCeti.Bialgebra.comul_pow_of_primitive`: the two mixed
terms in the coproduct of the square are both `d ⊗ d`. A linear functional
taking value one on `d` detects their sum without a choice of basis.

## References

* M. Khovanov, *Hopfological algebra and categorification at a root of unity:
  the first steps*, §1, for the characteristic-two square-zero Hopf algebra
  and its relation to complexes.
-/

public section

open scoped TensorProduct

namespace Bialgebra.IsPrimitiveElem

variable {k A : Type*} [Field k] [Ring A] [Bialgebra k A] {d : A}

/-- A nonzero square-zero primitive element forces characteristic two. -/
theorem two_eq_zero_of_sq_eq_zero (hd : Bialgebra.IsPrimitiveElem k d)
    (hd0 : d ≠ 0) (hsq : d ^ 2 = 0) : (2 : k) = 0 := by
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one k hd0
  have hΔ := TauCeti.Bialgebra.comul_pow_of_primitive d
    (by simpa only [add_comm] using hd.comul_eq_tmul_add_tmul) 2
  have h := congrArg (fun t : A ⊗[k] A =>
    TensorProduct.lid k k (TensorProduct.map f f t)) hΔ
  simpa [hsq, Finset.Nat.antidiagonal_succ, ← Nat.cast_smul_eq_nsmul k, hf] using h.symm

/-- Outside characteristic two a square-zero primitive element is zero.
In particular, the usual square-zero differential generator cannot be primitive
in an ordinary Hopf algebra over such a field. -/
theorem eq_zero_of_sq_eq_zero (hd : Bialgebra.IsPrimitiveElem k d)
    (h2 : (2 : k) ≠ 0) (hsq : d ^ 2 = 0) : d = 0 := by
  by_contra hd0
  exact h2 (hd.two_eq_zero_of_sq_eq_zero hd0 hsq)

end Bialgebra.IsPrimitiveElem
