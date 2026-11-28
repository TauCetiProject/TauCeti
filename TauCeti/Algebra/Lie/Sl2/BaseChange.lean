/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.BaseChange
public import Mathlib.Algebra.Lie.Sl2

/-!
# Base change of `sl₂` triples

This file records that extending scalars of a Lie algebra `L` along a commutative algebra
`R → A` carries an `sl₂` triple `(h, e, f)` in `L` to an `sl₂` triple `(1 ⊗ h, 1 ⊗ e, 1 ⊗ f)` in
`A ⊗[R] L`, provided `1 ⊗ h ≠ 0`.

## Main results

* `IsSl2Triple.baseChange`: scalar extension of an `sl₂` triple to `A ⊗[R] L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, §7.2.
-/

public section

open scoped TensorProduct

/-- **Scalar extension of an `sl₂` triple** to `A ⊗[R] L` when `1 ⊗ₜ h ≠ 0`. -/
theorem IsSl2Triple.baseChange {R A L : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [LieRing L] [LieAlgebra R L] {h e f : L} (t : IsSl2Triple h e f)
    (hh : ((1 : A) ⊗ₜ[R] h : A ⊗[R] L) ≠ 0) :
    IsSl2Triple ((1 : A) ⊗ₜ[R] h) ((1 : A) ⊗ₜ[R] e) ((1 : A) ⊗ₜ[R] f) :=
  ⟨hh, by simp [t.lie_e_f], by simp [t.lie_h_e_nsmul], by
    simp [t.lie_h_f_nsmul, two_nsmul, TensorProduct.tmul_add, TensorProduct.tmul_neg]⟩
