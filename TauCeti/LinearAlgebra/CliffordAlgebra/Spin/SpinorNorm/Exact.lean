/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.SpinorNorm.DoubleCover

/-!
# The exact Spin comparison sequence

For a finite-dimensional nondegenerate quadratic space over a field in which `2` is invertible,
the Spin comparison sequence is exact at the Spin group and at the special orthogonal group.
Exactness at Spin uses the positive-dimensional identification of the kernel with `ZMod 2`, while
exactness at the special orthogonal group also covers the zero-dimensional case.

## Main results

* `CliffordAlgebra.mulExact_spinDoubleCoverSpinorNormKernel_inl_spinToSpecialOrthogonal` states
  exactness at the Spin group.
* `CliffordAlgebra.mulExact_spinToSpecialOrthogonal_spinorNorm` states exactness at the special
  orthogonal group.

## References

See T. Y. Lam, *Introduction to Quadratic Forms over Fields* (2005), Chapter V, §5.
-/

public section

open QuadraticMap

namespace CliffordAlgebra

open TauCeti

universe u v

variable {K : Type u} {V : Type v} [Field K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Invertible (2 : K)]

/-- For a positive-dimensional nondegenerate quadratic space, the inclusion of `ZMod 2` as the
kernel of the Spin action and the Spin action form an exact pair. -/
theorem mulExact_spinDoubleCoverSpinorNormKernel_inl_spinToSpecialOrthogonal
    [Nontrivial V] (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.MulExact (spinDoubleCoverSpinorNormKernel Q hQ).inl
      (spinToSpecialOrthogonal Q) := by
  rw [MonoidHom.mulExact_iff]
  rw [← ker_spinToSpinorNormKernel Q hQ,
    ← spinDoubleCoverSpinorNormKernel_rightHom Q hQ]
  exact (spinDoubleCoverSpinorNormKernel Q hQ).range_inl_eq_ker_rightHom.symm

/-- The Spin action and the spinor norm form an exact pair at the special orthogonal group. -/
theorem mulExact_spinToSpecialOrthogonal_spinorNorm
    (Q : QuadraticForm K V) (hQ : Q.Nondegenerate) :
    Function.MulExact (spinToSpecialOrthogonal Q) (spinorNorm Q hQ) := by
  simpa only [Function.MulExact, ← MonoidHom.mem_ker, MonoidHom.mem_range,
    Set.mem_range] using
    SetLike.ext_iff.mp (range_spinToSpecialOrthogonal_eq_ker_spinorNorm Q hQ).symm

end CliffordAlgebra
