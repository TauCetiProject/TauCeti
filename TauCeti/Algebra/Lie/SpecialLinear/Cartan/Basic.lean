/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import TauCeti.Algebra.Lie.CartanInvolution.Decomposition
public import TauCeti.Algebra.Lie.Matrix.NegTranspose

import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Regular.SMul
import TauCeti.LinearAlgebra.Matrix.Alternating.Basic

/-!
# Negative transpose on the special linear Lie algebra

The special linear Lie algebra `sl n R` is stable under negative transpose. Restricting the matrix
Lie automorphism `TauCeti.negTransposeLieEquiv` via `LieSubalgebra.restrictNegTranspose` gives the
involutive automorphism `X ↦ -Xᵀ` (`LieAlgebra.SpecialLinear.cartanInvolution`) over every
commutative ring. Its fixed vectors are the skew-symmetric trace-zero matrices
(`LieAlgebra.SpecialLinear.mem_fixedSubalgebra_cartanInvolution_iff`, matching
`LieAlgebra.Orthogonal.so n R` via
`LieAlgebra.SpecialLinear.map_incl_fixedSubalgebra_cartanInvolution` whenever scaling by `2` is
injective), and its `-1`-eigenspace consists of the symmetric trace-zero matrices
(`LieAlgebra.SpecialLinear.mem_cartanP_cartanInvolution_iff`).

## Main definitions

* `LieAlgebra.SpecialLinear.cartanInvolution`: the negative-transpose involution `X ↦ -Xᵀ` on
  `sl n R`.

## Main results

* `LieAlgebra.SpecialLinear.mem_fixedSubalgebra_cartanInvolution_iff`: fixed vectors are the
  skew-symmetric matrices in `sl n R`.
* `LieAlgebra.SpecialLinear.mem_cartanP_cartanInvolution_iff`: the `-1`-eigenspace `cartanP`
  consists of the symmetric matrices in `sl n R`.
* `LieAlgebra.SpecialLinear.map_incl_fixedSubalgebra_cartanInvolution`: when scaling by `2` is
  regular on `R`, the fixed subalgebra maps onto `LieAlgebra.Orthogonal.so n R`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics 140,
  Birkhäuser, 2002, Chapter VI, §1–2.
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n] {R : Type*} [CommRing R]

attribute [local instance 100] LieRing.ofAssociativeRing

variable (n R)

/-- The involutive Lie automorphism `X ↦ -Xᵀ` of the special linear Lie algebra `sl n R`. -/
def cartanInvolution : sl n R ≃ₗ⁅R⁆ sl n R :=
  (sl n R).restrictNegTranspose fun X hX ↦ by
    rw [mem_sl_iff, trace_transpose, mem_sl_iff.mp hX]

variable {n R}

/-- The matrix value of `SpecialLinear.cartanInvolution` is negative transpose. -/
@[simp]
theorem coe_cartanInvolution (X : sl n R) :
    (cartanInvolution n R X : Matrix n n R) = -(X : Matrix n n R)ᵀ :=
  (sl n R).coe_restrictNegTranspose_apply _ X

/-- Applying `SpecialLinear.cartanInvolution` twice returns the original matrix. -/
@[simp]
theorem cartanInvolution_cartanInvolution (X : sl n R) :
    cartanInvolution n R (cartanInvolution n R X) = X :=
  (sl n R).restrictNegTranspose_restrictNegTranspose _ X

/-- `SpecialLinear.cartanInvolution` is its own inverse. -/
@[simp]
theorem cartanInvolution_symm : (cartanInvolution n R).symm = cartanInvolution n R :=
  (sl n R).restrictNegTranspose_symm _

/-- Fixed vectors of `SpecialLinear.cartanInvolution` are the skew-symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_self_iff (X : sl n R) :
    cartanInvolution n R X = X ↔ (X : Matrix n n R)ᵀ = -(X : Matrix n n R) :=
  (sl n R).restrictNegTranspose_eq_self_iff _ X

/-- Negated vectors of `SpecialLinear.cartanInvolution` are the symmetric trace-zero matrices. -/
@[simp]
theorem cartanInvolution_eq_neg_iff (X : sl n R) :
    cartanInvolution n R X = -X ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) :=
  (sl n R).restrictNegTranspose_eq_neg_iff _ X

/-- Fixed vectors of `SpecialLinear.cartanInvolution` are the skew-symmetric matrices in
`sl n R`. -/
theorem mem_fixedSubalgebra_cartanInvolution_iff (X : sl n R) :
    X ∈ (cartanInvolution n R).toLieHom.fixedSubalgebra ↔
      (X : Matrix n n R)ᵀ = -(X : Matrix n n R) := by
  rw [LieHom.mem_fixedSubalgebra, LieEquiv.coe_toLieHom, cartanInvolution_eq_self_iff]

/-- The `-1`-eigenspace of `SpecialLinear.cartanInvolution` consists of the symmetric matrices in
`sl n R`. -/
theorem mem_cartanP_cartanInvolution_iff (X : sl n R) :
    X ∈ (cartanInvolution n R).cartanP ↔ (X : Matrix n n R)ᵀ = (X : Matrix n n R) := by
  rw [LieEquiv.mem_cartanP, cartanInvolution_eq_neg_iff]

/-- When scaling by `2` is injective on `R`, the fixed subalgebra of
`SpecialLinear.cartanInvolution` embeds onto `LieAlgebra.Orthogonal.so n R`. -/
theorem map_incl_fixedSubalgebra_cartanInvolution (h2 : IsSMulRegular R (2 : R)) :
    (cartanInvolution n R).toLieHom.fixedSubalgebra.map (sl n R).incl =
      LieAlgebra.Orthogonal.so n R := by
  ext A
  rw [LieSubalgebra.mem_map, LieAlgebra.Orthogonal.mem_so]
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact (mem_fixedSubalgebra_cartanInvolution_iff X).mp hX
  · intro hA
    have htr : A.trace = 0 :=
      Matrix.trace_eq_zero_of_transpose_eq_neg_of_add_self A hA fun _ ↦ h2.eq_zero_of_add_self
    exact ⟨⟨A, mem_sl_iff.mpr htr⟩,
      (mem_fixedSubalgebra_cartanInvolution_iff _).mpr hA, rfl⟩

end LieAlgebra.SpecialLinear
