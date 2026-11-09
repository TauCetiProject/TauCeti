/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Quaternion.SquareSplit
import Mathlib.Tactic.FinCases

/-!
# Split quaternion algebras

This file constructs explicit algebra equivalences from split quaternion algebras to two-by-two
matrix algebras, over a commutative ring in which two is invertible.

For a unit `b`, the symbol algebra `ℍ[R,1,b]` is split. The equivalence is the case `a = 1` of
`TauCeti.QuaternionAlgebra.firstSquareEquivMatrix` for the symbol `(a²,b)`, and sends its
standard generators to

```text
i ↦ !![1, 0; 0, -1],   j ↦ !![0, b; 1, 0].
```

For a unit `a`, the symbol algebra `ℍ[R,a,-a]` is split. The equivalence sends its standard
generators to

```text
i ↦ !![0, a; 1, 0],   j ↦ !![0, -a; 1, 0].
```

Their squares are respectively `a` and `-a`, and they anticommute. This is one of the standard
symbol relations for quaternion algebras, useful for reducing identities involving the symbol
`(a, -a)` to computations in a matrix algebra.

The formulas for the equivalences and their inverses are recorded entrywise, so later splitting
arguments can use the constructions without unfolding the quaternion-basis implementation.

## Main definitions

* `TauCeti.QuaternionAlgebra.oneEquivMatrix`: the equivalence
  `ℍ[R,1,b] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R` for a unit `b`.
* `TauCeti.QuaternionAlgebra.aNegAEquivMatrix`: the equivalence
  `ℍ[R,a,-a] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R` for a unit `a`.

## References

* T. Y. Lam, *Introduction to Quadratic Forms over Fields*, Chapter III, Section 2.11.
-/

public section

open scoped Matrix Quaternion

namespace TauCeti

namespace QuaternionAlgebra

variable {R : Type*} [CommRing R]

section One

variable [Invertible (2 : R)]

/-- The explicit splitting `ℍ[R,1,b] ≃ₐ[R] M₂(R)` for a unit `b` over a commutative ring in
which two is invertible: the case `a = 1` of `firstSquareEquivMatrix`, after rewriting the first
parameter `1` as `1²`. It sends the quaternion generators `i` and `j` to `!![1, 0; 0, -1]` and
`!![0, b; 1, 0]`, respectively. -/
noncomputable def oneEquivMatrix (b : Rˣ) : ℍ[R,1,(b : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  (AlgEquiv.cast (A := fun t => ℍ[R,t,(b : R)]) (by simp : (1 : R) = ((1 : Rˣ) : R) ^ 2)).trans
    (firstSquareEquivMatrix 1 b)

/-- The splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem oneEquivMatrix_apply (b : Rˣ) (q : ℍ[R,1,(b : R)]) :
    oneEquivMatrix b q =
      !![q.re + q.imI, (b : R) * (q.imJ + q.imK);
        q.imJ - q.imK, q.re - q.imI] := by
  have hcast : ∀ {t : R} (h : (1 : R) = t),
      AlgEquiv.cast (R := R) (A := fun t => ℍ[R,t,(b : R)]) h q =
        ⟨q.re, q.imI, q.imJ, q.imK⟩ := by
    rintro _ rfl
    rfl
  rw [oneEquivMatrix, AlgEquiv.trans_apply, hcast, firstSquareEquivMatrix_apply]
  simp [mul_add]

/-- The inverse splitting equivalence recovers the four quaternion coordinates from the four
matrix entries. -/
@[simp]
theorem oneEquivMatrix_symm_apply (b : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (oneEquivMatrix b).symm M =
      ⟨⅟2 * (M 0 0 + M 1 1), ⅟2 * (M 0 0 - M 1 1),
        ⅟2 * (↑b⁻¹ * M 0 1 + M 1 0), ⅟2 * (↑b⁻¹ * M 0 1 - M 1 0)⟩ := by
  have hcast : ∀ {t : R} (h : (1 : R) = t) (q : ℍ[R,t,(b : R)]),
      (AlgEquiv.cast (R := R) (A := fun t => ℍ[R,t,(b : R)]) h).symm q =
        ⟨q.re, q.imI, q.imJ, q.imK⟩ := by
    rintro _ rfl q
    rfl
  rw [oneEquivMatrix, AlgEquiv.symm_trans_apply, hcast, firstSquareEquivMatrix_symm_apply]
  ext <;> simp [← mul_neg]

end One

section ANegA

private def aNegAMatrixBasis (a : R) :
    _root_.QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) R) a 0 (-a) where
  i := !![0, a; 1, 0]
  j := !![0, -a; 1, 0]
  k := !![a, 0; 0, -a]
  i_mul_i := by simp [Matrix.one_fin_two]
  j_mul_j := by simp [Matrix.one_fin_two]
  i_mul_j := by simp
  j_mul_i := by simp

private theorem aNegAMatrixBasis_liftHom_apply (a : R) (q : ℍ[R,a,-a]) :
    (aNegAMatrixBasis a).liftHom q =
      !![q.re + a * q.imK, a * (q.imI - q.imJ);
        q.imI + q.imJ, q.re - a * q.imK] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [aNegAMatrixBasis, _root_.QuaternionAlgebra.Basis.liftHom,
      _root_.QuaternionAlgebra.Basis.lift, Algebra.algebraMap_eq_smul_one] <;> ring

variable [Invertible (2 : R)]

private def aNegAMatrixInverse (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    ℍ[R,(a : R),-(a : R)] :=
  ⟨⅟2 * (M 0 0 + M 1 1), ⅟2 * (M 1 0 + ↑a⁻¹ * M 0 1),
    ⅟2 * (M 1 0 - ↑a⁻¹ * M 0 1), ⅟2 * (↑a⁻¹ * (M 0 0 - M 1 1))⟩

private theorem aNegAMatrixInverse_leftInverse (a : Rˣ) :
    Function.LeftInverse (aNegAMatrixInverse a) (aNegAMatrixBasis (a : R)).liftHom := by
  intro q
  rw [aNegAMatrixBasis_liftHom_apply]
  ext <;> simp [aNegAMatrixInverse] <;> grind [invOf_mul_self, Units.inv_mul]

private theorem aNegAMatrixInverse_rightInverse (a : Rˣ) :
    Function.RightInverse (aNegAMatrixInverse a) (aNegAMatrixBasis (a : R)).liftHom := by
  intro M
  rw [aNegAMatrixBasis_liftHom_apply]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aNegAMatrixInverse] <;>
    grind [invOf_mul_self, Units.inv_mul]

/-- The explicit splitting `ℍ[R,a,-a] ≃ₐ[R] M₂(R)` for a unit `a` over a commutative ring in
which two is invertible. It sends the quaternion generators `i` and `j` to
`!![0, a; 1, 0]` and `!![0, -a; 1, 0]`, respectively. -/
def aNegAEquivMatrix (a : Rˣ) : ℍ[R,(a : R),-(a : R)] ≃ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  { (aNegAMatrixBasis (a : R)).liftHom with
    invFun := aNegAMatrixInverse a
    left_inv := aNegAMatrixInverse_leftInverse a
    right_inv := aNegAMatrixInverse_rightInverse a }

/-- The splitting equivalence on an arbitrary quaternion. -/
@[simp]
theorem aNegAEquivMatrix_apply (a : Rˣ) (q : ℍ[R,(a : R),-(a : R)]) :
    aNegAEquivMatrix a q =
      !![q.re + (a : R) * q.imK, (a : R) * (q.imI - q.imJ);
        q.imI + q.imJ, q.re - (a : R) * q.imK] :=
  aNegAMatrixBasis_liftHom_apply _ q

/-- The inverse splitting equivalence recovers the four quaternion coordinates from the four
matrix entries. -/
@[simp]
theorem aNegAEquivMatrix_symm_apply (a : Rˣ) (M : Matrix (Fin 2) (Fin 2) R) :
    (aNegAEquivMatrix a).symm M =
      ⟨⅟2 * (M 0 0 + M 1 1), ⅟2 * (M 1 0 + ↑a⁻¹ * M 0 1),
        ⅟2 * (M 1 0 - ↑a⁻¹ * M 0 1), ⅟2 * (↑a⁻¹ * (M 0 0 - M 1 1))⟩ :=
  (rfl)

end ANegA

end QuaternionAlgebra

end TauCeti
