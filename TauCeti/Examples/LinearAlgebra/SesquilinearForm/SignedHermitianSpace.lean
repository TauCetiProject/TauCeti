/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.LinearAlgebra.SesquilinearForm.SignedHermitianSpace
import Mathlib.Algebra.Star.Rat
import Mathlib.Basic.Complex.Basic

/-!
# Regression examples: signed hermitian spaces

These examples exercise `TauCeti.SignedHermitianSpace` over `starRingEnd`:

* the zero rational space carries a signed hermitian structure of either sign;
* on the complex line, `conj x * y` is hermitian with value `1` at `(i, i)`, and `conj x * i * y`
  is skew-hermitian;
* no one-dimensional rational space is skew-hermitian, since its form would vanish;
* on the complex hermitian line the adjoint of multiplication by `i` is multiplication by `-i`,
  so the adjoint is conjugate-linear rather than linear.
-/

open TauCeti SignedHermitianSpace

-- The zero-dimensional rational space admits both signs: its empty pairing is perfect.
example (ε : ℤˣ) : Nonempty (SignedHermitianSpace ℚ (Fin 0 → ℚ) (starRingEnd ℚ) ε) :=
  ⟨{ form := 0
     form_swap := by simp
     separatingLeft := fun _ _ => Subsingleton.elim _ _ }⟩

-- On the complex line, `conj x * y` is hermitian and takes the value `1` at `(i, i)`.
example :
    (line (ε := 1) (1 : ℂ) (by simp) (one_mem _)).form Complex.I Complex.I = 1 := by
  simp

-- The form `conj x * i * y` on the complex line is skew-hermitian, with value `i` at `(1, 1)`.
example :
    (line (ε := -1) Complex.I (by simp) (mem_nonZeroDivisors_of_ne_zero Complex.I_ne_zero)).form
      1 1 = Complex.I := by
  simp

-- A one-dimensional rational skew-hermitian space cannot be perfect: its form vanishes.
example : IsEmpty (SignedHermitianSpace ℚ ℚ (starRingEnd ℚ) (-1)) := ⟨fun h => by
  have h11 : h.form 1 1 = 0 := by
    have := h.form_swap 1 1
    simp only [Units.neg_smul, one_smul, starRingEnd_apply, star_trivial] at this
    linarith
  refine one_ne_zero (h.separatingLeft 1 fun y => ?_)
  rw [← mul_one y, ← smul_eq_mul, map_smul, h11, smul_zero]⟩

-- The adjoint of multiplication by `i` on the complex hermitian line is multiplication by `-i`.
example :
    signedHermitianAdjoint (line (ε := 1) (1 : ℂ) (by simp) (one_mem _))
      (Complex.I • LinearMap.id) = (-Complex.I) • LinearMap.id := by
  rw [map_smulₛₗ, signedHermitianAdjoint_id, starRingEnd_apply, Complex.star_def,
    Complex.conj_I]
