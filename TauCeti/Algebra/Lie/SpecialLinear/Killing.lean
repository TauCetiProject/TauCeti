/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Classical
public import Mathlib.Algebra.Lie.TraceForm

import Mathlib.Algebra.Lie.Killing
import TauCeti.Algebra.Lie.GeneralLinear.Basic
import TauCeti.Algebra.Lie.GeneralLinear.Killing

/-!
# The Killing form of the special linear Lie algebra

The Killing form of `sl n R` is

`κ(X, Y) = 2 n trace (X * Y)`,

where `n` is the cardinality of the index type. Since `sl n R` is an ideal of
`gl n R = Matrix n n R` (`TauCeti.slIdeal`), over a principal ideal domain its Killing form is the
restriction of the Killing form of `gl n R` (`LieIdeal.killingForm_eq`), and the trace-squared term
in `Matrix.killingForm_apply` vanishes on trace-free matrices.

## Main results

* `LieAlgebra.SpecialLinear.killingForm_apply`: `κ(X, Y) = 2 n trace (X * Y)` on `sl n R`.

## References

* A. W. Knapp, *Lie Groups Beyond an Introduction*, second edition, Progress in Mathematics
  140, Birkhäuser, 2002, Chapter I (the Killing forms of the classical Lie algebras).
-/

public section

namespace LieAlgebra.SpecialLinear

open Matrix

attribute [local instance 100] LieRing.ofAssociativeRing

variable {n R : Type*} [Fintype n] [DecidableEq n] [CommRing R] [IsDomain R]
  [IsPrincipalIdealRing R]

/-- **The Killing form of `sl n R`**: `κ(X, Y) = 2 n trace (X * Y)`. -/
theorem killingForm_apply (X Y : sl n R) :
    killingForm R (sl n R) X Y =
      2 * Fintype.card n * ((X : Matrix n n R) * (Y : Matrix n n R)).trace := by
  let e : TauCeti.slIdeal R n ≃ₗ⁅R⁆ sl n R :=
    LieEquiv.ofEq (TauCeti.slIdeal R n).toLieSubalgebra (sl n R)
      (by rw [TauCeti.slIdeal_toLieSubalgebra_eq_sl])
  have hkill := killingForm_of_equiv_apply e (e.symm X) (e.symm Y)
  simp only [LieEquiv.apply_symm_apply] at hkill
  rw [hkill]
  have hres : killingForm R (TauCeti.slIdeal R n) (e.symm X) (e.symm Y) =
      killingForm R (Matrix n n R) (e.symm X : Matrix n n R) (e.symm Y : Matrix n n R) := by
    rw [LieIdeal.killingForm_eq]
    rfl
  rw [hres]
  have hX : (e.symm X : Matrix n n R) = X := rfl
  have hY : (e.symm Y : Matrix n n R) = Y := rfl
  rw [hX, hY, Matrix.killingForm_apply, mem_sl_iff.mp X.property, mem_sl_iff.mp Y.property]
  ring

end LieAlgebra.SpecialLinear
