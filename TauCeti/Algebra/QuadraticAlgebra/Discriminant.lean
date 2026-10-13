/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module
public import TauCeti.Algebra.QuadraticAlgebra.NormTrace
public import Mathlib.Algebra.QuadraticAlgebra.Discriminant
public import Mathlib.RingTheory.Discriminant

/-!
# The discriminant of the standard quadratic-algebra basis

The algebra discriminant of the basis `1, ω` is `b² + 4a`, where `ω² = a + bω`.
This identifies Mathlib's explicit quadratic discriminant with the discriminant computed
from the trace pairing. Over `ℤ`, choosing `a` and `b` with `b² + 4a = Δ` gives `Δ` as the
discriminant of the basis `1, ω` of `QuadraticAlgebra ℤ a b`.
-/

public section

namespace QuadraticAlgebra

/-- The discriminant of the standard basis `1, ω` is the explicit quadratic discriminant. -/
@[simp] theorem algebraDiscr_basis {R : Type*} [CommRing R] (a b : R) :
    Algebra.discr R (basis a b) = discr a b := by
  simp [Algebra.discr_def, Matrix.det_fin_two, Algebra.traceMatrix_apply,
    Algebra.traceForm_apply, basis_apply_zero, basis_apply_one, trace_def, discr_def]
  ring

end QuadraticAlgebra
