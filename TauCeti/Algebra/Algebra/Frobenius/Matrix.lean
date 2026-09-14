/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import TauCeti.Algebra.Algebra.Frobenius.Basic

/-!
# The matrix trace as a Frobenius functional

The trace of square matrices over a field is a symmetric Frobenius functional
(`Matrix.isSymmetricFrobeniusFunctional_traceLinearMap`), so a matrix algebra is a symmetric
algebra. This is the basic example of the notions defined in
`TauCeti.Algebra.Algebra.Frobenius.Basic`.

## References

* T. Y. Lam, *Lectures on modules and rings*, Section 16 (Frobenius and symmetric algebras).
-/

public section

namespace TauCeti

variable {k : Type*} [Field k]

/-- The trace of square matrices over a field is a symmetric Frobenius functional. -/
theorem _root_.Matrix.isSymmetricFrobeniusFunctional_traceLinearMap (n : Type*) [Fintype n]
    [DecidableEq n] : (Matrix.traceLinearMap n k k).IsSymmetricFrobeniusFunctional where
  isFrobeniusFunctional := LinearMap.isFrobeniusFunctional_iff.mpr
    ⟨fun a h => Matrix.ext_iff_trace_mul_right.mpr fun x => by simpa using h x,
      fun b h => Matrix.ext_iff_trace_mul_left.mpr fun x => by simpa using h x⟩
  apply_mul_comm a b := by simpa using Matrix.trace_mul_comm a b

end TauCeti
