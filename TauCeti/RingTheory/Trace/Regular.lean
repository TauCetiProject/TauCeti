/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs
public import TauCeti.LinearAlgebra.Matrix.Trace.IsIntegral

/-!
# The regular trace form of a possibly noncommutative algebra

Mathlib's `Algebra.trace` and `Algebra.traceForm` are stated for commutative algebras. For an
arbitrary `R`-algebra `S`, finite free over `R`, the regular trace of `x` is still the trace of left
multiplication by `x`, and the regular trace form pairs `x` and `y` to the regular trace of `x * y`.
This is the pairing used to bound orders in finite-dimensional algebras, such as group algebras and
matrix algebras, by a dual lattice.

## Main definitions

* `Algebra.regularTraceForm R S`: the bilinear form `(x, y) ↦ Tr_R (z ↦ x * y * z)`.

## Main results

* `Algebra.regularTraceForm_eq_traceForm`: for commutative `S` it is `Algebra.traceForm R S`.
* `Algebra.isIntegral_trace_lmul`: over a field `K` which is an `R`-algebra, the regular trace of an
  element integral over `R` is integral over `R`.
-/

public section

namespace Algebra

open LinearMap

variable (R S : Type*) [CommRing R] [Ring S] [Algebra R S]

/-- The regular trace form of an `R`-algebra `S`, which need not be commutative: it pairs `x` and
`y` to the trace over `R` of left multiplication by `x * y`. For commutative `S` this is
`Algebra.traceForm R S` (`Algebra.regularTraceForm_eq_traceForm`). -/
noncomputable def regularTraceForm : LinearMap.BilinForm R S :=
  (lmul R S).toLinearMap.compr₂ ((LinearMap.trace R S).comp (lmul R S).toLinearMap)

variable {S} in
@[simp]
theorem regularTraceForm_apply (x y : S) :
    regularTraceForm R S x y = LinearMap.trace R S (lmul R S (x * y)) :=
  (rfl)

/-- For a commutative algebra the regular trace form is Mathlib's trace form. -/
theorem regularTraceForm_eq_traceForm (S : Type*) [CommRing S] [Algebra R S] :
    regularTraceForm R S = traceForm R S := by
  ext x y
  rw [regularTraceForm_apply, traceForm_apply, trace_apply]

/-- **The regular trace of an integral element is integral.** Let `K` be a field which is an
`R`-algebra and `E` a finite-dimensional `K`-algebra, not necessarily commutative. If `x : E` is
integral over `R`, then so is the trace over `K` of left multiplication by `x`. -/
theorem isIntegral_trace_lmul {R K E : Type*} [CommRing R] [Field K] [Ring E] [Algebra K E]
    [Algebra R K] [Algebra R E] [IsScalarTower R K E] [FiniteDimensional K E] {x : E}
    (hx : IsIntegral R x) : IsIntegral R (LinearMap.trace K E (lmul K E x)) := by
  classical
  let b := Module.finBasis K E
  rw [LinearMap.trace_eq_matrix_trace K b, ← leftMulMatrix_apply]
  exact Matrix.isIntegral_trace (hx.map ((leftMulMatrix b).restrictScalars R))

end Algebra
