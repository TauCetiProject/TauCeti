/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace

/-!
# Nondegeneracy of the trace pairing

This file records that the trace pairing `(f, g) ↦ trace (f * g)` on the endomorphisms of a
finite free module over a commutative semiring is nondegenerate. This is the endomorphism
counterpart of `Matrix.ext_iff_trace_mul_right`.

## Main results

* `LinearMap.ext_iff_trace_mul_right`: two endomorphisms are equal exactly when their
  products with every endomorphism have equal trace.
* `LinearMap.forall_trace_mul_eq_zero_iff`: an endomorphism is zero exactly when its products
  with every endomorphism have zero trace.
-/

public section

namespace LinearMap

variable {K V : Type*} [CommSemiring K] [AddCommMonoid V] [Module K V]
  [Module.Free K V] [Module.Finite K V]

/-- The trace pairing on the endomorphisms of a finite free module over a commutative semiring is
nondegenerate: two endomorphisms are equal exactly when their products with every endomorphism
have equal trace. -/
theorem ext_iff_trace_mul_right {f g : Module.End K V} :
    f = g ↔ ∀ h : Module.End K V, trace K V (f * h) = trace K V (g * h) := by
  refine ⟨fun hfg _ ↦ hfg ▸ rfl, fun hfg ↦ ?_⟩
  let b := Module.Free.chooseBasis K V
  refine (toMatrix b b).injective <| Matrix.ext_iff_trace_mul_right.mpr fun Y ↦ ?_
  simpa [trace_eq_matrix_trace K b, toMatrix_mul] using hfg (Matrix.toLin b b Y)

/-- An endomorphism of a finite free module is zero exactly when its products with every
endomorphism have zero trace. -/
@[simp]
theorem forall_trace_mul_eq_zero_iff {f : Module.End K V} :
    (∀ g : Module.End K V, trace K V (f * g) = 0) ↔ f = 0 := by
  simp [ext_iff_trace_mul_right (g := 0)]

end LinearMap
