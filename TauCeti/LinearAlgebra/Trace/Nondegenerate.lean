/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Matrix.BilinearForm

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
* `LinearMap.det_trace_mul_ne_zero`: over an integral domain, the Gram matrix of the trace pairing
  on a basis of the endomorphisms has nonzero determinant.
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

/-- Over an integral domain, the Gram matrix `(trace (bᵢ * bⱼ))` of the trace pairing on a basis
`b` of the endomorphisms has nonzero determinant. -/
theorem det_trace_mul_ne_zero {K V : Type*} [CommRing K] [IsDomain K] [AddCommGroup V]
    [Module K V] [Module.Free K V] [Module.Finite K V] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K (Module.End K V)) :
    (Matrix.of fun i j => trace K V (b i * b j)).det ≠ 0 := by
  let B : LinearMap.BilinForm K (Module.End K V) := (mul K (Module.End K V)).compr₂ (trace K V)
  have hB : B.Nondegenerate :=
    ⟨fun f hf => forall_trace_mul_eq_zero_iff.mp hf,
      fun f hf => forall_trace_mul_eq_zero_iff.mp fun g => trace_mul_comm K f g ▸ hf g⟩
  convert (BilinForm.nondegenerate_iff_det_ne_zero b).mp hB using 2
  ext i j
  simp [B, BilinForm.toMatrix_apply]

end LinearMap
