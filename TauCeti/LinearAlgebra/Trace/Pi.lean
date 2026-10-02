/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Pi

/-!
# Traces of coordinate-reindexing maps

This file computes the trace of an endomorphism of a finite product that selects an input
coordinate for each output coordinate and applies a linear endomorphism there. Only fixed
coordinates contribute to the trace.

The results are linear-algebra inputs for character formulas of induced representations and
finite direct sums of representations.

## Main results

* `LinearMap.trace_pi_of_apply_eq`: the trace formula for a coordinate-reindexing map on a
  constant finite product.
* `LinearMap.trace_piMap`: the trace of a coordinatewise endomorphism `LinearMap.piMap f` of a
  finite dependent product is the sum of the traces of its components.
-/

public section

namespace TauCeti

universe u v w

variable {k : Type u} {ι : Type v} {M : Type w}
  [CommRing k] [Fintype ι]
  [AddCommGroup M] [Module k M] [Module.Free k M] [Module.Finite k M]

open scoped Classical in
/-- The trace of a coordinate-reindexing endomorphism of a finite product is the sum of the
traces on its fixed coordinates. -/
theorem _root_.LinearMap.trace_pi_of_apply_eq (T : (ι → M) →ₗ[k] (ι → M)) (σ : ι → ι)
    (f : ι → M →ₗ[k] M) (hT : ∀ x i, T x i = f i (x (σ i))) :
    LinearMap.trace k (ι → M) T =
      ∑ i : ι, if σ i = i then LinearMap.trace k M (f i) else 0 := by
  let b := Module.Free.chooseBasis k M
  let := Fintype.ofFinite (Module.Free.ChooseBasisIndex k M)
  let B := Pi.basis fun _ : ι => b
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : σ i = i
  · simp only [hi, ↓reduceIte]
    rw [LinearMap.trace_eq_matrix_trace k b, Matrix.trace]
    apply Finset.sum_congr rfl
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]
  · simp only [hi, ↓reduceIte]
    apply Finset.sum_eq_zero
    intro j _
    simp [LinearMap.toMatrix_apply, B, b, hT, hi]

/-- The trace of the coordinatewise endomorphism `LinearMap.piMap f` of a finite dependent product
of finite free modules is the sum of the traces of the `f i`. -/
@[simp]
theorem _root_.LinearMap.trace_piMap {M : ι → Type*}
    [∀ i, AddCommGroup (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
    [∀ i, Module.Finite k (M i)] (f : ∀ i, M i →ₗ[k] M i) :
    LinearMap.trace k ((i : ι) → M i) (LinearMap.piMap f) =
      ∑ i, LinearMap.trace k (M i) (f i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  rw [LinearMap.trace_eq_matrix_trace k (Pi.basis b), LinearMap.toMatrix_piMap,
    Matrix.trace_blockDiagonal']
  simp_rw [LinearMap.trace_eq_matrix_trace k (b _)]

end TauCeti
