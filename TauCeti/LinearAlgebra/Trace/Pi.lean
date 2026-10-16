/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.LinearAlgebra.Trace

/-!
# Traces on finite products

The trace of an endomorphism of a finite dependent product is the sum of the traces of its
diagonal blocks. In particular, a coordinatewise endomorphism has the sum of the component
traces, and a coordinate-reindexing endomorphism receives contributions only from fixed
coordinates.

The results are linear-algebra inputs for character formulas of induced representations and
finite direct sums of representations.

## Main results

* `LinearMap.trace_pi`: the trace of an arbitrary endomorphism of a finite dependent product is
  the sum of the traces of its diagonal blocks.
* `LinearMap.trace_piMap`: the trace of a coordinatewise endomorphism `LinearMap.piMap f` of a
  finite dependent product is the sum of the traces of its components.
-/

public section

namespace LinearMap

universe u v w

variable {k : Type u} {ι : Type v} [CommSemiring k] [Fintype ι] {M : ι → Type w}
  [∀ i, AddCommMonoid (M i)] [∀ i, Module k (M i)] [∀ i, Module.Free k (M i)]
  [∀ i, Module.Finite k (M i)]

/-- The trace of an endomorphism of a finite dependent product is the sum of the traces of its
diagonal blocks. -/
theorem trace_pi [DecidableEq ι] (T : ((i : ι) → M i) →ₗ[k] (i : ι) → M i) :
    trace k ((i : ι) → M i) T =
      ∑ i, trace k (M i) (proj i ∘ₗ T ∘ₗ single k M i) := by
  classical
  let b (i : ι) := Module.Free.chooseBasis k (M i)
  rw [trace_eq_matrix_trace k (Pi.basis b), Matrix.trace, Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro i _
  rw [trace_eq_matrix_trace k (b i), Matrix.trace]
  simp [toMatrix_apply]

/-- The trace of the coordinatewise endomorphism `LinearMap.piMap f` of a finite dependent product
of finite free modules is the sum of the traces of the `f i`. -/
@[simp]
theorem trace_piMap (f : ∀ i, M i →ₗ[k] M i) :
    trace k ((i : ι) → M i) (piMap f) = ∑ i, trace k (M i) (f i) := by
  classical
  rw [trace_pi]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext m
  simp

end LinearMap
