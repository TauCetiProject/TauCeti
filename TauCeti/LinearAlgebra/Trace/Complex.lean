/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.Module
public import Mathlib.LinearAlgebra.Trace
import TauCeti.LinearAlgebra.Trace.Basic

/-!
# Real traces of real-linear endomorphisms of complex spaces

The real trace of an arbitrary real-linear endomorphism of the complex plane is the sum
of its diagonal entries in the basis `(1, I)`. The formula turns the trace of a planar map's real
derivative into coordinate divergence.

More generally, a complex vector space `V` is also a real vector space. A real-linear
endomorphism `f` of `V` that anticommutes with multiplication by `i`, `f (i • v) = -(i • f v)`
(for instance a conjugate-linear map), has real trace zero. For finite-dimensional `V`, write `j`
for multiplication by `i`, so that `j ∘ j = -1` and `f ∘ j = -(j ∘ f)`; cyclicity of the trace
gives `-tr f = tr (f ∘ j ∘ j) = tr (j ∘ (f ∘ j)) = -tr (j ∘ j ∘ f) = tr f`. Otherwise the trace
vanishes by definition.

## Main results

* `LinearMap.trace_complex_apply`: the real trace of a real-linear endomorphism of `ℂ`.
* `LinearMap.trace_eq_zero_of_map_I_smul_eq_neg`: a real-linear endomorphism anticommuting with
  multiplication by `i` has real trace zero.
-/

public section

open Complex

/-- The real trace of a real-linear endomorphism `L` of `ℂ` is the sum of the diagonal entries of
its matrix in the basis `(1, I)`: the real part of `L 1` plus the imaginary part of `L I`. -/
theorem LinearMap.trace_complex_apply (L : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.trace ℝ ℂ L = (L 1).re + (L I).im := by
  simp [LinearMap.trace_eq_matrix_trace ℝ Complex.basisOneI, Matrix.trace_fin_two,
    LinearMap.toMatrix_apply]

namespace LinearMap

variable {V : Type*} [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]

/-- **A real-linear endomorphism anticommuting with multiplication by `i` has real trace zero.** -/
theorem trace_eq_zero_of_map_I_smul_eq_neg (f : V →ₗ[ℝ] V)
    (hf : ∀ v, f (I • v) = -(I • f v)) : trace ℝ V f = 0 := by
  by_cases hV : Module.Finite ℝ V
  swap
  · rw [TauCeti.LinearMap.trace_eq_zero_of_not_finite hV, LinearMap.zero_apply]
  let j : V →ₗ[ℝ] V := (I • LinearMap.id : V →ₗ[ℂ] V).restrictScalars ℝ
  have hj : j ∘ₗ j = -LinearMap.id := by
    ext v
    simp [j, smul_smul]
  have hfj : f ∘ₗ j = -(j ∘ₗ f) := by
    ext v
    simp [j, hf]
  have h1 : trace ℝ V (f ∘ₗ j ∘ₗ j) = -trace ℝ V f := by
    rw [hj, comp_neg, comp_id, map_neg]
  have h2 : trace ℝ V (f ∘ₗ j ∘ₗ j) = trace ℝ V f := by
    rw [← comp_assoc, trace_comp_comm', hfj, comp_neg, ← comp_assoc, hj, map_neg, neg_comp,
      id_comp, map_neg, neg_neg]
  linarith

end LinearMap
