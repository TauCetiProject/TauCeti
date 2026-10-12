/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs

/-!
# The trace along a tower of scalars

Let `A` be a commutative `R`-algebra that is free as an `R`-module, and let `M` be a free
`A`-module. An `A`-linear endomorphism `f` of `M` has a trace over `A`, and, viewed as an
`R`-linear endomorphism, a trace over `R`. The second is the algebra trace from `A` to `R` of the
first. This is the module version of the transitivity of the algebra trace
`Algebra.trace_trace_of_basis`, and the additive counterpart of `LinearMap.det_restrictScalars`.

## Main results

* `LinearMap.trace_restrictScalars`: `tr_R(f) = Tr_{A/R}(tr_A(f))`.
-/

public section

namespace LinearMap

open Module

variable {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
  [AddCommMonoid M] [Module R M] [Module A M] [IsScalarTower R A M] [Module.Free A M]

/-- **The trace along a tower of scalars.** For a free `A`-module `M`, where `A` is a free
`R`-algebra, the `R`-trace of an `A`-linear endomorphism is the algebra trace of its `A`-trace. -/
theorem trace_restrictScalars (f : M →ₗ[A] M) :
    trace R M (f.restrictScalars R) = Algebra.trace R A (trace A M f) := by
  classical
  nontriviality R
  cases subsingleton_or_nontrivial M
  · let bR : Basis (Fin 0) R M := Basis.empty M
    let bA : Basis (Fin 0) A M := Basis.empty M
    rw [trace_eq_matrix_trace R bR, trace_eq_matrix_trace A bA]
    simp [Matrix.trace]
  have := Module.nontrivial A M
  let ⟨ιA, bA⟩ := Module.Free.exists_basis (R := R) (M := A)
  let ⟨ιM, bM⟩ := Module.Free.exists_basis (R := A) (M := M)
  have := bA.index_nonempty
  have := bM.index_nonempty
  cases fintypeOrInfinite ιA; swap
  · have hA := Module.not_finite_of_infinite_basis bA
    have hM := Module.not_finite_of_infinite_basis (bA.smulTower' bM)
    have hA' : ¬∃ s : Finset A, Nonempty (Basis s R A) :=
      fun ⟨_, ⟨b⟩⟩ ↦ hA (Module.Finite.of_basis b)
    have hM' : ¬∃ s : Finset M, Nonempty (Basis s R M) :=
      fun ⟨_, ⟨b⟩⟩ ↦ hM (Module.Finite.of_basis b)
    simp [LinearMap.trace, Algebra.trace, hA', hM']
  cases fintypeOrInfinite ιM; swap
  · have hAM := Module.not_finite_of_infinite_basis bM
    have hRM := Module.not_finite_of_infinite_basis (bA.smulTower' bM)
    have hAM' : ¬∃ s : Finset M, Nonempty (Basis s A M) :=
      fun ⟨_, ⟨b⟩⟩ ↦ hAM (Module.Finite.of_basis b)
    have hRM' : ¬∃ s : Finset M, Nonempty (Basis s R M) :=
      fun ⟨_, ⟨b⟩⟩ ↦ hRM (Module.Finite.of_basis b)
    simp [LinearMap.trace, Algebra.trace, hAM', hRM']
  rw [trace_eq_matrix_trace R (bA.smulTower' bM), restrictScalars_toMatrix,
    trace_eq_matrix_trace A bM, Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type]
  simp [Algebra.trace_eq_matrix_trace bA, Matrix.trace]

end LinearMap
