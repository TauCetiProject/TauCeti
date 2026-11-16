/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Trace.Defs

import TauCeti.LinearAlgebra.Trace.Basic

/-!
# The trace along a tower of scalars

Let `A` be a commutative `R`-algebra that is free as an `R`-module, and let `M` be a free
`A`-module. An `A`-linear endomorphism `f` of `M` has a trace over `A`, and, viewed as an
`R`-linear endomorphism, a trace over `R`. The second is the algebra trace from `A` to `R` of the
first. This is the module version of the transitivity of the algebra trace
`Algebra.trace_trace_of_basis`, and the additive counterpart of `LinearMap.det_restrictScalars`.

## Main results

* `TauCeti.Algebra.trace_eq_zero_of_not_finite`: the algebra trace vanishes when the extension is
  not finite as a module.
* `TauCeti.Algebra.trace_one_smul`: scalar multiplication by `Tr_{A/R}(1)` on any `R`-module is
  multiplication by `finrank R A`.
* `LinearMap.trace_restrictScalars`: `tr_R(f) = Tr_{A/R}(tr_A(f))`.
* `TauCeti.Algebra.trace_trace_of_free`: `Tr_{A/R}(Tr_{B/A}(b)) = Tr_{B/R}(b)` in any tower of free
  extensions, without finiteness hypotheses.
-/

public section

namespace TauCeti.Algebra

/-- The algebra trace vanishes on an algebra that is not module-finite over the base ring. -/
theorem trace_eq_zero_of_not_finite {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    (h : ¬Module.Finite R A) : _root_.Algebra.trace R A = 0 :=
  _root_.Algebra.trace_eq_zero_of_not_exists_basis R fun ⟨_, ⟨b⟩⟩ ↦ h (.of_basis b)

/-- Scalar multiplication by `Tr_{A/R}(1)` on any `R`-module is multiplication by `finrank R A`,
without nontriviality or finiteness assumptions on `R` or `A`. -/
theorem trace_one_smul {R A M : Type*} [CommRing R] [CommRing A] [Algebra R A] [Module.Free R A]
    [AddCommMonoid M] [Module R M] (m : M) :
    _root_.Algebra.trace R A 1 • m = Module.finrank R A • m := by
  have h : _root_.Algebra.trace R A 1 = Module.finrank R A • 1 := by
    nontriviality R
    rw [← map_one (algebraMap R A), _root_.Algebra.trace_algebraMap]
  rw [h, smul_assoc, one_smul]

end TauCeti.Algebra

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
  nontriviality M using Subsingleton.elim f 0
  have := Module.nontrivial A M
  obtain ⟨ιA, bA⟩ := Free.exists_basis (R := R) (M := A)
  obtain ⟨ιM, bM⟩ := Free.exists_basis (R := A) (M := M)
  have := bA.index_nonempty
  have := bM.index_nonempty
  cases fintypeOrInfinite ιA; swap
  · simp [TauCeti.Algebra.trace_eq_zero_of_not_finite (not_finite_of_infinite_basis bA),
      TauCeti.LinearMap.trace_eq_zero_of_not_finite
        (not_finite_of_infinite_basis (bA.smulTower bM))]
  cases fintypeOrInfinite ιM; swap
  · simp [TauCeti.LinearMap.trace_eq_zero_of_not_finite (not_finite_of_infinite_basis bM),
      TauCeti.LinearMap.trace_eq_zero_of_not_finite
        (not_finite_of_infinite_basis (bA.smulTower bM))]
  rw [trace_eq_matrix_trace R (bA.smulTower' bM), restrictScalars_toMatrix,
    trace_eq_matrix_trace A bM, Matrix.trace, Matrix.trace, map_sum, Fintype.sum_prod_type]
  simp [Algebra.trace_eq_matrix_trace bA, Matrix.trace]

end LinearMap

namespace TauCeti.Algebra

/-- **Transitivity of the algebra trace along a tower of free extensions**, without finiteness
assumptions: when either step is infinite-rank, both sides vanish. -/
theorem trace_trace_of_free {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Module.Free R A] [Algebra A B] [Module.Free A B] [Algebra R B]
    [IsScalarTower R A B] (b : B) :
    _root_.Algebra.trace R A (_root_.Algebra.trace A B b) = _root_.Algebra.trace R B b := by
  have hlmul :
      LinearMap.restrictScalars R (_root_.Algebra.lmul A B b) = _root_.Algebra.lmul R B b := rfl
  rw [_root_.Algebra.trace_apply (R := R) (S := B), ← hlmul, LinearMap.trace_restrictScalars,
    _root_.Algebra.trace_apply (R := A) (S := B)]

end TauCeti.Algebra
