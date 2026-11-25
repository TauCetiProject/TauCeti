/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Lagrange
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.ContinuousMap.Polynomial

/-!
# Polynomial functions with values in an algebra

A polynomial `P` over a topological commutative semiring `A` defines the continuous function
`P.toContinuousMap : C(A, A)`. For a topological `A`-algebra `R`, pushing its values into `R`
gives the continuous function `x ↦ P.eval x • 1 : C(A, R)`. This is the same as evaluating `P` in
the `A`-algebra `C(A, R)` at the coordinate function `x_R = ContinuousMap.id A • 1`.

On a finite subset of a topological field every continuous function is a polynomial function, by
Lagrange interpolation.

## Main results

* `Polynomial.toContinuousMap_smul_one_eq_aeval`: `P.toContinuousMap • 1 = aeval x_R P`.
* `polynomialFunctions.eq_top_of_finite`: `polynomialFunctions s = ⊤` for finite `s`.
-/

public section

namespace Polynomial

/-- A polynomial function on a topological commutative semiring `A`, pushed into a topological
`A`-algebra `R`, is the same polynomial evaluated at the coordinate function
`x_R = ContinuousMap.id A • 1 : C(A, R)`. -/
theorem toContinuousMap_smul_one_eq_aeval {A R : Type*} [CommSemiring A] [TopologicalSpace A]
    [IsTopologicalSemiring A] [Semiring R] [TopologicalSpace R] [IsTopologicalSemiring R]
    [Algebra A R] [ContinuousSMul A R] (P : A[X]) :
    P.toContinuousMap • (1 : C(A, R)) = aeval (ContinuousMap.id A • 1 : C(A, R)) P := by
  ext x
  have h := aeval_algHom_apply ((Pi.evalAlgHom A (fun _ : A => R) x).comp
    (ContinuousMap.coeFnAlgHom A)) (ContinuousMap.id A • 1) P
  simp only [AlgHom.comp_apply, ContinuousMap.coeFnAlgHom_apply, Pi.evalAlgHom_apply] at h
  rw [← h]
  simp [← Algebra.algebraMap_eq_smul_one, aeval_algebraMap_apply_eq_algebraMap_eval]

end Polynomial

/-- On a finite subset `s` of a topological field, including the empty set, every continuous
function is a polynomial function. -/
theorem polynomialFunctions.eq_top_of_finite {F : Type*} [Field F] [TopologicalSpace F]
    [IsTopologicalSemiring F] {s : Set F} (hs : s.Finite) : polynomialFunctions s = ⊤ := by
  classical
  have := hs.fintype
  refine eq_top_iff.mpr fun φ _ ↦ ?_
  rw [← SetLike.mem_coe, polynomialFunctions_coe]
  refine ⟨Lagrange.interpolate Finset.univ Subtype.val φ, ?_⟩
  ext x
  simpa [-Lagrange.interpolate_apply] using
    Lagrange.eval_interpolate_at_node φ Subtype.val_injective.injOn (Finset.mem_univ x)
