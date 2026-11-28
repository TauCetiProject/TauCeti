/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.LinearAlgebra.Matrix.Notation
public import TauCeti.GroupTheory.Coxeter.DeformedReflection

/-!
# Deformed simple reflections on `A₂`

On `A₂ = SimpleGraph.pathGraph 2`, `SimpleGraph.deformedReflection` at a unit `q : Rˣ` over a
commutative ring `R` has standard-basis matrices `!![-q², -q; 0, 1]` at vertex `0` and
`!![1, 0; -q, -q²]` at vertex `1`, with common length-three braid product `!![0, q³; q³, 0]`.
Specializing to `q = -1` recovers Seidel and Thomas's numerical `A₂` reflection matrices
`!![-1, 1; 0, 1]` and `!![1, 0; 1, -1]` of determinant `-1` and common triple product
`!![0, -1; -1, 0]`.

## References

* P. Seidel and R. Thomas, *Braid group actions on derived categories of coherent sheaves*, §2d.
* M. Khovanov and P. Seidel, *Quivers, Floer cohomology, and braid group actions*, §2e.1.
-/

public section
noncomputable section

namespace TauCeti

open SimpleGraph

/-- On `A₂ = SimpleGraph.pathGraph 2`, `deformedReflection q 0` has matrix `!![-q², -q; 0, 1]`. -/
theorem toMatrix'_deformedReflection_pathGraph_two_zero {R : Type*} [CommRing R] (q : Rˣ) :
    LinearMap.toMatrix' ((pathGraph 2).deformedReflection q 0).toLinearMap =
      !![-(q : R) ^ 2, -(q : R); 0, 1] := by
  have hadj : (pathGraph 2).Adj 0 1 := by simp [pathGraph_adj]
  rw [toMatrix'_deformedReflection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, hadj]

/-- On `A₂ = SimpleGraph.pathGraph 2`, `deformedReflection q 1` has matrix `!![1, 0; -q, -q²]`. -/
theorem toMatrix'_deformedReflection_pathGraph_two_one {R : Type*} [CommRing R] (q : Rˣ) :
    LinearMap.toMatrix' ((pathGraph 2).deformedReflection q 1).toLinearMap =
      !![(1 : R), 0; -(q : R), -(q : R) ^ 2] := by
  have hadj : (pathGraph 2).Adj 1 0 := by simp [pathGraph_adj]
  rw [toMatrix'_deformedReflection]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.vecMulVec_apply, hadj]

/-- On `A₂ = SimpleGraph.pathGraph 2`, both length-three braid products of `deformedReflection q 0`
and `deformedReflection q 1` have matrix `!![0, q³; q³, 0]`. -/
theorem toMatrix'_deformedReflection_pathGraph_two_braid {R : Type*} [CommRing R] (q : Rˣ) :
    LinearMap.toMatrix'
        (((pathGraph 2).deformedReflection q 0 * (pathGraph 2).deformedReflection q 1 *
          (pathGraph 2).deformedReflection q 0).toLinearMap) =
      !![(0 : R), (q : R) ^ 3; (q : R) ^ 3, 0] ∧
    LinearMap.toMatrix'
        (((pathGraph 2).deformedReflection q 1 * (pathGraph 2).deformedReflection q 0 *
          (pathGraph 2).deformedReflection q 1).toLinearMap) =
      !![(0 : R), (q : R) ^ 3; (q : R) ^ 3, 0] := by
  have hbraid := congrArg
    (fun e : (Fin 2 → R) ≃ₗ[R] (Fin 2 → R) ↦ LinearMap.toMatrix' e.toLinearMap)
    ((pathGraph 2).deformedReflection_braid q (by simp [pathGraph_adj] : (pathGraph 2).Adj 0 1))
  have hABA : LinearMap.toMatrix'
      (((pathGraph 2).deformedReflection q 0 * (pathGraph 2).deformedReflection q 1 *
        (pathGraph 2).deformedReflection q 0).toLinearMap) =
      !![(0 : R), (q : R) ^ 3; (q : R) ^ 3, 0] := by
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix'_mul,
      LinearMap.toMatrix'_mul, toMatrix'_deformedReflection_pathGraph_two_zero,
      toMatrix'_deformedReflection_pathGraph_two_one]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> ring
  exact ⟨hABA, hbraid.symm.trans hABA⟩

/-- Seidel–Thomas numerical `A₂` check (`q = -1`): the vertex reflections have matrices
`!![-1, 1; 0, 1]` and `!![1, 0; 1, -1]`, determinant `-1`, and common triple product
`!![0, -1; -1, 0]`. -/
example :
    LinearMap.toMatrix' ((pathGraph 2).deformedReflection (-1 : ℤˣ) 0).toLinearMap =
      !![(-1 : ℤ), 1; 0, 1] ∧
    LinearMap.toMatrix' ((pathGraph 2).deformedReflection (-1 : ℤˣ) 1).toLinearMap =
      !![(1 : ℤ), 0; 1, -1] ∧
    (∀ r : Fin 2,
      (LinearMap.toMatrix' ((pathGraph 2).deformedReflection (-1 : ℤˣ) r).toLinearMap).det = -1) ∧
    LinearMap.toMatrix'
        (((pathGraph 2).deformedReflection (-1 : ℤˣ) 0 *
          (pathGraph 2).deformedReflection (-1 : ℤˣ) 1 *
          (pathGraph 2).deformedReflection (-1 : ℤˣ) 0).toLinearMap) =
      !![(0 : ℤ), -1; -1, 0] ∧
    LinearMap.toMatrix'
        (((pathGraph 2).deformedReflection (-1 : ℤˣ) 1 *
          (pathGraph 2).deformedReflection (-1 : ℤˣ) 0 *
          (pathGraph 2).deformedReflection (-1 : ℤˣ) 1).toLinearMap) =
      !![(0 : ℤ), -1; -1, 0] := by
  refine ⟨?_, ?_, fun r ↦ by simp, ?_⟩
  · simpa using toMatrix'_deformedReflection_pathGraph_two_zero (-1 : ℤˣ)
  · simpa using toMatrix'_deformedReflection_pathGraph_two_one (-1 : ℤˣ)
  · simpa using toMatrix'_deformedReflection_pathGraph_two_braid (-1 : ℤˣ)

end TauCeti

end
