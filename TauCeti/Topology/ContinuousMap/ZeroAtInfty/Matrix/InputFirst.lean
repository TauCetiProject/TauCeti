/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix.Basic

/-!
# Input-first coordinates for operators on null families

`ContinuousLinearMap.matrixCoeffInputFirst` writes the input index before the output index.
It is the transpose of the output-first array `ContinuousLinearMap.matrixCoeff`, rather than
a new operator on null families. This convention is useful when the image of each coordinate
vector is stored as a row, for example in distribution coordinates.

For normed coefficients the action is `(u x) i = ∑' j, x j * u.matrixCoeffInputFirst j i`.
The `HasSum` statements also apply to seminormed coefficients. Composition reverses
matrix multiplication order: the array of `u.comp v` is the product of the array of `v`
with that of `u`, with an unconditionally convergent sum over the middle index. In finite
dimensions this is ordinary matrix multiplication, and the array is the transpose of
Mathlib's `LinearMap.toMatrix'`.

Each row of the input-first array is null. Decay of the suprema of its columns is a different,
uniform condition: these are the output-first row norms used for output truncations.
Transposition of the array does not assert that it defines an operator on `C₀` in the opposite
direction. The continuous dual operator instead acts on bounded families; see
`ContinuousLinearMap.transposeLpInfty`.
-/

public section

open Filter Topology ZeroAtInftyContinuousMap
open scoped ZeroAtInfty

namespace ContinuousLinearMap

variable {I J K R : Type*} [TopologicalSpace I] [TopologicalSpace J] [DiscreteTopology J]
  [DecidableEq J]

section SeminormedRing

variable [SeminormedRing R]

/-- The input-first matrix of an operator between model spaces. Its row `j` is the image of
the input coordinate vector at `j`; it is the transpose of the output-first coefficient array. -/
noncomputable def matrixCoeffInputFirst (u : C₀(J, R) →L[R] C₀(I, R)) : Matrix J I R :=
  u.matrixCoeff.transpose

/-- Input-first coefficients are output-first coefficients with the indices interchanged. -/
@[simp]
theorem matrixCoeffInputFirst_apply (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) (i : I) :
    u.matrixCoeffInputFirst j i = u.matrixCoeff i j := (rfl)

/-- The input-first array is the transpose of the usual operator matrix. -/
theorem matrixCoeffInputFirst_eq_transpose (u : C₀(J, R) →L[R] C₀(I, R)) :
    u.matrixCoeffInputFirst = u.matrixCoeff.transpose := (rfl)

/-- Rows of the input-first array tend to zero in the output index. -/
theorem tendsto_matrixCoeffInputFirst_cofinite [DiscreteTopology I]
    (u : C₀(J, R) →L[R] C₀(I, R)) (j : J) :
    Tendsto (u.matrixCoeffInputFirst j) cofinite (𝓝 0) := by
  convert u.tendsto_matrixCoeff_cofinite j using 1
  exact funext fun i ↦ u.matrixCoeffInputFirst_apply j i

/-- The input-first matrix action is an unconditional sum. -/
theorem hasSum_mul_matrixCoeffInputFirst (u : C₀(J, R) →L[R] C₀(I, R))
    (x : C₀(J, R)) (i : I) :
    HasSum (fun j ↦ x j * u.matrixCoeffInputFirst j i) (u x i) := by
  simpa only [matrixCoeffInputFirst_apply] using u.hasSum_mul_matrixCoeff x i

/-- Composition in input-first coordinates reverses the order of the matrix product.
The displayed sum converges even for infinite index types. -/
theorem hasSum_matrixCoeffInputFirst_comp [TopologicalSpace K] [DiscreteTopology K]
    [DecidableEq K] (u : C₀(J, R) →L[R] C₀(I, R)) (v : C₀(K, R) →L[R] C₀(J, R))
    (k : K) (i : I) :
    HasSum (fun j ↦ v.matrixCoeffInputFirst k j * u.matrixCoeffInputFirst j i)
      ((u.comp v).matrixCoeffInputFirst k i) := by
  simpa only [matrixCoeffInputFirst_apply, matrixCoeff_apply, comp_apply] using
    u.hasSum_mul_matrixCoeff (v (ZeroAtInftyContinuousMap.single k 1)) i

/-- For a finite middle index, composition is ordinary multiplication in reverse order. -/
theorem matrixCoeffInputFirst_comp [TopologicalSpace K] [DiscreteTopology K] [DecidableEq K]
    [Fintype J] (u : C₀(J, R) →L[R] C₀(I, R))
    (v : C₀(K, R) →L[R] C₀(J, R)) :
    (u.comp v).matrixCoeffInputFirst = v.matrixCoeffInputFirst * u.matrixCoeffInputFirst := by
  ext k i
  have hv : v (ZeroAtInftyContinuousMap.single k 1) =
      ∑ j, v (ZeroAtInftyContinuousMap.single k 1) j •
        ZeroAtInftyContinuousMap.single j 1 := by
    ext j
    simp [Pi.single_apply]
  simp only [matrixCoeffInputFirst_apply, matrixCoeff_apply, comp_apply, Matrix.mul_apply]
  conv_lhs => rw [hv, map_sum]
  simp

end SeminormedRing

section SeminormedCommRing

variable [SeminormedCommRing R]

/-- On finite coordinate spaces, input-first coefficients are the transpose of Mathlib's
matrix of the underlying linear map. -/
theorem matrixCoeffInputFirst_eq_toMatrix'_transpose [DiscreteTopology I] [Fintype I]
    [Fintype J] (u : C₀(J, R) →L[R] C₀(I, R)) :
    u.matrixCoeffInputFirst = (LinearMap.toMatrix'
      ((equivFunOnFintype R R).toLinearEquiv.toLinearMap ∘ₗ
        (u : C₀(J, R) →ₗ[R] C₀(I, R)) ∘ₗ
        (equivFunOnFintype R R).symm.toLinearEquiv.toLinearMap)).transpose := by
  rw [matrixCoeffInputFirst_eq_transpose, matrixCoeff_eq_toMatrix']

end SeminormedCommRing

end ContinuousLinearMap
