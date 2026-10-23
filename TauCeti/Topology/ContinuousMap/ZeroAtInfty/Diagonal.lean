/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.ContinuousMap.ZeroAtInfty.Matrix

/-!
# Diagonal operators on the model space `C₀(I, R)`

Let `R` be a seminormed ring and `I` a discrete index type. A bounded family `d : I →ᵇ R`
acts on `C₀(I, R)` coordinatewise, `x ↦ (x i * d i)ᵢ`: the product of a family tending to zero
with a bounded family tends to zero. This is the **diagonal operator**
`ZeroAtInftyContinuousMap.diagonalCLM d`, a continuous linear map of norm at most `‖d‖`. The
scalar `d i` multiplies on the right, so that the map is linear over a noncommutative `R`; its
matrix is `Matrix.diagonal d` (`ZeroAtInftyContinuousMap.matrixCoeff_diagonalCLM`).

Diagonal operators are the basic test cases for compactness of operators between model spaces:
the identity is the diagonal operator of the constant family `1`, while in orthonormal bases of
rescaled monomials the inclusion of power series restricted at a larger radius into those
restricted at a smaller one is a diagonal operator with geometrically decaying entries. Their row
compactness is treated in `TauCeti.Analysis.Normed.Operator.RowCompact.Diagonal`.

## Main definitions

* `ZeroAtInftyContinuousMap.diagonalCLM`: the diagonal operator of a bounded family.

## Main results

* `ZeroAtInftyContinuousMap.diagonalCLM_apply`: `diagonalCLM d x i = x i * d i`.
* `ZeroAtInftyContinuousMap.norm_diagonalCLM_apply_le`: `‖diagonalCLM d x‖ ≤ ‖d‖ * ‖x‖`.
* `ZeroAtInftyContinuousMap.matrixCoeff_diagonalCLM`: the matrix is `Matrix.diagonal d`.
* `ZeroAtInftyContinuousMap.diagonalCLM_one`, `ZeroAtInftyContinuousMap.diagonalCLM_mul`:
  the constant family `1` gives the identity, and products of families give composites.

## References

* J.-P. Serre, *Endomorphismes complètement continus des espaces de Banach p-adiques*,
  Publ. Math. IHÉS 12 (1962), 69–85, §§2–3.
-/

public section

open Filter Topology
open scoped ZeroAtInfty BoundedContinuousFunction

namespace ZeroAtInftyContinuousMap

variable {I R : Type*} [TopologicalSpace I] [DiscreteTopology I] [SeminormedRing R]

private theorem tendsto_mul_cofinite (d : I →ᵇ R) (x : C₀(I, R)) :
    Tendsto (fun i ↦ x i * d i) cofinite (𝓝 0) :=
  x.tendsto_cofinite.zero_mul_isBoundedUnder_le
    ⟨‖d‖, eventually_map.2 <| Eventually.of_forall d.norm_coe_le_norm⟩

private theorem norm_mkOfDiscrete_mul_le (d : I →ᵇ R) (x : C₀(I, R)) :
    ‖mkOfDiscrete (fun i ↦ x i * d i) (tendsto_mul_cofinite d x)‖ ≤ ‖d‖ * ‖x‖ :=
  (norm_le (by positivity)).2 fun i ↦ by
    rw [coe_mkOfDiscrete]
    exact (norm_mul_le _ _).trans <| (mul_le_mul (norm_coe_le_norm x i) (d.norm_coe_le_norm i)
      (norm_nonneg _) (norm_nonneg _)).trans_eq (mul_comm _ _)

/-- The **diagonal operator** of a bounded family `d : I →ᵇ R`: the continuous linear map of
`C₀(I, R)` multiplying the `i`-th coordinate on the right by `d i`. Its matrix is
`Matrix.diagonal d` (`ZeroAtInftyContinuousMap.matrixCoeff_diagonalCLM`). -/
noncomputable def diagonalCLM (d : I →ᵇ R) : C₀(I, R) →L[R] C₀(I, R) :=
  LinearMap.mkContinuous
    { toFun x := mkOfDiscrete (fun i ↦ x i * d i) (tendsto_mul_cofinite d x)
      map_add' x y := by ext i; simp [add_mul]
      map_smul' c x := by ext i; simp [mul_assoc] }
    ‖d‖ (norm_mkOfDiscrete_mul_le d)

@[simp]
theorem diagonalCLM_apply (d : I →ᵇ R) (x : C₀(I, R)) (i : I) : diagonalCLM d x i = x i * d i :=
  congrFun (coe_mkOfDiscrete (fun i ↦ x i * d i) (tendsto_mul_cofinite d x)) i

/-- The diagonal operator of `d` has norm at most `‖d‖`. -/
theorem norm_diagonalCLM_apply_le (d : I →ᵇ R) (x : C₀(I, R)) :
    ‖diagonalCLM d x‖ ≤ ‖d‖ * ‖x‖ :=
  norm_mkOfDiscrete_mul_le d x

@[simp]
theorem diagonalCLM_single [DecidableEq I] (d : I →ᵇ R) (i : I) (b : R) :
    diagonalCLM d (single i b) = single i (b * d i) := by
  ext j
  by_cases h : j = i
  · subst h; simp
  · simp [h]

@[simp]
theorem matrixCoeff_diagonalCLM [DecidableEq I] (d : I →ᵇ R) :
    (diagonalCLM d).matrixCoeff = Matrix.diagonal d := by
  ext i j
  by_cases h : i = j
  · subst h; simp [ContinuousLinearMap.matrixCoeff_apply]
  · simp [ContinuousLinearMap.matrixCoeff_apply, h, single_apply]

@[simp]
theorem diagonalCLM_zero : diagonalCLM (0 : I →ᵇ R) = 0 := by
  ext; simp

@[simp]
theorem diagonalCLM_one : diagonalCLM (1 : I →ᵇ R) = 1 := by
  ext; simp

@[simp]
theorem diagonalCLM_add (d e : I →ᵇ R) : diagonalCLM (d + e) = diagonalCLM d + diagonalCLM e := by
  ext; simp [mul_add]

@[simp]
theorem diagonalCLM_neg (d : I →ᵇ R) : diagonalCLM (-d) = -diagonalCLM d := by
  ext; simp

@[simp]
theorem diagonalCLM_sub (d e : I →ᵇ R) : diagonalCLM (d - e) = diagonalCLM d - diagonalCLM e := by
  ext; simp [mul_sub]

/-- The diagonal operator of a product is the composite of the diagonal operators, in the order
dictated by multiplication on the right. -/
theorem diagonalCLM_mul (d e : I →ᵇ R) : diagonalCLM (d * e) = diagonalCLM e * diagonalCLM d := by
  ext; simp [mul_assoc]

end ZeroAtInftyContinuousMap
