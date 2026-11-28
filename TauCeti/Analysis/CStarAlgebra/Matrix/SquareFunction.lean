/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Matrix.EuclideanCLM
public import TauCeti.Analysis.CStarAlgebra.SquareFunction
public import TauCeti.Analysis.InnerProductSpace.Positive.SquareRoot

import TauCeti.Analysis.InnerProductSpace.FunctionalCalculusComparison
import TauCeti.Analysis.InnerProductSpace.Polar.Finite

/-!
# Column stacking and Euclidean square-function operators for `CStarMatrix`

For a finite family `b : ι → CStarMatrix m m ℂ`, stacking the Euclidean operators
`CStarMatrix.toEuclideanCLM (b k)` vertically yields the column operator
`TauCeti.columnEuclideanLM b : EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ m)`.

Its Gram operator `(columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b` agrees with
`CStarMatrix.toEuclideanCLM (∑ k, star (b k) * b k)`, its modulus
`(columnEuclideanLM b).operatorAbs` agrees with `CStarMatrix.toEuclideanCLM (columnSquare b)`,
and the polar decomposition gives `b k = u k * columnSquare b` with `‖columnSquare u‖ ≤ 1`.
We also record the pointwise Euclidean norm identities `TauCeti.norm_columnSquare_apply_sq_eq`
and `TauCeti.norm_rowSquare_apply_sq_eq`.

## Main declarations

* `TauCeti.columnEuclideanLM`, `TauCeti.columnEuclideanLM_apply`, `TauCeti.columnEuclideanLM_projₗ`:
  vertical stacking of matrix operators and projection recovery.
* `TauCeti.adjoint_comp_columnEuclideanLM`, `TauCeti.operatorAbs_columnEuclideanLM`:
  Gram operator and modulus identification with `columnSquare`.
* `TauCeti.norm_columnSquare_apply_sq_eq`, `TauCeti.norm_rowSquare_apply_sq_eq`:
  pointwise Euclidean norm formulas for `columnSquare` and `rowSquare`.
* `TauCeti.exists_mul_columnSquare_and_norm_columnSquare_le_one`:
  polar factorization `b k = u k * columnSquare b` with `‖columnSquare u‖ ≤ 1`.

## References

* G. Pisier and Q. Xu, *Non-commutative `Lᵖ`-spaces*, *Handbook of the Geometry of Banach Spaces*,
  Vol. 2, North-Holland, 2003, §2.
-/

public section

noncomputable section

open scoped BigOperators ComplexOrder InnerProductSpace

namespace TauCeti

variable {ι m : Type*} [Fintype m] [DecidableEq m]

/-- Stacking a finite family of `m × m` C⋆-matrices into a column operator
`EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 (fun _ : ι => EuclideanSpace ℂ m)`. -/
def columnEuclideanLM :
    (ι → CStarMatrix m m ℂ) →ₗ[ℂ]
      (EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 fun _ : ι => EuclideanSpace ℂ m) where
  toFun b := (WithLp.linearEquiv 2 ℂ (ι → EuclideanSpace ℂ m)).symm.toLinearMap.comp
    (LinearMap.pi fun k => (CStarMatrix.toEuclideanCLM (b k)).toLinearMap)
  map_add' _ _ := by ext v k; simp
  map_smul' _ _ := by ext v k; simp

/-- Applying `columnEuclideanLM b` to `v` and evaluating at coordinate `k` applies
`CStarMatrix.toEuclideanCLM (b k)` to `v`. -/
@[simp] theorem columnEuclideanLM_apply (b : ι → CStarMatrix m m ℂ) (v : EuclideanSpace ℂ m)
    (k : ι) : (columnEuclideanLM b v).ofLp k = CStarMatrix.toEuclideanCLM (b k) v := (rfl)

/-- Stacking the coordinate projections of an operator `T` into `PiLp` via `columnEuclideanLM`
recovers `T`. -/
theorem columnEuclideanLM_projₗ
    (T : EuclideanSpace ℂ m →ₗ[ℂ] PiLp 2 fun _ : ι => EuclideanSpace ℂ m) :
    columnEuclideanLM (fun k => CStarMatrix.toEuclideanCLM.symm
      ((PiLp.projₗ 2 (fun _ : ι => EuclideanSpace ℂ m) k).comp T).toContinuousLinearMap) = T := by
  ext v k
  simp

/-- The column Gram operator `(columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b` agrees with
the Euclidean operator of `∑ k, star (b k) * b k`. -/
theorem adjoint_comp_columnEuclideanLM [Fintype ι] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).adjoint ∘ₗ columnEuclideanLM b =
      (CStarMatrix.toEuclideanCLM (∑ k, star (b k) * b k)).toLinearMap :=
  LinearMap.ext fun _ => ext_inner_left ℂ fun _ => by
    simp only [LinearMap.comp_apply, LinearMap.adjoint_inner_right, PiLp.inner_apply,
      columnEuclideanLM_apply, map_sum, ContinuousLinearMap.coe_coe, sum_apply, inner_sum, map_mul,
      map_star, mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]

/-- The operator modulus `|columnEuclideanLM b|` agrees with the Euclidean operator of
`columnSquare b`. -/
theorem operatorAbs_columnEuclideanLM [Fintype ι] (b : ι → CStarMatrix m m ℂ) :
    (columnEuclideanLM b).operatorAbs =
      (CStarMatrix.toEuclideanCLM (columnSquare b)).toLinearMap := by
  set T := CStarMatrix.toEuclideanCLM (columnSquare b)
  have hnonneg : 0 ≤ T := map_zero (CStarMatrix.toEuclideanCLM (n := m)) ▸
    OrderHomClass.mono CStarMatrix.toEuclideanCLM (columnSquare_nonneg b)
  have hsq : T * T = (columnEuclideanLM b).adjoint.toContinuousLinearMap ∘L
      (columnEuclideanLM b).toContinuousLinearMap := by
    rw [← map_mul, columnSquare_mul_self]
    apply ContinuousLinearMap.coe_inj.mp
    rw [ContinuousLinearMap.toLinearMap_comp, LinearMap.coe_toContinuousLinearMap,
      LinearMap.coe_toContinuousLinearMap, adjoint_comp_columnEuclideanLM b]
  exact LinearMap.ext fun v => DFunLike.congr_fun
    ((LinearMap.toContinuousLinearMap_operatorAbs _).trans (CFC.sqrt_unique hsq hnonneg)) v

/-- Pointwise Euclidean norm of `columnSquare b`:
`‖toEuclideanCLM (columnSquare b) ξ‖ ^ 2 = ∑ k, ‖toEuclideanCLM (b k) ξ‖ ^ 2`. -/
theorem norm_columnSquare_apply_sq_eq [Fintype ι] (b : ι → CStarMatrix m m ℂ)
    (ξ : EuclideanSpace ℂ m) :
    ‖CStarMatrix.toEuclideanCLM (columnSquare b) ξ‖ ^ 2 =
      ∑ k, ‖CStarMatrix.toEuclideanCLM (b k) ξ‖ ^ 2 := by
  have h : CStarMatrix.toEuclideanCLM (columnSquare b) ξ = (columnEuclideanLM b).operatorAbs ξ := by
    rw [← ContinuousLinearMap.coe_coe, operatorAbs_columnEuclideanLM]
  rw [h, LinearMap.norm_operatorAbs_apply, PiLp.norm_sq_eq_of_L2]
  simp

/-- Pointwise Euclidean norm of `rowSquare x`:
`‖toEuclideanCLM (rowSquare x) ξ‖ ^ 2 = ∑ k, ‖toEuclideanCLM (star (x k)) ξ‖ ^ 2`. -/
theorem norm_rowSquare_apply_sq_eq [Fintype ι] (x : ι → CStarMatrix m m ℂ)
    (ξ : EuclideanSpace ℂ m) :
    ‖CStarMatrix.toEuclideanCLM (rowSquare x) ξ‖ ^ 2 =
      ∑ k, ‖CStarMatrix.toEuclideanCLM (star (x k)) ξ‖ ^ 2 := by
  rw [rowSquare_eq_columnSquare_star, norm_columnSquare_apply_sq_eq]

omit [DecidableEq m] in
/-- Polar decomposition through `columnSquare`: `b k = u k * columnSquare b` with
`‖columnSquare u‖ ≤ 1`. -/
theorem exists_mul_columnSquare_and_norm_columnSquare_le_one [Fintype ι]
    (b : ι → CStarMatrix m m ℂ) :
    ∃ u : ι → CStarMatrix m m ℂ, (∀ k, b k = u k * columnSquare b) ∧ ‖columnSquare u‖ ≤ 1 := by
  classical
  set A := columnEuclideanLM b
  let U := A.polarFactor
  let u : ι → CStarMatrix m m ℂ := fun k => CStarMatrix.toEuclideanCLM.symm
    ((PiLp.projₗ 2 (fun _ : ι => EuclideanSpace ℂ m) k).comp U).toContinuousLinearMap
  have hu_eq : columnEuclideanLM u = U := columnEuclideanLM_projₗ U
  have hu (k : ι) (v : EuclideanSpace ℂ m) :
      CStarMatrix.toEuclideanCLM (u k) v = (U v).ofLp k := by
    rw [← columnEuclideanLM_apply u v k, hu_eq]
  have hgram : CStarMatrix.toEuclideanCLM (∑ k, star (u k) * u k) =
      (U.adjoint ∘ₗ U).toContinuousLinearMap := by
    apply ContinuousLinearMap.coe_inj.mp
    rw [LinearMap.coe_toContinuousLinearMap, ← hu_eq, adjoint_comp_columnEuclideanLM u]
  refine ⟨u, fun k => EquivLike.injective CStarMatrix.toEuclideanCLM <|
      ContinuousLinearMap.ext fun v => ?_, ?_⟩
  · have hpol := congrArg (fun w : PiLp 2 fun _ : ι => EuclideanSpace ℂ m => w.ofLp k)
      (A.polarFactor_operatorAbs_apply v)
    rw [operatorAbs_columnEuclideanLM, columnEuclideanLM_apply] at hpol
    rw [map_mul, mul_apply_eq_comp, hu]; exact hpol.symm
  · rw [norm_columnSquare, Real.sqrt_le_one, ← CStarMatrix.norm_toEuclideanCLM, hgram]
    exact (LinearMap.isStarProjection_toContinuousLinearMap_iff.mpr
      A.isPartialIsometry_polarFactor.isStarProjection_adjoint_comp_self).norm_le

end TauCeti
