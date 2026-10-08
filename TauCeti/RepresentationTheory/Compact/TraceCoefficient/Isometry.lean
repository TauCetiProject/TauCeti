/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Compact.TraceCoefficient.Basic
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import TauCeti.RepresentationTheory.Continuous.Transport

/-!
# Normalized trace coefficients and Hilbert-Schmidt coordinates

For an irreducible unitary representation of dimension `d`, the trace coefficient
`T ↦ (x ↦ trace (T ∘ π x⁻¹))` scales the Hilbert-Schmidt inner product by `d⁻¹`.
Thus multiplying it by `√d` identifies the Hilbert-Schmidt space isometrically with the
Peter-Weyl block. We use `EuclideanSpace 𝕜 (Fin d × Fin d)` for the Hilbert-Schmidt
space: the coordinate `(i, j)` is the matrix entry in row `i`, column `j`.

The normalized trace identification intertwines the two-sided action on operators with
bi-translation on `L²(G)`. Over a skeleton of the unitary dual its images form a Hilbert
sum, providing the isometric block maps for the equivariant Peter-Weyl decomposition.

## References

* Daniel Bump, *Lie Groups*, second edition, Chapter 2.
-/

public section

open _root_.ContRepresentation

open MeasureTheory
open scoped InnerProductSpace
open TauCeti TauCeti.ContRepresentation

namespace ContRepresentation

variable {𝕜 G V : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G] [NormedAddCommGroup V] [InnerProductSpace 𝕜 V]
  [NormedSpace ℝ V] [SMulCommClass ℝ 𝕜 V] [FiniteDimensional 𝕜 V]

/-- The trace coefficient scales the Hilbert-Schmidt inner product by the inverse dimension.
The sum is independent of the chosen orthonormal basis. -/
theorem inner_traceCoeffLp (π : ContRepresentation 𝕜 G V) (hπ : Continuous π)
    (hunitary : IsUnitary π) (hirr : Representation.IsIrreducible π.toRepresentation)
    {ι : Type*} [Fintype ι] (e : OrthonormalBasis ι 𝕜 V) (T S : V →L[𝕜] V) :
    ⟪traceCoeffLp π hπ T, traceCoeffLp π hπ S⟫_𝕜 =
      (Module.finrank 𝕜 V : 𝕜)⁻¹ * ∑ i, ⟪T (e i), S (e i)⟫_𝕜 := by
  classical
  rw [traceCoeffLp_eq_sum π hπ hunitary e, traceCoeffLp_eq_sum π hπ hunitary e]
  simp_rw [sum_inner, inner_sum, π.schur_orthogonality_self hπ hunitary hirr,
    orthonormal_iff_ite.mp e.orthonormal]
  simp [Finset.mul_sum]

end ContRepresentation

namespace TauCeti

variable {𝕜 G : Type*} [RCLike 𝕜] [IsAlgClosed 𝕜] [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]

/-- The isometric normalized trace identification of Hilbert-Schmidt matrices with a Peter-Weyl
block. Row-column coordinates are transposed relative to the indexing of matrix coefficients. -/
noncomputable def traceCoeffBlockIsometry (model : IrrepModel 𝕜 G) :
    EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim) ≃ₗᵢ[𝕜] peterWeylBlock model :=
  (EuclideanSpace.basisFun _ 𝕜).equiv (peterWeylBlockOrthonormalBasis model)
    (Equiv.prodComm _ _)

/-- A matrix unit maps to `√d` times its trace coefficient, with the column index in the first
vector of the matrix coefficient. -/
@[simp]
theorem traceCoeffBlockIsometry_single (model : IrrepModel 𝕜 G)
    (p : Fin model.dim × Fin model.dim) :
    traceCoeffBlockIsometry model (EuclideanSpace.single p 1) =
      peterWeylBlockOrthonormalBasis model (p.2, p.1) := by
  rw [← EuclideanSpace.basisFun_apply]
  exact OrthonormalBasis.equiv_apply_basis _ _ _ p

/-- The isometry is `√d` times the trace coefficient of the matrix represented by its argument. -/
theorem coe_traceCoeffBlockIsometry (model : IrrepModel 𝕜 G)
    (a : EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim)) :
    (traceCoeffBlockIsometry model a : Lp 𝕜 2 (haarProb G)) =
      (Real.sqrt model.dim : 𝕜) • ContRepresentation.traceCoeffLp model.rep model.continuous_rep
        (Matrix.toEuclideanCLM (n := Fin model.dim) (𝕜 := 𝕜) (fun i j => a (i, j))) := by
  let M : EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim) →ₗ[𝕜]
      Matrix (Fin model.dim) (Fin model.dim) 𝕜 :=
    { toFun a := fun i j => a (i, j)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have hM (a : EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim)) (i j : Fin model.dim) :
      M a i j = a (i, j) := rfl
  have h : (peterWeylBlock model).subtype ∘ₗ
      (traceCoeffBlockIsometry model).toLinearEquiv.toLinearMap =
      (Real.sqrt model.dim : 𝕜) •
        ((ContRepresentation.traceCoeffLp model.rep model.continuous_rep).comp
          ((Matrix.toEuclideanCLM (n := Fin model.dim) (𝕜 := 𝕜)).toAlgEquiv.toLinearEquiv
            |>.toLinearMap.comp M)) := by
    apply (EuclideanSpace.basisFun _ 𝕜).toBasis.ext
    intro p
    have hmatrix : Matrix.toEuclideanCLM (n := Fin model.dim) (𝕜 := 𝕜)
        (M (EuclideanSpace.basisFun _ 𝕜 p)) =
        InnerProductSpace.rankOne 𝕜 (model.basis p.1) (model.basis p.2) := by
      apply ContinuousLinearMap.coe_injective
      apply Matrix.toEuclideanLin.symm.injective
      rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
        Matrix.toEuclideanLin.symm_apply_apply, InnerProductSpace.symm_toEuclideanLin_rankOne]
      ext i j
      by_cases hi : p.1 = i <;> by_cases hj : p.2 = j <;>
        simp [hM, IrrepModel.basis_def, EuclideanSpace.basisFun_apply,
          Matrix.vecMulVec_apply, PiLp.single_apply, hi, hj, Prod.ext_iff]
    rw [EuclideanSpace.basisFun_apply] at hmatrix
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, OrthonormalBasis.coe_toBasis,
      LinearMap.smul_apply, LinearIsometryEquiv.coe_toLinearEquiv,
      Submodule.subtype_apply, StarAlgEquiv.coe_toAlgEquiv, AlgEquiv.coe_toLinearEquiv,
      hmatrix, EuclideanSpace.basisFun_apply, traceCoeffBlockIsometry_single]
    rw [coe_peterWeylBlockOrthonormalBasis (fun _ : Unit => model) (),
      peterWeylFamily_apply, ContRepresentation.traceCoeffLp_rankOne model.rep
        model.continuous_rep model.isUnitary]
  exact congr($h a)

/-- The two-sided action on Hilbert-Schmidt matrices corresponding to a model. Its matrix form
is postcomposition by `π g` and precomposition by `π h⁻¹`. -/
noncomputable def peterWeylMatrixRep (model : IrrepModel 𝕜 G) :
    ContRepresentation 𝕜 (G × G) (EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim)) :=
  ContinuousLinearEquiv.congr (traceCoeffBlockIsometry model).symm.toContinuousLinearEquiv
    (peterWeylBlockRep model)

/-- The normalized trace isometry intertwines the matrix action and bi-translation. -/
theorem traceCoeffBlockIsometry_intertwines (model : IrrepModel 𝕜 G) (p : G × G)
    (a : EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim)) :
    (traceCoeffBlockIsometry model (peterWeylMatrixRep model p a) : Lp 𝕜 2 (haarProb G)) =
      biRegularLp 𝕜 G p (traceCoeffBlockIsometry model a : Lp 𝕜 2 (haarProb G)) := by
  rw [peterWeylMatrixRep, ContinuousLinearEquiv.congr_apply]
  simp [coe_peterWeylBlockRep_apply]

/-- The matrix action preserves the Hilbert-Schmidt inner product. -/
theorem isUnitary_peterWeylMatrixRep (model : IrrepModel 𝕜 G) :
    ContRepresentation.IsUnitary (peterWeylMatrixRep model) :=
  (isUnitary_peterWeylBlockRep model).congr (traceCoeffBlockIsometry model).symm

/-- The matrix action is continuous in the operator norm. -/
theorem continuous_peterWeylMatrixRep (model : IrrepModel 𝕜 G) :
    Continuous (peterWeylMatrixRep model) :=
  ContinuousLinearEquiv.continuous_congr _ (continuous_peterWeylBlockRep model)

/-- In operator form, the action on Hilbert-Schmidt matrices is `T ↦ π g ∘ T ∘ π h⁻¹`.
This characterizes the transported action without referring to Peter-Weyl blocks. -/
theorem toEuclideanCLM_peterWeylMatrixRep (model : IrrepModel 𝕜 G) (p : G × G)
    (a : EuclideanSpace 𝕜 (Fin model.dim × Fin model.dim)) :
    Matrix.toEuclideanCLM (n := Fin model.dim) (𝕜 := 𝕜)
        (fun i j => peterWeylMatrixRep model p a (i, j)) =
      ContRepresentation.biLinHom model.rep model.rep p
        (Matrix.toEuclideanCLM (n := Fin model.dim) (𝕜 := 𝕜) (fun i j => a (i, j))) := by
  have hinj : Function.Injective
      (ContRepresentation.traceCoeffLp model.rep model.continuous_rep) := by
    intro T S hTS
    apply (bijective_traceCoeffBlock model).1
    apply Subtype.ext
    simpa only [coe_traceCoeffBlock] using hTS
  apply hinj
  have h := traceCoeffBlockIsometry_intertwines model p a
  rw [coe_traceCoeffBlockIsometry, coe_traceCoeffBlockIsometry, map_smul,
    ContRepresentation.biRegularLp_traceCoeffLp] at h
  exact (smul_right_injective _ (by exact_mod_cast ne_of_gt (Real.sqrt_pos.2
    (by exact_mod_cast model.dim_pos)))).eq_iff.mp h

end TauCeti
