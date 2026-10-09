/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.BaseChange
public import TauCeti.Algebra.AlgebraicGroup.Connected.CommHopfAlgCat
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Levi
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.UnipotentGeneration
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Geometric connectedness of the symplectic flag stabilizer

The standard complete isotropic flag stabilizer in `Sp₂ₘ` is geometrically connected
over every field. Its matrices have the form `[A, A S; 0, (A⁻¹)ᵀ]`, where `A` is
invertible upper triangular and `S` is symmetric. Polynomial coordinates for `A` and
`S`, localized at `det A`, give a domain containing the flag coordinate algebra as
a retract. This works in characteristic two because symmetric matrices are
parametrized by their upper triangle, without dividing by two.

The coordinate-ring retraction argument follows
`TauCeti.Algebra.AlgebraicGroup.SpecialLinear.UpperTriangular.Connected`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6.
* T. A. Springer, *Linear Algebraic Groups*, §6.2.
-/

public section

open Matrix CategoryTheory WithConv
open scoped TensorProduct

namespace TauCeti.Symplectic.IsotropicFlag

open GLSymplecticFin.IsotropicFlag

universe u

noncomputable section

variable (R : Type u) [CommRing R] (m : ℕ)

/-- Polynomial parameters for the triangular and symmetric blocks. -/
private abbrev Parameters :=
  MvPolynomial ((Fin m × Fin m) ⊕ (Fin m × Fin m)) R

/-- The triangular block in the polynomial parameter space. -/
private def triangularMatrix : Matrix (Fin m) (Fin m) (Parameters R m) :=
  fun i j ↦ if i ≤ j then MvPolynomial.X (.inl (i, j)) else 0

/-- Invert the triangular determinant so that the Levi block is invertible. -/
private abbrev ParameterRing := Localization.Away (triangularMatrix R m).det

/-- The invertible triangular block in the localized parameter space. -/
private def parameterLevi : GL (Fin m) (ParameterRing R m) :=
  Matrix.GeneralLinearGroup.mk''
    ((triangularMatrix R m).map (algebraMap (Parameters R m) (ParameterRing R m)))
    (by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
      exact IsLocalization.Away.algebraMap_isUnit _)

private theorem parameterLevi_upper :
    (parameterLevi R m : Matrix (Fin m) (Fin m) (ParameterRing R m)).IsUpperTriangular := by
  intro i j hji
  simp only [id_eq] at hji
  simp [parameterLevi, triangularMatrix, not_le.mpr hji]

/-- Independent symmetric coordinates, with the lower triangle read from the upper one. -/
private def parameterSymmetric : Matrix (Fin m) (Fin m) (ParameterRing R m) :=
  fun i j ↦ algebraMap (Parameters R m) (ParameterRing R m)
    (MvPolynomial.X (.inr (min i j, max i j)))

private theorem parameterSymmetric_isSymm : (parameterSymmetric R m).IsSymm := by
  ext i j
  simp [parameterSymmetric, min_comm, max_comm]

/-- The flag point in the parameter ring. -/
private def parameterPoint : matrixSubgroup m (A := ParameterRing R m) :=
  ⟨GLSymplecticFin.leviHom (parameterLevi R m) *
    GLSymplecticFin.upperUnipotent (parameterSymmetric R m)
      (parameterSymmetric_isSymm R m), by
    apply (matrixSubgroup m).mul_mem
    · rw [mem_matrixSubgroup_iff]
      refine ⟨?_, ?_, ?_⟩
      · intro i j hji
        simpa [GLSymplecticFin.coe_leviHom, ← Fin.natAdd_eq_addNat] using
          parameterLevi_upper R m hji
      · intro i j hij
        have h := Matrix.blockTriangular_inv_of_blockTriangular (parameterLevi_upper R m)
        simpa [GLSymplecticFin.coe_leviHom, Matrix.coe_units_inv, ← Fin.natAdd_eq_addNat] using
          h hij
      · intro i j
        simp [GLSymplecticFin.coe_leviHom, ← Fin.natAdd_eq_addNat]
    · rw [mem_matrixSubgroup_iff]
      refine ⟨?_, ?_, ?_⟩ <;> intro i j
      · intro hji
        simp [GLSymplecticFin.coe_upperUnipotent, hji.ne']
      · intro hij
        simp [GLSymplecticFin.coe_upperUnipotent, ← Fin.natAdd_eq_addNat, hij.ne]
      · simp [GLSymplecticFin.coe_upperUnipotent, ← Fin.natAdd_eq_addNat]⟩

/-- The map induced by the universal flag matrix in the parameter ring. -/
private def parameterAlgHom : coordinateHopfAlgebra R m →ₐ[R] ParameterRing R m :=
  ((pointsMulEquiv R m (A := ParameterRing R m)).symm (parameterPoint R m)).ofConv

/-- The universal flag-preserving matrix. -/
private abbrev genericPoint : matrixSubgroup m (A := coordinateHopfAlgebra R m) :=
  pointsMulEquiv R m (A := coordinateHopfAlgebra R m)
    (toConv (AlgHom.id R (coordinateHopfAlgebra R m)))

/-- Read the universal matrix in paired sum coordinates. -/
private def genericMatrix : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m)
    (coordinateHopfAlgebra R m) :=
  (((GLSymplecticFin.mulEquivGLSymplectic m (coordinateHopfAlgebra R m)
      (genericPoint R m).val : GLSymplectic (Fin m) (coordinateHopfAlgebra R m)) :
      GL (Fin m ⊕ Fin m) (coordinateHopfAlgebra R m)) :
    Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) (coordinateHopfAlgebra R m))

private theorem genericMatrix_lowerLeft : (genericMatrix R m).toBlocks₂₁ = 0 := by
  ext i j
  have h := (mem_matrixSubgroup_iff m (genericPoint R m).val).mp (genericPoint R m).property
  simpa [genericMatrix, GLSymplecticFin.coe_mulEquivGLSymplectic,
    Equiv.coe_reindexGL, Matrix.toBlocks₂₁, ← Fin.natAdd_eq_addNat] using h.2.2 i j

private theorem genericMatrix_upper : (genericMatrix R m).toBlocks₁₁.IsUpperTriangular := by
  intro i j hji
  have h := (mem_matrixSubgroup_iff m (genericPoint R m).val).mp (genericPoint R m).property
  simpa [genericMatrix, GLSymplecticFin.coe_mulEquivGLSymplectic,
    Equiv.coe_reindexGL, Matrix.toBlocks₁₁] using h.1 i j hji

private theorem genericMatrix_equations :
    (genericMatrix R m).toBlocks₁₁ᵀ * (genericMatrix R m).toBlocks₂₂ = 1 ∧
    (genericMatrix R m).toBlocks₁₂ᵀ * (genericMatrix R m).toBlocks₂₂ =
      (genericMatrix R m).toBlocks₂₂ᵀ * (genericMatrix R m).toBlocks₁₂ := by
  have hmem := GLSymplectic.mem_iff_mem_symplecticGroup.mp
    (GLSymplecticFin.mulEquivGLSymplectic m _ (genericPoint R m).val).property
  have hmem : genericMatrix R m ∈ Matrix.symplecticGroup (Fin m) _ := hmem
  rw [← (genericMatrix R m).fromBlocks_toBlocks, genericMatrix_lowerLeft] at hmem
  have h := SymplecticGroup.fromBlocks_mem_iff.mp hmem
  exact ⟨by simpa using h.2.2, h.2.1⟩

private theorem genericMatrix_inverse :
    (genericMatrix R m).toBlocks₂₂ᵀ * (genericMatrix R m).toBlocks₁₁ = 1 ∧
    (genericMatrix R m).toBlocks₁₁ * (genericMatrix R m).toBlocks₂₂ᵀ = 1 := by
  have h := congrArg Matrix.transpose (genericMatrix_equations R m).1
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] at h
  exact ⟨h, mul_eq_one_comm.mp h⟩

/-- The upper-right block after removing the triangular Levi factor. -/
private def genericSymmetric : Matrix (Fin m) (Fin m) (coordinateHopfAlgebra R m) :=
  (genericMatrix R m).toBlocks₂₂ᵀ * (genericMatrix R m).toBlocks₁₂

private theorem genericSymmetric_isSymm : (genericSymmetric R m).IsSymm := by
  rw [Matrix.IsSymm, genericSymmetric, Matrix.transpose_mul, Matrix.transpose_transpose]
  exact (genericMatrix_equations R m).2

/-- Evaluate the polynomial parameters in the universal flag matrix. -/
private def evaluateParameters : Parameters R m →ₐ[R] coordinateHopfAlgebra R m :=
  MvPolynomial.aeval (Sum.elim
    (fun ij ↦ (genericMatrix R m).toBlocks₁₁ ij.1 ij.2)
    (fun ij ↦ genericSymmetric R m ij.1 ij.2))

private theorem evaluateParameters_triangularMatrix :
    (triangularMatrix R m).map (evaluateParameters R m) =
      (genericMatrix R m).toBlocks₁₁ := by
  ext i j
  by_cases hij : i ≤ j
  · simp [triangularMatrix, hij, evaluateParameters]
  · simp [triangularMatrix, hij, genericMatrix_upper R m (lt_of_not_ge hij)]

/-- The determinant parameter evaluates to a unit, so evaluation extends to the localization. -/
private theorem evaluateParameters_det_isUnit :
    IsUnit (evaluateParameters R m (triangularMatrix R m).det) := by
  rw [AlgHom.map_det, AlgHom.mapMatrix_apply, evaluateParameters_triangularMatrix]
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  exact isUnit_iff_exists_inv.mpr ⟨_, (genericMatrix_inverse R m).2⟩

/-- Evaluate the localized parameters in the universal flag coordinate algebra. -/
private def evaluateParameterRing : ParameterRing R m →ₐ[R] coordinateHopfAlgebra R m :=
  IsLocalization.Away.liftAlgHom (triangularMatrix R m).det
    (evaluateParameters_det_isUnit R m)

private theorem evaluateParameterRing_algebraMap (p : Parameters R m) :
    evaluateParameterRing R m (algebraMap (Parameters R m) (ParameterRing R m) p) =
      evaluateParameters R m p :=
  IsLocalization.Away.lift_eq _ (evaluateParameters_det_isUnit R m) _

private theorem evaluateParameterRing_levi :
    ((Matrix.GeneralLinearGroup.map (evaluateParameterRing R m).toRingHom
      (parameterLevi R m)) : Matrix (Fin m) (Fin m) (coordinateHopfAlgebra R m)) =
      (genericMatrix R m).toBlocks₁₁ := by
  ext i j
  simp only [Matrix.GeneralLinearGroup.map_apply, parameterLevi,
    Matrix.GeneralLinearGroup.val_mk'', Matrix.map_apply]
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evaluateParameterRing_algebraMap]
  exact congrFun (congrFun (evaluateParameters_triangularMatrix R m) i) j

private theorem evaluateParameterRing_symmetric :
    (parameterSymmetric R m).map (evaluateParameterRing R m).toRingHom = genericSymmetric R m := by
  ext i j
  simp only [Matrix.map_apply]
  dsimp only [parameterSymmetric]
  rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, evaluateParameterRing_algebraMap]
  simp only [evaluateParameters, MvPolynomial.aeval_X, Sum.elim_inr]
  rcases le_total i j with hij | hji
  · simp [min_eq_left hij, max_eq_right hij]
  · simp [min_eq_right hji, max_eq_left hji, (genericSymmetric_isSymm R m).apply i j]

/-- Reconstruct the universal matrix from its Levi and symmetric blocks. -/
private theorem genericMatrix_reconstruction
    (Q : GL (Fin m) (coordinateHopfAlgebra R m))
    (hQ : (Q : Matrix (Fin m) (Fin m) _) = (genericMatrix R m).toBlocks₁₁) :
    Matrix.fromBlocks (Q : Matrix (Fin m) (Fin m) _) 0 0
        ((Q⁻¹ : GL (Fin m) (coordinateHopfAlgebra R m)) : Matrix (Fin m) (Fin m) _)ᵀ *
      Matrix.fromBlocks 1 (genericSymmetric R m) 0 1 = genericMatrix R m := by
  have hinv :
      ((Q⁻¹ : GL (Fin m) (coordinateHopfAlgebra R m)) : Matrix (Fin m) (Fin m) _) =
        (genericMatrix R m).toBlocks₂₂ᵀ := by
    apply Units.inv_eq_of_mul_eq_one_right
    rw [hQ]
    exact (genericMatrix_inverse R m).2
  rw [Matrix.fromBlocks_multiply]
  apply Matrix.ext_iff_blocks.mpr
  simp [hQ, hinv, genericSymmetric, ← mul_assoc,
    (genericMatrix_inverse R m).2, genericMatrix_lowerLeft R m]

/-- The parameter point after any value-ring map is its mapped Levi–unipotent block product. -/
private theorem parameterPoint_map_matrix
    {S : Type*} [CommRing S] (f : ParameterRing R m →+* S) :
    (((GLSymplecticFin.mulEquivGLSymplectic m S
        (GLSymplecticFin.IsotropicFlag.map m f (parameterPoint R m)).val :
        GLSymplectic (Fin m) S) : GL (Fin m ⊕ Fin m) S) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) S) =
      Matrix.fromBlocks
          (Matrix.GeneralLinearGroup.map f (parameterLevi R m) : Matrix (Fin m) (Fin m) S) 0 0
          (((Matrix.GeneralLinearGroup.map f (parameterLevi R m))⁻¹ : GL (Fin m) S) :
            Matrix (Fin m) (Fin m) S)ᵀ *
        Matrix.fromBlocks 1 ((parameterSymmetric R m).map f) 0 1 := by
  rw [GLSymplecticFin.IsotropicFlag.coe_map]
  dsimp only [parameterPoint]
  rw [map_mul, GLSymplecticFin.map_leviHom, GLSymplecticFin.map_upperUnipotent, map_mul]
  simp

private theorem evaluateParameterRing_point :
    GLSymplecticFin.IsotropicFlag.map m (evaluateParameterRing R m).toRingHom
      (parameterPoint R m) = genericPoint R m := by
  apply Subtype.ext
  apply (GLSymplecticFin.mulEquivGLSymplectic m _).injective
  apply Subtype.ext
  apply Units.ext
  rw [parameterPoint_map_matrix, evaluateParameterRing_symmetric]
  exact genericMatrix_reconstruction R m _ (evaluateParameterRing_levi R m)

private theorem evaluateParameterRing_comp_parameterAlgHom :
    (evaluateParameterRing R m).comp (parameterAlgHom R m) =
      AlgHom.id R (coordinateHopfAlgebra R m) := by
  apply toConv_injective
  apply (pointsMulEquiv R m (A := coordinateHopfAlgebra R m)).injective
  rw [← AlgHom.mapValue_apply, pointsMulEquiv_mapValue]
  simp only [parameterAlgHom, toConv_ofConv, MulEquiv.apply_symm_apply]
  exact evaluateParameterRing_point R m

private theorem parameterAlgHom_injective : Function.Injective (parameterAlgHom R m) := by
  have hleft : Function.LeftInverse (evaluateParameterRing R m) (parameterAlgHom R m) :=
    fun x ↦ DFunLike.congr_fun (evaluateParameterRing_comp_parameterAlgHom R m) x
  exact hleft.injective

private theorem triangularMatrix_det_ne_zero [Nontrivial R] :
    (triangularMatrix R m).det ≠ 0 := by
  let e : Parameters R m →ₐ[R] R := MvPolynomial.aeval (Sum.elim
    (fun ij ↦ if ij.1 = ij.2 then 1 else 0) (fun _ ↦ 0))
  have hmatrix : (triangularMatrix R m).map e = 1 := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [triangularMatrix, e]
    · by_cases hle : i ≤ j <;> simp [triangularMatrix, e, hij, hle]
  intro hzero
  have h := congrArg e hzero
  rw [map_zero, AlgHom.map_det, AlgHom.mapMatrix_apply, hmatrix, Matrix.det_one] at h
  exact one_ne_zero h

/-- The standard complete isotropic flag stabilizer of `Sp₂ₘ` is geometrically connected
over every field, including characteristic two and rank zero. -/
theorem geometricallyConnectedCommHopfAlgProperty_coordinateHopfAlgebra
    (k : Type u) [Field k] :
    geometricallyConnectedCommHopfAlgProperty k (coordinateHopfAlgebra k m) := by
  rw [geometricallyConnectedCommHopfAlgProperty_iff]
  intro K _ _
  let _ : IsDomain (ParameterRing K m) :=
    Localization.Away.isDomain (triangularMatrix_det_ne_zero K m)
  have hconnected : ConnectedSpace (PrimeSpectrum (coordinateHopfAlgebra K m)) :=
    connectedSpace_primeSpectrum_of_injective (parameterAlgHom K m).toRingHom
      (parameterAlgHom_injective K m)
  let e := (Algebra.TensorProduct.comm k (coordinateHopfAlgebra k m) K).toRingEquiv.trans
    (CommHopfAlgCat.ofIso (coordinateHopfAlgebraBaseChangeIso k K m)).toAlgEquiv.toRingEquiv
  exact (PrimeSpectrum.homeomorphOfRingEquiv e).connectedSpace_iff.mpr hconnected

end

end TauCeti.Symplectic.IsotropicFlag
