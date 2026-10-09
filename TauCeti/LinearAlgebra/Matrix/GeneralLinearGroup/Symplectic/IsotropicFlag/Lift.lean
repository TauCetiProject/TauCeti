/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.IsotropicFlag.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.GaussianGeneration
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Lift

/-!
# Lifting symplectic isotropic flag matrices

A symplectic matrix preserving the standard complete isotropic flag factors as
`diag(P, P⁻ᵀ) [1 T; 0 1]`, with `P` upper triangular and invertible and `T` symmetric.
Both parameters lift along quotient maps that reflect units, including quotients by nilpotent
ideals, so the flag subgroup has the infinitesimal lifting property over every commutative
ring, including characteristic two.

The factorization reuses `GLSymplecticFin.exists_gaussian_decomposition_of_isUnit_toBlocks₁₁`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6.
* SGA 3, Exposé XXII, for the split symplectic group and its flag stabilizers.
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin.IsotropicFlag

noncomputable section

variable {m : ℕ} {R : Type*} [CommRing R]

/-- An upper-triangular general-linear Levi element preserves the isotropic flag. -/
@[simp↓] theorem leviHom_mem_matrixSubgroup (P : upperTriangularGroup (Fin m) R) :
    leviHom P.val ∈ matrixSubgroup m := by
  rw [mem_matrixSubgroup_iff]
  have hinv := UpperTriangularGroup.isUpperTriangular P⁻¹
  simp only [coe_leviHom, Matrix.submatrix_apply, finSumFinEquiv_symm_apply_castAdd,
    ← Fin.natAdd_eq_addNat, finSumFinEquiv_symm_apply_natAdd,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁,
    Matrix.transpose_apply, Matrix.zero_apply]
  exact ⟨fun i j hij ↦ (UpperTriangularGroup.mem_iff.mp P.2) hij,
    fun i j hij ↦ hinv hij, fun _ _ ↦ trivial⟩

/-- Every symmetric upper unipotent block preserves the isotropic flag. -/
@[simp↓] theorem upperUnipotent_mem_matrixSubgroup (T : Matrix (Fin m) (Fin m) R)
    (hT : T.IsSymm) : upperUnipotent T hT ∈ matrixSubgroup m := by
  rw [mem_matrixSubgroup_iff]
  simp only [coe_upperUnipotent, Matrix.submatrix_apply,
    finSumFinEquiv_symm_apply_castAdd, ← Fin.natAdd_eq_addNat,
    finSumFinEquiv_symm_apply_natAdd, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₂₂, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
  exact ⟨fun i j hij ↦ Matrix.one_apply_ne (ne_of_gt hij),
    fun i j hij ↦ Matrix.one_apply_ne (ne_of_lt hij), fun _ _ ↦ trivial⟩

/-- Every flag-preserving symplectic matrix is the product of an upper-triangular Levi element
and an upper unipotent with symmetric block. -/
theorem exists_leviHom_mul_upperUnipotent (g : matrixSubgroup m (A := R)) :
    ∃ (P : upperTriangularGroup (Fin m) R) (T : Matrix (Fin m) (Fin m) R)
      (hT : T.IsSymm), g.val = leviHom P.val * upperUnipotent T hT := by
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R :=
    (((mulEquivGLSymplectic m R g.val : GLSymplectic (Fin m) R) :
      GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R)
  -- The zero lower-left block makes the upper-left block invertible.
  have hzero : M.toBlocks₂₁ = 0 := by
    ext i j
    have hg := (mem_matrixSubgroup_iff m g.val).mp g.2
    simpa only [M, coe_mulEquivGLSymplectic, Equiv.coe_reindexGL,
      Matrix.submatrix_apply, Matrix.toBlocks₂₁, Matrix.of_apply, Equiv.symm_symm,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat,
      Matrix.zero_apply] using hg.2.2 i j
  have hsymp : M ∈ Matrix.symplecticGroup (Fin m) R :=
    GLSymplectic.mem_iff_mem_symplecticGroup.mp (mulEquivGLSymplectic m R g.val).2
  have hAD : M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 := by
    have hblocks := SymplecticGroup.fromBlocks_mem_iff.mp (M.fromBlocks_toBlocks.symm ▸ hsymp)
    simpa only [hzero, Matrix.transpose_zero, Matrix.zero_mul, sub_zero] using hblocks.2.2
  have hunit : IsUnit M.toBlocks₁₁ := by
    apply (Matrix.isUnit_iff_isUnit_det _).mpr
    apply isUnit_of_mul_isUnit_left (y := M.toBlocks₂₂.det)
    rw [← Matrix.det_transpose M.toBlocks₁₁, ← Matrix.det_mul, hAD, Matrix.det_one]
    exact isUnit_one
  obtain ⟨S, T, P, hS, hT, hfactor⟩ :=
    exists_gaussian_decomposition_of_isUnit_toBlocks₁₁ g.val hunit
  -- Read the Gaussian factors in paired coordinates to eliminate the lower unipotent.
  have hmatrix : M = Matrix.fromBlocks (P : Matrix _ _ R) ((P : Matrix _ _ R) * T)
      (S * (P : Matrix _ _ R))
      (S * (P : Matrix _ _ R) * T + ((P⁻¹ : GL _ R) : Matrix _ _ R)ᵀ) := by
    have h := congrArg (fun x : GLSymplecticFin m R ↦
      (((mulEquivGLSymplectic m R x : GLSymplectic (Fin m) R) :
        GL (Fin m ⊕ Fin m) R) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R))
      hfactor
    simpa only [M, map_mul, Subgroup.coe_mul, Units.val_mul,
      mulEquivGLSymplectic_leviHom, coe_mulEquivGLSymplectic,
      coe_mulEquivGLSymplectic_lowerUnipotent,
      coe_mulEquivGLSymplectic_upperUnipotent, GLSymplectic.coe_ofSymplecticGroup,
      GLSymplectic.coe_leviHom, Matrix.fromBlocks_multiply,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero,
      Matrix.zero_mul, zero_add, add_zero] using h
  have hSP : S * (P : Matrix _ _ R) = 0 := by
    simpa only [Matrix.toBlocks_fromBlocks₂₁, hzero] using
      (congrArg Matrix.toBlocks₂₁ hmatrix).symm
  have hSzero : S = 0 := by
    have h := congrArg (fun X : Matrix (Fin m) (Fin m) R ↦
      X * ((P⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R)) hSP
    simpa only [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.mul_one, Matrix.zero_mul] using h
  have hP : P ∈ upperTriangularGroup (Fin m) R := by
    rw [UpperTriangularGroup.mem_iff]
    intro i j hij
    have hg := (mem_matrixSubgroup_iff m g.val).mp g.2
    have hentry := congrArg (fun X : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R ↦
      X (Sum.inl i) (Sum.inl j)) hmatrix
    rw [Matrix.fromBlocks_apply₁₁] at hentry
    rw [← hentry]
    simpa only [M, coe_mulEquivGLSymplectic, Equiv.coe_reindexGL,
      Matrix.submatrix_apply, Equiv.symm_symm, finSumFinEquiv_apply_left] using hg.1 i j hij
  refine ⟨⟨P, hP⟩, T, hT, ?_⟩
  simpa only [hSzero, lowerUnipotent_zero, one_mul] using hfactor

/-- Reduction along a quotient map that reflects units is surjective on the symplectic
isotropic flag subgroup. No invertibility of two is required. -/
theorem map_quotient_mk_surjective (I : Ideal R) [IsLocalHom (Ideal.Quotient.mk I)] :
    Function.Surjective (map m (Ideal.Quotient.mk I)) := by
  classical
  intro g
  obtain ⟨P, T, hT, hg⟩ := exists_leviHom_mul_upperUnipotent g
  obtain ⟨Q, hQ⟩ := UpperTriangularGroup.map_quotient_mk_surjective I P
  choose a ha using fun i j ↦ Ideal.Quotient.mk_surjective (T i j)
  let U : Matrix (Fin m) (Fin m) R := Matrix.of fun i j ↦ if i ≤ j then a i j else a j i
  have hU : U.IsSymm := by
    rw [Matrix.IsSymm]
    ext i j
    simp only [Matrix.transpose_apply, U, Matrix.of_apply]
    split_ifs <;> grind
  have hUT : U.map (Ideal.Quotient.mk I) = T := by
    ext i j
    simp only [U, Matrix.map_apply, Matrix.of_apply]
    split_ifs with hij
    · exact ha i j
    · rw [ha j i, hT.apply]
  refine ⟨⟨leviHom Q.val * upperUnipotent U hU,
    (matrixSubgroup m).mul_mem (leviHom_mem_matrixSubgroup Q)
      (upperUnipotent_mem_matrixSubgroup U hU)⟩, ?_⟩
  apply Subtype.ext
  rw [coe_map, map_mul, map_leviHom, map_upperUnipotent]
  have hQval := congrArg Subtype.val hQ
  rw [UpperTriangularGroup.coe_map] at hQval
  rw [hQval]
  simpa only [hUT] using hg.symm

end

end TauCeti.GLSymplecticFin.IsotropicFlag
