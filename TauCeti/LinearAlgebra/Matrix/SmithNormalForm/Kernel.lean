/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Kernels after specialization of a diagonalization

A specified diagonalization `U * M * V = diagonal d`, with unit determinants for `U` and `V`,
computes the kernel of `M` over every coefficient ring. There is one free coordinate for each
zero entry of the original diagonal, and one annihilator coordinate for each nonzero entry.
The latter factors can become nonzero after specialization, even when the original kernel is
zero. In particular the zero positions must be tested before applying the coefficient map.

`Matrix.kerMapEquivOfMulMulEqDiagonal` gives this equivalence with both coordinate directions.
It does not choose a diagonalization or require a divisibility ordering of its entries.
This is useful for fixed modules by applying it to the matrix of an endomorphism minus identity.

The construction uses Mathlib's `Submodule.torsionBy`, `Matrix.toLinearEquiv` and restriction of
linear equivalences to submodules.

## References

* Bourbaki, *Algebra*, Chapter VII, §4 (elementary divisors).
-/

public section

open Matrix

namespace RingHom

variable {R A ι : Type*} [CommSemiring R] [CommSemiring A] [Fintype ι] [DecidableEq ι]

/-- The specialized diagonal kernel has free coordinates at the original zero entries and
annihilator coordinates at the original nonzero entries. No injectivity of `f` is required. -/
noncomputable def diagonalKerEquiv (f : R →+* A) (d : ι → R) :
    LinearMap.ker (diagonal (f ∘ d)).mulVecLin ≃ₗ[A]
      ({i // d i = 0} → A) ×
        ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i))) := by
  classical
  exact
    { toFun := fun x ↦ (fun i ↦ x.val i, fun i ↦ ⟨x.val i, by
        simpa only [Submodule.mem_torsionBy_iff, smul_eq_mul, mulVecLin_apply,
          mulVec_diagonal, Function.comp_apply, Pi.zero_apply] using
          congrFun (LinearMap.mem_ker.mp x.property) i⟩)
      invFun := fun x ↦ ⟨fun i ↦ if h : d i = 0 then x.1 ⟨i, h⟩ else (x.2 ⟨i, h⟩ : A), by
        apply LinearMap.mem_ker.mpr
        ext i
        by_cases h : d i = 0
        · simp [mulVec_diagonal, h]
        · simpa only [mulVecLin_apply, mulVec_diagonal, Function.comp_apply,
            dite_eq_right h, Pi.zero_apply, Submodule.mem_torsionBy_iff, smul_eq_mul] using
            (x.2 ⟨i, h⟩).property⟩
      left_inv := fun x ↦ by
        ext i
        dsimp only
        split_ifs <;> rfl
      right_inv := fun x ↦ by
        apply Prod.ext
        · funext i
          simp [i.property]
        · funext i
          apply Subtype.ext
          simp [i.property]
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- The free coordinate is the corresponding coordinate of the kernel vector. -/
@[simp]
theorem diagonalKerEquiv_fst (f : R →+* A) (d : ι → R)
    (x : LinearMap.ker (diagonal (f ∘ d)).mulVecLin) (i : {i // d i = 0}) :
    (diagonalKerEquiv f d x).1 i = x.val i := (rfl)

/-- The annihilator coordinate has the same underlying scalar as the kernel vector. -/
@[simp]
theorem diagonalKerEquiv_snd (f : R →+* A) (d : ι → R)
    (x : LinearMap.ker (diagonal (f ∘ d)).mulVecLin) (i : {i // d i ≠ 0}) :
    ((diagonalKerEquiv f d x).2 i : A) = x.val i := (rfl)

open scoped Classical in
/-- Reconstruct a vector by inserting its free and annihilator coordinates. -/
@[simp]
theorem diagonalKerEquiv_symm_apply (f : R →+* A) (d : ι → R)
    (x : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) (i : ι) :
    ((diagonalKerEquiv f d).symm x).val i =
      if h : d i = 0 then x.1 ⟨i, h⟩ else (x.2 ⟨i, h⟩ : A) := by
  classical
  rfl

end RingHom

namespace Matrix

variable {R A ι : Type*} [CommRing R] [CommRing A] [Fintype ι] [DecidableEq ι]

/-- A unimodular diagonalization identifies the specialized kernel with its free and
annihilator coordinates. The original vector is `V.map f` times the reconstructed diagonal
coordinates; thus the forward coordinate change uses the inverse of `V.map f`. -/
noncomputable def kerMapEquivOfMulMulEqDiagonal (M : Matrix ι ι R) (f : R →+* A)
    (U V : Matrix ι ι R) (d : ι → R) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = diagonal d) :
    LinearMap.ker (M.map f).mulVecLin ≃ₗ[A]
      ({i // d i = 0} → A) ×
        ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i))) := by
  let e := (V.map f).toLinearEquiv (Pi.basisFun A ι) (by
    simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hV.map f)
  have hk : LinearMap.ker (diagonal (f ∘ d)).mulVecLin =
      (LinearMap.ker (M.map f).mulVecLin).comap e.toLinearMap := by
    have hd : U.map f * M.map f * V.map f = diagonal (f ∘ d) := by
      simpa only [Matrix.map_mul, diagonal_map f.map_zero, Function.comp_def] using
        congrArg (fun N ↦ N.map f) h
    ext x
    simp only [Submodule.mem_comap, LinearMap.mem_ker, mulVecLin_apply, e]
    rw [← hd, ← mulVec_mulVec, ← mulVec_mulVec]
    exact (mulVec_injective_of_isUnit
      ((U.map f).isUnit_iff_isUnit_det.mpr (by
        simpa only [RingHom.map_det, RingHom.mapMatrix_apply] using hU.map f))).eq_iff' (by simp)
  exact ((LinearEquiv.ofEq _ _ hk).trans
    (e.ofSubmodule' (LinearMap.ker (M.map f).mulVecLin))).symm.trans
      (f.diagonalKerEquiv d)

open scoped Classical in
/-- Reconstruct an original kernel vector by applying the right diagonalizing matrix to its
free and annihilator coordinates. -/
@[simp]
theorem kerMapEquivOfMulMulEqDiagonal_symm_apply (M : Matrix ι ι R) (f : R →+* A)
    (U V : Matrix ι ι R) (d : ι → R) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = diagonal d)
    (x : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) :
    ((kerMapEquivOfMulMulEqDiagonal M f U V d hU hV h).symm x).val =
      V.map f *ᵥ (fun i ↦ if h : d i = 0 then x.1 ⟨i, h⟩ else (x.2 ⟨i, h⟩ : A)) := by
  classical
  simp only [kerMapEquivOfMulMulEqDiagonal, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.ofSubmodule'_apply,
    LinearEquiv.coe_ofEq_apply]
  rfl

/-- The free coordinates are read after applying the inverse right diagonalizing matrix. -/
@[simp]
theorem kerMapEquivOfMulMulEqDiagonal_fst (M : Matrix ι ι R) (f : R →+* A)
    (U V : Matrix ι ι R) (d : ι → R) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = diagonal d) (x : LinearMap.ker (M.map f).mulVecLin)
    (i : {i // d i = 0}) :
    (kerMapEquivOfMulMulEqDiagonal M f U V d hU hV h x).1 i =
      ((V.map f)⁻¹ *ᵥ x.val) i := by
  simp only [kerMapEquivOfMulMulEqDiagonal, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, RingHom.diagonalKerEquiv_fst, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofSubmodule'_symm_apply]
  rfl

/-- The annihilator coordinates are read after applying the same inverse coordinate change. -/
@[simp]
theorem kerMapEquivOfMulMulEqDiagonal_snd (M : Matrix ι ι R) (f : R →+* A)
    (U V : Matrix ι ι R) (d : ι → R) (hU : IsUnit U.det) (hV : IsUnit V.det)
    (h : U * M * V = diagonal d) (x : LinearMap.ker (M.map f).mulVecLin)
    (i : {i // d i ≠ 0}) :
    ((kerMapEquivOfMulMulEqDiagonal M f U V d hU hV h x).2 i : A) =
      ((V.map f)⁻¹ *ᵥ x.val) i := by
  simp only [kerMapEquivOfMulMulEqDiagonal, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, RingHom.diagonalKerEquiv_snd, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofSubmodule'_symm_apply]
  rfl

end Matrix
