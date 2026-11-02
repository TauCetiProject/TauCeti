/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Kernels after specializing a diagonalization

A specified diagonalization `U * M * V = diagonal d` over a commutative ring gives
coordinates for the kernel after any coefficient homomorphism. Zero positions of the
original diagonal contribute free coordinates; every other position contributes the
annihilator of its specialized entry. The indexing retains the original zero positions,
even if specialization kills further diagonal entries.

The inverse is multiplication by the specialized column transformation `V`. Applying
this construction to `γ - 1` computes fixed vectors, including torsion that need not
come from integral fixed vectors. No existence or uniqueness of a diagonalization is
assumed beyond the supplied matrix identity.

The construction uses Mathlib's `Matrix.GeneralLinearGroup.toLin` and
`Submodule.torsionBy`. For the diagonalization method see Bourbaki, *Algebra*,
Chapter VII, §4 (elementary divisors).
-/

public section

namespace Matrix

variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A]

/-- A diagonalization detects the specialized kernel in the coordinates given by its
column transformation, without any flatness hypothesis. -/
theorem mulVec_map_eq_zero_iff_of_diagonalization (M : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * M * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : ι → A) :
    M.map f *ᵥ ((GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ v) = 0 ↔
      ∀ i, f (d i) * v i = 0 := by
  have hd := congrArg (fun N : Matrix ι ι R ↦ N.map f) h
  simp only [Matrix.map_mul, diagonal_map (map_zero f)] at hd
  have he : diagonal (fun i ↦ f (d i)) *ᵥ v =
      (GeneralLinearGroup.map f U : Matrix ι ι A) *ᵥ
        (M.map f *ᵥ ((GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ v)) := by
    rw [← hd, mulVec_mulVec, mulVec_mulVec]
    rfl
  have hz : (GeneralLinearGroup.map f U : Matrix ι ι A) *ᵥ
      (M.map f *ᵥ ((GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ v)) = 0 ↔
      M.map f *ᵥ ((GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ v) = 0 :=
    (GeneralLinearGroup.toLin (GeneralLinearGroup.map f U)).toLinearEquiv.map_eq_zero_iff
  rw [← he] at hz
  simpa only [mulVec_diagonal, funext_iff, Pi.zero_apply] using hz.symm

/-- Kernel coordinates from a specified diagonalization. Original zero entries give free
factors, and original nonzero entries give their full specialized annihilators. -/
noncomputable def kerEquivOfDiagonalization (M : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * M * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) :
    LinearMap.ker (M.map f).mulVecLin ≃ₗ[A]
      ({i // d i = 0} → A) ×
        ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i))) := by
  classical
  let e := (GeneralLinearGroup.toLin (GeneralLinearGroup.map f V)).toLinearEquiv
  have heval (x : ι → A) :
      e x = (GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ x := rfl
  have hc (v : LinearMap.ker (M.map f).mulVecLin) :
      ∀ i, f (d i) * e.symm v.val i = 0 := by
    apply (mulVec_map_eq_zero_iff_of_diagonalization M U V d h f _).mp
    rw [← heval, e.apply_symm_apply]
    exact v.property
  let assemble (z : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) : ι → A :=
    fun i ↦ if hi : d i = 0 then z.1 ⟨i, hi⟩ else (z.2 ⟨i, hi⟩).val
  exact
    { toFun := fun v ↦ ⟨fun i ↦ e.symm v.val i,
        fun i ↦ ⟨e.symm v.val i, hc v i⟩⟩
      invFun := fun z ↦ ⟨e (assemble z), by
        apply (mulVec_map_eq_zero_iff_of_diagonalization M U V d h f _).mpr
        intro i
        by_cases hi : d i = 0
        · simp [assemble, hi]
        · have hz : f (d i) * (z.2 ⟨i, hi⟩).val = 0 := (z.2 ⟨i, hi⟩).property
          simpa only [assemble, dite_eq_right hi] using hz⟩
      left_inv := fun v ↦ by
        apply Subtype.ext
        apply e.symm.injective
        ext i
        simp only [LinearEquiv.symm_apply_apply, assemble]
        split_ifs <;> rfl
      right_inv := fun z ↦ by
        apply Prod.ext
        · ext i
          simp [assemble, i.property]
        · ext i
          simp [assemble, i.property]
      map_add' := fun v w ↦ by
        apply Prod.ext
        · ext i
          exact congrFun (e.symm.map_add v.val w.val) i
        · ext i
          exact congrFun (e.symm.map_add v.val w.val) i
      map_smul' := fun a v ↦ by
        apply Prod.ext
        · ext i
          exact congrFun (e.symm.map_smul a v.val) i
        · ext i
          exact congrFun (e.symm.map_smul a v.val) i }

/-- The free coordinates are the zero positions of the original diagonal, read after
applying the inverse specialized column transformation. -/
@[simp]
theorem kerEquivOfDiagonalization_fst_apply (M : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * M * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i = 0}) :
    (kerEquivOfDiagonalization M U V d h f v).1 i =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  rfl

/-- The annihilator coordinates use the same inverse column transformation. -/
@[simp]
theorem kerEquivOfDiagonalization_snd_apply (M : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * M * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i ≠ 0}) :
    ((kerEquivOfDiagonalization M U V d h f v).2 i : A) =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  rfl

open Classical in
/-- The inverse assembles free and annihilator coordinates and applies the specialized
column transformation. The zero/nonzero split is made before specialization. -/
@[simp]
theorem kerEquivOfDiagonalization_symm_apply (M : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * M * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A)
    (z : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) :
    ((kerEquivOfDiagonalization M U V d h f).symm z : ι → A) =
      (GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ
        (fun i ↦ if hi : d i = 0 then z.1 ⟨i, hi⟩ else (z.2 ⟨i, hi⟩).val) := by
  classical
  rfl

/-- Fixed vectors after specialization, computed from a diagonalization of `γ - 1`.
The nonzero diagonal factors retain all torsion in the coefficient ring. -/
noncomputable def fixedEquivOfDiagonalization (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) :
    (γ.map f).mulVecLin.fixedSubmodule ≃ₗ[A]
      ({i // d i = 0} → A) ×
        ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i))) :=
  (LinearEquiv.ofEq _ _ (by
    rw [Matrix.map_sub f (map_sub f), Matrix.map_one f (map_zero f) (map_one f)]
    ext v
    simp only [LinearMap.mem_fixedSubmodule_iff, LinearMap.mem_ker,
      mulVecLin_apply, sub_mulVec, one_mulVec, sub_eq_zero])).trans
    (kerEquivOfDiagonalization (γ - 1) U V d h f)

/-- The free fixed-vector coordinates are read by the inverse column transformation. -/
@[simp]
theorem fixedEquivOfDiagonalization_fst_apply (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : (γ.map f).mulVecLin.fixedSubmodule) (i : {i // d i = 0}) :
    (fixedEquivOfDiagonalization γ U V d h f v).1 i =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  rfl

/-- The torsion fixed-vector coordinates are read by the inverse column transformation. -/
@[simp]
theorem fixedEquivOfDiagonalization_snd_apply (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : (γ.map f).mulVecLin.fixedSubmodule) (i : {i // d i ≠ 0}) :
    ((fixedEquivOfDiagonalization γ U V d h f v).2 i : A) =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  rfl

open Classical in
/-- Reconstruct a fixed vector by the specialized column transformation. -/
@[simp]
theorem fixedEquivOfDiagonalization_symm_apply (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A)
    (z : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) :
    ((fixedEquivOfDiagonalization γ U V d h f).symm z : ι → A) =
      (GeneralLinearGroup.map f V : Matrix ι ι A) *ᵥ
        (fun i ↦ if hi : d i = 0 then z.1 ⟨i, hi⟩ else (z.2 ⟨i, hi⟩).val) := by
  classical
  rfl

end Matrix
