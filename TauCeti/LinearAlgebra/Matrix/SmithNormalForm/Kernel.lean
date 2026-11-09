/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.FixedSubmodule
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import TauCeti.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Algebra.Module.Submodule.Equiv

/-!
# Kernel coordinates from a diagonalization

A specified diagonalization `L * M * Q = diagonal d` gives kernel coordinates after
any change of coefficient rings. Zero entries of the original diagonal give free
coordinates; each remaining entry gives its annihilator in the new ring. In
particular, a nonzero integral entry may contribute new kernel vectors after reduction.

The transformations are retained explicitly: coordinates are read using `Q⁻¹`, and
vectors are reconstructed using `Q`. No flatness or injectivity of the coefficient
map is needed. Applying this to `M = γ - 1` computes fixed vectors of a lattice action.
The diagonal step, `RingHom.diagonalKerEquiv`, works over commutative semirings.

We use Mathlib's `Submodule.torsionBy`, its general linear group and restriction of
linear equivalences to submodules. See Bourbaki, *Algebra*, Chapter VII, §4,
for elementary divisors and diagonal presentations over principal ideal domains.
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

variable {ι R A : Type*} [Fintype ι] [DecidableEq ι] [CommRing R] [CommRing A]

/-- A diagonalization tests kernel membership after any coefficient-ring map, using
inverse right-transformation coordinates. Nonzero diagonal entries are not cancelled. -/
theorem mulVec_eq_zero_iff_of_diagonalization (M : Matrix ι ι R)
    (L Q : GeneralLinearGroup ι R) (d : ι → R)
    (h : (L : Matrix ι ι R) * M * (Q : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (x : ι → A) :
    M.map f *ᵥ x = 0 ↔
      ∀ i, f (d i) * ((GeneralLinearGroup.map f Q⁻¹ : GeneralLinearGroup ι A) *ᵥ x) i = 0 := by
  have hd := congrArg (fun N : Matrix ι ι R ↦ N.map f) h
  simp only [Matrix.map_mul, diagonal_map (map_zero f)] at hd
  have he : (GeneralLinearGroup.map f L : Matrix ι ι A) *ᵥ (M.map f *ᵥ x) =
      diagonal (fun i ↦ f (d i)) *ᵥ
        ((GeneralLinearGroup.map f Q⁻¹ : GeneralLinearGroup ι A) *ᵥ x) := by
    rw [← hd]
    rw [← mulVec_mulVec, ← mulVec_mulVec,
      mulVec_mulVec x ((Q : Matrix ι ι R).map f)]
    have hq : (Q : Matrix ι ι R).map f *
        (GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) = 1 :=
      congrArg Units.val (GeneralLinearGroup.map_mul_map_inv f Q)
    rw [hq, one_mulVec]
    congr 1
  constructor
  · intro hx i
    have hz := congrFun (he.symm.trans (by rw [hx, mulVec_zero])) i
    simpa only [mulVec_diagonal, Pi.zero_apply] using hz
  · intro hx
    have hz : (GeneralLinearGroup.map f L : Matrix ι ι A) *ᵥ (M.map f *ᵥ x) = 0 := by
      rw [he]
      ext i
      simpa only [mulVec_diagonal, Pi.zero_apply] using hx i
    have hz' := congrArg
      (fun y ↦ (GeneralLinearGroup.map f L⁻¹ : Matrix ι ι A) *ᵥ y) hz
    rw [mulVec_mulVec, ← GeneralLinearGroup.coe_mul,
      GeneralLinearGroup.map_inv_mul_map, GeneralLinearGroup.coe_one, one_mulVec] at hz'
    simpa only [mulVec_zero] using hz'

/-- Given a diagonalization, the kernel over a new coefficient ring is the product of
free coordinates at the original zero entries and annihilators at the other entries.
The partition is made before applying `f`, so entries killed by `f` are retained. -/
noncomputable def kerEquivProdTorsionOfDiagonalization (M : Matrix ι ι R)
    (L Q : GeneralLinearGroup ι R) (d : ι → R)
    (h : (L : Matrix ι ι R) * M * (Q : Matrix ι ι R) = diagonal d)
    (f : R →+* A) :
    LinearMap.ker (M.map f).mulVecLin ≃ₗ[A]
      ({i // d i = 0} → A) ×
        ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i))) := by
  let e := (GeneralLinearGroup.map f Q : Matrix ι ι A).toLinearEquiv
    (Pi.basisFun A ι) (isUnits_det_units _)
  have hk : LinearMap.ker (diagonal (f ∘ d)).mulVecLin =
      (LinearMap.ker (M.map f).mulVecLin).comap e.toLinearMap := by
    have hd : (GeneralLinearGroup.map f L : Matrix ι ι A) * M.map f *
        (GeneralLinearGroup.map f Q : Matrix ι ι A) = diagonal (f ∘ d) := by
      -- Expose the entrywise matrix maps underlying the mapped GL coercions so that
      -- Matrix.map_mul can match the mapped diagonalization hypothesis below.
      change (L : Matrix ι ι R).map f * M.map f * (Q : Matrix ι ι R).map f = _
      simpa only [Matrix.map_mul, diagonal_map f.map_zero, Function.comp_def] using
        congrArg (fun N : Matrix ι ι R ↦ N.map f) h
    ext x
    simp only [Submodule.mem_comap, LinearMap.mem_ker, LinearEquiv.coe_toLinearMap, e,
      toLinearEquiv_basisFun_apply, mulVecLin_apply]
    rw [← hd, ← mulVec_mulVec, ← mulVec_mulVec]
    exact (mulVec_injective_of_isUnit (GeneralLinearGroup.map f L).isUnit).eq_iff'
      (by simp)
  exact ((LinearEquiv.ofEq _ _ hk).trans
    (e.ofSubmodule' (LinearMap.ker (M.map f).mulVecLin))).symm.trans
      (f.diagonalKerEquiv d)

variable (M : Matrix ι ι R) (L Q : GeneralLinearGroup ι R) (d : ι → R)
  (h : (L : Matrix ι ι R) * M * (Q : Matrix ι ι R) = diagonal d) (f : R →+* A)

/-- Free coordinates are the entries of the inverse right transformation at the
original zero diagonal positions. -/
@[simp]
theorem kerEquivProdTorsionOfDiagonalization_fst_apply
    (x : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i = 0}) :
    (kerEquivProdTorsionOfDiagonalization M L Q d h f x).1 i =
      ((GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) *ᵥ (x : ι → A)) i := by
  simp only [kerEquivProdTorsionOfDiagonalization, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, RingHom.diagonalKerEquiv_fst, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofSubmodule'_symm_apply,
    toLinearEquiv_basisFun_symm_apply, map_inv, GeneralLinearGroup.coe_inv]

/-- Annihilator coordinates retain the entries of the inverse right transformation
at every originally nonzero diagonal position. -/
@[simp]
theorem kerEquivProdTorsionOfDiagonalization_snd_apply
    (x : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i ≠ 0}) :
    ((kerEquivProdTorsionOfDiagonalization M L Q d h f x).2 i : A) =
      ((GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) *ᵥ (x : ι → A)) i := by
  simp only [kerEquivProdTorsionOfDiagonalization, LinearEquiv.trans_apply,
    LinearEquiv.symm_trans_apply, RingHom.diagonalKerEquiv_snd, LinearEquiv.ofEq_symm,
    LinearEquiv.coe_ofEq_apply, LinearEquiv.ofSubmodule'_symm_apply,
    toLinearEquiv_basisFun_symm_apply, map_inv, GeneralLinearGroup.coe_inv]

open scoped Classical in
/-- Reconstruct a kernel vector by combining its free and annihilator coordinates,
then applying the right transformation. -/
@[simp]
theorem kerEquivProdTorsionOfDiagonalization_symm_apply
    (z : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) :
    ((kerEquivProdTorsionOfDiagonalization M L Q d h f).symm z : ι → A) =
      (GeneralLinearGroup.map f Q : Matrix ι ι A) *ᵥ
        (fun i ↦ if hi : d i = 0 then z.1 ⟨i, hi⟩ else (z.2 ⟨i, hi⟩ : A)) := by
  classical
  simp only [kerEquivProdTorsionOfDiagonalization, LinearEquiv.symm_trans_apply,
    LinearEquiv.symm_symm, LinearEquiv.trans_apply, LinearEquiv.ofSubmodule'_apply,
    LinearEquiv.coe_ofEq_apply, toLinearEquiv_basisFun_apply]
  rw [funext (f.diagonalKerEquiv_symm_apply d z)]

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
    (kerEquivProdTorsionOfDiagonalization (γ - 1) U V d h f)

/-- The free fixed-vector coordinates are read by the inverse column transformation. -/
@[simp]
theorem fixedEquivOfDiagonalization_fst_apply (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : (γ.map f).mulVecLin.fixedSubmodule) (i : {i // d i = 0}) :
    (fixedEquivOfDiagonalization γ U V d h f v).1 i =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  simp [fixedEquivOfDiagonalization]

/-- The torsion fixed-vector coordinates are read by the inverse column transformation. -/
@[simp]
theorem fixedEquivOfDiagonalization_snd_apply (γ : Matrix ι ι R)
    (U V : GeneralLinearGroup ι R) (d : ι → R)
    (h : (U : Matrix ι ι R) * (γ - 1) * (V : Matrix ι ι R) = diagonal d)
    (f : R →+* A) (v : (γ.map f).mulVecLin.fixedSubmodule) (i : {i // d i ≠ 0}) :
    ((fixedEquivOfDiagonalization γ U V d h f v).2 i : A) =
      ((GeneralLinearGroup.map f V⁻¹ : Matrix ι ι A) *ᵥ v.val) i := by
  simp [fixedEquivOfDiagonalization]

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
  simp [fixedEquivOfDiagonalization]

end Matrix
