/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-!
# Kernel coordinates from a diagonalization

A specified diagonalization `L * M * Q = diagonal d` gives kernel coordinates after
any change of coefficient rings. Zero entries of the original diagonal give free
coordinates; each remaining entry gives its annihilator in the new ring. In
particular, a nonzero integral entry may contribute new kernel vectors after reduction.

The transformations are retained explicitly: coordinates are read using `Q⁻¹`, and
vectors are reconstructed using `Q`. No flatness or injectivity of the coefficient
map is needed. Applying this to `M = γ - 1` computes fixed vectors of a lattice action.

We use Mathlib's `Submodule.torsionBy` for annihilators and its general linear group
for the invertible transformations. See Bourbaki, *Algebra*, Chapter VII, §4,
for elementary divisors and diagonal presentations over principal ideal domains.
-/

public section

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
  classical
  let read (x : ι → A) := (GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) *ᵥ x
  let assemble (z : ({i // d i = 0} → A) ×
      ((i : {i // d i ≠ 0}) → Submodule.torsionBy A A (f (d i)))) (i : ι) : A :=
    if hi : d i = 0 then z.1 ⟨i, hi⟩ else z.2 ⟨i, hi⟩
  have hread (x : LinearMap.ker (M.map f).mulVecLin) (i : ι) :
      f (d i) * read x i = 0 :=
    (mulVec_eq_zero_iff_of_diagonalization M L Q d h f x).mp x.property i
  refine
    { toFun := fun x ↦ (fun i ↦ read x i, fun i ↦ ⟨read x i, hread x i⟩)
      invFun := fun z ↦ ⟨(GeneralLinearGroup.map f Q : Matrix ι ι A) *ᵥ assemble z, ?_⟩
      left_inv := ?_
      right_inv := ?_
      map_add' := by
        intro x y
        ext i <;> simp [read, mulVec_add]
      map_smul' := by
        intro a x
        ext i <;> simp [read, mulVec_smul] }
  · apply (mulVec_eq_zero_iff_of_diagonalization M L Q d h f _).mpr
    intro i
    simp only [mulVec_mulVec, ← GeneralLinearGroup.coe_mul,
      GeneralLinearGroup.map_inv_mul_map, GeneralLinearGroup.coe_one, one_mulVec]
    dsimp [assemble]
    split_ifs with hi
    · simp [hi]
    · exact (z.2 ⟨i, hi⟩).property
  · intro x
    apply Subtype.ext
    have ha : assemble (fun i ↦ read x i, fun i ↦ ⟨read x i, hread x i⟩) = read x := by
      ext i
      simp [assemble]
    simp only [ha, read, mulVec_mulVec, ← GeneralLinearGroup.coe_mul,
      GeneralLinearGroup.map_mul_map_inv, GeneralLinearGroup.coe_one, one_mulVec]
  · intro z
    have hr : read ((GeneralLinearGroup.map f Q : Matrix ι ι A) *ᵥ assemble z) =
        assemble z := by
      simp only [read, mulVec_mulVec, ← GeneralLinearGroup.coe_mul,
        GeneralLinearGroup.map_inv_mul_map, GeneralLinearGroup.coe_one, one_mulVec]
    apply Prod.ext
    · funext i
      simp only [hr]
      simp [assemble, i.property]
    · funext i
      apply Subtype.ext
      simp only [hr]
      simp [assemble, i.property]

variable (M : Matrix ι ι R) (L Q : GeneralLinearGroup ι R) (d : ι → R)
  (h : (L : Matrix ι ι R) * M * (Q : Matrix ι ι R) = diagonal d) (f : R →+* A)

/-- Free coordinates are the entries of the inverse right transformation at the
original zero diagonal positions. -/
@[simp]
theorem kerEquivProdTorsionOfDiagonalization_fst_apply
    (x : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i = 0}) :
    (kerEquivProdTorsionOfDiagonalization M L Q d h f x).1 i =
      ((GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) *ᵥ (x : ι → A)) i := by
  rfl

/-- Annihilator coordinates retain the entries of the inverse right transformation
at every originally nonzero diagonal position. -/
@[simp]
theorem kerEquivProdTorsionOfDiagonalization_snd_apply
    (x : LinearMap.ker (M.map f).mulVecLin) (i : {i // d i ≠ 0}) :
    ((kerEquivProdTorsionOfDiagonalization M L Q d h f x).2 i : A) =
      ((GeneralLinearGroup.map f Q⁻¹ : Matrix ι ι A) *ᵥ (x : ι → A)) i := by
  rfl

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
  rfl

end Matrix
