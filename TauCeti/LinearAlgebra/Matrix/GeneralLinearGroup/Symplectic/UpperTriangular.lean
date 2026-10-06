/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Diagonal.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# The standard triangular symplectic matrix subgroup

The standard symplectic flag orders the basis as
`e₀, …, eₘ₋₁, fₘ₋₁, …, f₀`. Reversing the second block is essential:
in the usual paired coordinates its stabilizer has upper-triangular upper-left block,
zero lower-left block, and lower-triangular lower-right block.

This file constructs that subgroup over every commutative ring, gives its matrix
membership criterion, and proves solvability and containment of the paired diagonal torus.
The subgroup supplies the point groups of the standard symplectic flag stabilizer scheme.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III.
* The construction reuses `TauCeti.upperTriangularGroup` and its solvability instance.
-/

public section

namespace TauCeti.GLSymplecticFin

open Matrix

variable (m : ℕ)

/-- The position of a paired basis vector in the standard symplectic flag order. -/
def flagOrder : Fin m ⊕ Fin m ≃ Fin (m + m) :=
  (Equiv.sumCongr (Equiv.refl _) Fin.revPerm).trans finSumFinEquiv

@[simp] theorem flagOrder_inl (i : Fin m) : flagOrder m (.inl i) = Fin.castAdd m i := by
  simp [flagOrder]

@[simp] theorem flagOrder_inr (i : Fin m) :
    flagOrder m (.inr i) = Fin.natAdd m i.rev := by
  simp [flagOrder]

/-- A matrix is triangular in flag order exactly when its paired blocks have the
upper/zero/lower pattern. Its upper-right block has no vanishing condition. -/
theorem blockTriangular_flagOrder_iff {R : Type*} [Zero R]
    (M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) R) :
    M.BlockTriangular (flagOrder m) ↔
      (∀ i j, j < i → M (.inl i) (.inl j) = 0) ∧
      (∀ i j, M (.inr i) (.inl j) = 0) ∧
      (∀ i j, i < j → M (.inr i) (.inr j) = 0) := by
  constructor
  · intro h
    refine ⟨fun i j hij => h ?_, fun i j => h ?_, fun i j hij => h ?_⟩ <;>
      simp only [flagOrder_inl, flagOrder_inr, Fin.lt_def,
        Fin.val_castAdd, Fin.val_natAdd, Fin.val_rev] at * <;> omega
  · rintro ⟨hA, hC, hD⟩ (i | i) (j | j) hij
    · apply hA
      simp only [flagOrder_inl, Fin.lt_def, Fin.val_castAdd] at hij ⊢
      exact hij
    · simp only [flagOrder_inl, flagOrder_inr, Fin.lt_def,
        Fin.val_castAdd, Fin.val_natAdd, Fin.val_rev] at hij
      omega
    · exact hC i j
    · apply hD
      simp only [flagOrder_inr, Fin.lt_def,
        Fin.val_natAdd, Fin.val_rev] at hij ⊢
      omega

variable (R : Type*) [CommRing R]

/-- Read a symplectic matrix in the standard flag order, as a general-linear matrix. -/
def flagMatrixHom : GLSymplecticFin m R →* GL (Fin (m + m)) R :=
  (Equiv.reindexGL ((finSumFinEquiv.symm).trans (flagOrder m)) R).toMonoidHom.comp
    (Subgroup.subtype _)

/-- In flag order, the entry at the positions of paired vectors `i,j` is the original entry. -/
@[simp] theorem flagMatrixHom_apply (g : GLSymplecticFin m R) (i j : Fin m ⊕ Fin m) :
    flagMatrixHom m R g (flagOrder m i) (flagOrder m j) =
      g.val (finSumFinEquiv i) (finSumFinEquiv j) := by
  simp [flagMatrixHom, Equiv.coe_reindexGL]

/-- The standard triangular subgroup of the symplectic matrix group. -/
def upperTriangular : Subgroup (GLSymplecticFin m R) :=
  (upperTriangularGroup (Fin (m + m)) R).comap (flagMatrixHom m R)

/-- Membership means triangularity of the paired matrix in standard flag order. -/
@[simp] theorem mem_upperTriangular_iff (g : GLSymplecticFin m R) :
    g ∈ upperTriangular m R ↔
      (g.val.val.submatrix finSumFinEquiv finSumFinEquiv).BlockTriangular (flagOrder m) := by
  rw [upperTriangular, Subgroup.mem_comap, UpperTriangularGroup.mem_iff]
  constructor
  · intro h i j hij
    simpa only [Matrix.submatrix_apply, ← flagMatrixHom_apply] using h hij
  · intro h i j hij
    obtain ⟨i, rfl⟩ := (flagOrder m).surjective i
    obtain ⟨j, rfl⟩ := (flagOrder m).surjective j
    simpa only [flagMatrixHom_apply, Matrix.submatrix_apply] using h hij

/-- The standard triangular symplectic subgroup contains the paired diagonal torus. -/
theorem diagonal_mem_upperTriangular (t : Fin m → Rˣ) :
    diagonal t ∈ upperTriangular m R := by
  rw [mem_upperTriangular_iff, coe_diagonal, diagGL_coe]
  intro i j hij
  have hne : finSumFinEquiv i ≠ finSumFinEquiv j :=
    finSumFinEquiv.injective.ne ((flagOrder m).injective.ne_iff.mp (ne_of_gt hij))
  simp only [Matrix.submatrix_apply, Matrix.diagonal_apply_ne _ hne]

/-- The triangular symplectic matrix group is solvable over a commutative ring. -/
instance : Group.IsSolvable (upperTriangular m R) := by
  let f : upperTriangular m R →* upperTriangularGroup (Fin (m + m)) R :=
    ((flagMatrixHom m R).comp (Subgroup.subtype _)).codRestrict _ fun g => g.2
  have hf : Function.Injective f := by
    intro g h heq
    apply Subtype.ext
    apply Subtype.ext
    exact (Equiv.reindexGL _ R).injective (congrArg Subtype.val heq)
  exact Group.isSolvable_of_isSolvable_injective hf

end TauCeti.GLSymplecticFin
