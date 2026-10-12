/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Symplectic.Basic
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.UpperTriangular.Solvable

/-!
# The symplectic isotropic flag matrix subgroup

The self-dual basis order fixes the isotropic half and reverses its dual half.
The subgroup of symplectic matrices upper triangular in this order has an upper-triangular
upper-left block, a lower-triangular lower-right block, and a zero lower-left block.
It is solvable over every commutative ring, by its inclusion in the upper-triangular general
linear group. Its representing Hopf algebra is constructed in
`TauCeti.Algebra.AlgebraicGroup.Symplectic.IsotropicFlag.Basic`.

## References

* J. S. Milne, *Algebraic Groups* (2017), §24.6 (symplectic groups and isotropic flags).
-/

public section

open Matrix

namespace TauCeti.GLSymplecticFin.IsotropicFlag

variable (m : ℕ) {A : Type*} [CommRing A]

/-- The basis permutation giving the self-dual flag order: fix the `e` block and reverse
the `f` block. -/
def flagOrder : Equiv.Perm (Fin (m + m)) :=
  finSumFinEquiv.symm.trans ((Equiv.refl (Fin m)).sumCongr Fin.revPerm) |>.trans
    finSumFinEquiv

/-- The isotropic half of the basis keeps its standard order. -/
@[simp]
theorem flagOrder_castAdd (i : Fin m) : flagOrder m (i.castAdd m) = i.castAdd m := by
  simp [flagOrder]

/-- The dual half of the basis is reversed in the self-dual flag order. -/
@[simp]
theorem flagOrder_addNat (i : Fin m) :
    flagOrder m (i.addNat m) = i.rev.addNat m := by
  simp only [← Fin.natAdd_eq_addNat, flagOrder, Equiv.trans_apply,
    finSumFinEquiv_symm_apply_natAdd,
    Equiv.sumCongr_apply, Sum.map_inr, Fin.revPerm_apply, finSumFinEquiv_apply_right]

/-- Flag order preserves comparisons within the isotropic half. -/
theorem flagOrder_castAdd_lt_castAdd_iff (i j : Fin m) :
    flagOrder m (j.castAdd m) < flagOrder m (i.castAdd m) ↔ j < i := by
  simp only [flagOrder_castAdd, Fin.lt_def, Fin.val_castAdd]

/-- Flag order reverses comparisons within the dual half. -/
theorem flagOrder_addNat_lt_addNat_iff (i j : Fin m) :
    flagOrder m (j.addNat m) < flagOrder m (i.addNat m) ↔ i < j := by
  simp only [flagOrder_addNat, Fin.lt_def, Fin.val_addNat, Fin.val_rev]
  omega

/-- Every isotropic basis index precedes every dual basis index in flag order. -/
theorem flagOrder_castAdd_lt_addNat (i j : Fin m) :
    flagOrder m (j.castAdd m) < flagOrder m (i.addNat m) := by
  simp only [flagOrder_castAdd, flagOrder_addNat, Fin.lt_def, Fin.val_castAdd, Fin.val_addNat]
  omega

/-- No dual basis index precedes an isotropic basis index in flag order. -/
theorem not_flagOrder_addNat_lt_castAdd (i j : Fin m) :
    ¬ flagOrder m (j.addNat m) < flagOrder m (i.castAdd m) :=
  (flagOrder_castAdd_lt_addNat m j i).not_gt

/-- The self-dual flag-order permutation is its own inverse. -/
@[simp]
theorem flagOrder_symm : (flagOrder m).symm = flagOrder m := by
  simp only [flagOrder, Equiv.symm_trans, Equiv.symm_symm, Equiv.sumCongr_symm,
    Equiv.refl_symm, Fin.revPerm_symm, Equiv.trans_assoc]

/-- The subgroup of symplectic matrices that become upper triangular after reindexing by
`flagOrder m`. Its paired-block form is recorded in `mem_matrixSubgroup_iff`. -/
def matrixSubgroup : Subgroup (GLSymplecticFin m A) :=
  (upperTriangularGroup (Fin (m + m)) A).comap
    (((flagOrder m).reindexGL A).toMonoidHom.comp (GLSymplecticFin m A).subtype)

/-- Membership in the flag subgroup is entrywise vanishing below the diagonal in flag order. -/
theorem mem_matrixSubgroup_iff_flagOrder (g : GLSymplecticFin m A) :
    g ∈ matrixSubgroup m (A := A) ↔
      ∀ i j, flagOrder m j < flagOrder m i → (g.val : Matrix _ _ A) i j = 0 := by
  calc
    _ ↔ (flagOrder m).reindexGL A g.val ∈ upperTriangularGroup (Fin (m + m)) A := by
      simp only [matrixSubgroup, Subgroup.mem_comap, MonoidHom.comp_apply,
        Subgroup.subtype_apply, MulEquiv.coe_toMonoidHom]
    _ ↔ (Matrix.reindex (flagOrder m) (flagOrder m)
          (g.val : Matrix _ _ A)).BlockTriangular id := by
      simp only [UpperTriangularGroup.mem_iff, Equiv.coe_reindexGL,
        Matrix.IsUpperTriangular, Matrix.reindex_apply]
    _ ↔ (g.val : Matrix _ _ A).BlockTriangular (id ∘ flagOrder m) :=
      Matrix.blockTriangular_reindex_iff
    _ ↔ ∀ i j, flagOrder m j < flagOrder m i → (g.val : Matrix _ _ A) i j = 0 := by
      simp only [Matrix.BlockTriangular, Function.comp_apply, id_eq]

/-- In paired coordinates, the flag subgroup consists of matrices whose upper-left block
is upper triangular, whose lower-right block is lower triangular, and whose lower-left
block vanishes. -/
theorem mem_matrixSubgroup_iff (g : GLSymplecticFin m A) :
    g ∈ matrixSubgroup m (A := A) ↔
      (∀ i j : Fin m, j < i → (g.val : Matrix _ _ A) (i.castAdd m) (j.castAdd m) = 0) ∧
      (∀ i j : Fin m, i < j → (g.val : Matrix _ _ A) (i.addNat m) (j.addNat m) = 0) ∧
      (∀ i j : Fin m, (g.val : Matrix _ _ A) (i.addNat m) (j.castAdd m) = 0) := by
  rw [mem_matrixSubgroup_iff_flagOrder]
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i j hij
      exact h _ _ ((flagOrder_castAdd_lt_castAdd_iff m i j).mpr hij)
    · intro i j hij
      exact h _ _ ((flagOrder_addNat_lt_addNat_iff m i j).mpr hij)
    · intro i j
      exact h _ _ (flagOrder_castAdd_lt_addNat m i j)
  · rintro ⟨hupper, hlower, hzero⟩ i j
    refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;>
      refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j
    · intro hij
      exact hupper i j ((flagOrder_castAdd_lt_castAdd_iff m i j).mp hij)
    · simp only [Fin.natAdd_eq_addNat, not_flagOrder_addNat_lt_castAdd, false_implies]
    · intro _
      simpa only [Fin.natAdd_eq_addNat] using hzero i j
    · intro hij
      simp only [Fin.natAdd_eq_addNat] at hij ⊢
      exact hlower i j ((flagOrder_addNat_lt_addNat_iff m i j).mp hij)

/-- **A symplectic matrix preserving the isotropic half of the standard flag preserves the whole
flag.** It suffices that the upper-left block is upper triangular and the lower-left block
vanishes: the symplectic equations then make the lower-right block the inverse transpose of the
upper-left one, hence lower triangular. -/
@[simp]
theorem mem_matrixSubgroup_iff_castAdd (g : GLSymplecticFin m A) :
    g ∈ matrixSubgroup m (A := A) ↔
      (∀ i j : Fin m, j < i → (g.val : Matrix _ _ A) (i.castAdd m) (j.castAdd m) = 0) ∧
      (∀ i j : Fin m, (g.val : Matrix _ _ A) (i.addNat m) (j.castAdd m) = 0) := by
  rw [mem_matrixSubgroup_iff]
  refine ⟨fun h ↦ ⟨h.1, h.2.2⟩, fun ⟨hupper, hzero⟩ ↦ ⟨hupper, ?_, hzero⟩⟩
  let M : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) A :=
    (g.val : Matrix _ _ A).submatrix finSumFinEquiv finSumFinEquiv
  have hsymp : M ∈ Matrix.symplecticGroup (Fin m) A :=
    submatrix_mem_symplecticGroup (GLSymplecticFin.mem_iff.mp g.2)
  have hM₂₁ : M.toBlocks₂₁ = 0 := by
    ext i j
    simpa only [M, Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.submatrix_apply,
      finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat,
      Matrix.zero_apply] using hzero i j
  -- The symplectic equations give `M₁₁ᵀ * M₂₂ = 1` once the lower-left block vanishes.
  have hAD : M.toBlocks₁₁ᵀ * M.toBlocks₂₂ = 1 := by
    have hblocks := SymplecticGroup.fromBlocks_mem_iff.mp (M.fromBlocks_toBlocks.symm ▸ hsymp)
    simpa only [hM₂₁, Matrix.transpose_zero, Matrix.zero_mul, sub_zero] using hblocks.2.2
  let _ : Invertible M.toBlocks₁₁ := Matrix.invertibleOfIsUnitDet _ <|
    IsUnit.of_mul_eq_one M.toBlocks₂₂.det <| by
      rw [← Matrix.det_transpose M.toBlocks₁₁, ← Matrix.det_mul, hAD, Matrix.det_one]
  have hA : M.toBlocks₁₁.BlockTriangular id := fun i j hij ↦ by
    simpa only [M, Matrix.toBlocks₁₁, Matrix.of_apply, Matrix.submatrix_apply,
      finSumFinEquiv_apply_left] using hupper i j hij
  have hD : M.toBlocks₂₂ = (M.toBlocks₁₁⁻¹)ᵀ := by
    rw [Matrix.transpose_nonsing_inv, Matrix.inv_eq_right_inv hAD]
  intro i j hij
  have h := congrFun (congrFun hD i) j
  simp only [M, Matrix.toBlocks₂₂, Matrix.of_apply, Matrix.submatrix_apply,
    finSumFinEquiv_apply_right, Fin.natAdd_eq_addNat, Matrix.transpose_apply] at h
  rw [h]
  exact Matrix.blockTriangular_inv_of_blockTriangular hA hij

/-- Apply a ring homomorphism entrywise to a flag-preserving symplectic matrix. -/
def map {B : Type*} [CommRing B] (phi : A →+* B) :
    matrixSubgroup m (A := A) →* matrixSubgroup m (A := B) :=
  ((GLSymplecticFin.map m A phi).domRestrict (matrixSubgroup m)).codRestrict
    (matrixSubgroup m) fun g ↦ by
      rw [mem_matrixSubgroup_iff_flagOrder]
      intro i j hij
      rw [MonoidHom.domRestrict_apply, GLSymplecticFin.coe_map,
        Matrix.GeneralLinearGroup.map_apply,
        (mem_matrixSubgroup_iff_flagOrder m g.val).mp g.property i j hij, map_zero]

/-- The underlying symplectic matrix of coefficient change is the ambient coefficient map. -/
@[simp]
theorem coe_map {B : Type*} [CommRing B] (phi : A →+* B)
    (g : matrixSubgroup m (A := A)) :
    (map m phi g : GLSymplecticFin m B) = GLSymplecticFin.map m A phi g := by
  rfl

/-- The symplectic isotropic flag subgroup is solvable over every commutative ring. -/
instance instIsSolvableMatrixSubgroup : Group.IsSolvable (matrixSubgroup m (A := A)) := by
  let φ := ((flagOrder m).reindexGL A).toMonoidHom.comp (GLSymplecticFin m A).subtype
  exact Group.isSolvable_of_isSolvable_injective
    (φ.subgroupComap_injective (upperTriangularGroup (Fin (m + m)) A)
      (((flagOrder m).reindexGL A).injective.comp (Subgroup.subtype_injective _)))

end TauCeti.GLSymplecticFin.IsotropicFlag
