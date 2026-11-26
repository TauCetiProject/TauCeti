/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Contiguous block sums of invertible matrices and their `K₁` classes

For a possibly noncommutative ring `A`, the **contiguous block sum** of `g ∈ GL_m(A)` and
`h ∈ GL_n(A)` is the invertible matrix `g ⊞ h ∈ GL_{m+n}(A)` with diagonal blocks `g` and `h`, the
rows and columns of `g` coming first in `Fin (m + n)`. It is the block diagonal homomorphism
`TauCeti.fromBlocksGL` reindexed along `finSumFinEquiv : Fin m ⊕ Fin n ≃ Fin (m + n)`, so it keeps
the actual finite size of both blocks.

Block sum refines the stable picture: `g ⊞ 1` is the stabilization `TauCeti.stabilizeGL` of `g`,
and in algebraic `K₁` the class of `g ⊞ h` is the product of the classes of `g` and `h`. It is
not an operation on stable representatives, since stabilizing the first block shifts the
second; the class formula is what survives in the limit. Its proof uses that relabelling the
indices of an invertible matrix, in particular swapping the two blocks, does not change its
class in `K₁`, because such a relabelling is conjugation by a permutation matrix. The same holds
already in `GL_∞(A)` for a matrix indexed by an arbitrary finite type: each enumeration of the
indices gives an image in `GL_∞(A)`, and two enumerations give images conjugate by the image of a
permutation matrix.

## Main definitions

* `TauCeti.blockSumGL`: the block sum homomorphism
  `GL (Fin m) A × GL (Fin n) A →* GL (Fin (m + n)) A`, `(g, h) ↦ g ⊞ h`.
* `TauCeti.StableGeneralLinearGroup.ofEquiv`: the image `GL ι A →* GL_∞(A)` of invertible
  matrices indexed by a finite type `ι`, through an enumeration `ι ≃ Fin k`.

## Main results

* `TauCeti.coe_blockSumGL_apply_castAdd_castAdd` and its three companions: the entries of
  `g ⊞ h`, those of `g` and `h` in the diagonal blocks and `0` off them.
* `TauCeti.blockSumGL_mulVec_append`, `TauCeti.blockSumGL_vecMul_append`: `g ⊞ h` acts on
  concatenated column and row vectors blockwise.
* `TauCeti.blockSumGL_injective`: block sum is injective.
* `TauCeti.blockSumGL_one_right`, `TauCeti.blockSumGL_one_left`: `g ⊞ 1` is the stabilization
  of `g`, and `1 ⊞ h` is the stabilization of `h` with its blocks swapped.
* `TauCeti.blockSumGL_left_nil`, `TauCeti.blockSumGL_right_nil`: blocks of size zero are units
  for block sum, up to relabelling `Fin (0 + n)` and `Fin (m + 0)`.
* `TauCeti.blockSumGL_assoc`: block sum is associative, up to relabelling
  `Fin (l + m + n) ≃ Fin (l + (m + n))`.
* `TauCeti.blockSumGL_map`: block sum commutes with ring homomorphisms applied to entries.
* `TauCeti.det_blockSumGL`: over a commutative ring, `det (g ⊞ h) = det g * det h`.
* `TauCeti.coe_blockSumGL_mem_unitary`: the block sum of unitary matrices is unitary.
* `TauCeti.reindexGL_finAddFlip_blockSumGL`, `TauCeti.permutationGL_mul_blockSumGL_mul_inv`:
  swapping the two blocks of `g ⊞ h` gives `h ⊞ g`, and at a common size this is conjugation by
  the block-swap permutation matrix.
* `TauCeti.blockSumGL_mem_elementarySubgroup`: the block sum of elementary matrices is
  elementary.
* `TauCeti.StableGeneralLinearGroup.ofEquiv_eq_mul_mul_inv`: two enumerations of the indices of a
  matrix give images in `GL_∞(A)` conjugate by the image of a permutation matrix.
* `TauCeti.AlgebraicK1.mk_reindexGL`: relabelling the indices does not change the class in `K₁`.
* `TauCeti.AlgebraicK1.mk_blockSumGL`: `[g ⊞ h] = [g] [h]` in `K₁(A)`.

## References

* C. A. Weibel, *The K-book*, Chapter III, §1, Definition 1.1 and §1.2.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {A : Type*} [Ring A] {l m n : ℕ}

/-! ## The block sum -/

variable (A) in
/-- The **contiguous block sum** `(g, h) ↦ g ⊞ h` from `GL (Fin m) A × GL (Fin n) A` to
`GL (Fin (m + n)) A`: the block diagonal matrix with blocks `g` and `h`, the indices of `g`
coming first. -/
def blockSumGL : GL (Fin m) A × GL (Fin n) A →* GL (Fin (m + n)) A :=
  (finSumFinEquiv.reindexGL A).toMonoidHom.comp fromBlocksGL

/-- The matrix underlying a block sum is the block diagonal matrix `fromBlocks g 0 0 h`,
reindexed along `Fin m ⊕ Fin n ≃ Fin (m + n)`. -/
theorem coe_blockSumGL (u : GL (Fin m) A × GL (Fin n) A) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) =
      reindex finSumFinEquiv finSumFinEquiv (fromBlocks u.1 0 0 u.2) := by
  simp [blockSumGL, reindex_apply]

/-- The upper left block of `g ⊞ h` is `g`. -/
@[simp]
theorem coe_blockSumGL_apply_castAdd_castAdd (u : GL (Fin m) A × GL (Fin n) A) (i j : Fin m) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) (Fin.castAdd n i) (Fin.castAdd n j) =
      (u.1 : Matrix (Fin m) (Fin m) A) i j := by
  simp [coe_blockSumGL]

/-- The upper right block of `g ⊞ h` is zero. -/
@[simp]
theorem coe_blockSumGL_apply_castAdd_natAdd (u : GL (Fin m) A × GL (Fin n) A) (i : Fin m)
    (j : Fin n) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) (Fin.castAdd n i) (Fin.natAdd m j) =
      0 := by
  simp [coe_blockSumGL]

/-- The lower left block of `g ⊞ h` is zero. -/
@[simp]
theorem coe_blockSumGL_apply_natAdd_castAdd (u : GL (Fin m) A × GL (Fin n) A) (i : Fin n)
    (j : Fin m) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) (Fin.natAdd m i) (Fin.castAdd n j) =
      0 := by
  simp [coe_blockSumGL]

/-- The lower right block of `g ⊞ h` is `h`. -/
@[simp]
theorem coe_blockSumGL_apply_natAdd_natAdd (u : GL (Fin m) A × GL (Fin n) A) (i j : Fin n) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) (Fin.natAdd m i) (Fin.natAdd m j) =
      (u.2 : Matrix (Fin n) (Fin n) A) i j := by
  simp [coe_blockSumGL]

/-- Block sum acts on concatenated column vectors blockwise:
`(g ⊞ h) (v ++ w) = g v ++ h w`. -/
@[simp]
theorem blockSumGL_mulVec_append (u : GL (Fin m) A × GL (Fin n) A) (v : Fin m → A)
    (w : Fin n → A) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) *ᵥ Fin.append v w =
      Fin.append ((u.1 : Matrix (Fin m) (Fin m) A) *ᵥ v)
        ((u.2 : Matrix (Fin n) (Fin n) A) *ᵥ w) := by
  ext i
  induction i using Fin.addCases <;> simp [mulVec, dotProduct, Fin.sum_univ_add]

/-- Block sum acts on concatenated row vectors blockwise:
`(v ++ w) (g ⊞ h) = v g ++ w h`. -/
@[simp]
theorem blockSumGL_vecMul_append (u : GL (Fin m) A × GL (Fin n) A) (v : Fin m → A)
    (w : Fin n → A) :
    Fin.append v w ᵥ* (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) =
      Fin.append (v ᵥ* (u.1 : Matrix (Fin m) (Fin m) A))
        (w ᵥ* (u.2 : Matrix (Fin n) (Fin n) A)) := by
  ext i
  induction i using Fin.addCases <;> simp [vecMul, dotProduct, Fin.sum_univ_add]

/-- Block sum is injective: `g` and `h` are the diagonal blocks of `g ⊞ h`. -/
theorem blockSumGL_injective :
    Function.Injective (blockSumGL A : GL (Fin m) A × GL (Fin n) A →* GL (Fin (m + n)) A) :=
  (finSumFinEquiv.reindexGL A).injective.comp fromBlocksGL_injective

/-- The block sum `g ⊞ 1` is the stabilization `g ↦ g ⊕ 1` of `g`. -/
theorem blockSumGL_one_right (g : GL (Fin m) A) :
    blockSumGL A (g, (1 : GL (Fin n) A)) = stabilizeGL A (Nat.le_add_right m n) g :=
  (stabilizeGL_eq_reindexGL_fromBlocksGL m n g).symm

/-- A block of size zero on the left is a unit for block sum, up to relabelling
`Fin (0 + n) ≃ Fin n`. -/
theorem blockSumGL_left_nil (g : GL (Fin 0) A) (h : GL (Fin n) A) :
    (finCongr (zero_add n)).reindexGL A (blockSumGL A (g, h)) = h := by
  ext i j
  simpa [Fin.natAdd_zero] using coe_blockSumGL_apply_natAdd_natAdd (g, h) i j

/-- A block of size zero on the right is a unit for block sum, up to relabelling
`Fin (m + 0) ≃ Fin m`. -/
theorem blockSumGL_right_nil (g : GL (Fin m) A) (h : GL (Fin 0) A) :
    (finCongr (add_zero m)).reindexGL A (blockSumGL A (g, h)) = g := by
  ext i j
  simpa using coe_blockSumGL_apply_castAdd_castAdd (g, h) i j

/-- **Block sum is associative**, up to relabelling `Fin (l + m + n) ≃ Fin (l + (m + n))`:
`(f ⊞ g) ⊞ h = f ⊞ (g ⊞ h)`. -/
theorem blockSumGL_assoc (f : GL (Fin l) A) (g : GL (Fin m) A) (h : GL (Fin n) A) :
    (finCongr (add_assoc l m n)).reindexGL A (blockSumGL A (blockSumGL A (f, g), h)) =
      blockSumGL A (f, blockSumGL A (g, h)) := by
  -- Relabelling the indices of the last block along `Fin (l + (m + n)) ≃ Fin (l + m + n)`.
  have hcast (c : Fin n) :
      (Fin.natAdd l (Fin.natAdd m c)).cast (add_assoc l m n).symm = Fin.natAdd (l + m) c :=
    Fin.ext (by simp [add_assoc])
  ext i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i) i <;>
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j) j <;>
    simp [← Fin.castAdd_castAdd, ← Fin.castAdd_natAdd, hcast]

/-- Block sum commutes with applying a ring homomorphism to the entries of invertible
matrices. -/
theorem blockSumGL_map {B : Type*} [Ring B] (f : A →+* B) (u : GL (Fin m) A × GL (Fin n) A) :
    blockSumGL B (Units.map (f.mapMatrix (m := Fin m)).toMonoidHom u.1,
        Units.map (f.mapMatrix (m := Fin n)).toMonoidHom u.2) =
      Units.map (f.mapMatrix (m := Fin (m + n))).toMonoidHom (blockSumGL A u) := by
  ext i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;>
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j <;> simp

/-- The determinant of a block sum over a commutative ring is the product of the determinants of
its blocks. -/
@[simp]
theorem det_blockSumGL {R : Type*} [CommRing R] (u : GL (Fin m) R × GL (Fin n) R) :
    GeneralLinearGroup.det (blockSumGL R u) =
      GeneralLinearGroup.det u.1 * GeneralLinearGroup.det u.2 := by
  ext
  simp [GeneralLinearGroup.val_det_apply, coe_blockSumGL, det_fromBlocks_zero₂₁]

/-- The block sum of unitary matrices is unitary. -/
theorem coe_blockSumGL_mem_unitary [StarRing A] {u : GL (Fin m) A × GL (Fin n) A}
    (hu₁ : (u.1 : Matrix (Fin m) (Fin m) A) ∈ unitary _)
    (hu₂ : (u.2 : Matrix (Fin n) (Fin n) A) ∈ unitary _) :
    (blockSumGL A u : Matrix (Fin (m + n)) (Fin (m + n)) A) ∈ unitary _ := by
  rw [coe_blockSumGL]
  exact (reindex_fromBlocks_zero_zero_mem_unitary_iff _).2 ⟨hu₁, hu₂⟩

/-- Swapping the two blocks: relabelling the indices of `g ⊞ h` along
`finAddFlip : Fin (m + n) ≃ Fin (n + m)` gives `h ⊞ g`. -/
theorem reindexGL_finAddFlip_blockSumGL (u : GL (Fin m) A × GL (Fin n) A) :
    finAddFlip.reindexGL A (blockSumGL A u) = blockSumGL A u.swap := by
  have hcast (k : Fin n) : finAddFlip.symm (Fin.castAdd m k) = Fin.natAdd m k := by
    simp [Equiv.symm_apply_eq]
  have hnat (k : Fin m) : finAddFlip.symm (Fin.natAdd n k) = Fin.castAdd n k := by
    simp [Equiv.symm_apply_eq]
  ext i j
  refine Fin.addCases (fun i ↦ ?_) (fun i ↦ ?_) i <;>
    refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) j <;> simp [hcast, hnat]

/-- **The block-swap conjugacy formula.** Conjugating `g ⊞ h` by the permutation matrix of the
block swap `Fin (m + n) ≃ Fin (n + m) = Fin (m + n)` gives `h ⊞ g`, relabelled along
`Fin (n + m) = Fin (m + n)`. -/
theorem permutationGL_mul_blockSumGL_mul_inv (u : GL (Fin m) A × GL (Fin n) A) :
    permutationGL (finAddFlip.trans (finCongr (add_comm n m))) * blockSumGL A u *
        (permutationGL (finAddFlip.trans (finCongr (add_comm n m))))⁻¹ =
      (finCongr (add_comm n m)).reindexGL A (blockSumGL A u.swap) := by
  rw [permutationGL_mul_mul_inv, ← reindexGL_finAddFlip_blockSumGL,
    ← Equiv.reindexGL_trans_reindexGL, MulEquiv.trans_apply]

/-- The block sum `1 ⊞ h` is the stabilization `h ↦ h ⊕ 1` of `h` with its two blocks
swapped, along `finAddFlip : Fin (n + m) ≃ Fin (m + n)`. -/
theorem blockSumGL_one_left (h : GL (Fin n) A) :
    blockSumGL A ((1 : GL (Fin m) A), h) =
      finAddFlip.reindexGL A (stabilizeGL A (Nat.le_add_right n m) h) := by
  rw [← blockSumGL_one_right, reindexGL_finAddFlip_blockSumGL, Prod.swap_prod_mk]

/-- **Block sums of elementary matrices are elementary.** -/
theorem blockSumGL_mem_elementarySubgroup {g : GL (Fin m) A} {h : GL (Fin n) A}
    (hg : g ∈ elementarySubgroup (Fin m) A) (hh : h ∈ elementarySubgroup (Fin n) A) :
    blockSumGL A (g, h) ∈ elementarySubgroup (Fin (m + n)) A := by
  rw [← Prod.fst_mul_snd (g, h), map_mul, blockSumGL_one_right, blockSumGL_one_left]
  refine mul_mem (map_stabilizeGL_elementarySubgroup_le _ ⟨g, hg, rfl⟩) ?_
  rw [← Equiv.map_reindexGL_elementarySubgroup finAddFlip]
  exact ⟨_, map_stabilizeGL_elementarySubgroup_le _ ⟨h, hh, rfl⟩, rfl⟩

/-! ## Enumerations of the indices -/

namespace StableGeneralLinearGroup

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (A) in
/-- The image in `GL_∞(A)` of an invertible matrix indexed by a finite type `ι`, through an
enumeration `e : ι ≃ Fin k` of its indices: the image of its reindexing along `e`. -/
def ofEquiv {k : ℕ} (e : ι ≃ Fin k) : GL ι A →* StableGeneralLinearGroup A :=
  (of A k).comp (e.reindexGL A).toMonoidHom

/-- The image through an enumeration `e` is the image of the reindexing along `e`. -/
@[simp]
theorem ofEquiv_apply {k : ℕ} (e : ι ≃ Fin k) (u : GL ι A) :
    ofEquiv A e u = of A k (e.reindexGL A u) :=
  (rfl)

/-- The image in `GL_∞(A)` through an enumeration of the indices is injective. -/
theorem ofEquiv_injective {k : ℕ} (e : ι ≃ Fin k) : Function.Injective (ofEquiv A e) :=
  (of_injective k).comp (e.reindexGL A).injective

/-- Two enumerations `e` and `e'` of the indices give images in `GL_∞(A)` which are conjugate by
the image of the permutation matrix of `e.symm.trans e'`. -/
theorem ofEquiv_eq_mul_mul_inv {k : ℕ} (e e' : ι ≃ Fin k) (u : GL ι A) :
    ofEquiv A e' u =
      of A k (permutationGL (k := A) (e.symm.trans e')) * ofEquiv A e u *
        (of A k (permutationGL (k := A) (e.symm.trans e')))⁻¹ := by
  rw [ofEquiv_apply, ofEquiv_apply, ← map_inv, ← map_mul, ← map_mul, permutationGL_mul_mul_inv]
  congr 1
  ext : 1
  simp [Function.comp_def]

end StableGeneralLinearGroup

/-! ## Block sums in algebraic `K₁` -/

namespace AlgebraicK1

/-- **Relabelling the indices does not change the class in `K₁`**: for `e : Fin m ≃ Fin n`, the
reindexed matrix is conjugate to the original one by a permutation matrix. -/
theorem mk_reindexGL (e : Fin m ≃ Fin n) (u : GL (Fin m) A) :
    mk A n (e.reindexGL A u) = mk A m u := by
  obtain rfl : m = n := by simpa using Fintype.card_congr e
  rw [← permutationGL_mul_mul_inv, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-- **Block sum is multiplication in `K₁`**: the class of `g ⊞ h` is the product of the classes
of `g` and `h`. -/
@[simp]
theorem mk_blockSumGL (u : GL (Fin m) A × GL (Fin n) A) :
    mk A (m + n) (blockSumGL A u) = mk A m u.1 * mk A n u.2 := by
  conv_lhs => rw [← Prod.fst_mul_snd u]
  rw [map_mul, blockSumGL_one_right, blockSumGL_one_left, map_mul, mk_reindexGL, mk_stabilizeGL,
    mk_stabilizeGL]

end AlgebraicK1

end TauCeti
