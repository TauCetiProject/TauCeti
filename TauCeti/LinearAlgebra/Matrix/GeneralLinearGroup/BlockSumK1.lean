/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.AlgebraicK1
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.DeterminantK1
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# Classes in algebraic `K₁` of matrices over arbitrary finite index types

The stable general linear group `GL_∞(A)` and algebraic `K₁(A)` are built from the groups
`GL (Fin k) A`. Invertible matrices arise naturally over other finite index types: block
matrices are indexed by `n ⊕ m`, matrices of endomorphisms of a free module by a chosen basis.
An enumeration `e : n ≃ Fin k` of the indices sends `GL n A` into `GL_∞(A)`, and two
enumerations give images which are conjugate by a permutation matrix. In `K₁(A)` the class
`TauCeti.AlgebraicK1.mkOfFintype` is therefore independent of the enumeration.

This file develops the formulas for these classes which mix several index types. The class of a
block triangular matrix with diagonal blocks `u` and `v` is `[u] [v]`, whatever its off-diagonal
block. A class is trivial exactly when `u ⊕ 1` is elementary for an identity block of some size.
The class of an invertible diagonal matrix is the product of the classes of its entries.

## Main definitions

* `TauCeti.StableGeneralLinearGroup.ofEquiv`: the image `GL n A →* GL_∞(A)` through an
  enumeration `n ≃ Fin k`.

## Main results

* `TauCeti.StableGeneralLinearGroup.ofEquiv_eq_mul_mul_inv`: two enumerations give images in
  `GL_∞(A)` conjugate by the image of a permutation matrix.
* `TauCeti.AlgebraicK1.elementarySubgroup_le_ker_mkOfFintype`: elementary matrices have trivial
  class.
* `TauCeti.AlgebraicK1.mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₂₁`,
  `TauCeti.AlgebraicK1.mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₁₂`: a block triangular matrix
  with invertible diagonal blocks `u` and `v` has class `[u] [v]`.
* `TauCeti.AlgebraicK1.mkOfFintype_eq_one_iff`: `[u]` is trivial exactly when `u ⊕ 1` is
  elementary for an identity block of some size.
* `TauCeti.AlgebraicK1.mkOfFintype_scalar`, `TauCeti.AlgebraicK1.mkOfFintype_diagGL`: the class of
  an invertible diagonal matrix is the product of the classes of its diagonal entries.
* `TauCeti.AlgebraicK1.det_mkOfFintype`: compatibility with the determinant.

## References

* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §1: Definition 1.1 of `K₁(R)` and Whitehead's
  Lemma 1.3.3.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

variable {A : Type*} [Ring A] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

namespace StableGeneralLinearGroup

variable (A) in
/-- The image in `GL_∞(A)` of an invertible matrix indexed by a finite type `n`, through an
enumeration `e : n ≃ Fin k` of its indices: the image of its reindexing along `e`. -/
def ofEquiv {k : ℕ} (e : n ≃ Fin k) : GL n A →* StableGeneralLinearGroup A :=
  (of A k).comp (e.reindexGL A).toMonoidHom

/-- The image through an enumeration `e` is the image of the reindexing along `e`. -/
@[simp]
theorem ofEquiv_apply {k : ℕ} (e : n ≃ Fin k) (u : GL n A) :
    ofEquiv A e u = of A k (e.reindexGL A u) :=
  (rfl)

/-- The image in `GL_∞(A)` through an enumeration of the indices is injective. -/
theorem ofEquiv_injective {k : ℕ} (e : n ≃ Fin k) : Function.Injective (ofEquiv A e) :=
  (of_injective k).comp (e.reindexGL A).injective

/-- Two enumerations `e` and `e'` of the indices give images in `GL_∞(A)` which are conjugate by
the image of the permutation matrix of `e.symm.trans e'`. -/
theorem ofEquiv_eq_mul_mul_inv {k : ℕ} (e e' : n ≃ Fin k) (u : GL n A) :
    ofEquiv A e' u =
      of A k (permutationGL (k := A) (e.symm.trans e')) * ofEquiv A e u *
        (of A k (permutationGL (k := A) (e.symm.trans e')))⁻¹ := by
  rw [ofEquiv_apply, ofEquiv_apply, ← map_inv, ← map_mul, ← map_mul, permutationGL_mul_mul_inv,
    ← MulEquiv.trans_apply, Equiv.reindexGL_trans_reindexGL, ← Equiv.trans_assoc,
    Equiv.self_trans_symm, Equiv.refl_trans]

end StableGeneralLinearGroup

namespace AlgebraicK1

/-- The class of `u ⊕ 1` is the class of `u`. -/
private theorem mkOfFintype_fromBlocksGL_one (u : GL n A) :
    mkOfFintype A (n ⊕ m) (fromBlocksGL (u, 1)) = mkOfFintype A n u := by
  rw [mkOfFintype_fromBlocksGL, map_one, mul_one]

/-- Elementary matrices have trivial class in `K₁(A)`. -/
theorem elementarySubgroup_le_ker_mkOfFintype :
    elementarySubgroup n A ≤ (mkOfFintype A n).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, mkOfFintype_eq_mk_reindexGL (Fintype.equivFin n)]
  exact elementarySubgroup_le_ker_mk _ ((Equiv.reindexGL_mem_elementarySubgroup_iff _).2 hu)

/-- The class of an invertible matrix is trivial exactly when its block sum `u ⊕ 1` with an
identity matrix of some size is elementary. -/
theorem mkOfFintype_eq_one_iff {u : GL n A} :
    mkOfFintype A n u = 1 ↔
      ∃ k : ℕ, fromBlocksGL (u, (1 : GL (Fin k) A)) ∈ elementarySubgroup (n ⊕ Fin k) A := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rw [mkOfFintype_eq_mk_reindexGL (Fintype.equivFin n), mk_eq_one_iff] at h
    obtain ⟨_, hk, hmem⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
    refine ⟨k, ?_⟩
    rw [stabilizeGL_eq_reindexGL_fromBlocksGL, ← map_one ((Equiv.refl (Fin k)).reindexGL A),
      ← Equiv.reindexGL_sumCongr_fromBlocksGL, ← MulEquiv.trans_apply,
      Equiv.reindexGL_trans_reindexGL,
      Equiv.reindexGL_mem_elementarySubgroup_iff] at hmem
    exact hmem
  · rw [← mkOfFintype_fromBlocksGL_one (m := Fin k)]
    exact elementarySubgroup_le_ker_mkOfFintype hk

/-- A block upper triangular matrix with invertible diagonal blocks `u` and `v` has class
`[u] [v]`, whatever its off-diagonal block. -/
theorem mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₂₁ {g : GL (n ⊕ m) A} {u : GL n A}
    {v : GL m A} {X : Matrix n m A} (hg : (g : Matrix (n ⊕ m) (n ⊕ m) A) = fromBlocks u X 0 v) :
    mkOfFintype A (n ⊕ m) g = mkOfFintype A n u * mkOfFintype A m v := by
  have hfac : g = fromBlocksGL (u, v) * upperBlockGL ((↑u⁻¹ : Matrix n n A) * X) :=
    Units.ext (by simp [hg, fromBlocks_multiply, ← Matrix.mul_assoc])
  rw [hfac, map_mul, mkOfFintype_fromBlocksGL,
    elementarySubgroup_le_ker_mkOfFintype (upperBlockGL_mem_elementarySubgroup _), mul_one]

/-- A block lower triangular matrix with invertible diagonal blocks `u` and `v` has class
`[u] [v]`, whatever its off-diagonal block. -/
theorem mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₁₂ {g : GL (n ⊕ m) A} {u : GL n A}
    {v : GL m A} {Y : Matrix m n A} (hg : (g : Matrix (n ⊕ m) (n ⊕ m) A) = fromBlocks u 0 Y v) :
    mkOfFintype A (n ⊕ m) g = mkOfFintype A n u * mkOfFintype A m v := by
  have hfac : g = fromBlocksGL (u, v) * lowerBlockGL ((↑v⁻¹ : Matrix m m A) * Y) :=
    Units.ext (by simp [hg, fromBlocks_multiply, ← Matrix.mul_assoc])
  rw [hfac, map_mul, mkOfFintype_fromBlocksGL,
    elementarySubgroup_le_ker_mkOfFintype (lowerBlockGL_mem_elementarySubgroup _), mul_one]

/-- Over an index type with exactly one element, the class of the scalar matrix `(a)` is the
class `AlgebraicK1.ofUnits A a` of the unit `a`. -/
@[simp]
theorem mkOfFintype_scalar [Unique n] (a : Aˣ) :
    mkOfFintype A n (GeneralLinearGroup.scalar n a) = ofUnits A a := by
  rw [mkOfFintype_eq_mk_reindexGL (Equiv.ofUnique n (Fin 1)), ofUnits_apply]
  congr 1
  ext i j
  simp [Subsingleton.elim i j]

/-- The class of the diagonal matrix with one diagonal entry `a` and all others `1` is the class
of the unit `a`. -/
private theorem mkOfFintype_diagGL_mulSingle (i : n) (a : Aˣ) :
    mkOfFintype A n (diagGL (Pi.mulSingle i a)) = ofUnits A a := by
  have hblock : (Equiv.sumCompl (· = i)).symm.reindexGL A (diagGL (Pi.mulSingle i a)) =
      fromBlocksGL (GeneralLinearGroup.scalar {j // j = i} a, 1) := by
    refine Units.ext ?_
    ext (⟨j, rfl⟩ | ⟨j, hj⟩) (⟨l, hl⟩ | ⟨l, hl⟩) <;>
      simp_all [Pi.mulSingle_apply, Matrix.one_apply, Matrix.diagonal_apply, Ne.symm]
  rw [← mkOfFintype_reindexGL (Equiv.sumCompl (· = i)).symm, hblock,
    mkOfFintype_fromBlocksGL_one, mkOfFintype_scalar]

/-- The class of the invertible diagonal matrix with diagonal entries `t i` is the product of the
classes of the units `t i`. -/
@[simp]
theorem mkOfFintype_diagGL (t : n → Aˣ) :
    mkOfFintype A n (diagGL t) = ∏ i, ofUnits A (t i) := by
  -- both sides are homomorphisms in `t`, which agree on the families `Pi.mulSingle i a`
  have h : (mkOfFintype A n).comp diagGL =
      ∏ i, (ofUnits A).comp (Pi.evalMonoidHom (fun _ ↦ Aˣ) i) :=
    MonoidHom.pi_ext fun i a ↦ by
      simp [mkOfFintype_diagGL_mulSingle, MonoidHom.finsetProd_apply, Pi.mulSingle_apply,
        apply_ite]
  simpa [MonoidHom.finsetProd_apply] using DFunLike.congr_fun h t

/-- The determinant of the class of an invertible matrix over a commutative ring is its
determinant. -/
@[simp]
theorem det_mkOfFintype {R : Type*} [CommRing R] (u : GL n R) :
    det R (mkOfFintype R n u) = GeneralLinearGroup.det u := by
  rw [mkOfFintype_eq_mk_reindexGL (Fintype.equivFin n), det_mk, Equiv.det_reindexGL]

end AlgebraicK1

end TauCeti
