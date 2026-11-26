/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Prod
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable.BlockSum

/-!
# Calculations in algebraic `K₁`

Algebraic `K₁(A)` of a ring `A` is built from the invertible matrices indexed by `Fin n`
(`TauCeti.AlgebraicK1.mk`). This file gives every invertible matrix over an arbitrary finite index
type a class in `K₁(A)`, and proves the elementary rules for computing with classes, written
additively as in the usual notation `[u]`:

* the class does not depend on how the index type is enumerated, nor on a relabelling of the
  indices, and conjugate matrices have the same class;
* the class of a block diagonal matrix is the sum of the classes of its blocks,
  `[diag(u, v)] = [u] + [v]`, which reduces to the contiguous block sum formula
  `TauCeti.AlgebraicK1.mk_blockSumGL` over `Fin`;
* the class of a block triangular matrix with diagonal blocks `u` and `v` is `[u] + [v]`,
  whatever its off-diagonal block, and a class is trivial exactly when `u ⊕ 1` is elementary for
  an identity block of some size;
* the class of an invertible diagonal matrix is the sum of the classes of its entries.

It then computes `K₁` of the zero ring, which is trivial, and of a product of two rings,
`K₁(A × B) ≅ K₁(A) × K₁(B)` through the two projections. The latter holds because an invertible
matrix over `A × B` is a pair of invertible matrices, and the class of such a pair splits as the
product of the classes of the matrices `(u, 1)` and `(1, v)`.

## Main definitions

* `TauCeti.AlgebraicK1.mkOfFintype`: the class in `K₁(A)` of an invertible matrix indexed by an
  arbitrary finite type.
* `TauCeti.AlgebraicK1.prodEquiv`: `K₁(A × B) ≃* K₁(A) × K₁(B)`, induced by the projections.

## Main results

* `TauCeti.AlgebraicK1.mkOfFintype_eq_mk_reindexGL`: the class of a matrix over a finite index
  type is the class of its reindexing along any enumeration of the index type.
* `TauCeti.AlgebraicK1.of_ofEquiv`: the class of a matrix over a finite index type is the image in
  `K₁(A)` of its image in `GL_∞(A)` through any enumeration of the index type.
* `TauCeti.AlgebraicK1.mkOfFintype_reindexGL`,
  `TauCeti.AlgebraicK1.mkOfFintype_mul_mul_inv`: invariance under relabelling and conjugation.
* `TauCeti.AlgebraicK1.mkOfFintype_fromBlocksGL`: the block sum formula
  `[diag(u, v)] = [u] + [v]`.
* `TauCeti.AlgebraicK1.elementarySubgroup_le_ker_mkOfFintype`: elementary matrices have trivial
  class.
* `TauCeti.AlgebraicK1.mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₂₁`,
  `TauCeti.AlgebraicK1.mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₁₂`: a block triangular matrix
  with invertible diagonal blocks `u` and `v` has class `[u] + [v]`.
* `TauCeti.AlgebraicK1.mkOfFintype_eq_one_iff`: `[u]` is trivial exactly when `u ⊕ 1` is
  elementary for an identity block of some size.
* `TauCeti.AlgebraicK1.mkOfFintype_scalar`, `TauCeti.AlgebraicK1.mkOfFintype_diagGL`: the class of
  an invertible diagonal matrix is the sum of the classes of its diagonal entries.
* `TauCeti.AlgebraicK1.instSubsingleton`: `K₁` of the zero ring is trivial.
* `TauCeti.AlgebraicK1.prodEquiv_apply`, `TauCeti.AlgebraicK1.prodEquiv_symm_mk`: the isomorphism
  `K₁(A × B) ≃* K₁(A) × K₁(B)` and its inverse on classes.

## References

* C. Weibel, *The K-book: An Introduction to Algebraic K-theory*, GSM 145 (2013), Chapter III,
  Definition 1.1 and the paragraph after it, and Whitehead's Lemma 1.3.3.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §3.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

namespace AlgebraicK1

variable {A : Type*} [Ring A]

/-! ## Relabelling indices -/

variable (A) in
/-- The class in algebraic `K₁` of an invertible matrix indexed by an arbitrary finite type `ι`:
the class of its reindexing along an enumeration `ι ≃ Fin n`. By
`TauCeti.AlgebraicK1.mkOfFintype_eq_mk_reindexGL` the class does not depend on the enumeration. -/
def mkOfFintype (ι : Type*) [Fintype ι] [DecidableEq ι] : GL ι A →* AlgebraicK1 A :=
  (mk A (Fintype.card ι)).comp ((Fintype.equivFin ι).reindexGL A).toMonoidHom

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Unfolding `TauCeti.AlgebraicK1.mkOfFintype`: the class of the reindexing along the enumeration
`Fintype.equivFin ι`. -/
theorem mkOfFintype_apply (u : GL ι A) :
    mkOfFintype A ι u = mk A (Fintype.card ι) ((Fintype.equivFin ι).reindexGL A u) := by
  rw [mkOfFintype, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]

/-- The class of an invertible matrix over a finite index type `ι` is the class of its
reindexing along **any** enumeration `ι ≃ Fin n`. -/
theorem mkOfFintype_eq_mk_reindexGL {n : ℕ} (e : ι ≃ Fin n) (u : GL ι A) :
    mkOfFintype A ι u = mk A n (e.reindexGL A u) := by
  -- Reindexing along `e` is reindexing along the enumeration `Fintype.equivFin ι`, followed by
  -- the relabelling `(Fintype.equivFin ι).symm.trans e` of `Fin`, which does not change classes.
  have h : e.reindexGL A u =
      ((Fintype.equivFin ι).symm.trans e).reindexGL A ((Fintype.equivFin ι).reindexGL A u) := by
    ext : 1
    simp [Function.comp_def]
  rw [h, mk_reindexGL, mkOfFintype_apply]

/-- Over the index type `Fin n`, the class of an invertible matrix is `TauCeti.AlgebraicK1.mk`. -/
@[simp]
theorem mkOfFintype_fin (n : ℕ) : mkOfFintype A (Fin n) = mk A n :=
  MonoidHom.ext fun u ↦ by simp [mkOfFintype_eq_mk_reindexGL (Equiv.refl (Fin n))]

/-- The class of the reindexing of an invertible matrix along an enumeration `ι ≃ Fin n` is its
class over `ι`. -/
@[simp]
theorem mk_reindexGL_eq_mkOfFintype {n : ℕ} (e : ι ≃ Fin n) (u : GL ι A) :
    mk A n (e.reindexGL A u) = mkOfFintype A ι u :=
  (mkOfFintype_eq_mk_reindexGL e u).symm

/-- The image in `K₁(A)` of the image in `GL_∞(A)` of an invertible matrix through any enumeration
of its indices is its class `TauCeti.AlgebraicK1.mkOfFintype`. -/
theorem of_ofEquiv {n : ℕ} (e : ι ≃ Fin n) (u : GL ι A) :
    Group.Abelianization.of (StableGeneralLinearGroup.ofEquiv A e u) = mkOfFintype A ι u := by
  rw [StableGeneralLinearGroup.ofEquiv_apply, ← mk_apply, mk_reindexGL_eq_mkOfFintype]

/-- **Relabelling invariance**: reindexing an invertible matrix along an equivalence of finite
index types does not change its class in algebraic `K₁`. -/
@[simp]
theorem mkOfFintype_reindexGL (e : ι ≃ κ) (u : GL ι A) :
    mkOfFintype A κ (e.reindexGL A u) = mkOfFintype A ι u := by
  rw [mkOfFintype_eq_mk_reindexGL (e.symm.trans (Fintype.equivFin ι)),
    mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι)]
  congr 1
  ext : 1
  simp [Function.comp_def]

/-- **Conjugation invariance**: conjugate invertible matrices have the same class in algebraic
`K₁`. -/
@[simp]
theorem mkOfFintype_mul_mul_inv (g u : GL ι A) :
    mkOfFintype A ι (g * u * g⁻¹) = mkOfFintype A ι u := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-! ## Block sums -/

/-- **The block sum formula**: the class of a block diagonal matrix `u ⊕ v` is the product of the
classes of its blocks, `[diag(u, v)] = [u] + [v]` in additive notation. -/
@[simp]
theorem mkOfFintype_fromBlocksGL (u : GL ι A) (v : GL κ A) :
    mkOfFintype A (ι ⊕ κ) (fromBlocksGL (u, v)) = mkOfFintype A ι u * mkOfFintype A κ v := by
  set e := Fintype.equivFin ι
  set f := Fintype.equivFin κ
  -- Relabel both blocks along their enumerations; the result is a contiguous block sum.
  have h : finSumFinEquiv.reindexGL A (fromBlocksGL (e.reindexGL A u, f.reindexGL A v)) =
      blockSumGL A (e.reindexGL A u, f.reindexGL A v) := by
    ext : 1
    rw [coe_blockSumGL, Equiv.coe_reindexGL, coe_fromBlocksGL, reindex_apply]
  calc mkOfFintype A (ι ⊕ κ) (fromBlocksGL (u, v))
      = mkOfFintype A _ ((e.sumCongr f).reindexGL A (fromBlocksGL (u, v))) :=
        (mkOfFintype_reindexGL (e.sumCongr f) _).symm
    _ = mk A _ (blockSumGL A (e.reindexGL A u, f.reindexGL A v)) := by
        rw [Equiv.reindexGL_sumCongr_fromBlocksGL, mkOfFintype_eq_mk_reindexGL finSumFinEquiv, h]
    _ = mkOfFintype A ι u * mkOfFintype A κ v := by
        rw [mk_blockSumGL, mkOfFintype_eq_mk_reindexGL e, mkOfFintype_eq_mk_reindexGL f]

/-- Applying a ring homomorphism to the entries commutes with taking classes over an arbitrary
finite index type. -/
@[simp]
theorem map_mkOfFintype {B : Type*} [Ring B] (f : A →+* B) (u : GL ι A) :
    map f (mkOfFintype A ι u) = mkOfFintype B ι (Units.map f.mapMatrix.toMonoidHom u) := by
  rw [mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι),
    mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι), map_mk]
  congr 1
  ext : 1
  simp [Matrix.submatrix_map]

/-! ## Elementary matrices and triangular matrices -/

/-- The class of `u ⊕ 1` is the class of `u`. -/
private theorem mkOfFintype_fromBlocksGL_one (u : GL ι A) :
    mkOfFintype A (ι ⊕ κ) (fromBlocksGL (u, 1)) = mkOfFintype A ι u := by
  rw [mkOfFintype_fromBlocksGL, map_one, mul_one]

/-- Elementary matrices have trivial class in `K₁(A)`. -/
theorem elementarySubgroup_le_ker_mkOfFintype :
    elementarySubgroup ι A ≤ (mkOfFintype A ι).ker := by
  intro u hu
  rw [MonoidHom.mem_ker, mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι)]
  exact elementarySubgroup_le_ker_mk _ ((Equiv.reindexGL_mem_elementarySubgroup_iff _).2 hu)

/-- The class of an invertible matrix is trivial exactly when its block sum `u ⊕ 1` with an
identity matrix of some size is elementary. -/
theorem mkOfFintype_eq_one_iff {u : GL ι A} :
    mkOfFintype A ι u = 1 ↔
      ∃ k : ℕ, fromBlocksGL (u, (1 : GL (Fin k) A)) ∈ elementarySubgroup (ι ⊕ Fin k) A := by
  refine ⟨fun h ↦ ?_, fun ⟨k, hk⟩ ↦ ?_⟩
  · rw [mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι), mk_eq_one_iff] at h
    obtain ⟨_, hk, hmem⟩ := h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hk
    rw [stabilizeGL_reindexGL, Equiv.reindexGL_mem_elementarySubgroup_iff] at hmem
    exact ⟨k, hmem⟩
  · rw [← mkOfFintype_fromBlocksGL_one (κ := Fin k)]
    exact elementarySubgroup_le_ker_mkOfFintype hk

/-- A block upper triangular matrix with invertible diagonal blocks `u` and `v` has class
`[u] [v]`, whatever its off-diagonal block. -/
theorem mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₂₁ {g : GL (ι ⊕ κ) A} {u : GL ι A}
    {v : GL κ A} {X : Matrix ι κ A} (hg : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) A) = fromBlocks u X 0 v) :
    mkOfFintype A (ι ⊕ κ) g = mkOfFintype A ι u * mkOfFintype A κ v := by
  have hfac : g = fromBlocksGL (u, v) * upperBlockGL ((↑u⁻¹ : Matrix ι ι A) * X) :=
    Units.ext (by simp [hg, fromBlocks_multiply, ← Matrix.mul_assoc])
  rw [hfac, map_mul, mkOfFintype_fromBlocksGL,
    elementarySubgroup_le_ker_mkOfFintype (upperBlockGL_mem_elementarySubgroup _), mul_one]

/-- A block lower triangular matrix with invertible diagonal blocks `u` and `v` has class
`[u] [v]`, whatever its off-diagonal block. -/
theorem mkOfFintype_eq_mul_of_coe_eq_fromBlocks_zero₁₂ {g : GL (ι ⊕ κ) A} {u : GL ι A}
    {v : GL κ A} {Y : Matrix κ ι A} (hg : (g : Matrix (ι ⊕ κ) (ι ⊕ κ) A) = fromBlocks u 0 Y v) :
    mkOfFintype A (ι ⊕ κ) g = mkOfFintype A ι u * mkOfFintype A κ v := by
  have hfac : g = fromBlocksGL (u, v) * lowerBlockGL ((↑v⁻¹ : Matrix κ κ A) * Y) :=
    Units.ext (by simp [hg, fromBlocks_multiply, ← Matrix.mul_assoc])
  rw [hfac, map_mul, mkOfFintype_fromBlocksGL,
    elementarySubgroup_le_ker_mkOfFintype (lowerBlockGL_mem_elementarySubgroup _), mul_one]

/-! ## Diagonal matrices and the determinant -/

/-- Over an index type with exactly one element, the class of the scalar matrix `(a)` is the
class `AlgebraicK1.ofUnits A a` of the unit `a`. -/
@[simp]
theorem mkOfFintype_scalar [Unique ι] (a : Aˣ) :
    mkOfFintype A ι (GeneralLinearGroup.scalar ι a) = ofUnits A a := by
  rw [mkOfFintype_eq_mk_reindexGL (Equiv.ofUnique ι (Fin 1)), ofUnits_apply]
  congr 1
  ext i j
  simp [Subsingleton.elim i j]

/-- The class of the diagonal matrix with one diagonal entry `a` and all others `1` is the class
of the unit `a`. -/
private theorem mkOfFintype_diagGL_mulSingle (i : ι) (a : Aˣ) :
    mkOfFintype A ι (diagGL (Pi.mulSingle i a)) = ofUnits A a := by
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
theorem mkOfFintype_diagGL (t : ι → Aˣ) :
    mkOfFintype A ι (diagGL t) = ∏ i, ofUnits A (t i) := by
  -- both sides are homomorphisms in `t`, which agree on the families `Pi.mulSingle i a`
  have h : (mkOfFintype A ι).comp diagGL =
      ∏ i, (ofUnits A).comp (Pi.evalMonoidHom (fun _ ↦ Aˣ) i) :=
    MonoidHom.pi_ext fun i a ↦ by
      simp [mkOfFintype_diagGL_mulSingle, MonoidHom.finsetProd_apply, Pi.mulSingle_apply,
        apply_ite]
  simpa [MonoidHom.finsetProd_apply] using DFunLike.congr_fun h t

/-! ## The zero ring -/

/-- **`K₁` of the zero ring is trivial**: over the zero ring every invertible matrix is the
identity. -/
instance instSubsingleton [Subsingleton A] : Subsingleton (AlgebraicK1 A) := by
  refine ⟨fun x y ↦ ?_⟩
  obtain ⟨m, u, rfl⟩ := exists_mk x
  obtain ⟨n, v, rfl⟩ := exists_mk y
  rw [Subsingleton.elim u 1, Subsingleton.elim v 1, map_one, map_one]

/-! ## Products of rings -/

section Prod

variable {B : Type*} [Ring B]

/-- The class in `K₁(A × B)` of the invertible matrix over `A × B` whose two components are the
invertible matrices `u` over `A` and `v` over `B`. -/
private def mkProd (n : ℕ) : GL (Fin n) A × GL (Fin n) B →* AlgebraicK1 (A × B) :=
  (mk (A × B) n).comp (prodEquivGL (Fin n) A B).symm.toMonoidHom

/-- The class of a pair is unchanged by stabilizing both matrices. -/
private theorem mkProd_stabilizeGL {m n : ℕ} (h : m ≤ n) (p : GL (Fin m) A × GL (Fin m) B) :
    mkProd n (stabilizeGL A h p.1, stabilizeGL B h p.2) = mkProd m p := by
  simp only [mkProd, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← mk_stabilizeGL h]
  congr 1
  -- Stabilization commutes with the two projections `A × B → A` and `A × B → B`.
  rw [MulEquiv.symm_apply_eq]
  ext : 1
  · rw [prodEquivGL_apply_fst, ← stabilizeGL_map, ← prodEquivGL_apply_fst,
      MulEquiv.apply_symm_apply]
  · rw [prodEquivGL_apply_snd, ← stabilizeGL_map, ← prodEquivGL_apply_snd,
      MulEquiv.apply_symm_apply]

/-- The first projection sends the class of a pair to the class of its first matrix. -/
private theorem map_fst_mkProd {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.fst A B) (mkProd n p) = mk A n p.1 := by
  rw [mkProd, MonoidHom.comp_apply, map_mk, MulEquiv.coe_toMonoidHom, ← prodEquivGL_apply_fst,
    MulEquiv.apply_symm_apply]

/-- The second projection sends the class of a pair to the class of its second matrix. -/
private theorem map_snd_mkProd {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.snd A B) (mkProd n p) = mk B n p.2 := by
  rw [mkProd, MonoidHom.comp_apply, map_mk, MulEquiv.coe_toMonoidHom, ← prodEquivGL_apply_snd,
    MulEquiv.apply_symm_apply]

/-- The homomorphism `K₁(A) →* K₁(A × B)` sending the class of `u` to the class of the pair
`(u, 1)`. -/
private def inlK1 : AlgebraicK1 A →* AlgebraicK1 (A × B) :=
  lift (fun n ↦ (mkProd n).comp (MonoidHom.inl _ _)) fun m n h u ↦ by
    simpa using mkProd_stabilizeGL (B := B) h (u, 1)

/-- The homomorphism `K₁(B) →* K₁(A × B)` sending the class of `v` to the class of the pair
`(1, v)`. -/
private def inrK1 : AlgebraicK1 B →* AlgebraicK1 (A × B) :=
  lift (fun n ↦ (mkProd n).comp (MonoidHom.inr _ _)) fun m n h v ↦ by
    simpa using mkProd_stabilizeGL (A := A) h (1, v)

variable (A B) in
/-- **`K₁` of a product of rings** is the product of the `K₁`-groups of the factors, through the
homomorphisms induced by the two projections. -/
def prodEquiv : AlgebraicK1 (A × B) ≃* AlgebraicK1 A × AlgebraicK1 B where
  toFun := (map (RingHom.fst A B)).prod (map (RingHom.snd A B))
  invFun := inlK1.coprod inrK1
  left_inv x := by
    obtain ⟨n, w, rfl⟩ := exists_mk x
    -- Write `w` through its pair of components `p`, and split `p` as `(p.1, 1) * (1, p.2)`.
    obtain ⟨p, rfl⟩ := (prodEquivGL (Fin n) A B).symm.surjective w
    calc inlK1.coprod inrK1 ((map (RingHom.fst A B)).prod (map (RingHom.snd A B)) (mkProd n p))
        _ = mkProd n (p.1, 1) * mkProd n (1, p.2) := by
          simp [map_fst_mkProd, map_snd_mkProd, inlK1, inrK1]
        _ = mkProd n p := by rw [← map_mul, Prod.fst_mul_snd]
  right_inv y := by
    obtain ⟨x, y⟩ := y
    obtain ⟨m, u, rfl⟩ := exists_mk x
    obtain ⟨n, v, rfl⟩ := exists_mk y
    simp [inlK1, inrK1, map_fst_mkProd, map_snd_mkProd]
  map_mul' := map_mul _

/-- The isomorphism `K₁(A × B) ≃* K₁(A) × K₁(B)` is given by the homomorphisms induced by the two
projections. -/
@[simp]
theorem prodEquiv_apply (x : AlgebraicK1 (A × B)) :
    prodEquiv A B x = (map (RingHom.fst A B) x, map (RingHom.snd A B) x) :=
  (rfl)

/-- The inverse of `K₁(A × B) ≃* K₁(A) × K₁(B)` sends the pair of classes of invertible matrices
`u` over `A` and `v` over `B` of the same size to the class of the invertible matrix over `A × B`
with components `u` and `v`. -/
@[simp]
theorem prodEquiv_symm_mk {n : ℕ} (u : GL (Fin n) A) (v : GL (Fin n) B) :
    (prodEquiv A B).symm (mk A n u, mk B n v) =
      mk (A × B) n ((prodEquivGL (Fin n) A B).symm (u, v)) := by
  rw [MulEquiv.symm_apply_eq, prodEquiv_apply]
  exact Prod.ext (map_fst_mkProd (u, v)).symm (map_snd_mkProd (u, v)).symm

end Prod

end AlgebraicK1

end TauCeti
