/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable

/-!
# Calculations in algebraic `K₁`

Algebraic `K₁(A)` of a ring `A` is built from the invertible matrices indexed by `Fin n`
(`TauCeti.AlgebraicK1.mk`). This file gives every invertible matrix over an arbitrary finite index
type a class in `K₁(A)`, and proves the elementary rules for computing with classes, written
additively as in the usual notation `[u]`:

* the class does not depend on how the index type is enumerated, nor on a relabelling of the
  indices, and conjugate matrices have the same class;
* the class of a block diagonal matrix is the sum of the classes of its blocks,
  `[diag(u, v)] = [u] + [v]`.

It then computes `K₁` of the zero ring, which is trivial, and of a product of two rings,
`K₁(A × B) ≅ K₁(A) × K₁(B)` through the two projections. The latter holds because an invertible
matrix over `A × B` is a pair of invertible matrices, and the class of such a pair splits as the
product of the classes of the matrices `(u, 1)` and `(1, v)`.

## Main definitions

* `TauCeti.AlgebraicK1.mkOfFintype`: the class in `K₁(A)` of an invertible matrix indexed by an
  arbitrary finite type.
* `TauCeti.AlgebraicK1.prodEquiv`: `K₁(A × B) ≃* K₁(A) × K₁(B)`, induced by the projections.

## Main results

* `TauCeti.AlgebraicK1.mk_reindexGL`: relabelling the indices of a matrix by a permutation does
  not change its class.
* `TauCeti.AlgebraicK1.mkOfFintype_eq_mk_reindexGL`: the class of a matrix over a finite index
  type is the class of its reindexing along any enumeration of the index type.
* `TauCeti.AlgebraicK1.mkOfFintype_reindexGL`,
  `TauCeti.AlgebraicK1.mkOfFintype_mul_mul_inv`: invariance under relabelling and conjugation.
* `TauCeti.AlgebraicK1.mkOfFintype_fromBlocksGL`: the block sum formula
  `[diag(u, v)] = [u] + [v]`.
* `TauCeti.AlgebraicK1.instSubsingleton`: `K₁` of the zero ring is trivial.

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

/-- **Relabelling invariance**: permuting the rows and columns of an invertible matrix by the
same permutation does not change its class in algebraic `K₁`, since the permuted matrix is a
conjugate of the original one by a permutation matrix. -/
@[simp]
theorem mk_reindexGL {n : ℕ} (σ : Equiv.Perm (Fin n)) (u : GL (Fin n) A) :
    mk A n (σ.reindexGL A u) = mk A n u := by
  rw [← permutationGL_mul_mul_inv, map_mul, map_mul, map_inv, mul_inv_cancel_comm]

variable (A) in
/-- The class in algebraic `K₁` of an invertible matrix indexed by an arbitrary finite type `ι`:
the class of its reindexing along an enumeration `ι ≃ Fin n`. By
`TauCeti.AlgebraicK1.mkOfFintype_eq_mk_reindexGL` the class does not depend on the enumeration. -/
def mkOfFintype (ι : Type*) [Fintype ι] [DecidableEq ι] : GL ι A →* AlgebraicK1 A :=
  (mk A (Fintype.card ι)).comp ((Fintype.equivFin ι).reindexGL A).toMonoidHom

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- The class of an invertible matrix over a finite index type `ι` is the class of its
reindexing along **any** enumeration `ι ≃ Fin n`. -/
theorem mkOfFintype_eq_mk_reindexGL {n : ℕ} (e : ι ≃ Fin n) (u : GL ι A) :
    mkOfFintype A ι u = mk A n (e.reindexGL A u) := by
  obtain rfl : Fintype.card ι = n := Fintype.card_fin n ▸ Fintype.card_congr e
  -- `e` differs from the enumeration `Fintype.equivFin ι` by a permutation of `Fin n`.
  have h : e = (Fintype.equivFin ι).trans ((Fintype.equivFin ι).symm.trans e) := by
    rw [← Equiv.trans_assoc, Equiv.self_trans_symm, Equiv.refl_trans]
  rw [h, ← Equiv.reindexGL_trans_reindexGL, MulEquiv.trans_apply, mk_reindexGL]
  rfl

/-- Over the index type `Fin n`, the class of an invertible matrix is `TauCeti.AlgebraicK1.mk`. -/
@[simp]
theorem mkOfFintype_fin (n : ℕ) : mkOfFintype A (Fin n) = mk A n :=
  MonoidHom.ext fun u ↦ by simp [mkOfFintype_eq_mk_reindexGL (Equiv.refl (Fin n))]

/-- **Relabelling invariance**: reindexing an invertible matrix along an equivalence of finite
index types does not change its class in algebraic `K₁`. -/
@[simp]
theorem mkOfFintype_reindexGL (e : ι ≃ κ) (u : GL ι A) :
    mkOfFintype A κ (e.reindexGL A u) = mkOfFintype A ι u := by
  rw [mkOfFintype_eq_mk_reindexGL (e.symm.trans (Fintype.equivFin ι)), ← MulEquiv.trans_apply,
    Equiv.reindexGL_trans_reindexGL, ← Equiv.trans_assoc, Equiv.self_trans_symm,
    Equiv.refl_trans, mkOfFintype_eq_mk_reindexGL (Fintype.equivFin ι)]

/-- **Conjugation invariance**: conjugate invertible matrices have the same class in algebraic
`K₁`. -/
@[simp]
theorem mkOfFintype_mul_mul_inv (g u : GL ι A) :
    mkOfFintype A ι (g * u * g⁻¹) = mkOfFintype A ι u := by
  rw [map_mul, map_mul, map_inv, mul_inv_cancel_comm]

/-! ## Block sums -/

/-- The class of the block diagonal matrix `u ⊕ 1` is the class of `u`. -/
theorem mkOfFintype_fromBlocksGL_one (u : GL ι A) :
    mkOfFintype A (ι ⊕ κ) (fromBlocksGL (u, 1)) = mkOfFintype A ι u := by
  set e := Fintype.equivFin ι
  set f := Fintype.equivFin κ
  rw [mkOfFintype_eq_mk_reindexGL ((e.sumCongr f).trans finSumFinEquiv),
    ← Equiv.reindexGL_trans_reindexGL, MulEquiv.trans_apply,
    Equiv.sumCongr_reindexGL_fromBlocksGL, map_one, ← stabilizeGL_eq_reindexGL_fromBlocksGL,
    mk_stabilizeGL, mkOfFintype_eq_mk_reindexGL e]

/-- The class of the block diagonal matrix `1 ⊕ v` is the class of `v`. -/
theorem mkOfFintype_one_fromBlocksGL (v : GL κ A) :
    mkOfFintype A (ι ⊕ κ) (fromBlocksGL (1, v)) = mkOfFintype A κ v := by
  rw [← mkOfFintype_reindexGL (Equiv.sumComm ι κ), Equiv.sumComm_reindexGL_fromBlocksGL,
    mkOfFintype_fromBlocksGL_one]

/-- **The block sum formula**: the class of a block diagonal matrix `u ⊕ v` is the product of the
classes of its blocks, `[diag(u, v)] = [u] + [v]` in additive notation. -/
@[simp]
theorem mkOfFintype_fromBlocksGL (u : GL ι A) (v : GL κ A) :
    mkOfFintype A (ι ⊕ κ) (fromBlocksGL (u, v)) = mkOfFintype A ι u * mkOfFintype A κ v := by
  have h : ((u, v) : GL ι A × GL κ A) = (u, 1) * (1, v) := by simp
  rw [h, map_mul, map_mul, mkOfFintype_fromBlocksGL_one, mkOfFintype_one_fromBlocksGL]

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
  (mk (A × B) n).comp ((Units.mapEquiv (Matrix.prodRingEquiv (Fin n) A B).toMulEquiv).trans
    MulEquiv.prodUnits).symm.toMonoidHom

/-- The class of a pair is unchanged by stabilizing both matrices. -/
private theorem mkProd_stabilizeGL {m n : ℕ} (h : m ≤ n) (p : GL (Fin m) A × GL (Fin m) B) :
    mkProd n (stabilizeGL A h p.1, stabilizeGL B h p.2) = mkProd m p := by
  rw [mkProd, mkProd, MonoidHom.comp_apply, MonoidHom.comp_apply, ← mk_stabilizeGL h]
  congr 1
  ext i j : 2
  -- The entries of the pairing are the pairs of entries by definition, but `simp` cannot reach
  -- them: the coercion produced by `MulEquiv.prodUnits` goes through the monoid structure of the
  -- matrix ring, which `TauCeti.coe_stabilizeGL_apply` does not match syntactically.
  change (stabilizeGL A h p.1 i j, stabilizeGL B h p.2 i j) = _
  -- Both sides are computed entrywise: the block of `p` in the corner, identity entries elsewhere.
  simp only [coe_stabilizeGL_apply]
  split_ifs
  · rfl
  · simp only [Matrix.one_apply]
    split_ifs <;> rfl

/-- An invertible matrix over `A × B` has the class of the pair of its two components. -/
private theorem mkProd_unitsMap_fst_snd {n : ℕ} (w : GL (Fin n) (A × B)) :
    mkProd n (Units.map (RingHom.fst A B).mapMatrix.toMonoidHom w,
      Units.map (RingHom.snd A B).mapMatrix.toMonoidHom w) = mk (A × B) n w :=
  congrArg (mk (A × B) n) (Units.ext (by ext <;> rfl))

/-- The first projection sends the class of a pair to the class of its first matrix. -/
private theorem map_fst_mkProd {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.fst A B) (mkProd n p) = mk A n p.1 := by
  rw [mkProd, MonoidHom.comp_apply, map_mk]
  exact congrArg (mk A n) (Units.ext (by ext; rfl))

/-- The second projection sends the class of a pair to the class of its second matrix. -/
private theorem map_snd_mkProd {n : ℕ} (p : GL (Fin n) A × GL (Fin n) B) :
    map (RingHom.snd A B) (mkProd n p) = mk B n p.2 := by
  rw [mkProd, MonoidHom.comp_apply, map_mk]
  exact congrArg (mk B n) (Units.ext (by ext; rfl))

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
    suffices ∀ p : GL (Fin n) A × GL (Fin n) B,
        inlK1.coprod inrK1 ((map (RingHom.fst A B)).prod (map (RingHom.snd A B)) (mkProd n p)) =
          mkProd n p by
      rw [← mkProd_unitsMap_fst_snd]
      exact this _
    intro p
    -- Split the pair `p` as `(p.1, 1) * (1, p.2)`.
    conv_rhs => rw [show p = (p.1, 1) * (1, p.2) by simp, map_mul]
    simp only [MonoidHom.prod_apply, MonoidHom.coprod_apply, map_fst_mkProd, map_snd_mkProd,
      inlK1, inrK1, lift_mk, MonoidHom.comp_apply, MonoidHom.inl_apply, MonoidHom.inr_apply]
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

end Prod

end AlgebraicK1

end TauCeti
