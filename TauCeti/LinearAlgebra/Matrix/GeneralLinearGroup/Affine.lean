/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.ColumnRowPartitioned
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Equivalence
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.Logic.Equiv.Fin.Basic

/-!
# The affine subgroups of general linear groups

For a ring `R` and finite index types `n` and `m`, the **affine group** `A_{n,m}(R)` is the
subgroup of `GL (n ⊕ m) R` fixing the vectors `(0; e_j)` of the summand `Rᵐ` of `Rⁿ ⊕ Rᵐ`: the
invertible matrices `M` with `M * (0; 1) = (0; 1)`, which are exactly the lower block triangular
matrices `(g 0; u 1)`. The diagonal block `g` is then invertible, and `(g 0; u 1)` acts on
`Rⁿ ⊕ Rᵐ` by `(x; y) ↦ (g x; u x + y)`. For `m = 1`, right multiplication on the row vectors
`(x, 1)` is `(x, 1) ↦ (x g + u, 1)`, by the affine transformation `x ↦ x g + u` of the row vectors
of length `n`.

The group `A_{n,m}(R)` is a split extension of `GL n R` by the additive group of `m × n`
matrices:

* `GL n R` embeds by `g ↦ (g 0; 0 1)` (`TauCeti.affineInclusion`);
* the additive group of `m × n` matrices embeds by `u ↦ (1 0; u 1)`
  (`TauCeti.affineTranslation`);
* the projection `(g 0; u 1) ↦ g` (`TauCeti.affineProjection`) is a retraction of the first
  embedding, and its kernel is the image of the second.

Over a commutative ring, `A_{n,m}(R)` is the stabilizer of the matrix `(0; 1)` for the action of
`GL (n ⊕ m) R` on rectangular matrices by left multiplication. More generally, for an
equivalence `ι ≃ n ⊕ m`, the stabilizer in `GL ι R` of the frame of standard basis columns
indexed by `m` is isomorphic to `A_{n,m}(R)`; in particular the stabilizer in `GL (Fin n) R` of
the first `r` standard basis vectors `(e₁, …, e_r)` is isomorphic to `A_{n-r,r}(R)`. Through
these stabilizers of standard frames, the action of `GL (Fin n) R` on the unimodular frames of
`Rⁿ` computes the homology of general linear groups: over a semilocal ring with infinite residue
fields, a theorem of Nesterenko and Suslin (not proved here) says that the inclusion
`GL n R → A_{n,m}(R)` induces isomorphisms on integral homology.

## Main definitions

* `TauCeti.affineGroup R n m`: the subgroup of `GL (n ⊕ m) R` of matrices fixing `(0; 1)`.
* `TauCeti.affineInclusion R n m`: the inclusion `GL n R →* A_{n,m}(R)`, `g ↦ (g 0; 0 1)`.
* `TauCeti.affineProjection R n m`: the projection `A_{n,m}(R) →* GL n R`, `(g 0; u 1) ↦ g`.
* `TauCeti.affineTranslation R n m`: the embedding of the additive group of `m × n` matrices,
  `u ↦ (1 0; u 1)`.
* `TauCeti.affineTranslationEquivKer R n m`: the additive group of `m × n` matrices is
  isomorphic to the kernel of the projection.
* `TauCeti.stabilizerEquivAffineGroup`: for `e : ι ≃ n ⊕ m`, the stabilizer of the standard
  columns `e⁻¹ (inr j)` in `GL ι R` is isomorphic to `A_{n,m}(R)`.
* `TauCeti.stabilizerCastLEEquivAffineGroup`: the stabilizer of `(e₁, …, e_r)` in
  `GL (Fin n) R` is isomorphic to `A_{n-r,r}(R)`.

## Main results

* `TauCeti.mem_affineGroup_iff`: `M ∈ A_{n,m}(R)` exactly when its upper right block is zero and
  its lower right block is the identity.
* `TauCeti.affineProjection_comp_affineInclusion`: the projection is a retraction of the
  inclusion.
* `TauCeti.ker_affineProjection`: the kernel of the projection is the range of
  `affineTranslation`.
* `TauCeti.affineInclusion_affineProjection_mul_affineTranslation`: every element of
  `A_{n,m}(R)` is `(g 0; 0 1) (1 0; u 1)`.
* `TauCeti.affineGroup_eq_stabilizer`: over a commutative ring, `A_{n,m}(R)` is the stabilizer of
  `(0; 1)`.
* `TauCeti.reindexGL_affineInclusion`: along `Fin n ⊕ Fin m ≃ Fin (n + m)`, the inclusion
  `GL (Fin n) R → A_{n,m}(R)` is the stabilization `g ↦ g ⊕ 1`.

## References

* Yu. P. Nesterenko, A. A. Suslin, *Homology of the full linear group over a local ring, and
  Milnor's K-theory*, Izv. Akad. Nauk SSSR Ser. Mat. 53 (1989), §1, Proposition 1.10.
* S. Galatius, A. Kupers, O. Randal-Williams, *E∞-cells and general linear groups of infinite
  fields* (2025), Definition 5.12.
-/

public section

noncomputable section

open Matrix

namespace TauCeti

section Ring

variable (R : Type*) [Ring R] (n m : Type*) [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m]

/-- The **affine group** `A_{n,m}(R)`: the subgroup of `GL (n ⊕ m) R` of the invertible matrices
`M` fixing the vectors `(0; e_j)` of the summand `Rᵐ`, that is, with `M * (0; 1) = (0; 1)`. These
are the block matrices `(g 0; u 1)` (`TauCeti.mem_affineGroup_iff`). -/
def affineGroup : Subgroup (GL (n ⊕ m) R) where
  carrier := {M | (M : Matrix (n ⊕ m) (n ⊕ m) R) * fromRows (0 : Matrix n m R) (1 : Matrix m m R) =
    fromRows 0 1}
  mul_mem' {M N} hM hN := by
    simp only [Set.mem_ofPred_eq, Units.val_mul] at hM hN ⊢
    rw [Matrix.mul_assoc, hN, hM]
  one_mem' := by simp
  inv_mem' {M} hM := by
    simp only [Set.mem_ofPred_eq] at hM ⊢
    conv_lhs => rw [← hM]
    rw [← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul]

variable {R n m}

/-- Membership in the affine group, by its defining equation `M * (0; 1) = (0; 1)`. -/
theorem mem_affineGroup_iff_mul_fromRows {M : GL (n ⊕ m) R} :
    M ∈ affineGroup R n m ↔
      (M : Matrix (n ⊕ m) (n ⊕ m) R) * fromRows (0 : Matrix n m R) (1 : Matrix m m R) =
        fromRows 0 1 :=
  Iff.rfl

/-- An invertible block matrix lies in the affine group exactly when its upper right block is
zero and its lower right block is the identity. -/
theorem mem_affineGroup_iff {M : GL (n ⊕ m) R} :
    M ∈ affineGroup R n m ↔
      (M : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₂ = 0 ∧
        (M : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₂₂ = 1 := by
  rw [mem_affineGroup_iff_mul_fromRows]
  conv_lhs => rw [← fromBlocks_toBlocks (M : Matrix (n ⊕ m) (n ⊕ m) R)]
  simp [fromBlocks_mul_fromRows, fromRows_ext_iff]

/-- An element of the affine group is the block matrix `(g 0; u 1)` of its two left blocks. -/
theorem coe_eq_fromBlocks_of_mem_affineGroup {M : GL (n ⊕ m) R} (hM : M ∈ affineGroup R n m) :
    (M : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (M : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ 0
        (M : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₂₁ 1 := by
  obtain ⟨h₁₂, h₂₂⟩ := mem_affineGroup_iff.1 hM
  rw [← h₁₂, ← h₂₂, fromBlocks_toBlocks]

/-- The upper left block of a product whose left factor has zero upper right block is the
product of the upper left blocks. -/
private theorem toBlocks₁₁_mul_of_mem_affineGroup {M : GL (n ⊕ m) R}
    (hM : M ∈ affineGroup R n m) (N : GL (n ⊕ m) R) :
    ((M * N : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ =
      (M : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ * (N : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ := by
  conv_lhs => rw [Units.val_mul, ← fromBlocks_toBlocks (M : Matrix (n ⊕ m) (n ⊕ m) R),
    ← fromBlocks_toBlocks (N : Matrix (n ⊕ m) (n ⊕ m) R)]
  simp [fromBlocks_multiply, (mem_affineGroup_iff.1 hM).1]

variable (R n m)

/-- The affine group of an empty fixed summand is the whole general linear group. -/
theorem affineGroup_eq_top_of_isEmpty [IsEmpty m] : affineGroup R n m = ⊤ :=
  eq_top_iff.2 fun _ _ => mem_affineGroup_iff_mul_fromRows.2 (Subsingleton.elim _ _)

/-- The affine group with an empty moving summand is trivial. -/
theorem affineGroup_eq_bot_of_isEmpty [IsEmpty n] : affineGroup R n m = ⊥ := by
  refine eq_bot_iff.2 fun M hM => Subgroup.mem_bot.2 (Units.ext ?_)
  have h := (mem_affineGroup_iff.1 hM).2
  ext (i | i) (j | j)
  · exact isEmptyElim i
  · exact isEmptyElim i
  · exact isEmptyElim j
  · simpa [Matrix.one_apply, toBlocks₂₂] using congrFun (congrFun h i) j

/-! ## The inclusion `GL n R → A_{n,m}(R)` -/

/-- The inclusion `GL n R →* A_{n,m}(R)`, `g ↦ (g 0; 0 1)`, through the block diagonal
homomorphism `TauCeti.fromBlocksGL`. -/
def affineInclusion : GL n R →* affineGroup R n m :=
  (fromBlocksGL.comp (MonoidHom.inl (GL n R) (GL m R))).codRestrict _ fun g =>
    mem_affineGroup_iff.2 ⟨by simp, by simp⟩

/-- The matrix underlying the image of `g` under the inclusion is `(g 0; 0 1)`. -/
@[simp]
theorem coe_affineInclusion (g : GL n R) :
    ((affineInclusion R n m g : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks (g : Matrix n n R) 0 0 1 := by
  simp [affineInclusion]

/-- The image of `g` under the inclusion is the block diagonal matrix `g ⊕ 1`. -/
theorem affineInclusion_eq_fromBlocksGL (g : GL n R) :
    (affineInclusion R n m g : GL (n ⊕ m) R) = fromBlocksGL (g, 1) :=
  Units.ext (by simp)

/-! ## The projection `A_{n,m}(R) → GL n R` -/

/-- The projection `A_{n,m}(R) →* GL n R`, `(g 0; u 1) ↦ g`, taking an element of the affine
group to its upper left block. -/
def affineProjection : affineGroup R n m →* GL n R where
  toFun M :=
    { val := ((M : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁
      inv := (((M⁻¹ : affineGroup R n m) : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁
      val_inv := by
        rw [← toBlocks₁₁_mul_of_mem_affineGroup M.property, ← Subgroup.coe_mul]
        simp [← fromBlocks_one]
      inv_val := by
        rw [← toBlocks₁₁_mul_of_mem_affineGroup M⁻¹.property, ← Subgroup.coe_mul]
        simp [← fromBlocks_one] }
  map_one' := Units.ext (by simp [← fromBlocks_one])
  map_mul' M N := Units.ext (toBlocks₁₁_mul_of_mem_affineGroup M.property N)

/-- The matrix underlying the projection of `M` is the upper left block of `M`. -/
@[simp]
theorem coe_affineProjection (M : affineGroup R n m) :
    (affineProjection R n m M : Matrix n n R) =
      ((M : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ :=
  (rfl)

/-- The projection recovers `g` from `(g 0; 0 1)`. -/
@[simp]
theorem affineProjection_affineInclusion (g : GL n R) :
    affineProjection R n m (affineInclusion R n m g) = g :=
  Units.ext (by simp)

/-- The projection is a retraction of the inclusion. -/
theorem affineProjection_comp_affineInclusion :
    (affineProjection R n m).comp (affineInclusion R n m) = MonoidHom.id (GL n R) :=
  MonoidHom.ext (affineProjection_affineInclusion R n m)

/-- The inclusion `GL n R → A_{n,m}(R)` is injective. -/
theorem affineInclusion_injective : Function.Injective (affineInclusion R n m) :=
  Function.LeftInverse.injective (affineProjection_affineInclusion R n m)

/-- The projection `A_{n,m}(R) → GL n R` is surjective. -/
theorem affineProjection_surjective : Function.Surjective (affineProjection R n m) :=
  Function.LeftInverse.surjective (affineProjection_affineInclusion R n m)

/-! ## The translations `u ↦ (1 0; u 1)` and the kernel of the projection -/

/-- The embedding of the additive group of `m × n` matrices into `A_{n,m}(R)`,
`u ↦ (1 0; u 1)`, through the lower block unipotent matrices `Matrix.lowerBlockGL`. -/
def affineTranslation : Multiplicative (Matrix m n R) →* affineGroup R n m where
  toFun u := ⟨lowerBlockGL u.toAdd, mem_affineGroup_iff.2 ⟨by simp, by simp⟩⟩
  map_one' := Subtype.ext lowerBlockGL_zero
  map_mul' u v := Subtype.ext (lowerBlockGL_add u.toAdd v.toAdd)

/-- The matrix underlying the translation by `u` is `(1 0; u 1)`. -/
@[simp]
theorem coe_affineTranslation (u : Multiplicative (Matrix m n R)) :
    ((affineTranslation R n m u : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R) =
      fromBlocks 1 0 u.toAdd 1 := by
  simp [affineTranslation]

/-- The embedding of the `m × n` matrices into the affine group is injective. -/
theorem affineTranslation_injective : Function.Injective (affineTranslation R n m) := by
  intro u v huv
  have h := congrArg toBlocks₂₁ congr(((($huv : affineGroup R n m) : GL (n ⊕ m) R) :
    Matrix (n ⊕ m) (n ⊕ m) R))
  simpa using h

/-- The translations lie in the kernel of the projection. -/
@[simp]
theorem affineProjection_affineTranslation (u : Multiplicative (Matrix m n R)) :
    affineProjection R n m (affineTranslation R n m u) = 1 :=
  Units.ext (by simp)

/-- The kernel of the projection `A_{n,m}(R) → GL n R` consists of the translations
`(1 0; u 1)`. -/
theorem ker_affineProjection :
    (affineProjection R n m).ker = (affineTranslation R n m).range := by
  ext M
  refine ⟨fun hM => ⟨Multiplicative.ofAdd ((M : GL (n ⊕ m) R) :
    Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₂₁, ?_⟩, ?_⟩
  · have h₁₁ : ((M : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₁₁ = 1 :=
      congrArg Units.val (MonoidHom.mem_ker.1 hM)
    refine Subtype.ext (Units.ext ?_)
    rw [coe_affineTranslation, toAdd_ofAdd]
    conv_rhs => rw [coe_eq_fromBlocks_of_mem_affineGroup M.property, h₁₁]
  · rintro ⟨u, rfl⟩
    exact MonoidHom.mem_ker.2 (affineProjection_affineTranslation R n m u)

/-- The additive group of `m × n` matrices is isomorphic to the kernel of the projection
`A_{n,m}(R) → GL n R`, by `u ↦ (1 0; u 1)`. -/
def affineTranslationEquivKer :
    Multiplicative (Matrix m n R) ≃* (affineProjection R n m).ker :=
  (MonoidHom.ofInjective (affineTranslation_injective R n m)).trans
    (MulEquiv.subgroupCongr (ker_affineProjection R n m).symm)

/-- The isomorphism with the kernel sends `u` to the translation `(1 0; u 1)`. -/
@[simp]
theorem coe_affineTranslationEquivKer_apply (u : Multiplicative (Matrix m n R)) :
    (affineTranslationEquivKer R n m u : affineGroup R n m) = affineTranslation R n m u :=
  (rfl)

/-- Every element of the affine group factors as `(g 0; u 1) = (g 0; 0 1) (1 0; u 1)`. -/
theorem affineInclusion_affineProjection_mul_affineTranslation (M : affineGroup R n m) :
    affineInclusion R n m (affineProjection R n m M) *
        affineTranslation R n m
          (Multiplicative.ofAdd ((M : GL (n ⊕ m) R) : Matrix (n ⊕ m) (n ⊕ m) R).toBlocks₂₁) =
      M := by
  refine Subtype.ext (Units.ext ?_)
  rw [Subgroup.coe_mul, Units.val_mul, coe_affineInclusion, coe_affineTranslation,
    fromBlocks_multiply, coe_eq_fromBlocks_of_mem_affineGroup M.property]
  simp

/-! ## Stabilization -/

/-- Along `Fin n ⊕ Fin m ≃ Fin (n + m)`, the inclusion `GL (Fin n) R → A_{n,m}(R)` is the
stabilization `g ↦ g ⊕ 1` of `TauCeti.stabilizeGL`. -/
theorem reindexGL_affineInclusion (n m : ℕ) (g : GL (Fin n) R) :
    finSumFinEquiv.reindexGL R (affineInclusion R (Fin n) (Fin m) g : GL (Fin n ⊕ Fin m) R) =
      stabilizeGL R (Nat.le_add_right n m) g := by
  rw [stabilizeGL_eq_reindexGL_fromBlocksGL, affineInclusion_eq_fromBlocksGL]

end Ring

/-! ## Stabilizers of standard frames -/

section CommRing

variable {R : Type*} [CommRing R] {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m]
  [DecidableEq m] {ι : Type*} [Fintype ι] [DecidableEq ι]

variable (R n m) in
/-- Over a commutative ring, the affine group is the stabilizer of the matrix `(0; 1)` for the
action of `GL (n ⊕ m) R` on rectangular matrices by left multiplication. -/
theorem affineGroup_eq_stabilizer :
    affineGroup R n m =
      MulAction.stabilizer (GL (n ⊕ m) R) (fromRows (0 : Matrix n m R) (1 : Matrix m m R)) := by
  ext M
  rw [MulAction.mem_stabilizer_iff, GeneralLinearGroup.smul_def,
    mem_affineGroup_iff_mul_fromRows]

/-- For an equivalence `e : ι ≃ n ⊕ m`, reindexing along `e` carries the stabilizer in `GL ι R`
of the standard basis columns `e⁻¹ (inr j)`, `j : m`, onto the affine group `A_{n,m}(R)`. -/
theorem map_stabilizer_eq_affineGroup (e : ι ≃ n ⊕ m) :
    (MulAction.stabilizer (GL ι R) ((1 : Matrix ι ι R).submatrix id (e.symm ∘ Sum.inr))).map
        (e.reindexGL R).toMonoidHom =
      affineGroup R n m := by
  ext M
  rw [Subgroup.mem_map_equiv, mem_affineGroup_iff_mul_fromRows,
    ← fromRows_zero_one_submatrix_equiv e]
  simp [MulAction.mem_stabilizer_iff, GeneralLinearGroup.smul_def, submatrix_mul_equiv,
    (submatrix_injective e.surjective Function.surjective_id).eq_iff]

/-- For an equivalence `e : ι ≃ n ⊕ m`, the stabilizer in `GL ι R` of the standard basis columns
`e⁻¹ (inr j)`, `j : m`, is isomorphic to the affine group `A_{n,m}(R)`, by reindexing along
`e`. -/
def stabilizerEquivAffineGroup (e : ι ≃ n ⊕ m) :
    MulAction.stabilizer (GL ι R) ((1 : Matrix ι ι R).submatrix id (e.symm ∘ Sum.inr)) ≃*
      affineGroup R n m :=
  ((e.reindexGL R).subgroupMap _).trans (MulEquiv.subgroupCongr (map_stabilizer_eq_affineGroup e))

/-- The isomorphism of the stabilizer with the affine group is reindexing along `e`. -/
@[simp]
theorem coe_stabilizerEquivAffineGroup_apply (e : ι ≃ n ⊕ m)
    (M : MulAction.stabilizer (GL ι R) ((1 : Matrix ι ι R).submatrix id (e.symm ∘ Sum.inr))) :
    (stabilizerEquivAffineGroup e M : GL (n ⊕ m) R) = e.reindexGL R M :=
  (rfl)

/-- The inverse of the isomorphism of the stabilizer with the affine group is reindexing along
`e.symm`. -/
@[simp]
theorem coe_stabilizerEquivAffineGroup_symm_apply (e : ι ≃ n ⊕ m) (M : affineGroup R n m) :
    ((stabilizerEquivAffineGroup e).symm M : GL ι R) = e.symm.reindexGL R M := by
  rw [← Equiv.reindexGL_symm, MulEquiv.eq_symm_apply, ← coe_stabilizerEquivAffineGroup_apply,
    MulEquiv.apply_symm_apply]

variable (R) in
/-- The stabilizer in `GL (Fin n) R` of the first `r` standard basis vectors `(e₁, …, e_r)`,
the frame given by the `n × r` matrix `(1; 0)`, is isomorphic to the affine group
`A_{n-r,r}(R)`, by reindexing along `TauCeti.finSubSumEquiv`. -/
def stabilizerCastLEEquivAffineGroup {r n : ℕ} (h : r ≤ n) :
    MulAction.stabilizer (GL (Fin n) R) ((1 : Matrix (Fin n) (Fin n) R).submatrix id
      (Fin.castLE h)) ≃* affineGroup R (Fin (n - r)) (Fin r) :=
  (MulEquiv.subgroupCongr (by simp [Function.comp_def])).trans
    (stabilizerEquivAffineGroup (finSubSumEquiv h))

/-- The isomorphism of the stabilizer of `(e₁, …, e_r)` with `A_{n-r,r}(R)` is reindexing along
`TauCeti.finSubSumEquiv`. -/
@[simp]
theorem coe_stabilizerCastLEEquivAffineGroup_apply {r n : ℕ} (h : r ≤ n)
    (M : MulAction.stabilizer (GL (Fin n) R) ((1 : Matrix (Fin n) (Fin n) R).submatrix id
      (Fin.castLE h))) :
    (stabilizerCastLEEquivAffineGroup R h M : GL (Fin (n - r) ⊕ Fin r) R) =
      (finSubSumEquiv h).reindexGL R M :=
  (rfl)

/-- The inverse of the isomorphism of the stabilizer of `(e₁, …, e_r)` with `A_{n-r,r}(R)` is
reindexing along the inverse of `TauCeti.finSubSumEquiv`. -/
@[simp]
theorem coe_stabilizerCastLEEquivAffineGroup_symm_apply {r n : ℕ} (h : r ≤ n)
    (M : affineGroup R (Fin (n - r)) (Fin r)) :
    ((stabilizerCastLEEquivAffineGroup R h).symm M : GL (Fin n) R) =
      (finSubSumEquiv h).symm.reindexGL R M := by
  rw [← Equiv.reindexGL_symm, MulEquiv.eq_symm_apply, ← coe_stabilizerCastLEEquivAffineGroup_apply,
    MulEquiv.apply_symm_apply]

end CommRing

end TauCeti
