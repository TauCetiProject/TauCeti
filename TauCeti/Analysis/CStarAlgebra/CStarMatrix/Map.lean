/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.CStarMatrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Data.Matrix.PEquiv

/-!
# Entrywise maps, reindexing, permutation matrices, and corner embeddings for `CStarMatrix`

Within the `CStarMatrix` module split, choose `Map` for change of coefficients and index types,
`Norm` to connect rectangular operator-norm estimates with entrywise continuity, and `Block` for
block-matrix direct sums and amplification used in stabilization.

This file provides entrywise functoriality (`map_zero`, `map_one`, `map_algebraMap`, `map_add`,
`map_neg`, `map_sub`, `map_smul`, `map_mul`, `map_conjTranspose`, `map_star`), bundled
`⋆`-homomorphism lifts (`mapₙₐ`, `mapₐ`), rectangular and square reindexing equivalences
(`reindexₗ`, `reindexₐ`), permutation matrices (`permMatrix`), and diagonal corner embeddings
(`singleNonUnitalStarAlgHom`).

## Main declarations

* `CStarMatrix.instIsProperStar`, `CStarMatrix.ofMatrix_symm_map`, `CStarMatrix.mapₐ`,
  `CStarMatrix.mapₙₐ_eq_map`, `CStarMatrix.ofMatrix_symm_reindexₗ`,
  `CStarMatrix.ofMatrix_symm_reindexₐ`, `CStarMatrix.reindexₗ_mul`,
  `CStarMatrix.reindexₗ_self_eq_reindexₐ`, `CStarMatrix.isStarProjection_reindexₐ_iff`,
  `CStarMatrix.permMatrix`, `CStarMatrix.conjTranspose_permMatrix_mul_mul_permMatrix_eq_reindexₐ`,
  `CStarMatrix.singleNonUnitalStarAlgHom`.

## References

* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

open Matrix

namespace CStarMatrix

section Rectangular
variable {k l m n R A : Type*}
/-- A `CStarMatrix` with an empty row index type is a subsingleton. -/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (CStarMatrix m n A) :=
  ⟨fun _ _ => ext fun i => isEmptyElim i⟩
/-- A `CStarMatrix` with an empty column index type is a subsingleton. -/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (CStarMatrix m n A) :=
  ⟨fun _ _ => ext fun _ j => isEmptyElim j⟩
@[simp] theorem of_one [DecidableEq n] [Zero A] [One A] : ofMatrix (1 : Matrix n n A) = 1 := (rfl)
theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A] (f : Matrix l m A)
    (g : Matrix m n A) : ofMatrix f * ofMatrix g = ofMatrix (f * g) := (rfl)
theorem star_of [Star A] (f : Matrix n n A) : star (ofMatrix f) = ofMatrix fᴴ := (rfl)
theorem conjTranspose_of [Star A] (f : Matrix m n A) :
    (ofMatrix f).conjTranspose = ofMatrix fᴴ := (rfl)
/-- A self-adjoint square `CStarMatrix` equals its conjugate transpose. -/
theorem _root_.IsSelfAdjoint.conjTranspose_eq [Star A] {M : CStarMatrix n n A}
    (hM : IsSelfAdjoint M) : M.conjTranspose = M := by rw [← star_eq_conjTranspose, hM.star_eq]
/-- Scalars pull out of both factors in a rectangular `CStarMatrix` product. -/
protected theorem smul_mul_smul [Fintype m] [Monoid R] [AddCommMonoid A] [Mul A]
    [DistribMulAction R A] [IsScalarTower R A A] [SMulCommClass R A A] (a b : R)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (a • M) * (b • N) = (a * b) • (M * N) := by
  rw [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul]
@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_one, Matrix.one_mul])
@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_one, Matrix.mul_one])
section
variable [Fintype m] [NonUnitalNonAssocRing A]
protected theorem mul_sub (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_sub, Matrix.mul_sub])
protected theorem sub_mul (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_sub, Matrix.sub_mul])
@[simp] protected theorem neg_mul (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_neg, Matrix.neg_mul])
@[simp] protected theorem mul_neg (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) :=
  ofMatrix.symm.injective (by simp only [ofMatrix_symm_mul, ofMatrix_symm_neg, Matrix.mul_neg])
end
theorem conjTranspose_injective [InvolutiveStar A] :
    Function.Injective (conjTranspose : CStarMatrix m n A → CStarMatrix n m A) :=
  Function.LeftInverse.injective conjTranspose_conjTranspose
@[simp] theorem conjTranspose_inj [InvolutiveStar A] {M N : CStarMatrix m n A} :
    M.conjTranspose = N.conjTranspose ↔ M = N := conjTranspose_injective.eq_iff
@[simp] theorem conjTranspose_eq_zero [AddMonoid A] [StarAddMonoid A] {M : CStarMatrix m n A} :
    M.conjTranspose = 0 ↔ M = 0 := by
  rw [← conjTranspose_zero, conjTranspose_inj]
@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_add, Matrix.conjTranspose_add]
@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_sub, Matrix.conjTranspose_sub]
@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_neg, Matrix.conjTranspose_neg]
@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A] (r : R)
    (M : CStarMatrix m n A) : (r • M).conjTranspose = star r • M.conjTranspose :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_smul, Matrix.conjTranspose_smul]
@[simp] theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 :=
  ofMatrix.symm.injective (by
    simp only [ofMatrix_symm_conjTranspose, ofMatrix_symm_one, Matrix.conjTranspose_one])
@[simp] theorem conjTranspose_eq_one [DecidableEq n] [NonAssocSemiring A] [StarRing A]
    {M : CStarMatrix n n A} : M.conjTranspose = 1 ↔ M = 1 := by
  conv_lhs => rw [← conjTranspose_one, conjTranspose_inj]
/-- Right-multiplying `M` by a star projection `p` gives `(M * p) * (M * p)ᴴ = M * p * Mᴴ`. -/
theorem self_mul_conjTranspose_mul_of_isStarProjection [Fintype n] [NonUnitalSemiring A]
    [StarRing A] (M : CStarMatrix m n A) {p : CStarMatrix n n A} (hp : IsStarProjection p) :
    (M * p) * (M * p).conjTranspose = M * p * M.conjTranspose := by
  rw [conjTranspose_mul, hp.isSelfAdjoint.conjTranspose_eq, mul_assoc_rectangular,
    ← mul_assoc_rectangular p, hp.isIdempotentElem.eq, mul_assoc_rectangular]
section
variable [Fintype m] [Fintype n] [NonUnitalSemiring A] [StarRing A] {p : CStarMatrix n n A}
/-- If `uᴴ * u` acts as the identity on the range of a star projection `p`, then
`(u * p)ᴴ * (u * p) = p`. -/
theorem _root_.IsStarProjection.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq
    (hp : IsStarProjection p) {u : CStarMatrix m n A} (hu : u.conjTranspose * u * p = p) :
    (u * p).conjTranspose * (u * p) = p := by
  rw [conjTranspose_mul, hp.isSelfAdjoint.conjTranspose_eq, mul_assoc_rectangular,
    ← mul_assoc_rectangular u.conjTranspose, hu, hp.isIdempotentElem.eq]
end
section
variable [Fintype m] [Fintype n] [DecidableEq n] [Semiring A] [StarRing A] {p : CStarMatrix n n A}
/-- Initial projection of `u * p` for an isometry `u` (`uᴴ * u = 1`) and star projection `p`. -/
theorem _root_.IsStarProjection.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_eq_one
    (hp : IsStarProjection p) {u : CStarMatrix m n A} (hu : u.conjTranspose * u = 1) :
    (u * p).conjTranspose * (u * p) = p :=
  hp.conjTranspose_mul_self_mul_of_conjTranspose_mul_self_mul_eq (by rw [hu, CStarMatrix.one_mul])
end
section
variable [NonUnitalSemiring A] [StarRing A] [PartialOrder A] [StarOrderedRing A] [IsProperStar A]
/-- Over a star-ordered ring with proper star, `M.conjTranspose * M = 0` iff `M = 0`. -/
@[simp] theorem conjTranspose_mul_self_eq_zero [Fintype m] {M : CStarMatrix m n A} :
    M.conjTranspose * M = 0 ↔ M = 0 := by
  refine ⟨fun h => ext fun i j => ?_, fun h => by simp [h]⟩
  have hjj : ∑ k, star (M k j) * M k j = 0 := by simpa [mul_apply] using congr_fun (congr_fun h j) j
  exact star_mul_self_eq_zero.mp ((Finset.sum_eq_zero_iff_of_nonneg fun k _ =>
    star_mul_self_nonneg (M k j)).mp hjj i (Finset.mem_univ i))
/-- Square matrices over a star-ordered ring with proper star have a proper star. -/
instance instIsProperStar [Fintype n] : IsProperStar (CStarMatrix n n A) :=
  ⟨fun h => by rwa [star_eq_conjTranspose, conjTranspose_mul_self_eq_zero] at h⟩
/-- Over a star-ordered ring with proper star, `M * M.conjTranspose = 0` iff `M = 0`. -/
@[simp] theorem self_mul_conjTranspose_eq_zero [Fintype n] {M : CStarMatrix m n A} :
    M * M.conjTranspose = 0 ↔ M = 0 := by
  rw [← conjTranspose_inj (M := M), conjTranspose_zero]
  simpa using conjTranspose_mul_self_eq_zero (M := M.conjTranspose)
end
end Rectangular

section MapAndReindex
variable {k l m n o p R A B C F : Type*}
@[simp] theorem ofMatrix_symm_map (M : CStarMatrix m n A) (f : A → B) :
    ofMatrix.symm (M.map f) = (ofMatrix.symm M).map f := (rfl)
@[simp] theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_map, ofMatrix_symm_zero, Matrix.map_zero f hf]
@[simp] protected theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B]
    {f : A → B} (h₀ : f 0 = 0) (h₁ : f 1 = 1) : (1 : CStarMatrix n n A).map f = 1 :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_map, ofMatrix_symm_one, Matrix.map_one f h₀ h₁]
@[simp] theorem ofMatrix_symm_algebraMap [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Algebra R A] (r : R) :
    ofMatrix.symm (algebraMap R (CStarMatrix n n A) r) = algebraMap R (Matrix n n A) r :=
  Matrix.ext fun _ _ => by
    simp [algebraMap_apply, Matrix.algebraMap_eq_diagonal, Matrix.diagonal_apply]
@[simp] theorem map_algebraMap [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (r : R) {f : A → B} (hf : f 0 = 0)
    (hf₂ : f (algebraMap R A r) = algebraMap R B r) :
    (algebraMap R (CStarMatrix n n A) r).map f = algebraMap R (CStarMatrix n n B) r :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_algebraMap] using Matrix.map_algebraMap r f hf hf₂
theorem map_add [AddZeroClass A] [AddZeroClass B] [FunLike F A B] [AddMonoidHomClass F A B]
    (φ : F) (M N : CStarMatrix m n A) : (M + N).map φ = M.map φ + N.map φ :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_add] using
      Matrix.map_add φ (_root_.map_add φ) _ _
section
variable [AddGroup A] [SubtractionMonoid B] [FunLike F A B] [AddMonoidHomClass F A B] (φ : F)
  (M N : CStarMatrix m n A)
protected theorem map_neg : (-M).map φ = -(M.map φ) :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_neg] using
      Matrix.map_neg φ (_root_.map_neg φ) _
protected theorem map_sub : (M - N).map φ = M.map φ - N.map φ :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_sub] using
      Matrix.map_sub φ (_root_.map_sub φ) _ _
end
protected theorem map_smul [SMul R A] [SMul R B] [FunLike F A B] [MulActionHomClass F R A B]
    (φ : F) (r : R) (M : CStarMatrix m n A) : (r • M).map φ = r • M.map φ :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_smul] using
      Matrix.map_smul φ r (_root_.map_smul φ r) _
/-- Mapping entries by a non-unital ring homomorphism commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (φ : F) (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (M * N).map φ = M.map φ * N.map φ :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_mul] using
      Matrix.map_mul (L := ofMatrix.symm M) (M := ofMatrix.symm N) (f := φ)
section
variable [Star A] [Star B] [FunLike F A B] [StarHomClass F A B] (φ : F)
/-- Mapping entries by a `⋆`-homomorphism commutes with `conjTranspose`. -/
theorem map_conjTranspose (M : CStarMatrix m n A) :
    M.conjTranspose.map φ = (M.map φ).conjTranspose :=
  ofMatrix.symm.injective <| by
    simpa only [ofMatrix_symm_map, ofMatrix_symm_conjTranspose] using
      Matrix.conjTranspose_map φ (map_star φ)
/-- Mapping entries of a square matrix by a `⋆`-homomorphism commutes with `star`. -/
protected theorem map_star (M : CStarMatrix n n A) : (star M).map φ = star (M.map φ) :=
  map_conjTranspose φ M
end
section
variable [Fintype n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A] [Star A]
/-- Applying `mapₙₐ φ` acts entrywise as `CStarMatrix.map φ`. -/
theorem mapₙₐ_eq_map [NonUnitalNonAssocSemiring B] [Module R B] [Star B] (φ : A →⋆ₙₐ[R] B)
    (M : CStarMatrix n n A) : mapₙₐ φ M = M.map φ := by simp [mapₙₐ_apply, mapₗ_apply]
@[simp] theorem mapₙₐ_id : mapₙₐ (.id R A) = .id R (CStarMatrix n n A) := by ext; rfl
theorem mapₙₐ_comp [NonUnitalNonAssocSemiring B] [Module R B] [Star B] [NonUnitalNonAssocSemiring C]
    [Module R C] [Star C] (ψ : B →⋆ₙₐ[R] C) (φ : A →⋆ₙₐ[R] B) :
    mapₙₐ (ψ.comp φ) = (mapₙₐ (n := n) ψ).comp (mapₙₐ φ) := by ext; rfl
end
section
variable [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]
/-- Entrywise lift of a unital `⋆`-algebra homomorphism to square matrix algebras. -/
def mapₐ (φ : A →⋆ₐ[R] B) : CStarMatrix n n A →⋆ₐ[R] CStarMatrix n n B :=
  { mapₙₐ φ.toNonUnitalStarAlgHom with
    map_one' := (mapₙₐ_eq_map _ 1).trans (CStarMatrix.map_one φ.map_zero φ.map_one)
    commutes' r := (mapₙₐ_eq_map _ _).trans (map_algebraMap r φ.map_zero (φ.commutes r)) }
@[simp low] theorem mapₐ_apply (φ : A →⋆ₐ[R] B) (M : CStarMatrix n n A) :
    mapₐ φ M = M.map φ := mapₙₐ_eq_map φ.toNonUnitalStarAlgHom M
@[simp] theorem mapₐ_id : mapₐ (.id R A) = .id R (CStarMatrix n n A) := by ext; rfl
theorem mapₐ_comp [Semiring C] [Algebra R C] [Star C] (ψ : B →⋆ₐ[R] C) (φ : A →⋆ₐ[R] B) :
    mapₐ (ψ.comp φ) = (mapₐ (n := n) ψ).comp (mapₐ φ) := by ext; rfl
/-- `mapₐ φ` is injective whenever `φ` is injective. -/
theorem mapₐ_injective {φ : A →⋆ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapₐ φ : CStarMatrix n n A → CStarMatrix n n B) := fun _ _ h =>
  map_injective hφ (by simpa only [mapₐ_apply] using h)
end
section
variable [Semiring R] [AddCommMonoid A] [Module R A]
@[simp] theorem ofMatrix_symm_reindexₗ (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    ofMatrix.symm (reindexₗ R A eₘ eₙ M) = Matrix.reindex eₘ eₙ (ofMatrix.symm M) := (rfl)
@[simp] theorem conjTranspose_reindexₗ [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by ext; rfl
/-- `reindexₗ` is multiplicative across matching intermediate equivalences. -/
@[simp] theorem reindexₗ_mul [Fintype m] [Fintype o] [Mul A] (eₗ : l ≃ k) (eₘ : m ≃ o) (eₙ : n ≃ p)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N = reindexₗ R A eₗ eₙ (M * N) :=
  ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_mul, ofMatrix_symm_reindexₗ, ofMatrix_symm_reindexₗ,
      ofMatrix_symm_reindexₗ, Matrix.reindex_apply, Matrix.reindex_apply, Matrix.reindex_apply,
      Matrix.submatrix_mul_equiv _ _ _ eₘ.symm, ofMatrix_symm_mul]
@[simp] theorem reindexₗ_refl :
    reindexₗ R A (.refl m) (.refl n) = LinearEquiv.refl R (CStarMatrix m n A) := by ext; rfl
@[simp] theorem reindexₗ_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    reindexₗ R A eₘ.symm eₙ.symm = (reindexₗ R A eₘ eₙ).symm := by ext; rfl
theorem reindexₗ_trans (e₁ : m ≃ l) (e₂ : l ≃ k) (f₁ : n ≃ o) (f₂ : o ≃ p) :
    reindexₗ R A (e₁.trans e₂) (f₁.trans f₂) =
      (reindexₗ R A e₁ f₁).trans (reindexₗ R A e₂ f₂) := by ext; rfl
section
variable [Fintype m] [Fintype n] [Mul A] [Star A]
@[simp] theorem ofMatrix_symm_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    ofMatrix.symm (reindexₐ R A e M) = Matrix.reindex e e (ofMatrix.symm M) := (rfl)
/-- Reindexing rows and columns of a square `CStarMatrix` by `e` via `reindexₗ` is `reindexₐ`. -/
theorem reindexₗ_self_eq_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := by ext; rfl
@[simp] theorem reindexₐ_refl :
    reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by ext; rfl
theorem reindexₐ_trans [Fintype l] (e₁ : l ≃ m) (e₂ : m ≃ n) :
    reindexₐ R A (e₁.trans e₂) = (reindexₐ R A e₁).trans (reindexₐ R A e₂) := by ext; rfl
/-- Reindexing a square `CStarMatrix` along `e : m ≃ n` preserves star projections. -/
@[simp] theorem isStarProjection_reindexₐ_iff (e : m ≃ n) {p : CStarMatrix m m A} :
    IsStarProjection (reindexₐ R A e p) ↔ IsStarProjection p :=
  ⟨fun h => (reindexₐ R A e).symm_apply_apply p ▸ h.map _, fun h => h.map _⟩
end
end
section Permutation
/-- The permutation `CStarMatrix` associated with a bijection `e : m ≃ n`. -/
def permMatrix (A : Type*) [DecidableEq n] [Zero A] [One A] (e : m ≃ n) : CStarMatrix m n A :=
  ofMatrix e.toPEquiv.toMatrix
@[simp] theorem ofMatrix_symm_permMatrix [DecidableEq n] [Zero A] [One A] (e : m ≃ n) :
    ofMatrix.symm (permMatrix A e) = e.toPEquiv.toMatrix := (rfl)
@[simp] theorem permMatrix_apply [DecidableEq n] [Zero A] [One A] (e : m ≃ n) (i : m) (j : n) :
    permMatrix A e i j = if e i = j then 1 else 0 := by
  simp [permMatrix, PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, eq_comm]
@[simp] theorem permMatrix_refl [DecidableEq n] [Zero A] [One A] :
    permMatrix A (Equiv.refl n) = 1 :=
  ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_permMatrix, Equiv.toPEquiv_refl, PEquiv.toMatrix_refl,
      ofMatrix_symm_one]
@[simp] theorem conjTranspose_permMatrix [DecidableEq m] [DecidableEq n] [NonAssocSemiring A]
    [StarRing A] (e : m ≃ n) : (permMatrix A e).conjTranspose = permMatrix A e.symm := by
  ext i j; simp [Equiv.eq_symm_apply, eq_comm, apply_ite star]
@[simp] theorem permMatrix_trans [Fintype n] [DecidableEq n] [DecidableEq o] [NonAssocSemiring A]
    (e₁ : m ≃ n) (e₂ : n ≃ o) :
    permMatrix A e₁ * permMatrix A e₂ = permMatrix A (e₁.trans e₂) :=
  ofMatrix.symm.injective <| by
    rw [ofMatrix_symm_mul, ofMatrix_symm_permMatrix, ofMatrix_symm_permMatrix,
      ofMatrix_symm_permMatrix, ← PEquiv.toMatrix_trans, Equiv.toPEquiv_trans]
@[simp] theorem conjTranspose_permMatrix_mul_self [Fintype m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    (permMatrix A e).conjTranspose * permMatrix A e = 1 := by
  classical
  rw [conjTranspose_permMatrix, permMatrix_trans, Equiv.symm_trans_self, permMatrix_refl]
theorem permMatrix_mul_conjTranspose_self [Fintype n] [DecidableEq m] [DecidableEq n]
    [NonAssocSemiring A] [StarRing A] (e : m ≃ n) :
    permMatrix A e * (permMatrix A e).conjTranspose = 1 := by
  rw [conjTranspose_permMatrix, permMatrix_trans, Equiv.self_trans_symm, permMatrix_refl]
@[simp] theorem permMatrix_mem_unitary [Fintype n] [DecidableEq n] [Semiring A] [StarRing A]
    (e : n ≃ n) : permMatrix A e ∈ unitary (CStarMatrix n n A) := by
  rw [Unitary.mem_iff, star_eq_conjTranspose, conjTranspose_permMatrix_mul_self,
    permMatrix_mul_conjTranspose_self, and_self]
/-- Conjugating `M` by `(permMatrix A e).conjTranspose` on the left and `permMatrix A e` on the
right computes `reindexₐ R A e M`. -/
theorem conjTranspose_permMatrix_mul_mul_permMatrix_eq_reindexₐ [Fintype m] [Fintype n]
    [DecidableEq n] [Semiring R] [NonAssocSemiring A] [Module R A] [StarRing A] (e : m ≃ n)
    (M : CStarMatrix m m A) :
    (permMatrix A e).conjTranspose * M * permMatrix A e = reindexₐ R A e M := by
  classical
  apply ofMatrix.symm.injective
  simp only [ofMatrix_symm_mul, conjTranspose_permMatrix, ofMatrix_symm_permMatrix,
    ofMatrix_symm_reindexₐ, PEquiv.toMatrix_toPEquiv_mul, PEquiv.mul_toMatrix_toPEquiv,
    Matrix.submatrix_submatrix, Matrix.reindex_apply, Function.comp_id, Function.id_comp]
/-- Conjugating `N` by `(permMatrix A e)` on the left and its adjoint on the right computes
`reindexₐ R A e.symm N`. -/
theorem permMatrix_mul_mul_conjTranspose_permMatrix_eq_reindexₐ_symm [Fintype m] [Fintype n]
    [DecidableEq n] [Semiring R] [NonAssocSemiring A] [Module R A] [StarRing A] (e : m ≃ n)
    (N : CStarMatrix n n A) :
    permMatrix A e * N * (permMatrix A e).conjTranspose = reindexₐ R A e.symm N := by
  classical
  simpa [conjTranspose_permMatrix] using
    conjTranspose_permMatrix_mul_mul_permMatrix_eq_reindexₐ (R := R) e.symm N
end Permutation
section
variable [Fintype n] [DecidableEq n] [Semiring R] [NonUnitalNonAssocSemiring A] [Module R A]
  [StarAddMonoid A]
/-- Diagonal `(i, i)`-corner embedding `a ↦ single i i a` as a non-unital `⋆`-algebra morphism. -/
def singleNonUnitalStarAlgHom (R : Type*) [Semiring R] [Module R A] (i : n) :
    A →⋆ₙₐ[R] CStarMatrix n n A where
  toFun a := ofMatrix (Matrix.single i i a)
  map_smul' _ _ := by simp [smul_of, Matrix.smul_single]
  map_zero' := by rw [Matrix.single_zero, of_zero]
  map_add' _ _ := by rw [of_add_of, Matrix.single_add]
  map_mul' _ _ := ofMatrix.symm.injective <| by
    simp only [ofMatrix_symm_mul, Equiv.symm_apply_apply, Matrix.single_mul_single_same]
  map_star' _ := by rw [star_of, Matrix.conjTranspose_single]
@[simp low] theorem singleNonUnitalStarAlgHom_apply (i : n) (a : A) :
    singleNonUnitalStarAlgHom R i a = ofMatrix (Matrix.single i i a) := (rfl)
/-- The diagonal `(i, i)`-corner embedding `singleNonUnitalStarAlgHom` is injective. -/
theorem singleNonUnitalStarAlgHom_injective (i : n) :
    Function.Injective (singleNonUnitalStarAlgHom R i : A → CStarMatrix n n A) := fun _ _ h => by
  simpa using congr_fun (congr_fun (congrArg ofMatrix.symm h) i) i
end
end MapAndReindex

end CStarMatrix
