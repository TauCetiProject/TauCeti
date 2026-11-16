/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Hom
public import Mathlib.Data.Matrix.Basis
import TauCeti.Algebra.Star.Basic
import TauCeti.Analysis.CStarAlgebra.Module.AdjointPair
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Rectangular algebra, operator norms, and quadratic-form positivity for `CStarMatrix`

Rectangular `conjTranspose`, multiplication, proper-star (`IsProperStar`), `map`/`mapₐ`/`mapₙₐ`,
`reindexₗ`/`reindexₐ`, diagonal embeddings (`singleNonUnitalStarAlgHom`), operator-norm laws via
adjoint pairs (`‖M * N‖ ≤ ‖M‖ * ‖N‖`, `‖Mᴴ‖ = ‖M‖`, `‖M * Mᴴ‖ = ‖Mᴴ * M‖ = ‖M‖ ^ 2`,
`norm_reindexₗ`, `norm_single`), entrywise continuity (`continuous_iff`), quadratic-form positivity
(`nonneg_iff_forall_sum_nonneg`), and real CFC (`instNonUnitalContinuousFunctionalCalculusReal`).

## Main declarations

* `CStarMatrix.instIsProperStar`, `mapₐ`, `singleNonUnitalStarAlgHom`, `reindexₗ_self_eq_reindexₐ`,
  `norm_conjTranspose`, `norm_self_mul_conjTranspose`, `norm_conjTranspose_mul_self`,
  `norm_reindexₗ`, `norm_single`, `continuous_iff`, `isSelfAdjoint_of_forall_isSelfAdjoint_sum`,
  `nonneg_iff_forall_sum_nonneg`, `instNonUnitalContinuousFunctionalCalculusReal`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Ch. 1 and Lemma 4.1.
* B. Blackadar, *K-Theory for Operator Algebras*, 2nd ed., §4.6 and §5.1.
-/

public section

open Matrix
open scoped ComplexOrder InnerProductSpace WithCStarModule

namespace CStarMatrix

section Algebraic
variable {k l m n o R A : Type*}
/-- A `CStarMatrix` with an empty row index type is a subsingleton. -/
instance subsingleton_of_empty_left [IsEmpty m] : Subsingleton (CStarMatrix m n A) :=
  ⟨fun _ _ => ext fun i => isEmptyElim i⟩
/-- A `CStarMatrix` with an empty column index type is a subsingleton. -/
instance subsingleton_of_empty_right [IsEmpty n] : Subsingleton (CStarMatrix m n A) :=
  ⟨fun _ _ => ext fun _ j => isEmptyElim j⟩
/-- Scalars commute past matrix multiplication on the left, as for `Matrix`. -/
instance instIsScalarTowerSelf [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A]
    [DistribMulAction R A] [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix n n A) (CStarMatrix n n A) := ⟨fun r M N => smul_mul r M N⟩
/-- Scalars commute past matrix multiplication on the right, as for `Matrix`. -/
instance instSMulCommClassSelf [Fintype n] [Monoid R] [AddCommMonoid A] [Mul A]
    [DistribMulAction R A] [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix n n A) (CStarMatrix n n A) := ⟨fun r M N => (mul_smul M r N).symm⟩
@[simp] lemma ofMatrix_symm_zero [Zero A] : ofMatrix.symm (0 : CStarMatrix m n A) = 0 := (rfl)
@[simp] lemma ofMatrix_symm_one [DecidableEq n] [Zero A] [One A] :
    ofMatrix.symm (1 : CStarMatrix n n A) = 1 := (rfl)
@[simp] lemma ofMatrix_symm_add [Add A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M + N) = ofMatrix.symm M + ofMatrix.symm N := (rfl)
@[simp] lemma ofMatrix_symm_neg [Neg A] (M : CStarMatrix m n A) :
    ofMatrix.symm (-M) = -ofMatrix.symm M := (rfl)
@[simp] lemma ofMatrix_symm_sub [Sub A] (M N : CStarMatrix m n A) :
    ofMatrix.symm (M - N) = ofMatrix.symm M - ofMatrix.symm N := (rfl)
@[simp] lemma ofMatrix_symm_smul [SMul R A] (r : R) (M : CStarMatrix m n A) :
    ofMatrix.symm (r • M) = r • ofMatrix.symm M := (rfl)
/-- Reading a C⋆-matrix as an ordinary matrix respects multiplication. -/
@[simp] lemma ofMatrix_symm_mul [Fintype m] [Mul A] [AddCommMonoid A] (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)
/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp] lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)
@[simp] theorem of_one [DecidableEq n] [Zero A] [One A] : ofMatrix (1 : Matrix n n A) = 1 := (rfl)
@[simp] theorem of_mul_of [Fintype m] [Mul A] [AddCommMonoid A] (f : Matrix l m A)
    (g : Matrix m n A) : ofMatrix f * ofMatrix g = ofMatrix (f * g) := (rfl)
@[simp] theorem star_of [Star A] (f : Matrix n n A) : star (ofMatrix f) = ofMatrix fᴴ := (rfl)
@[simp] theorem ofMatrix_symm_conjTranspose [Star A] (M : CStarMatrix m n A) :
    ofMatrix.symm M.conjTranspose = (ofMatrix.symm M)ᴴ := (rfl)
@[simp] theorem conjTranspose_of [Star A] (f : Matrix m n A) :
    (ofMatrix f).conjTranspose = ofMatrix fᴴ := (rfl)
/-- A self-adjoint square `CStarMatrix` equals its conjugate transpose. -/
theorem conjTranspose_eq_of_isSelfAdjoint [Star A] {M : CStarMatrix n n A} (hM : IsSelfAdjoint M) :
    M.conjTranspose = M := by rw [← star_eq_conjTranspose, hM.star_eq]
/-- Rectangular matrix multiplication on `CStarMatrix` is associative. -/
protected theorem mul_assoc [Fintype l] [Fintype m] [NonUnitalSemiring A] (L : CStarMatrix k l A)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : L * M * N = L * (M * N) :=
  ofMatrix.symm.injective (Matrix.mul_assoc (ofMatrix.symm L) (ofMatrix.symm M) (ofMatrix.symm N))
/-- Scalars pull out of both factors in a rectangular `CStarMatrix` product. -/
protected theorem smul_mul_smul [Fintype m] [Monoid R] [AddCommMonoid A] [Mul A]
    [DistribMulAction R A] [IsScalarTower R A A] [SMulCommClass R A A] (a b : R)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : (a • M) * (b • N) = (a * b) • (M * N) := by
  rw [CStarMatrix.smul_mul, CStarMatrix.mul_smul, smul_smul]
@[simp] protected theorem one_mul [Fintype m] [DecidableEq m] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : (1 : CStarMatrix m m A) * M = M :=
  ofMatrix.symm.injective (Matrix.one_mul (ofMatrix.symm M))
@[simp] protected theorem mul_one [Fintype n] [DecidableEq n] [NonAssocSemiring A]
    (M : CStarMatrix m n A) : M * (1 : CStarMatrix n n A) = M :=
  ofMatrix.symm.injective (Matrix.mul_one (ofMatrix.symm M))
section
variable [Fintype m] [NonUnitalNonAssocRing A]
protected theorem mul_sub (L : CStarMatrix l m A) (M N : CStarMatrix m n A) :
    L * (M - N) = L * M - L * N := ofMatrix.symm.injective (Matrix.mul_sub _ _ _)
protected theorem sub_mul (L M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (L - M) * N = L * N - M * N := ofMatrix.symm.injective (Matrix.sub_mul _ _ _)
@[simp] protected theorem neg_mul (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (-M) * N = -(M * N) := ofMatrix.symm.injective (Matrix.neg_mul _ _)
@[simp] protected theorem mul_neg (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    M * (-N) = -(M * N) := ofMatrix.symm.injective (Matrix.mul_neg _ _)
end
@[simp] theorem conjTranspose_conjTranspose [InvolutiveStar A] (M : CStarMatrix m n A) :
    M.conjTranspose.conjTranspose = M := by ext; simp
theorem conjTranspose_injective [InvolutiveStar A] :
    Function.Injective (conjTranspose : CStarMatrix m n A → CStarMatrix n m A) :=
  Function.LeftInverse.injective conjTranspose_conjTranspose
@[simp] theorem conjTranspose_inj [InvolutiveStar A] {M N : CStarMatrix m n A} :
    M.conjTranspose = N.conjTranspose ↔ M = N := conjTranspose_injective.eq_iff
@[simp] theorem conjTranspose_add [AddMonoid A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M + N).conjTranspose = M.conjTranspose + N.conjTranspose := by ext; simp
@[simp] theorem conjTranspose_sub [AddGroup A] [StarAddMonoid A] (M N : CStarMatrix m n A) :
    (M - N).conjTranspose = M.conjTranspose - N.conjTranspose := by ext; simp
@[simp] theorem conjTranspose_neg [AddGroup A] [StarAddMonoid A] (M : CStarMatrix m n A) :
    (-M).conjTranspose = -M.conjTranspose := by ext; simp
@[simp] theorem conjTranspose_smul [Star R] [Star A] [SMul R A] [StarModule R A] (r : R)
    (M : CStarMatrix m n A) : (r • M).conjTranspose = star r • M.conjTranspose := by ext; simp
@[simp] theorem conjTranspose_one [DecidableEq n] [NonAssocSemiring A] [StarRing A] :
    (1 : CStarMatrix n n A).conjTranspose = 1 := ofMatrix.symm.injective Matrix.conjTranspose_one
/-- Conjugate transposition reverses rectangular matrix products. -/
@[simp] theorem conjTranspose_mul [Fintype m] [NonUnitalNonAssocSemiring A] [StarRing A]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    (M * N).conjTranspose = N.conjTranspose * M.conjTranspose :=
  ofMatrix.symm.injective (Matrix.conjTranspose_mul _ _)
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
/-- If all quadratic forms of `M` over a complex proper-star algebra are self-adjoint, so is `M`. -/
theorem isSelfAdjoint_of_forall_isSelfAdjoint_sum [Fintype n] [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [IsProperStar A]
    {M : CStarMatrix n n A}
    (hM : ∀ x : n → A, IsSelfAdjoint (∑ i, ∑ j, star (x i) * M i j * x j)) : IsSelfAdjoint M := by
  classical
  replace hM (x : n → A) : IsSelfAdjoint (star x ⬝ᵥ (ofMatrix.symm M *ᵥ x)) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]; exact hM x
  have hP (x y : n → A) :
      star (star x ⬝ᵥ (ofMatrix.symm M *ᵥ y)) = star y ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    have h₁ := (hM (x + y)).star_eq; have h₂ := (hM (x + Complex.I • y)).star_eq
    simp only [star_add, star_smul, star_neg, Complex.star_def, Complex.conj_I, mulVec_add,
      mulVec_smul, add_dotProduct, dotProduct_add, neg_dotProduct, smul_dotProduct,
      dotProduct_smul, neg_smul, (hM x).star_eq, (hM y).star_eq] at h₁ h₂
    linear_combination (norm := match_scalars) (1 / 2 : ℂ) • h₁ + (Complex.I / 2) • h₂ <;>
      simp [Complex.ext_iff] <;> norm_num
  refine ext fun i j => sub_eq_zero.mp <|
    TauCeti.eq_zero_of_forall_star_mul_mul_eq_zero fun c d => ?_
  have := hP (Pi.single j c) (Pi.single i d)
  simp only [← Pi.single_star, single_dotProduct, mulVec_single, Pi.smul_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, star_mul, star_star,
    ofMatrix_symm_apply] at this
  rw [star_apply, mul_sub, sub_mul, this, mul_assoc, sub_self]
end Algebraic

section MapAndReindex
variable {k l m n o p R A B C F : Type*}
@[simp] theorem map_zero [Zero A] [Zero B] {f : A → B} (hf : f 0 = 0) :
    (0 : CStarMatrix m n A).map f = 0 := by ext; simp [hf]
@[simp] protected theorem map_one [DecidableEq n] [Zero A] [One A] [Zero B] [One B]
    {f : A → B} (h₀ : f 0 = 0) (h₁ : f 1 = 1) : (1 : CStarMatrix n n A).map f = 1 :=
  ofMatrix.symm.injective (Matrix.map_one f h₀ h₁)
@[simp] theorem map_algebraMap [Fintype n] [DecidableEq n] [CommSemiring R] [Semiring A]
    [Semiring B] [Algebra R A] [Algebra R B] (r : R) {f : A → B} (hf : f 0 = 0)
    (hf₂ : f (algebraMap R A r) = algebraMap R B r) :
    (algebraMap R (CStarMatrix n n A) r).map f = algebraMap R (CStarMatrix n n B) r :=
  ofMatrix.symm.injective (Matrix.map_algebraMap r f hf hf₂)
theorem map_add [AddZeroClass A] [AddZeroClass B] [FunLike F A B] [AddMonoidHomClass F A B]
    (φ : F) (M N : CStarMatrix m n A) : (M + N).map φ = M.map φ + N.map φ := by ext; simp
section
variable [AddGroup A] [SubtractionMonoid B] [FunLike F A B] [AddMonoidHomClass F A B] (φ : F)
  (M N : CStarMatrix m n A)
protected theorem map_neg : (-M).map φ = -(M.map φ) := by ext; simp
protected theorem map_sub : (M - N).map φ = M.map φ - N.map φ := by ext; simp
end
protected theorem map_smul [SMul R A] [SMul R B] [FunLike F A B] [MulActionHomClass F R A B]
    (φ : F) (r : R) (M : CStarMatrix m n A) : (r • M).map φ = r • M.map φ := by ext; simp
/-- Entrywise mapping of a composition factors into successive `CStarMatrix.map` calls. -/
theorem map_comp (M : CStarMatrix m n A) (f : A → B) (g : B → C) :
    M.map (g ∘ f) = (M.map f).map g := by ext; rfl
/-- Mapping entries by a non-unital ring homomorphism commutes with rectangular multiplication. -/
theorem map_mul [Fintype m] [NonUnitalNonAssocSemiring A] [NonUnitalNonAssocSemiring B]
    [FunLike F A B] [NonUnitalRingHomClass F A B] (φ : F) (M : CStarMatrix l m A)
    (N : CStarMatrix m n A) : (M * N).map φ = M.map φ * N.map φ := by ext; simp [mul_apply, map_sum]
section
variable [Star A] [Star B] [FunLike F A B] [StarHomClass F A B] (φ : F)
/-- Mapping entries by a `⋆`-homomorphism commutes with `conjTranspose`. -/
theorem map_conjTranspose (M : CStarMatrix m n A) :
    M.conjTranspose.map φ = (M.map φ).conjTranspose := by ext; simp [map_star]
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
@[simp] theorem conjTranspose_reindexₗ [Star A] (eₘ : m ≃ l) (eₙ : n ≃ o) (M : CStarMatrix m n A) :
    (reindexₗ R A eₘ eₙ M).conjTranspose = reindexₗ R A eₙ eₘ M.conjTranspose := by ext; rfl
/-- `reindexₗ` is multiplicative across matching intermediate equivalences. -/
@[simp] theorem reindexₗ_mul [Fintype m] [Fintype o] [Mul A] (eₗ : l ≃ k) (eₘ : m ≃ o) (eₙ : n ≃ p)
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    reindexₗ R A eₗ eₘ M * reindexₗ R A eₘ eₙ N = reindexₗ R A eₗ eₙ (M * N) := by
  ext i j; simp only [mul_apply, reindexₗ_apply]; exact Fintype.sum_equiv eₘ.symm _ _ fun _ => rfl
@[simp] theorem reindexₗ_refl :
    reindexₗ R A (.refl m) (.refl n) = LinearEquiv.refl R (CStarMatrix m n A) := by ext; rfl
@[simp] theorem reindexₗ_symm (eₘ : m ≃ l) (eₙ : n ≃ o) :
    reindexₗ R A eₘ.symm eₙ.symm = (reindexₗ R A eₘ eₙ).symm := by ext; rfl
theorem reindexₗ_trans (e₁ : m ≃ l) (e₂ : l ≃ k) (f₁ : n ≃ o) (f₂ : o ≃ p) :
    reindexₗ R A (e₁.trans e₂) (f₁.trans f₂) =
      (reindexₗ R A e₁ f₁).trans (reindexₗ R A e₂ f₂) := by ext; rfl
section
variable [Fintype l] [Fintype m] [Fintype n] [Mul A] [Star A]
/-- Reindexing rows and columns of a square `CStarMatrix` by `e` via `reindexₗ` is `reindexₐ`. -/
theorem reindexₗ_self_eq_reindexₐ (e : m ≃ n) (M : CStarMatrix m m A) :
    reindexₗ R A e e M = reindexₐ R A e M := by ext; simp
@[simp] theorem reindexₐ_refl :
    reindexₐ R A (Equiv.refl n) = StarAlgEquiv.refl R (CStarMatrix n n A) := by ext; rfl
theorem reindexₐ_trans (e₁ : l ≃ m) (e₂ : m ≃ n) :
    reindexₐ R A (e₁.trans e₂) = (reindexₐ R A e₁).trans (reindexₐ R A e₂) := by ext; rfl
/-- Reindexing a square `CStarMatrix` along `e : m ≃ n` preserves star projections. -/
@[simp] theorem isStarProjection_reindexₐ_iff (e : m ≃ n) {p : CStarMatrix m m A} :
    IsStarProjection (reindexₐ R A e p) ↔ IsStarProjection p :=
  ⟨fun h => (reindexₐ R A e).symm_apply_apply p ▸ h.map _, fun h => h.map _⟩
end
end
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
  map_mul' _ _ := ofMatrix.symm.injective (by simp)
  map_star' _ := by rw [star_of, Matrix.conjTranspose_single]
@[simp low] theorem singleNonUnitalStarAlgHom_apply (i : n) (a : A) :
    singleNonUnitalStarAlgHom R i a = ofMatrix (Matrix.single i i a) := (rfl)
/-- The diagonal `(i, i)`-corner embedding `singleNonUnitalStarAlgHom` is injective. -/
theorem singleNonUnitalStarAlgHom_injective (i : n) :
    Function.Injective (singleNonUnitalStarAlgHom R i : A → CStarMatrix n n A) := fun _ _ h => by
  simpa using congr_fun (congr_fun (congrArg ofMatrix.symm h) i) i
end
end MapAndReindex

section Order
variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
/-! Register real CFC directly since `CStarMatrix`'s entrywise `ℝ`-action differs syntactically
from `ℂ`-restriction, though both agree definitionally. -/
instance instNonUnitalContinuousFunctionalCalculusReal : NonUnitalContinuousFunctionalCalculus ℝ
    (CStarMatrix n n A) IsSelfAdjoint := IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus
instance instNonnegSpectrumClassReal : NonnegSpectrumClass ℝ (CStarMatrix n n A) :=
  CStarAlgebra.instNonnegSpectrumClass'
/-- A matrix over a C⋆-algebra is positive iff all its finite quadratic forms are positive. -/
theorem nonneg_iff_forall_sum_nonneg {M : CStarMatrix n n A} :
    0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j := by
  have key (R : CStarMatrix n n A) (x : n → A) : star x ⬝ᵥ (ofMatrix.symm (star R * R) *ᵥ x) =
      star (ofMatrix.symm R *ᵥ x) ⬝ᵥ (ofMatrix.symm R *ᵥ x) := by
    rw [ofMatrix_symm_mul, ofMatrix_symm_star, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  have hform (x) : ∑ i, ∑ j, star (x i) * M i j * x j = star x ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]; rfl
  simp_rw [hform]; refine ⟨fun hM x => ?_, fun hQ => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [key]; exact dotProduct_star_self_nonneg _
  have hsa : IsSelfAdjoint M := isSelfAdjoint_of_forall_isSelfAdjoint_sum fun x =>
    (hform x).symm ▸ .of_nonneg (hQ x)
  refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
  set N := M⁻; have hN : 0 ≤ N := CFC.negPart_nonneg M
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
  have hMN : M * N = -(star R * R * N) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart M hsa]
    rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
  have hRN : R * N = 0 := by
    classical
    refine ext fun i j => ?_
    have h := hQ (ofMatrix.symm N *ᵥ Pi.single j (star ((R * N) i j)))
    rw [mulVec_mulVec, ← ofMatrix_symm_mul, hMN, ofMatrix_symm_neg, neg_mulVec, dotProduct_neg,
      ofMatrix_symm_mul, ← mulVec_mulVec, key, Left.nonneg_neg_iff] at h
    have hv := congrFun (dotProduct_star_self_eq_zero.mp
      (le_antisymm h (dotProduct_star_self_nonneg _))) i
    rw [mulVec_mulVec, ← ofMatrix_symm_mul] at hv
    simpa only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ofMatrix_symm_apply, Pi.zero_apply, mul_star_self_eq_zero,
      zero_apply] using hv
  rw [← star_mul_self_eq_zero, hN.star_eq]; nth_rw 1 [hR]; rw [mul_assoc, hRN, mul_zero]
end Order

section Norms
variable {l m n o R A : Type*} [NonUnitalCStarAlgebra A]
/-- `toCLM` reverses rectangular matrix multiplication into operator composition. -/
theorem toCLM_mul [Fintype l] [Fintype m] (M : CStarMatrix l m A) (N : CStarMatrix m n A) :
    toCLM (M * N) = (toCLM N).comp (toCLM M) := by
  ext v j; simp only [ContinuousLinearMap.comp_apply, toCLM_apply_eq_sum,
    WithCStarModule.equiv_symm_pi_apply, mul_apply, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm
variable [PartialOrder A] [StarOrderedRing A]
/-- Rectangular submultiplicativity of the `CStarMatrix` operator norm. -/
theorem norm_mul_le [Fintype l] [Fintype m] [Fintype n]
    (M : CStarMatrix l m A) (N : CStarMatrix m n A) : ‖M * N‖ ≤ ‖M‖ * ‖N‖ := by
  rw [norm_def, norm_def, norm_def, toCLM_mul, mul_comm]; exact (toCLM N).opNorm_comp_le (toCLM M)
section
variable [Fintype m] [Fintype n]
/-- `toCLM M` and `toCLM M.conjTranspose` form a C⋆-module adjoint pair. -/
theorem isAdjointPair_toCLM_conjTranspose (M : CStarMatrix m n A) :
    LinearMap.IsAdjointPair (CStarModule.innerₛₗ (A := A)).flip
      (CStarModule.innerₛₗ (A := A)).flip (toCLM M) (toCLM M.conjTranspose) :=
  CStarModule.isAdjointPair_inner_iff.mpr fun _ _ => by
    simp only [toCLM_apply_eq_sum, WithCStarModule.pi_inner, WithCStarModule.equiv_symm_pi_apply,
      WithCStarModule.inner_def, conjTranspose_apply, Finset.mul_sum, Finset.sum_mul, star_sum,
      star_mul, mul_assoc]; exact Finset.sum_comm
/-- Conjugate transposition on rectangular `CStarMatrix` is isometric. -/
@[simp] theorem norm_conjTranspose (M : CStarMatrix m n A) : ‖M.conjTranspose‖ = ‖M‖ := by
  rw [norm_def, norm_def]; exact (isAdjointPair_toCLM_conjTranspose M).norm_eq_cstarModule
/-- Rectangular C⋆-identity `‖M * M.conjTranspose‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_self_mul_conjTranspose (M : CStarMatrix m n A) :
    ‖M * M.conjTranspose‖ = ‖M‖ ^ 2 := by
  rw [norm_def, norm_def, toCLM_mul]
  exact (isAdjointPair_toCLM_conjTranspose M).norm_adjoint_comp_self_cstarModule
/-- Rectangular C⋆-identity `‖M.conjTranspose * M‖ = ‖M‖ ^ 2`. -/
@[simp] theorem norm_conjTranspose_mul_self (M : CStarMatrix m n A) :
    ‖M.conjTranspose * M‖ = ‖M‖ ^ 2 := by simpa using norm_self_mul_conjTranspose M.conjTranspose
@[simp] theorem norm_reindexₐ [Semiring R] [Module R A] (e : m ≃ n) (M : CStarMatrix m m A) :
    ‖reindexₐ R A e M‖ = ‖M‖ :=
  (by ext; simp : reindexₐ R A e M = reindexₐ ℂ A e M) ▸ StarAlgEquiv.norm_map (reindexₐ ℂ A e) M
/-- `reindexₗ` along arbitrary row and column equivalences is isometric. -/
@[simp] theorem norm_reindexₗ [Fintype l] [Fintype o] [Semiring R] [Module R A] (eₘ : m ≃ l)
    (eₙ : n ≃ o) (M : CStarMatrix m n A) : ‖reindexₗ R A eₘ eₙ M‖ = ‖M‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    rw [← norm_conjTranspose_mul_self, conjTranspose_reindexₗ, reindexₗ_mul,
      reindexₗ_self_eq_reindexₐ, norm_reindexₐ, norm_conjTranspose_mul_self]
/-- A matrix with a single entry `a` at `(i, j)` has operator norm `‖a‖`. -/
@[simp] theorem norm_single [DecidableEq m] [DecidableEq n] (i : m) (j : n) (a : A) :
    ‖ofMatrix (Matrix.single i j a)‖ = ‖a‖ :=
  (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp <| by
    have hmul : (ofMatrix (Matrix.single i j a)).conjTranspose * ofMatrix (Matrix.single i j a) =
        singleNonUnitalStarAlgHom ℂ j (star a * a) :=
      ofMatrix.symm.injective (by simp [Matrix.conjTranspose_single])
    rw [← norm_conjTranspose_mul_self, hmul, NonUnitalStarAlgHom.norm_map
      (singleNonUnitalStarAlgHom ℂ (A := A) j) (singleNonUnitalStarAlgHom_injective j) _,
      CStarRing.norm_star_mul_self, sq]
end
end Norms

section Continuity
variable {m n X A : Type*} [TopologicalSpace X] [NonUnitalCStarAlgebra A]
/-- `CStarMatrix.ofMatrix` is continuous. -/
@[fun_prop] theorem continuous_ofMatrix :
    Continuous (ofMatrix : Matrix m n A → CStarMatrix m n A) := by
  rw [ofMatrix_eq_ofMatrixL]; exact ofMatrixL.continuous
/-- `CStarMatrix.ofMatrix.symm` is continuous. -/
@[fun_prop] theorem continuous_ofMatrix_symm :
    Continuous (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) :=
  (show (ofMatrix.symm : CStarMatrix m n A → Matrix m n A) = ofMatrixL.symm from funext fun _ =>
    ofMatrix.injective (by simp [ofMatrix_eq_ofMatrixL])) ▸ ofMatrixL.symm.continuous
/-- A map into `CStarMatrix m n A` is continuous iff every entry function is continuous. -/
theorem continuous_iff {f : X → CStarMatrix m n A} :
    Continuous f ↔ ∀ i j, Continuous fun x => f x i j :=
  ⟨fun hf i j => by
     simpa [ofMatrix_symm_apply] using (continuous_ofMatrix_symm.comp hf).matrix_elem i j,
   fun hf => (funext fun x => (ofMatrix.apply_symm_apply (f x)).symm) ▸ continuous_ofMatrix.comp
     (continuous_matrix fun i j => by simpa [ofMatrix_symm_apply] using hf i j)⟩
end Continuity
end CStarMatrix
