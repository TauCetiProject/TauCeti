/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.Tactic.Ring

/-!
# The bilinear form of a matrix on finitely supported vectors

Mathlib's `Matrix.toBilin'` reads a square matrix over a finite index type as a bilinear form on
`n → R`. For an arbitrary index set `I`, a matrix `A : Matrix I I R` over a commutative semiring
still defines the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on the free module `I →₀ R`, whose Gram matrix in
the standard basis is `A`. This is the form used, for example, to pair the simple roots of a
Coxeter system with infinite rank, and to twist the exponent lattice of a based quantum torus.

## Main definitions

* `Matrix.finsuppBilinForm`: the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on `I →₀ R`.

## Main results

* `Matrix.finsuppBilinForm_apply`: the form is `∑ᵢⱼ xᵢ A i j yⱼ`, as a double `Finsupp.sum`.
* `Matrix.finsuppBilinForm_single_single`: the Gram matrix of `Matrix.finsuppBilinForm A` is `A`.
* `Matrix.finsuppBilinForm_submatrix` and `Matrix.finsuppBilinForm_reindex`: compatibility with
  pullback and reindexing of indices.
* `Matrix.finsuppBilinForm_apply_eq_dotProduct` and `Matrix.finsuppBilinForm_apply_eq_toBilin'`:
  for finite `I` the form agrees with `x ⬝ᵥ (A *ᵥ y)` and `Matrix.toBilin' A`.
* `Matrix.isAlt_finsuppBilinForm_iff`: over a commutative ring, alternation is skew-symmetry
  together with a zero diagonal, for an arbitrary index set.
* `Matrix.strictUpper`: the strictly upper-triangular part of a matrix over a linearly ordered
  index set, splitting an alternating `finsuppBilinForm` as `strictUpper - flip strictUpper`.
* `Matrix.updateSkew`: skew-symmetric replacement of row and column `k`, producing the unique
  alternating form agreeing with `A` off `k` with prescribed pairing at `eₖ`.
-/

public section

namespace Matrix

variable {I J R : Type*} [CommSemiring R] (A : Matrix I I R)

/-- **The bilinear form of a matrix** on the free module `I →₀ R`, the form `∑ᵢⱼ xᵢ A i j yⱼ`
whose Gram matrix in the standard basis is `A`. -/
noncomputable def finsuppBilinForm : LinearMap.BilinForm R (I →₀ R) :=
  Finsupp.linearCombination R fun i ↦ Finsupp.linearCombination R (A i)

/-- `Matrix.finsuppBilinForm A` pairs `eᵢ` with `y` by the functional `y ↦ ∑ⱼ A i j yⱼ`. -/
theorem finsuppBilinForm_def :
    A.finsuppBilinForm = Finsupp.linearCombination R fun i ↦ Finsupp.linearCombination R (A i) :=
  (rfl)

/-- The zero matrix induces the zero bilinear form on finitely supported vectors. -/
@[simp]
theorem finsuppBilinForm_zero : (0 : Matrix I I R).finsuppBilinForm = 0 := by
  ext i j
  simp [finsuppBilinForm]

/-- **Evaluation of the bilinear form of a matrix**: `A.finsuppBilinForm x y = ∑ᵢⱼ xᵢ A i j yⱼ`,
for an arbitrary index set. -/
theorem finsuppBilinForm_apply (x y : I →₀ R) :
    A.finsuppBilinForm x y = x.sum fun i a ↦ y.sum fun j b ↦ a * A i j * b := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply,
    Finsupp.mul_sum, mul_comm, mul_left_comm]

/-- `Matrix.finsuppBilinForm` is additive in the matrix. -/
@[simp]
theorem finsuppBilinForm_add (A B : Matrix I I R) :
    (A + B).finsuppBilinForm = A.finsuppBilinForm + B.finsuppBilinForm := by
  ext i j
  simp [finsuppBilinForm]

/-- Transposing the matrix flips the arguments of `Matrix.finsuppBilinForm`. -/
@[simp]
theorem finsuppBilinForm_transpose_apply (x y : I →₀ R) :
    Aᵀ.finsuppBilinForm x y = A.finsuppBilinForm y x := by
  rw [finsuppBilinForm_apply, finsuppBilinForm_apply, Finsupp.sum_comm]
  refine Finsupp.sum_congr fun j _ ↦ Finsupp.sum_congr fun i _ ↦ ?_
  simp only [transpose_apply]
  ring

/-- Pairing with a basis vector `a • eᵢ` on the left is the functional `y ↦ a * ∑ⱼ A i j yⱼ`. -/
@[simp]
theorem finsuppBilinForm_single_left (i : I) (a : R) :
    A.finsuppBilinForm (Finsupp.single i a) = a • Finsupp.linearCombination R (A i) :=
  Finsupp.linearCombination_single R a i

/-- Pairing with a basis vector `b • eⱼ` on the right evaluates `(∑ᵢ xᵢ A i j) * b`. -/
theorem finsuppBilinForm_single_right (x : I →₀ R) (j : I) (b : R) :
    A.finsuppBilinForm x (Finsupp.single j b) =
      Finsupp.linearCombination R (fun i ↦ A i j) x * b := by
  rw [finsuppBilinForm_apply, Finsupp.linearCombination_apply, Finsupp.sum_mul]
  refine Finsupp.sum_congr fun i _ ↦ ?_
  rw [Finsupp.sum_single_index (by ring)]
  ring

/-- The Gram matrix of `Matrix.finsuppBilinForm` is the matrix itself. -/
theorem finsuppBilinForm_single_single (i j : I) (a b : R) :
    A.finsuppBilinForm (Finsupp.single i a) (Finsupp.single j b) = a * b * A i j := by
  simp only [finsuppBilinForm_single_left, LinearMap.smul_apply, Finsupp.linearCombination_single,
    smul_eq_mul]
  ring

/-- Pulling back a matrix along `f : J → I` pulls back `finsuppBilinForm` along `mapDomain f`. -/
@[simp]
theorem finsuppBilinForm_submatrix (f : J → I) (x y : J →₀ R) :
    (A.submatrix f f).finsuppBilinForm x y =
      A.finsuppBilinForm (x.mapDomain f) (y.mapDomain f) := by
  rw [finsuppBilinForm, finsuppBilinForm, Finsupp.linearCombination_mapDomain]
  have h : (fun i ↦ Finsupp.linearCombination R (A.submatrix f f i)) =
      fun i ↦ (Finsupp.linearCombination R (A (f i))).comp (Finsupp.lmapDomain R R f) := by
    ext i j
    simp
  simp [Function.comp_def, h, Finsupp.linearCombination_apply]

/-- Reindexing a matrix along `e : I ≃ J` pulls back `finsuppBilinForm` along `e.symm`. -/
theorem finsuppBilinForm_reindex (e : I ≃ J) (x y : J →₀ R) :
    (A.reindex e e).finsuppBilinForm x y =
      A.finsuppBilinForm (x.mapDomain e.symm) (y.mapDomain e.symm) :=
  A.finsuppBilinForm_submatrix e.symm x y

/-- For a finite index set, `Matrix.finsuppBilinForm` is the usual form `x ⬝ᵥ (A *ᵥ y)` of the
matrix `A`. -/
theorem finsuppBilinForm_apply_eq_dotProduct [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = ⇑x ⬝ᵥ (A *ᵥ ⇑y) := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, Finsupp.sum_fintype, dotProduct,
    mulVec, Finset.mul_sum, mul_comm]

/-- For a finite index set, `Matrix.finsuppBilinForm` agrees with `Matrix.toBilin'`. -/
theorem finsuppBilinForm_apply_eq_toBilin' [Fintype I] [DecidableEq I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = A.toBilin' x y := by
  rw [finsuppBilinForm_apply_eq_dotProduct, toBilin'_apply']

/-- Every diagonal entry of an alternating `finsuppBilinForm` vanishes. -/
theorem apply_self_eq_zero_of_isAlt_finsuppBilinForm {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (i : I) : A i i = 0 := by
  simpa [finsuppBilinForm_single_single] using hA.self_eq_zero (Finsupp.single i 1)

/-- For a finite index set, `finsuppBilinForm` is alternating if and only if `toBilin'` is. -/
@[simp]
theorem isAlt_finsuppBilinForm_iff_isAlt_toBilin' [Fintype I] [DecidableEq I] :
    A.finsuppBilinForm.IsAlt ↔ A.toBilin'.IsAlt := by
  refine ⟨fun h x ↦ ?_, fun h x ↦ ?_⟩
  · simpa [finsuppBilinForm_apply_eq_toBilin'] using h (Finsupp.equivFunOnFinite.symm x)
  · rw [finsuppBilinForm_apply_eq_toBilin']
    exact h x

/-- The strictly upper-triangular part of a square matrix with respect to `<` on `I`. -/
def strictUpper [LT I] [DecidableLT I] {α : Type*} [Zero α] (A : Matrix I I α) : Matrix I I α :=
  of fun i j ↦ if i < j then A i j else 0

@[simp]
theorem strictUpper_apply [LT I] [DecidableLT I] {α : Type*} [Zero α] (A : Matrix I I α)
    (i j : I) : A.strictUpper i j = if i < j then A i j else 0 := by
  simp [strictUpper]

/-- Replace row and column `k` skew-symmetrically with `(k, k)`-entry `0`, off-diagonal row
entries `ℓ j`, and off-diagonal column entries `-ℓ i`. -/
def updateSkew [DecidableEq I] {α : Type*} [Zero α] [Neg α] (A : Matrix I I α) (k : I)
    (ℓ : I → α) : Matrix I I α :=
  of fun i j ↦ if i = k then (if j = k then 0 else ℓ j) else if j = k then -ℓ i else A i j

@[simp]
theorem updateSkew_apply_same [DecidableEq I] {α : Type*} [Zero α] [Neg α] (A : Matrix I I α)
    (k : I) (ℓ : I → α) : A.updateSkew k ℓ k k = 0 := by
  simp [updateSkew]

theorem updateSkew_apply_left_of_ne [DecidableEq I] {α : Type*} [Zero α] [Neg α]
    (A : Matrix I I α) (k : I) (ℓ : I → α) {j : I} (hj : j ≠ k) :
    A.updateSkew k ℓ k j = ℓ j := by
  simp [updateSkew, hj]

theorem updateSkew_apply_right_of_ne [DecidableEq I] {α : Type*} [Zero α] [Neg α]
    (A : Matrix I I α) (k : I) (ℓ : I → α) {i : I} (hi : i ≠ k) :
    A.updateSkew k ℓ i k = -ℓ i := by
  simp [updateSkew, hi]

theorem updateSkew_apply_of_ne [DecidableEq I] {α : Type*} [Zero α] [Neg α]
    (A : Matrix I I α) (k : I) (ℓ : I → α) {i j : I} (hi : i ≠ k) (hj : j ≠ k) :
    A.updateSkew k ℓ i j = A i j := by
  simp [updateSkew, hi, hj]

section CommRing

variable {S : Type*} [CommRing S]

/-- Over a commutative ring, `Matrix.finsuppBilinForm` respects negation. -/
@[simp]
theorem finsuppBilinForm_neg (A : Matrix I I S) :
    (-A).finsuppBilinForm = -A.finsuppBilinForm := by
  ext i j
  simp [finsuppBilinForm]

/-- Over a commutative ring, `Matrix.finsuppBilinForm` respects subtraction. -/
@[simp]
theorem finsuppBilinForm_sub (A B : Matrix I I S) :
    (A - B).finsuppBilinForm = A.finsuppBilinForm - B.finsuppBilinForm := by
  ext i j
  simp [finsuppBilinForm]

/-- Over a commutative ring, an alternating `finsuppBilinForm` has skew-symmetric matrix. -/
theorem neg_apply_eq_of_isAlt_finsuppBilinForm {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (i j : I) : -A i j = A j i := by
  simpa [finsuppBilinForm_single_single] using
    hA.neg_eq (Finsupp.single i 1) (Finsupp.single j 1)

/-- Over a commutative ring, `A.finsuppBilinForm` is alternating if and only if `A` is
skew-symmetric with zero diagonal, for any index type `I`. -/
theorem isAlt_finsuppBilinForm_iff (A : Matrix I I S) :
    A.finsuppBilinForm.IsAlt ↔ Aᵀ = -A ∧ ∀ i, A i i = 0 := by
  refine ⟨fun h ↦ ⟨Matrix.ext fun i j ↦ (neg_apply_eq_of_isAlt_finsuppBilinForm h i j).symm,
    apply_self_eq_zero_of_isAlt_finsuppBilinForm h⟩, ?_⟩
  rintro ⟨ht, hd⟩ x
  classical
  rw [finsuppBilinForm_apply, Finsupp.sum]
  simp only [Finsupp.sum]
  rw [← Finset.sum_coe_sort x.support]
  simp_rw [← Finset.sum_coe_sort x.support, ← Fintype.sum_prod_type']
  refine Finset.sum_ninvolution Prod.swap (fun p ↦ ?_) (fun p hf he ↦ ?_)
    (fun _ ↦ Finset.mem_univ _) (fun _ ↦ Prod.swap_swap _)
  · have hij : A p.2 p.1 = -A p.1 p.2 := congr_fun (congr_fun ht p.1) p.2
    simp only [Prod.fst_swap, Prod.snd_swap, hij]
    ring
  · rcases p with ⟨i, j⟩
    have hij : j = i := congrArg Prod.fst he
    subst hij
    exact hf (by simp [hd])

/-- An alternating matrix over a linearly ordered index type is `strictUpper - strictUpperᵀ`. -/
theorem strictUpper_sub_transpose_of_isAlt [LinearOrder I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) :
    A.strictUpper - A.strictUpperᵀ = A := by
  refine Matrix.ext fun i j ↦ ?_
  rw [Matrix.sub_apply, Matrix.transpose_apply, strictUpper_apply, strictUpper_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, asymm hij]
  · simp [apply_self_eq_zero_of_isAlt_finsuppBilinForm hA]
  · simp [hji, asymm hji, neg_apply_eq_of_isAlt_finsuppBilinForm hA]

/-- Over a linearly ordered index type, an alternating `finsuppBilinForm` splits as
`strictUpper.finsuppBilinForm x y - strictUpper.finsuppBilinForm y x`. -/
theorem finsuppBilinForm_eq_strictUpper_sub_flip [LinearOrder I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (x y : I →₀ S) :
    A.finsuppBilinForm x y =
      A.strictUpper.finsuppBilinForm x y - A.strictUpper.finsuppBilinForm y x := by
  conv_lhs => rw [← strictUpper_sub_transpose_of_isAlt hA]
  simp

/-- Updating row and column `k` skew-symmetrically preserves alternation of `finsuppBilinForm`. -/
theorem isAlt_finsuppBilinForm_updateSkew [DecidableEq I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (k : I) (ℓ : I → S) :
    (A.updateSkew k ℓ).finsuppBilinForm.IsAlt := by
  rw [isAlt_finsuppBilinForm_iff] at hA ⊢
  refine ⟨Matrix.ext fun i j ↦ ?_, fun i ↦ ?_⟩
  · rw [Matrix.transpose_apply, Matrix.neg_apply]
    rcases eq_or_ne k i with rfl | hi
    · rcases eq_or_ne k j with rfl | hj
      · simp
      · rw [updateSkew_apply_right_of_ne A k ℓ hj.symm, updateSkew_apply_left_of_ne A k ℓ hj.symm]
    · rcases eq_or_ne k j with rfl | hj
      · rw [updateSkew_apply_left_of_ne A k ℓ hi.symm, updateSkew_apply_right_of_ne A k ℓ hi.symm,
          neg_neg]
      · rw [updateSkew_apply_of_ne A k ℓ hj.symm hi.symm,
          updateSkew_apply_of_ne A k ℓ hi.symm hj.symm]
        exact congr_fun (congr_fun hA.1 i) j
  · rcases eq_or_ne k i with rfl | hi
    · simp
    · rw [updateSkew_apply_of_ne A k ℓ hi.symm hi.symm, hA.2 i]

/-- On vectors vanishing at `k`, `updateSkew k ℓ` agrees with the original bilinear form. -/
theorem finsuppBilinForm_updateSkew_of_apply_eq_zero [DecidableEq I] (A : Matrix I I S) (k : I)
    (ℓ : I → S) {x y : I →₀ S} (hx : x k = 0) (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm x y = A.finsuppBilinForm x y := by
  rw [finsuppBilinForm_apply, finsuppBilinForm_apply]
  refine Finsupp.sum_congr fun i hi ↦ Finsupp.sum_congr fun j hj ↦ ?_
  have hik : i ≠ k := by rintro rfl; exact Finsupp.mem_support_iff.mp hi hx
  have hjk : j ≠ k := by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy
  rw [updateSkew_apply_of_ne A k ℓ hik hjk]

/-- Pairing `single k r` with a vector vanishing at `k` under `updateSkew k ℓ` evaluates `ℓ`. -/
theorem finsuppBilinForm_updateSkew_single_left [DecidableEq I] (A : Matrix I I S) (k : I)
    (ℓ : I → S) (r : S) {y : I →₀ S} (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm (Finsupp.single k r) y =
      r * Finsupp.linearCombination S ℓ y := by
  rw [finsuppBilinForm_single_left, LinearMap.smul_apply, smul_eq_mul]
  congr 1
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  refine Finsupp.sum_congr fun j hj ↦ ?_
  have hjk : j ≠ k := by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy
  rw [updateSkew_apply_left_of_ne A k ℓ hjk]

/-- Two alternating matrices whose forms agree on vectors vanishing at `k` and at `single k 1`
against vectors vanishing at `k` are equal. -/
theorem eq_of_isAlt_finsuppBilinForm_of_eq_off {A₁ A₂ : Matrix I I S} {k : I}
    (h₁ : A₁.finsuppBilinForm.IsAlt) (h₂ : A₂.finsuppBilinForm.IsAlt)
    (h_off : ∀ x y : I →₀ S, x k = 0 → y k = 0 →
      A₁.finsuppBilinForm x y = A₂.finsuppBilinForm x y)
    (h_row : ∀ y : I →₀ S, y k = 0 →
      A₁.finsuppBilinForm (Finsupp.single k 1) y = A₂.finsuppBilinForm (Finsupp.single k 1) y) :
    A₁ = A₂ := by
  classical
  refine Matrix.ext fun i j ↦ ?_
  rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj
  · rw [apply_self_eq_zero_of_isAlt_finsuppBilinForm h₁,
      apply_self_eq_zero_of_isAlt_finsuppBilinForm h₂]
  · simpa [finsuppBilinForm_single_single] using
      h_row (Finsupp.single j 1) (Finsupp.single_eq_of_ne hj)
  · have hji : A₁ k i = A₂ k i := by
      simpa [finsuppBilinForm_single_single] using
        h_row (Finsupp.single i 1) (Finsupp.single_eq_of_ne hi)
    rw [← neg_apply_eq_of_isAlt_finsuppBilinForm h₁ k i,
      ← neg_apply_eq_of_isAlt_finsuppBilinForm h₂ k i, hji]
  · simpa [finsuppBilinForm_single_single] using
      h_off (Finsupp.single i 1) (Finsupp.single j 1)
        (Finsupp.single_eq_of_ne hi) (Finsupp.single_eq_of_ne hj)

end CommRing

end Matrix
