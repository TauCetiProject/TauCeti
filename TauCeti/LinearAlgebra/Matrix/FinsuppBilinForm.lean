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
public import TauCeti.LinearAlgebra.Matrix.Alternating
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
* `Matrix.finsuppBilinForm_apply_eq_dotProduct`: for finite `I` the form is `x ⬝ᵥ (A *ᵥ y)`.
* `Matrix.isAlt_finsuppBilinForm_iff`: over a commutative ring, alternation is skew-symmetry
  together with a zero diagonal, for an arbitrary index set.
* `Matrix.finsuppBilinForm_eq_strictUpper_sub_flip`: an alternating form decomposes into its
  strictly upper-triangular part minus its flip.
* `Matrix.isAlt_finsuppBilinForm_updateSkew` and `Matrix.eq_of_isAlt_finsuppBilinForm_of_eq_off`:
  skew-symmetric row/column replacement preserves alternation, and an alternating matrix is
  determined by its restriction off `k` together with its `k`-th row off `k`.
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

/-- **Evaluation of the bilinear form of a matrix**: `A.finsuppBilinForm x y = ∑ᵢⱼ xᵢ A i j yⱼ`,
for an arbitrary index set. -/
theorem finsuppBilinForm_apply (x y : I →₀ R) :
    A.finsuppBilinForm x y = x.sum fun i a ↦ y.sum fun j b ↦ a * A i j * b := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, LinearMap.finsupp_sum_apply,
    Finsupp.mul_sum, mul_comm, mul_left_comm]

/-- Pairing with a basis vector `a • eᵢ` on the left is the functional `y ↦ a * ∑ⱼ A i j yⱼ`. -/
@[simp]
theorem finsuppBilinForm_single_left (i : I) (a : R) :
    A.finsuppBilinForm (Finsupp.single i a) = a • Finsupp.linearCombination R (A i) :=
  Finsupp.linearCombination_single R a i

/-- The Gram matrix of `Matrix.finsuppBilinForm` is the matrix itself. -/
theorem finsuppBilinForm_single_single (i j : I) (a b : R) :
    A.finsuppBilinForm (Finsupp.single i a) (Finsupp.single j b) = a * b * A i j := by
  simp only [finsuppBilinForm_single_left, LinearMap.smul_apply, Finsupp.linearCombination_single,
    smul_eq_mul]
  ring

/-- For a finite index set, `Matrix.finsuppBilinForm` is the usual form `x ⬝ᵥ (A *ᵥ y)` of the
matrix `A`. -/
theorem finsuppBilinForm_apply_eq_dotProduct [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = ⇑x ⬝ᵥ (A *ᵥ ⇑y) := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, Finsupp.sum_fintype, dotProduct,
    mulVec, Finset.mul_sum, mul_comm]

/-- The zero matrix induces the zero bilinear form on `I →₀ R`. -/
@[simp] theorem finsuppBilinForm_zero : (0 : Matrix I I R).finsuppBilinForm = 0 := by
  ext; simp [finsuppBilinForm]
/-- `Matrix.finsuppBilinForm` preserves matrix addition. -/
@[simp] theorem finsuppBilinForm_add (A B : Matrix I I R) :
    (A + B).finsuppBilinForm = A.finsuppBilinForm + B.finsuppBilinForm := by
  ext; simp [finsuppBilinForm]
/-- Transposing the matrix swaps the two arguments of `Matrix.finsuppBilinForm`. -/
@[simp] theorem finsuppBilinForm_transpose_apply (x y : I →₀ R) :
    Aᵀ.finsuppBilinForm x y = A.finsuppBilinForm y x := by
  rw [finsuppBilinForm_apply, finsuppBilinForm_apply, Finsupp.sum_comm]
  exact Finsupp.sum_congr fun _ _ ↦ Finsupp.sum_congr fun _ _ ↦ by simp; ring
/-- Pairing on the right with `b • eⱼ` evaluates the `j`-th column functional scaled by `b`. -/
theorem finsuppBilinForm_single_right (x : I →₀ R) (j : I) (b : R) :
    A.finsuppBilinForm x (Finsupp.single j b) =
      Finsupp.linearCombination R (fun i ↦ A i j) x * b := by
  rw [← finsuppBilinForm_transpose_apply, finsuppBilinForm_single_left, LinearMap.smul_apply,
    smul_eq_mul, mul_comm]; rfl
/-- Pulling back a matrix along `f : J → I` pulls back `Matrix.finsuppBilinForm` along
`Finsupp.mapDomain f`. -/
@[simp] theorem finsuppBilinForm_submatrix (f : J → I) (x y : J →₀ R) :
    (A.submatrix f f).finsuppBilinForm x y =
      A.finsuppBilinForm (x.mapDomain f) (y.mapDomain f) := by
  rw [finsuppBilinForm, finsuppBilinForm, Finsupp.linearCombination_mapDomain]
  have h : (fun i ↦ Finsupp.linearCombination R (A.submatrix f f i)) =
      fun i ↦ (Finsupp.linearCombination R (A (f i))).comp (Finsupp.lmapDomain R R f) := by
    ext; simp
  simp [Function.comp_def, h, Finsupp.linearCombination_apply]
/-- Reindexing a matrix along `e : I ≃ J` pulls back `Matrix.finsuppBilinForm` along `e.symm`. -/
theorem finsuppBilinForm_reindex (e : I ≃ J) (x y : J →₀ R) :
    (A.reindex e e).finsuppBilinForm x y =
      A.finsuppBilinForm (x.mapDomain e.symm) (y.mapDomain e.symm) :=
  A.finsuppBilinForm_submatrix e.symm x y
/-- For finite `I`, `Matrix.finsuppBilinForm` agrees with `Matrix.toBilin'`. -/
theorem finsuppBilinForm_apply_eq_toBilin' [Fintype I] [DecidableEq I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = A.toBilin' x y := by
  rw [finsuppBilinForm_apply_eq_dotProduct, toBilin'_apply']
/-- Every diagonal entry of a matrix whose `finsuppBilinForm` is alternating vanishes. -/
theorem apply_self_eq_zero_of_isAlt_finsuppBilinForm {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (i : I) : A i i = 0 := by
  simpa [finsuppBilinForm_single_single] using hA.self_eq_zero (Finsupp.single i 1)
/-- For finite `I`, `A.finsuppBilinForm` is alternating if and only if `A.toBilin'` is. -/
@[simp] theorem isAlt_finsuppBilinForm_iff_isAlt_toBilin' [Fintype I] [DecidableEq I] :
    A.finsuppBilinForm.IsAlt ↔ A.toBilin'.IsAlt :=
  ⟨fun h x ↦ by
      simpa [finsuppBilinForm_apply_eq_toBilin'] using h (Finsupp.equivFunOnFinite.symm x),
    fun h x ↦ (A.finsuppBilinForm_apply_eq_toBilin' x x).trans (h x)⟩
section CommRing
variable {S : Type*} [CommRing S]
/-- `Matrix.finsuppBilinForm` commutes with matrix negation. -/
@[simp] theorem finsuppBilinForm_neg (A : Matrix I I S) :
    (-A).finsuppBilinForm = -A.finsuppBilinForm := by ext; simp [finsuppBilinForm]
/-- `Matrix.finsuppBilinForm` commutes with matrix subtraction. -/
@[simp] theorem finsuppBilinForm_sub (A B : Matrix I I S) :
    (A - B).finsuppBilinForm = A.finsuppBilinForm - B.finsuppBilinForm := by
  ext; simp [finsuppBilinForm]
/-- If `A.finsuppBilinForm` is alternating, `A` is skew-symmetric entrywise (`-A i j = A j i`). -/
theorem neg_apply_eq_of_isAlt_finsuppBilinForm {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (i j : I) : -A i j = A j i := by
  simpa [finsuppBilinForm_single_single] using hA.neg_eq (Finsupp.single i 1) (Finsupp.single j 1)
/-- Over a commutative ring and an arbitrary index type, `A.finsuppBilinForm` is alternating if and
only if `A` is skew-symmetric (`Aᵀ = -A`) and has zero diagonal. -/
theorem isAlt_finsuppBilinForm_iff (A : Matrix I I S) :
    A.finsuppBilinForm.IsAlt ↔ Aᵀ = -A ∧ ∀ i, A i i = 0 := by
  refine ⟨fun h ↦ ⟨Matrix.ext fun i j ↦ (neg_apply_eq_of_isAlt_finsuppBilinForm h i j).symm,
    apply_self_eq_zero_of_isAlt_finsuppBilinForm h⟩, fun ⟨ht, hd⟩ x ↦ ?_⟩
  classical
  rw [finsuppBilinForm_apply, Finsupp.sum]; simp only [Finsupp.sum]
  rw [← Finset.sum_coe_sort x.support]
  simp_rw [← Finset.sum_coe_sort x.support, ← Fintype.sum_prod_type']
  refine Finset.sum_ninvolution Prod.swap
    (fun p ↦ by
      have hp : A p.2 p.1 = -A p.1 p.2 := by simpa using congr_fun (congr_fun ht p.1) p.2
      simp only [Prod.fst_swap, Prod.snd_swap, hp]; ring)
    (fun ⟨_, _⟩ hf he ↦ by cases congrArg Prod.fst he; exact hf (by simp [hd]))
    (fun _ ↦ Finset.mem_univ _) (fun _ ↦ Prod.swap_swap _)
/-- A matrix whose `finsuppBilinForm` is alternating equals `A.strictUpper - A.strictUpperᵀ`. -/
theorem strictUpper_sub_transpose_of_isAlt [LinearOrder I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) : A.strictUpper - A.strictUpperᵀ = A := Matrix.ext fun i j ↦ by
  rw [Matrix.sub_apply, Matrix.transpose_apply, strictUpper_apply, strictUpper_apply]
  rcases lt_trichotomy i j with hij | rfl | hji
  · simp [hij, asymm hij]
  · simp [apply_self_eq_zero_of_isAlt_finsuppBilinForm hA]
  · simp [hji, asymm hji, neg_apply_eq_of_isAlt_finsuppBilinForm hA]
/-- Over a linearly ordered index type, an alternating `finsuppBilinForm` decomposes as the form of
`A.strictUpper` minus its argument-swapped flip, used to normalize ordered coordinate products. -/
theorem finsuppBilinForm_eq_strictUpper_sub_flip [LinearOrder I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (x y : I →₀ S) :
    A.finsuppBilinForm x y =
      A.strictUpper.finsuppBilinForm x y - A.strictUpper.finsuppBilinForm y x := by
  conv_lhs => rw [← strictUpper_sub_transpose_of_isAlt hA]; simp
/-- Replacing row and column `k` skew-symmetrically via `Matrix.updateSkew` preserves alternation of
`Matrix.finsuppBilinForm`. -/
theorem isAlt_finsuppBilinForm_updateSkew [DecidableEq I] {A : Matrix I I S}
    (hA : A.finsuppBilinForm.IsAlt) (k : I) (ℓ : I → S) :
    (A.updateSkew k ℓ).finsuppBilinForm.IsAlt := by
  rw [isAlt_finsuppBilinForm_iff] at hA ⊢
  refine ⟨Matrix.ext fun i j ↦ ?_, fun i ↦ ?_⟩
  · rw [Matrix.transpose_apply, Matrix.neg_apply]
    rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj
    · simp
    · rw [updateSkew_apply_right_of_ne _ _ _ hj.symm, updateSkew_apply_left_of_ne _ _ _ hj.symm]
    · rw [updateSkew_apply_left_of_ne _ _ _ hi.symm, updateSkew_apply_right_of_ne _ _ _ hi.symm,
        neg_neg]
    · rw [updateSkew_apply_of_ne _ _ _ hj.symm hi.symm,
        updateSkew_apply_of_ne _ _ _ hi.symm hj.symm]; exact congr_fun (congr_fun hA.1 i) j
  · rcases eq_or_ne k i with rfl | hi
    · simp
    · rw [updateSkew_apply_of_ne _ _ _ hi.symm hi.symm]; exact hA.2 i
/-- On vectors vanishing at `k`, `(A.updateSkew k ℓ).finsuppBilinForm` agrees with
`A.finsuppBilinForm`. -/
theorem finsuppBilinForm_updateSkew_of_apply_eq_zero [DecidableEq I] (A : Matrix I I S) (k : I)
    (ℓ : I → S) {x y : I →₀ S} (hx : x k = 0) (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm x y = A.finsuppBilinForm x y := by
  rw [finsuppBilinForm_apply, finsuppBilinForm_apply]
  refine Finsupp.sum_congr fun i hi ↦ Finsupp.sum_congr fun j hj ↦ ?_
  rw [updateSkew_apply_of_ne A k ℓ (by rintro rfl; exact Finsupp.mem_support_iff.mp hi hx)
    (by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy)]
/-- Pairing `r • eₖ` on the left with a vector `y` vanishing at `k` under `A.updateSkew k ℓ`
evaluates `r * ∑ⱼ ℓ j * yⱼ`. -/
theorem finsuppBilinForm_updateSkew_single_left [DecidableEq I] (A : Matrix I I S) (k : I)
    (ℓ : I → S) (r : S) {y : I →₀ S} (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm (Finsupp.single k r) y =
      r * Finsupp.linearCombination S ℓ y := by
  rw [finsuppBilinForm_single_left, LinearMap.smul_apply, smul_eq_mul,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  refine congrArg (r * ·) (Finsupp.sum_congr fun j hj ↦ ?_)
  rw [updateSkew_apply_left_of_ne A k ℓ (by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy)]
/-- Two matrices with alternating `finsuppBilinForm` are equal as soon as their forms agree on
vectors vanishing at `k` and on pairs `(eₖ, y)` with `y k = 0`. -/
theorem eq_of_isAlt_finsuppBilinForm_of_eq_off {A₁ A₂ : Matrix I I S} {k : I}
    (h₁ : A₁.finsuppBilinForm.IsAlt) (h₂ : A₂.finsuppBilinForm.IsAlt)
    (h_off : ∀ x y, x k = 0 → y k = 0 → A₁.finsuppBilinForm x y = A₂.finsuppBilinForm x y)
    (h_row : ∀ y, y k = 0 →
      A₁.finsuppBilinForm (Finsupp.single k 1) y = A₂.finsuppBilinForm (Finsupp.single k 1) y) :
    A₁ = A₂ := by
  classical refine Matrix.ext fun i j ↦ ?_
  rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj
  · rw [apply_self_eq_zero_of_isAlt_finsuppBilinForm h₁,
      apply_self_eq_zero_of_isAlt_finsuppBilinForm h₂]
  · simpa [finsuppBilinForm_single_single] using
      h_row (Finsupp.single j 1) (Finsupp.single_eq_of_ne hj)
  · rw [← neg_apply_eq_of_isAlt_finsuppBilinForm h₁ k i,
      ← neg_apply_eq_of_isAlt_finsuppBilinForm h₂ k i]
    exact congrArg Neg.neg <| by
      simpa [finsuppBilinForm_single_single] using
        h_row (Finsupp.single i 1) (Finsupp.single_eq_of_ne hi)
  · simpa [finsuppBilinForm_single_single] using h_off (Finsupp.single i 1) (Finsupp.single j 1)
      (Finsupp.single_eq_of_ne hi) (Finsupp.single_eq_of_ne hj)
end CommRing
end Matrix
