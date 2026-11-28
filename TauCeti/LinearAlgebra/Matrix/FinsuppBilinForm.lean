/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Reflection
public import TauCeti.LinearAlgebra.Matrix.Alternating.Basic
import Mathlib.Tactic.Ring

/-!
# The bilinear form of a matrix on finitely supported vectors

Mathlib's `Matrix.toBilin'` reads a square matrix over a finite index type as a bilinear form on
`n → R`. For an arbitrary index set `I`, a matrix `A : Matrix I I R` over a commutative semiring
still defines the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on the free module `I →₀ R`, whose Gram matrix in
the standard basis is `A`. This is the form used, for example, to pair the simple roots of a
Coxeter system with infinite rank, and to twist the exponent lattice of a based quantum torus.

Evaluating `LinearMap.BilinForm.toMatrixAux` on the standard basis `i ↦ Finsupp.single i 1`
recovers `A` without finiteness or decidability hypotheses on `I`, upgrading
`Matrix.finsuppBilinForm` to an `R`-linear isomorphism `Matrix.finsuppBilinFormLinearEquiv`
between `Matrix I I R` and `LinearMap.BilinForm R (I →₀ R)`. Over a commutative ring, the
pre-reflections `Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i))`
commute with scalar maps along ring homomorphisms and preserve `A.finsuppBilinForm` whenever `A`
is symmetric and `A i i = 2`.

## Main definitions

* `Matrix.finsuppBilinForm`: the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on `I →₀ R`.
* `Matrix.finsuppBilinFormLinearEquiv`: the `R`-linear equivalence
  `Matrix I I R ≃ₗ[R] LinearMap.BilinForm R (I →₀ R)` with inverse
  `LinearMap.BilinForm.toMatrixAux (fun i ↦ Finsupp.single i 1)`.

## Main results

* `Matrix.finsuppBilinForm_apply`: the form is `∑ᵢⱼ xᵢ A i j yⱼ`, as a double `Finsupp.sum`.
* `Matrix.finsuppBilinForm_single_single`: the Gram matrix of `Matrix.finsuppBilinForm A` is `A`.
* `Matrix.finsuppBilinForm_transpose` and `Matrix.isSymm_finsuppBilinForm_iff`: transposing `A`
  flips `A.finsuppBilinForm`, so `A.finsuppBilinForm` is symmetric if and only if `A` is.
* `Matrix.map_finsuppBilinForm` and `Matrix.mapRange_preReflection_single_linearCombination`:
  compatibility of `Matrix.finsuppBilinForm` and its standard-basis pre-reflections with ring
  homomorphisms.
* `Matrix.finsuppBilinForm_apply_eq_dotProduct`, `Matrix.finsuppBilinForm_apply_eq_toBilin'`, and
  `Matrix.finsuppBilinForm_repr_eq_toBilin`: agreement with `dotProduct`, `Matrix.toBilin'`, and
  `Matrix.toBilin` when `I` is finite.
* `Matrix.finsuppBilinForm_preReflection_single_linearCombination`: when `A` is symmetric and
  `A i i = 2`, the `i`-th pre-reflection preserves `A.finsuppBilinForm`.
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

section CommSemiring

variable {I J R S : Type*} [CommSemiring R] [CommSemiring S] (A B : Matrix I I R)

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

/-- The zero matrix defines the zero bilinear form on `I →₀ R`. -/
@[simp]
theorem finsuppBilinForm_zero : (0 : Matrix I I R).finsuppBilinForm = 0 :=
  Finsupp.lhom_ext fun _ _ ↦ Finsupp.lhom_ext fun _ _ ↦ by simp

/-- `Matrix.finsuppBilinForm` preserves matrix addition. -/
@[simp]
theorem finsuppBilinForm_add : (A + B).finsuppBilinForm = A.finsuppBilinForm + B.finsuppBilinForm :=
  Finsupp.lhom_ext fun _ _ ↦ Finsupp.lhom_ext fun _ _ ↦ by simp [mul_add]

/-- `Matrix.finsuppBilinForm` commutes with scalar multiplication. -/
@[simp]
theorem finsuppBilinForm_smul (c : R) : (c • A).finsuppBilinForm = c • A.finsuppBilinForm :=
  Finsupp.lhom_ext fun _ _ ↦ Finsupp.lhom_ext fun _ _ ↦ by simp [mul_left_comm]

/-- Evaluating `LinearMap.BilinForm.toMatrixAux` on the standard basis vectors `Finsupp.single i 1`
recovers `A` from `A.finsuppBilinForm`. -/
@[simp]
theorem toMatrixAux_single_finsuppBilinForm :
    LinearMap.BilinForm.toMatrixAux (fun i : I ↦ Finsupp.single i (1 : R)) A.finsuppBilinForm =
      A := by
  ext i j
  simp

/-- Every bilinear form on `I →₀ R` is `Matrix.finsuppBilinForm` of its Gram matrix on the standard
basis `i ↦ Finsupp.single i 1`. -/
@[simp]
theorem finsuppBilinForm_toMatrixAux_single (Φ : LinearMap.BilinForm R (I →₀ R)) :
    (Φ.toMatrixAux (fun i : I ↦ Finsupp.single i (1 : R))).finsuppBilinForm = Φ := by
  ext i j
  simp

/-- `Matrix.finsuppBilinForm` is injective on `Matrix I I R`. -/
theorem finsuppBilinForm_injective :
    Function.Injective (Matrix.finsuppBilinForm (I := I) (R := R)) :=
  Function.LeftInverse.injective toMatrixAux_single_finsuppBilinForm

/-- Two matrices define the same bilinear form on `I →₀ R` if and only if they are equal. -/
@[simp]
theorem finsuppBilinForm_inj {A B : Matrix I I R} :
    A.finsuppBilinForm = B.finsuppBilinForm ↔ A = B :=
  finsuppBilinForm_injective.eq_iff

/-- `Matrix.finsuppBilinForm A` vanishes if and only if `A = 0`. -/
@[simp]
theorem finsuppBilinForm_eq_zero {A : Matrix I I R} :
    A.finsuppBilinForm = 0 ↔ A = 0 := by
  rw [← finsuppBilinForm_zero, finsuppBilinForm_inj]

/-- **The `R`-linear isomorphism between `I × I` matrices and bilinear forms on `I →₀ R`**, valid
without finiteness or decidable equality on `I`. -/
noncomputable def finsuppBilinFormLinearEquiv :
    Matrix I I R ≃ₗ[R] LinearMap.BilinForm R (I →₀ R) where
  toFun := finsuppBilinForm
  map_add' := finsuppBilinForm_add
  map_smul' c A := finsuppBilinForm_smul A c
  invFun := LinearMap.BilinForm.toMatrixAux (fun i : I ↦ Finsupp.single i (1 : R))
  left_inv := toMatrixAux_single_finsuppBilinForm
  right_inv := finsuppBilinForm_toMatrixAux_single

/-- Forward application of `Matrix.finsuppBilinFormLinearEquiv` is `Matrix.finsuppBilinForm`. -/
@[simp]
theorem finsuppBilinFormLinearEquiv_apply :
    finsuppBilinFormLinearEquiv A = A.finsuppBilinForm :=
  (rfl)

/-- Inverse application of `Matrix.finsuppBilinFormLinearEquiv` evaluates `toMatrixAux` on the
standard basis vectors `Finsupp.single i 1`. -/
@[simp]
theorem finsuppBilinFormLinearEquiv_symm_apply (Φ : LinearMap.BilinForm R (I →₀ R)) :
    finsuppBilinFormLinearEquiv.symm Φ = Φ.toMatrixAux (fun i : I ↦ Finsupp.single i (1 : R)) :=
  (rfl)

/-- Transposing `A` flips the arguments of `A.finsuppBilinForm`. -/
@[simp]
theorem finsuppBilinForm_transpose : (Aᵀ).finsuppBilinForm = A.finsuppBilinForm.flip :=
  Finsupp.lhom_ext fun _ _ ↦ Finsupp.lhom_ext fun _ _ ↦ by simp [mul_left_comm]

/-- Transposing `A` swaps the two arguments of `A.finsuppBilinForm`. -/
theorem finsuppBilinForm_transpose_apply (x y : I →₀ R) :
    Aᵀ.finsuppBilinForm x y = A.finsuppBilinForm y x := by
  rw [finsuppBilinForm_transpose]
  simp

/-- Pairing with a basis vector `b • eⱼ` on the right evaluates the `j`-th column functional
`x ↦ b * ∑ᵢ xᵢ A i j`. -/
theorem finsuppBilinForm_single_right (x : I →₀ R) (j : I) (b : R) :
    A.finsuppBilinForm x (Finsupp.single j b) = b * Finsupp.linearCombination R (Aᵀ j) x := by
  calc A.finsuppBilinForm x (Finsupp.single j b)
      _ = A.finsuppBilinForm.flip (Finsupp.single j b) x := (LinearMap.flip_apply _ _ _).symm
      _ = (Aᵀ).finsuppBilinForm (Finsupp.single j b) x := by rw [finsuppBilinForm_transpose]
      _ = b * Finsupp.linearCombination R (Aᵀ j) x := by
        rw [finsuppBilinForm_single_left, LinearMap.smul_apply, smul_eq_mul]

/-- Pulling back a matrix along `f : J → I` pulls back `Matrix.finsuppBilinForm` along
`Finsupp.mapDomain f`. -/
@[simp]
theorem finsuppBilinForm_submatrix (f : J → I) (x y : J →₀ R) :
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

/-- **`A.finsuppBilinForm` is symmetric if and only if `A` is symmetric.** -/
@[simp]
theorem isSymm_finsuppBilinForm_iff {A : Matrix I I R} :
    A.finsuppBilinForm.IsSymm ↔ A.IsSymm := by
  rw [LinearMap.BilinForm.isSymm_iff_flip, Matrix.IsSymm, ← finsuppBilinForm_inj,
    finsuppBilinForm_transpose]

/-- A symmetric matrix defines a symmetric bilinear form on `I →₀ R`. -/
theorem IsSymm.finsuppBilinForm {A : Matrix I I R} (hA : A.IsSymm) :
    A.finsuppBilinForm.IsSymm :=
  isSymm_finsuppBilinForm_iff.mpr hA

/-- **Compatibility of `Matrix.finsuppBilinForm` with ring homomorphisms**: mapping entries by `f`
agrees with applying `f` after pairing and pushing vectors forward by `Finsupp.mapRange`. -/
theorem map_finsuppBilinForm (f : R →+* S) (x y : I →₀ R) :
    f (A.finsuppBilinForm x y) =
      (A.map f).finsuppBilinForm (x.mapRange f f.map_zero) (y.mapRange f f.map_zero) := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x₁ x₂ hx₁ hx₂ =>
    simp only [map_add, LinearMap.add_apply, hx₁, hx₂, Finsupp.mapRange_add f.map_add]
  | single i a =>
    induction y using Finsupp.induction_linear with
    | zero => simp
    | add y₁ y₂ hy₁ hy₂ =>
      simp only [map_add, hy₁, hy₂, Finsupp.mapRange_add f.map_add]
    | single j b =>
      simp [Finsupp.mapRange_single]

/-- For a finite index set, `Matrix.finsuppBilinForm` is the usual form `x ⬝ᵥ (A *ᵥ y)` of the
matrix `A`. -/
theorem finsuppBilinForm_apply_eq_dotProduct [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = ⇑x ⬝ᵥ (A *ᵥ ⇑y) := by
  simp [finsuppBilinForm, Finsupp.linearCombination_apply, Finsupp.sum_fintype, dotProduct,
    mulVec, Finset.mul_sum, mul_comm]

/-- For a finite index set, `Matrix.finsuppBilinForm` expands as the double `Finset.univ` sum
`∑ i, ∑ j, x i * A i j * y j`, without requiring decidable equality on `I`. -/
theorem finsuppBilinForm_apply_eq_sum [Fintype I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = ∑ i, ∑ j, x i * A i j * y j := by
  rw [finsuppBilinForm_apply_eq_dotProduct, dotProduct]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [mulVec, dotProduct, Finset.mul_sum, mul_assoc]

/-- For a finite index set with decidable equality, `Matrix.finsuppBilinForm` agrees with
`Matrix.toBilin'`. -/
theorem finsuppBilinForm_apply_eq_toBilin' [Fintype I] [DecidableEq I] (x y : I →₀ R) :
    A.finsuppBilinForm x y = Matrix.toBilin' A x y :=
  (A.finsuppBilinForm_apply_eq_sum x y).trans (Matrix.toBilin'_apply A x y).symm

/-- For a finite basis `b : Module.Basis I R M`, `Matrix.finsuppBilinForm` in the coordinates of `b`
agrees with `Matrix.toBilin b A`. -/
theorem finsuppBilinForm_repr_eq_toBilin {M : Type*} [AddCommMonoid M] [Module R M]
    [Fintype I] [DecidableEq I] (b : Module.Basis I R M) (x y : M) :
    A.finsuppBilinForm (b.repr x) (b.repr y) = Matrix.toBilin b A x y := by
  rw [finsuppBilinForm_apply_eq_toBilin', Matrix.toBilin'_apply, Matrix.toBilin_apply]

/-- Every diagonal entry of a matrix whose `finsuppBilinForm` is alternating vanishes. -/
theorem apply_self_eq_zero_of_isAlt_finsuppBilinForm {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (i : I) : A i i = 0 := by
  simpa [finsuppBilinForm_single_single] using hA.self_eq_zero (Finsupp.single i 1)

/-- For finite `I`, `A.finsuppBilinForm` is alternating if and only if `A.toBilin'` is. -/
theorem isAlt_finsuppBilinForm_iff_isAlt_toBilin' [Fintype I] [DecidableEq I] :
    A.finsuppBilinForm.IsAlt ↔ A.toBilin'.IsAlt :=
  ⟨fun h x ↦ by
      simpa [finsuppBilinForm_apply_eq_toBilin'] using h (Finsupp.equivFunOnFinite.symm x),
    fun h x ↦ (A.finsuppBilinForm_apply_eq_toBilin' x x).trans (h x)⟩

/-- Pairing `r • eᵢ` on the left with `x` under `A.strictUpper` agrees with `A.finsuppBilinForm`
whenever every index in `x.support` is strictly greater than `i`. -/
theorem finsuppBilinForm_strictUpper_single_left_of_lt [LT I] [DecidableLT I] {i : I} (r : R)
    {x : I →₀ R} (hx : ∀ j ∈ x.support, i < j) :
    A.strictUpper.finsuppBilinForm (Finsupp.single i r) x =
      A.finsuppBilinForm (Finsupp.single i r) x := by
  rw [finsuppBilinForm_apply, Finsupp.sum_single_index (by simp),
    finsuppBilinForm_apply, Finsupp.sum_single_index (by simp)]
  exact Finset.sum_congr rfl fun j hj ↦ by simp [hx j hj]

/-- Pairing `x` with `r • eᵢ` on the right under `A.strictUpper` vanishes whenever every index in
`x.support` is at least `i`. -/
theorem finsuppBilinForm_strictUpper_single_right_eq_zero [Preorder I] [DecidableLT I] {i : I}
    (r : R) {x : I →₀ R} (hx : ∀ j ∈ x.support, i ≤ j) :
    A.strictUpper.finsuppBilinForm x (Finsupp.single i r) = 0 := by
  rw [finsuppBilinForm_apply, Finsupp.sum]
  exact Finset.sum_eq_zero fun j hj ↦ by
    rw [Finsupp.sum_single_index (by simp)]
    simp [(hx j hj).not_gt]

end CommSemiring

section CommRing

variable {I R S : Type*} [CommRing R] [CommRing S]

/-- `Matrix.finsuppBilinForm` commutes with matrix negation. -/
@[simp]
theorem finsuppBilinForm_neg (A : Matrix I I R) :
    (-A).finsuppBilinForm = -A.finsuppBilinForm :=
  map_neg finsuppBilinFormLinearEquiv A

/-- `Matrix.finsuppBilinForm` preserves matrix subtraction. -/
@[simp]
theorem finsuppBilinForm_sub (A B : Matrix I I R) :
    (A - B).finsuppBilinForm = A.finsuppBilinForm - B.finsuppBilinForm :=
  map_sub finsuppBilinFormLinearEquiv A B

/-- **Ring homomorphisms intertwine the standard-basis pre-reflections of a matrix with entrywise
matrix maps.** -/
theorem mapRange_preReflection_single_linearCombination (A : Matrix I I R) (f : R →+* S) (i : I)
    (x : I →₀ R) :
    (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) x).mapRange
        f f.map_zero =
      Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination S (A.map f i))
        (x.mapRange f f.map_zero) := by
  have hpair := A.map_finsuppBilinForm f (Finsupp.single i 1) x
  rw [Finsupp.mapRange_single, map_one, finsuppBilinForm_single_left,
    finsuppBilinForm_single_left, one_smul, one_smul] at hpair
  rw [Module.preReflection_apply, Module.preReflection_apply, Finsupp.mapRange_sub f.map_sub,
    Finsupp.smul_single_one, Finsupp.smul_single_one, Finsupp.mapRange_single, hpair]

/-- **When `A` is symmetric and `A i i = 2`, the `i`-th pre-reflection preserves
`A.finsuppBilinForm`.** -/
theorem finsuppBilinForm_preReflection_single_linearCombination {A : Matrix I I R} {i : I}
    (hA : A.IsSymm) (hii : A i i = 2) (x y : I →₀ R) :
    A.finsuppBilinForm
        (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) x)
        (Module.preReflection (Finsupp.single i 1) (Finsupp.linearCombination R (A i)) y) =
      A.finsuppBilinForm x y := by
  have hrow (z : I →₀ R) :
      Finsupp.linearCombination R (A i) z = A.finsuppBilinForm (Finsupp.single i 1) z := by
    rw [finsuppBilinForm_single_left, one_smul]
  rw [Module.preReflection_apply, Module.preReflection_apply, hrow x, hrow y]
  simp only [map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul,
    finsuppBilinForm_single_single, one_mul, hii, (hA.finsuppBilinForm).eq (Finsupp.single i 1) x]
  ring

/-- If `A.finsuppBilinForm` is alternating, `A` is skew-symmetric entrywise (`-A i j = A j i`). -/
theorem neg_apply_eq_of_isAlt_finsuppBilinForm {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (i j : I) : -A i j = A j i := by
  simpa [finsuppBilinForm_single_single] using hA.neg_eq (Finsupp.single i 1) (Finsupp.single j 1)

/-- Over a commutative ring and an arbitrary index type, `A.finsuppBilinForm` is alternating if and
only if `A` is skew-symmetric (`Aᵀ = -A`) and has zero diagonal. -/
theorem isAlt_finsuppBilinForm_iff (A : Matrix I I R) :
    A.finsuppBilinForm.IsAlt ↔ Aᵀ = -A ∧ ∀ i, A i i = 0 := by
  refine ⟨fun h ↦ ⟨Matrix.ext fun i j ↦ (neg_apply_eq_of_isAlt_finsuppBilinForm h i j).symm,
    apply_self_eq_zero_of_isAlt_finsuppBilinForm h⟩, fun ⟨ht, hd⟩ x ↦ ?_⟩
  classical
  simp only [finsuppBilinForm_apply, Finsupp.sum]
  simp_rw [← Finset.sum_coe_sort x.support, ← Fintype.sum_prod_type']
  refine Finset.sum_ninvolution Prod.swap
    (fun p ↦ by
      have hp : A p.2 p.1 = -A p.1 p.2 := by simpa using congr_fun (congr_fun ht p.1) p.2
      simp only [Prod.fst_swap, Prod.snd_swap, hp]; ring)
    (fun ⟨_, _⟩ hf he ↦ by cases congrArg Prod.fst he; exact hf (by simp [hd]))
    (fun _ ↦ Finset.mem_univ _) (fun _ ↦ Prod.swap_swap _)

/-- A matrix whose `finsuppBilinForm` is alternating equals `A.strictUpper - A.strictUpperᵀ`. -/
theorem strictUpper_sub_transpose_of_isAlt [LinearOrder I] {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) : A.strictUpper - A.strictUpperᵀ = A :=
  Matrix.ext fun i j ↦ by
    rw [Matrix.sub_apply, Matrix.transpose_apply, strictUpper_apply, strictUpper_apply]
    rcases lt_trichotomy i j with hij | rfl | hji
    · simp [hij, asymm hij]
    · simp [apply_self_eq_zero_of_isAlt_finsuppBilinForm hA]
    · simp [hji, asymm hji, neg_apply_eq_of_isAlt_finsuppBilinForm hA]

/-- Over a linearly ordered index type, an alternating `finsuppBilinForm` decomposes as the form of
`A.strictUpper` minus its argument-swapped flip, used to normalize ordered coordinate products. -/
theorem finsuppBilinForm_eq_strictUpper_sub_flip [LinearOrder I] {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (x y : I →₀ R) :
    A.finsuppBilinForm x y =
      A.strictUpper.finsuppBilinForm x y - A.strictUpper.finsuppBilinForm y x := by
  conv_lhs => rw [← strictUpper_sub_transpose_of_isAlt hA]
  simp

/-- Replacing row and column `k` skew-symmetrically via `Matrix.updateSkew` preserves alternation of
`Matrix.finsuppBilinForm`. -/
theorem isAlt_finsuppBilinForm_updateSkew [DecidableEq I] {A : Matrix I I R}
    (hA : A.finsuppBilinForm.IsAlt) (k : I) (ℓ : I → R) :
    (A.updateSkew k ℓ).finsuppBilinForm.IsAlt := by
  rw [isAlt_finsuppBilinForm_iff] at hA ⊢
  refine ⟨Matrix.ext fun i j ↦ ?_, fun i ↦ ?_⟩
  · rw [Matrix.transpose_apply, Matrix.neg_apply]
    rcases eq_or_ne k i with rfl | hi <;> rcases eq_or_ne k j with rfl | hj
    · simp
    · simp [hj.symm]
    · simp [hi.symm]
    · rw [updateSkew_apply_of_ne _ _ _ hj.symm hi.symm,
        updateSkew_apply_of_ne _ _ _ hi.symm hj.symm]
      exact congr_fun (congr_fun hA.1 i) j
  · rcases eq_or_ne k i with rfl | hi
    · simp
    · simp [hi.symm, hA.2 i]

/-- On vectors vanishing at `k`, `(A.updateSkew k ℓ).finsuppBilinForm` agrees with
`A.finsuppBilinForm`. -/
theorem finsuppBilinForm_updateSkew_of_apply_eq_zero [DecidableEq I] (A : Matrix I I R) (k : I)
    (ℓ : I → R) {x y : I →₀ R} (hx : x k = 0) (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm x y = A.finsuppBilinForm x y := by
  rw [finsuppBilinForm_apply, finsuppBilinForm_apply]
  refine Finsupp.sum_congr fun i hi ↦ Finsupp.sum_congr fun j hj ↦ ?_
  rw [updateSkew_apply_of_ne A k ℓ (by rintro rfl; exact Finsupp.mem_support_iff.mp hi hx)
    (by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy)]

/-- Pairing `r • eₖ` on the left with a vector `y` vanishing at `k` under `A.updateSkew k ℓ`
evaluates `r * ∑ⱼ ℓ j * yⱼ`. -/
theorem finsuppBilinForm_updateSkew_single_left [DecidableEq I] (A : Matrix I I R) (k : I)
    (ℓ : I → R) (r : R) {y : I →₀ R} (hy : y k = 0) :
    (A.updateSkew k ℓ).finsuppBilinForm (Finsupp.single k r) y =
      r * Finsupp.linearCombination R ℓ y := by
  rw [finsuppBilinForm_single_left, LinearMap.smul_apply, smul_eq_mul,
    Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  refine congrArg (r * ·) (Finsupp.sum_congr fun j hj ↦ ?_)
  rw [updateSkew_apply_left_of_ne A k ℓ (by rintro rfl; exact Finsupp.mem_support_iff.mp hj hy)]

/-- Pairing `eₖ` on the left with `y` (`y k = 0`) under `A.updateSkew k (fun j ↦ φ (single j 1))`
recovers `φ y` for any linear functional `φ : (I →₀ R) →ₗ[R] R`. -/
theorem finsuppBilinForm_updateSkew_single_one_left [DecidableEq I] (A : Matrix I I R) (k : I)
    (φ : (I →₀ R) →ₗ[R] R) {y : I →₀ R} (hy : y k = 0) :
    (A.updateSkew k fun j ↦ φ (Finsupp.single j 1)).finsuppBilinForm (Finsupp.single k 1) y =
      φ y := by
  rw [finsuppBilinForm_updateSkew_single_left A k _ 1 hy, one_mul]
  exact LinearMap.congr_fun (Finsupp.lhom_ext' fun _ ↦ LinearMap.ext_ring <| by simp) y

/-- Two matrices with alternating `finsuppBilinForm` are equal as soon as their forms agree on
vectors vanishing at `k` and on pairs `(eₖ, y)` with `y k = 0`. -/
theorem eq_of_isAlt_finsuppBilinForm_of_eq_off {A₁ A₂ : Matrix I I R} {k : I}
    (h₁ : A₁.finsuppBilinForm.IsAlt) (h₂ : A₂.finsuppBilinForm.IsAlt)
    (h_off : ∀ x y, x k = 0 → y k = 0 → A₁.finsuppBilinForm x y = A₂.finsuppBilinForm x y)
    (h_row : ∀ y, y k = 0 →
      A₁.finsuppBilinForm (Finsupp.single k 1) y = A₂.finsuppBilinForm (Finsupp.single k 1) y) :
    A₁ = A₂ := by
  classical
  refine Matrix.ext fun i j ↦ ?_
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
