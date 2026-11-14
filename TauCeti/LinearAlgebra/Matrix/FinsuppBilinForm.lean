/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.Reflection
import Mathlib.Tactic.Ring

/-!
# The bilinear form of a matrix on finitely supported vectors

Mathlib's `Matrix.toBilin'` reads a square matrix over a finite index type as a bilinear form on
`n → R`. For an arbitrary index set `I`, a matrix `A : Matrix I I R` over a commutative semiring
still defines the bilinear form `∑ᵢⱼ xᵢ A i j yⱼ` on the free module `I →₀ R`, whose Gram matrix in
the standard basis is `A`. This is the form used, for example, to pair the simple roots of a
Coxeter system with infinite rank.

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
-/

public section

namespace Matrix

section CommSemiring

variable {I R S : Type*} [CommSemiring R] [CommSemiring S] (A B : Matrix I I R)

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
    (Φ.toMatrixAux (fun i : I ↦ Finsupp.single i (1 : R))).finsuppBilinForm = Φ :=
  Finsupp.lhom_ext fun i a ↦ Finsupp.lhom_ext fun j b ↦ by
    conv_rhs =>
      rw [← Finsupp.smul_single_one i a, ← Finsupp.smul_single_one j b, map_smul, map_smul,
        LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, mul_left_comm]
    simp

/-- `Matrix.finsuppBilinForm` is injective on `Matrix I I R`. -/
theorem finsuppBilinForm_injective :
    Function.Injective (Matrix.finsuppBilinForm (I := I) (R := R)) :=
  Function.LeftInverse.injective toMatrixAux_single_finsuppBilinForm

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

/-- Pairing with a basis vector `b • eⱼ` on the right evaluates the `j`-th column functional
`x ↦ b * ∑ᵢ xᵢ A i j`. -/
theorem finsuppBilinForm_single_right (x : I →₀ R) (j : I) (b : R) :
    A.finsuppBilinForm x (Finsupp.single j b) = b * Finsupp.linearCombination R (Aᵀ j) x := by
  calc A.finsuppBilinForm x (Finsupp.single j b)
      _ = A.finsuppBilinForm.flip (Finsupp.single j b) x := (LinearMap.flip_apply _ _ _).symm
      _ = (Aᵀ).finsuppBilinForm (Finsupp.single j b) x := by rw [finsuppBilinForm_transpose]
      _ = b * Finsupp.linearCombination R (Aᵀ j) x := by
        rw [finsuppBilinForm_single_left, LinearMap.smul_apply, smul_eq_mul]

/-- **`A.finsuppBilinForm` is symmetric if and only if `A` is symmetric.** -/
@[simp]
theorem isSymm_finsuppBilinForm_iff {A : Matrix I I R} :
    A.finsuppBilinForm.IsSymm ↔ A.IsSymm := by
  rw [Matrix.IsSymm, ← finsuppBilinForm_injective.eq_iff, finsuppBilinForm_transpose,
    LinearMap.BilinForm.isSymm_def]
  refine ⟨fun h ↦ LinearMap.ext fun x ↦ LinearMap.ext fun y ↦ ?_, fun h x y ↦ ?_⟩
  · simpa using h y x
  · simpa using DFunLike.congr_fun (DFunLike.congr_fun h y) x

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

end CommSemiring

section CommRing

variable {I R S : Type*} [CommRing R] [CommRing S]

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

end CommRing

end Matrix
