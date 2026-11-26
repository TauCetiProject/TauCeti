/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Vec
public import TauCeti.LinearAlgebra.Matrix.BlockSucc
public import TauCeti.LinearAlgebra.Matrix.Triangular.Coordinates

/-!
# Measurability of matrix operations

The column-stacking vectorization `Matrix.vec` is a measurable equivalence between `m × n`
matrices and functions on `n × m`. It is packaged with target `WithLp p (n × m → α)`, so that for
real entries and `p = 2` it identifies matrices with `EuclideanSpace ℝ (n × m)`.

Matrix inversion is not continuous: it jumps at the singular matrices, where Mathlib's totalized
inverse takes the value `0`. It is still measurable, because Cramer's rule writes it as the
adjugate — a polynomial in the entries — scaled by the inverse of the determinant, and inversion
of scalars is measurable even at zero.

## Main results

* `TauCeti.measurable_matrix_vec` — vectorization is measurable.
* `TauCeti.matrixVecMeasurableEquiv` — vectorization as a measurable equivalence.
* `TauCeti.instMeasurableAddMatrix` — entrywise addition of matrices is measurable.
* `TauCeti.measurable_matrix_mul` — matrix multiplication is measurable, and the
  `MeasurableMul₂` instance it supplies for square matrices.
* `TauCeti.measurable_matrix_mul_conjTranspose` — the Gram matrix `X * Xᴴ` is measurable.
* `TauCeti.measurable_matrix_blockSucc` — the upper-left block extension `Matrix.blockSucc` is
  measurable.
* `Measurable.matrix_det` — the determinant of a measurable family of matrices is measurable.
* `TauCeti.measurable_matrix_inv` — matrix inversion is measurable, and the `MeasurableInv`
  instance it supplies.
-/

public section

namespace TauCeti

/-- The column-stacking vectorization of matrices is measurable. -/
@[fun_prop]
theorem measurable_matrix_vec {m n α : Type*} [MeasurableSpace α] :
    Measurable fun A : Matrix m n α => A.vec :=
  .of_eval fun _ => Matrix.measurable_apply

/-- The column-stacking vectorization `Matrix.vec` as a measurable equivalence onto the `L^p` copy
of functions on the transposed index type. Its inverse reads entry `(i, j)` from coordinate
`(j, i)`. -/
def matrixVecMeasurableEquiv {m n α : Type*} [MeasurableSpace α] (p : ENNReal) :
    Matrix m n α ≃ᵐ WithLp p (n × m → α) where
  toFun A := WithLp.toLp p A.vec
  invFun x := Matrix.of fun i j => x.ofLp (j, i)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (WithLp.measurable_toLp p _).comp measurable_matrix_vec
  measurable_invFun := by
    -- The goal is stated for the coercion of the bundled `Equiv.symm`, which `fun_prop` cannot
    -- see through, so restate it for the underlying function.
    change Measurable fun x : WithLp p (n × m → α) => Matrix.of fun i j => x.ofLp (j, i)
    fun_prop

@[simp]
theorem matrixVecMeasurableEquiv_apply {m n α : Type*} [MeasurableSpace α] (p : ENNReal)
    (A : Matrix m n α) : matrixVecMeasurableEquiv p A = WithLp.toLp p A.vec :=
  (rfl)

@[simp]
theorem matrixVecMeasurableEquiv_symm_apply {m n α : Type*} [MeasurableSpace α] (p : ENNReal)
    (x : WithLp p (n × m → α)) :
    (matrixVecMeasurableEquiv p).symm x = Matrix.of fun i j => x.ofLp (j, i) :=
  (rfl)

section Triangular

variable {ι R : Type*} [LinearOrder ι] [MeasurableSpace R]

/-- Assemble a matrix from its upper triangular and strict lower entries as a measurable
equivalence. -/
def schurMatrixMeasurableEquiv :
    SchurCoordinates ι R ≃ᵐ Matrix ι ι R :=
  ((Matrix.ofMeasurableEquiv ι ι R).symm.trans <|
    (MeasurableEquiv.curry ι ι R).symm.trans <|
      (MeasurableEquiv.piEquivPiSubtypeProd (fun _ ↦ R)
        (fun ij : ι × ι ↦ ij.1 ≤ ij.2)).trans <|
        (MeasurableEquiv.refl _).prodCongr
          (MeasurableEquiv.piCongrLeft (fun _ ↦ R) (schurLowerIndexEquiv ι)).symm).symm

/-- The first coordinate of the measurable split reads the upper triangular entries. -/
@[simp] theorem _root_.Matrix.schurMatrixMeasurableEquiv_symm_fst (A : Matrix ι ι R)
    (ij : {ij : ι × ι // ij.1 ≤ ij.2}) :
    (schurMatrixMeasurableEquiv.symm A).1 ij = A ij.val.1 ij.val.2 := by
  simp [schurMatrixMeasurableEquiv, MeasurableEquiv.prodCongr,
    MeasurableEquiv.coe_curry_symm, Function.uncurry]

/-- The second coordinate of the measurable split reads the strict lower entries. -/
@[simp] theorem _root_.Matrix.schurMatrixMeasurableEquiv_symm_snd (A : Matrix ι ι R)
    (ij : SchurLowerIndex ι) :
    (schurMatrixMeasurableEquiv.symm A).2 ij = A ij.val.2 ij.val.1 := by
  simp [schurMatrixMeasurableEquiv, MeasurableEquiv.prodCongr, MeasurableEquiv.piCongrLeft,
    MeasurableEquiv.coe_curry_symm, Function.uncurry]

/-- Measurable assembly reads the first coordinate at an upper triangular position. -/
@[simp] theorem schurMatrixMeasurableEquiv_apply_of_le (x : SchurCoordinates ι R) {i j : ι}
    (h : i ≤ j) : schurMatrixMeasurableEquiv x i j = x.1 ⟨(i, j), h⟩ := by
  have he := Matrix.schurMatrixMeasurableEquiv_symm_fst (schurMatrixMeasurableEquiv x) ⟨(i, j), h⟩
  rwa [MeasurableEquiv.symm_apply_apply, eq_comm] at he

/-- Measurable assembly reads the second coordinate at a strict lower position. -/
@[simp] theorem schurMatrixMeasurableEquiv_apply_of_gt (x : SchurCoordinates ι R) {i j : ι}
    (h : j < i) : schurMatrixMeasurableEquiv x i j = x.2 ⟨(j, i), h⟩ := by
  have he := Matrix.schurMatrixMeasurableEquiv_symm_snd (schurMatrixMeasurableEquiv x) ⟨(j, i), h⟩
  rwa [MeasurableEquiv.symm_apply_apply, eq_comm] at he

/-- Reading the entries with the measurable equivalence agrees with the linear split. -/
theorem _root_.Matrix.schurMatrixMeasurableEquiv_symm_apply [Semiring R] (A : Matrix ι ι R) :
    schurMatrixMeasurableEquiv.symm A = schurMatrixEquiv.symm A := by
  apply Prod.ext <;> funext ij <;> simp

/-- The measurable and linear assembly maps agree pointwise. -/
theorem schurMatrixMeasurableEquiv_apply [Semiring R] (x : SchurCoordinates ι R) :
    schurMatrixMeasurableEquiv x = schurMatrixEquiv x := by
  apply schurMatrixMeasurableEquiv.symm.injective
  rw [MeasurableEquiv.symm_apply_apply, Matrix.schurMatrixMeasurableEquiv_symm_apply,
    LinearEquiv.symm_apply_apply]

end Triangular

/-- Entrywise addition of matrices is measurable when addition of the entries is. -/
instance instMeasurableAddMatrix {m n α : Type*} [MeasurableSpace α] [Add α] [MeasurableAdd α] :
    MeasurableAdd (Matrix m n α) :=
  inferInstanceAs (MeasurableAdd (m → n → α))

/-- Matrix multiplication is measurable: each entry of a product is a finite sum of products of
entries. -/
@[fun_prop]
theorem measurable_matrix_mul {l m n R : Type*} [Fintype m] [MeasurableSpace R]
    [Mul R] [AddCommMonoid R] [MeasurableMul₂ R] [MeasurableAdd₂ R] :
    Measurable fun A : Matrix l m R × Matrix m n R => A.1 * A.2 := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.measurable_sum _ fun k _ =>
    measurable_fst.eval_matrix.mul measurable_snd.eval_matrix

/-- The Gram matrix `X * Xᴴ` is measurable in `X`. -/
@[fun_prop]
theorem measurable_matrix_mul_conjTranspose {R : Type*} [Mul R] [AddCommMonoid R] [Star R]
    [MeasurableSpace R] [MeasurableMul₂ R] [MeasurableAdd₂ R]
    (hstar : Measurable (star : R → R)) {m n : Type*} [Fintype n] :
    Measurable fun X : Matrix m n R ↦ X * X.conjTranspose := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact Finset.measurable_sum _ fun k _ ↦
    measurable_id.eval_matrix.mul (hstar.comp measurable_id.eval_matrix)

example {m n : Type*} [Fintype n] :
    Measurable fun X : Matrix m n (ℝ × ℝ) ↦ X * X.conjTranspose :=
  measurable_matrix_mul_conjTranspose (continuous_star.measurable)

/-- Square matrices inherit `MeasurableMul₂` from the measurability of matrix multiplication, which
makes the generic `Measurable.mul` dot notation available for matrix-valued maps. -/
instance {m R : Type*} [Fintype m] [MeasurableSpace R] [Mul R] [AddCommMonoid R]
    [MeasurableMul₂ R] [MeasurableAdd₂ R] : MeasurableMul₂ (Matrix m m R) :=
  ⟨measurable_matrix_mul⟩

/-- Placing a square matrix in the upper-left block of the next size, `Matrix.blockSucc`, is
measurable: each entry of the result is an entry of the matrix or a constant. -/
@[fun_prop]
theorem measurable_matrix_blockSucc {n : ℕ} {R : Type*} [Semiring R] [MeasurableSpace R] :
    Measurable (Matrix.blockSucc : Matrix (Fin n) (Fin n) R → _) := by
  refine Measurable.of_eval_matrix _ fun i j ↦ ?_
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    simp [Matrix.measurable_apply]

/-- The determinant of a measurable family of square matrices is measurable, since the determinant
is a polynomial in the entries. -/
@[fun_prop]
theorem _root_.Measurable.matrix_det {m R α : Type*} [Fintype m] [DecidableEq m] [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R] [MeasurableSpace α] {A : α → Matrix m m R} (hA : Measurable A) :
    Measurable fun x ↦ (A x).det :=
  (Continuous.matrix_det continuous_id).measurable.comp hA

variable {m : Type*} [Fintype m] [DecidableEq m] {𝕜 : Type*} [Field 𝕜] [TopologicalSpace 𝕜]
  [IsTopologicalRing 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [SecondCountableTopology 𝕜]
  [MeasurableInv 𝕜]

/-- Matrix inversion is measurable. -/
@[fun_prop]
theorem measurable_matrix_inv : Measurable fun A : Matrix m m 𝕜 => A⁻¹ := by
  rw [Matrix.measurable_iff]
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv]
  exact ((Continuous.matrix_det continuous_id).measurable.inv).mul
    ((Continuous.matrix_adjugate continuous_id).matrix_elem i j).measurable

/-- Square matrices inherit `MeasurableInv` from the measurability of Cramer's rule, which makes
the generic `measurable_inv` API and `Measurable.inv` dot notation available for matrices. -/
instance : MeasurableInv (Matrix m m 𝕜) := ⟨measurable_matrix_inv⟩

end TauCeti
