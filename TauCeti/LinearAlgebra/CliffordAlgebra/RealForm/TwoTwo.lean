/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.LinearAlgebra.CliffordAlgebra.BottPeriodicity
public import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Scaling
public import TauCeti.LinearAlgebra.Matrix.Adjugate.Basic
public import TauCeti.LinearAlgebra.Matrix.Adjugate.FinTwo

/-!
# The split four-dimensional real even Clifford algebra

The even Clifford algebra of the split real quadratic form of signature `(2,2)` is a product of
two real two-by-two matrix algebras. Under this identification, Clifford reversal is matrix
adjugation in each factor, so the reverse norm-one equation is exactly the pair of determinant-one
equations.

The construction first uses hyperbolic Bott periodicity to identify `Cl(2,1)` with
`Cl(1,0) ⊗ M₂(ℝ)`, and then uses the two characters of `Cl(1,0) ≃ ℝ × ℝ`. Even-algebra dimension
reduction identifies `Cl⁺(2,2)` with `Cl(2,1)` and carries reversal to Clifford conjugation.

## Main definitions and results

* `TauCeti.realCliffordTwoOneEquivMatrixProd` identifies `Cl(2,1)` with two matrix algebras.
* `TauCeti.realCliffordTwoOneEquivMatrixProd_ι` gives its value on a Clifford generator.
* `TauCeti.realCliffordTwoOneEquivMatrixProd_star` identifies Clifford conjugation with
  componentwise adjugation.
* `TauCeti.realCliffordTwoTwoEvenEquivMatrixProd` identifies `Cl⁺(2,2)` with the same product.
* `TauCeti.realCliffordTwoTwoEvenEquivMatrixProd_ι` gives its value on a product of generators.
* `TauCeti.realCliffordTwoTwoEvenEquivMatrixProd_reverseEven` identifies reversal with
  componentwise adjugation.
* `TauCeti.realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one` characterizes the
  reverse-unitary carrier by two determinant-one equations.
* `TauCeti.realCliffordTwoTwoVectorEquivMatrix` identifies the quadratic space with two-by-two
  matrices, carrying the quadratic form to the determinant.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §4.
* M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions* (1998), §8.
-/

public section

open scoped Matrix TensorProduct

namespace TauCeti

/-! ## The quadratic space as two-by-two matrices -/

/-- The split four-dimensional real Clifford form in coordinates. -/
@[simp]
theorem realCliffordForm_two_two_apply (v : Fin 4 → ℝ) :
    realCliffordForm 2 2 v = v 0 ^ 2 + v 1 ^ 2 - v 2 ^ 2 - v 3 ^ 2 := by
  rw [realCliffordForm_apply, Fin.sum_univ_four]
  rw [realCliffordWeight_of_lt (p := 2) (q := 2) (i := (0 : Fin 4)) (by decide),
    realCliffordWeight_of_lt (p := 2) (q := 2) (i := (1 : Fin 4)) (by decide),
    realCliffordWeight_of_le (p := 2) (q := 2) (i := (2 : Fin 4)) (by decide),
    realCliffordWeight_of_le (p := 2) (q := 2) (i := (3 : Fin 4)) (by decide)]
  simp only [one_mul, neg_one_mul]
  ring

/-- The standard determinant model of the split quadratic space of signature `(2,2)`. The
coordinate convention is chosen compatibly with `realCliffordTwoTwoEvenEquivMatrixProd`, so the
two factors of the Spin group act by left and inverse-right multiplication. -/
noncomputable def realCliffordTwoTwoVectorEquivMatrix :
    (Fin 4 → ℝ) ≃ₗ[ℝ] Matrix (Fin 2) (Fin 2) ℝ where
  toFun v := !![-v 0 - v 2, -v 1 - v 3; v 1 - v 3, -v 0 + v 2]
  invFun A := ![-(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2,
    (A 1 1 - A 0 0) / 2, -(A 0 1 + A 1 0) / 2]
  map_add' v w := by
    ext i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp
    all_goals ring
  map_smul' r v := by
    ext i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp
    all_goals ring
  left_inv v := by
    funext i
    fin_cases i <;> simp
  right_inv A := by
    ext i j
    all_goals fin_cases i
    all_goals fin_cases j
    all_goals simp
    all_goals ring

/-- The matrix coordinates of a vector in the split four-dimensional real model. -/
@[simp]
theorem realCliffordTwoTwoVectorEquivMatrix_apply (v : Fin 4 → ℝ) :
    realCliffordTwoTwoVectorEquivMatrix v =
      !![-v 0 - v 2, -v 1 - v 3; v 1 - v 3, -v 0 + v 2] := (rfl)

/-- The vector coordinates recovered from a two-by-two real matrix. -/
@[simp]
theorem realCliffordTwoTwoVectorEquivMatrix_symm_apply
    (A : Matrix (Fin 2) (Fin 2) ℝ) :
    realCliffordTwoTwoVectorEquivMatrix.symm A =
      ![-(A 0 0 + A 1 1) / 2, (A 1 0 - A 0 1) / 2,
        (A 1 1 - A 0 0) / 2, -(A 0 1 + A 1 0) / 2] := (rfl)

/-- The determinant in the matrix model is the split quadratic form. -/
-- Keep this as a named rewrite: simplification first expands the matrix coordinates on its
-- left-hand side.
theorem realCliffordTwoTwoVectorEquivMatrix_det (v : Fin 4 → ℝ) :
    (realCliffordTwoTwoVectorEquivMatrix v).det = realCliffordForm 2 2 v := by
  rw [Matrix.det_fin_two, realCliffordForm_two_two_apply]
  simp
  ring

/-! ## The even Clifford algebra -/

private def prodTensorMatrixEquiv :
    (ℝ × ℝ) ⊗[ℝ] Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  (Algebra.TensorProduct.comm ℝ _ _).trans <|
    (Algebra.TensorProduct.prodRight ℝ ℝ _ ℝ ℝ).trans <|
      AlgEquiv.prodCongr
        (Algebra.TensorProduct.rid ℝ ℝ (Matrix (Fin 2) (Fin 2) ℝ))
        (Algebra.TensorProduct.rid ℝ ℝ (Matrix (Fin 2) (Fin 2) ℝ))

/-- The split algebra model `Cl(2,1) ≃ M₂(ℝ) × M₂(ℝ)`. -/
noncomputable def realCliffordTwoOneEquivMatrixProd :
    CliffordAlgebra (realCliffordForm 2 1) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  (realCliffordBottEquiv 1 0).trans <|
    (Algebra.TensorProduct.congr realCliffordOneZeroEquivProd
      (AlgEquiv.refl : Matrix (Fin 2) (Fin 2) ℝ ≃ₐ[ℝ] _)).trans prodTensorMatrixEquiv

private theorem realBottSplitIsometry_one_zero_apply (v : Fin (2 + 1) → ℝ) :
    realBottSplitIsometry 1 0 v = (![v 0], ![v 1, v 2]) := by
  apply Prod.ext
  · funext i
    fin_cases i
    simpa using realBottSplitIsometry_fst_pos 1 0 v (0 : Fin 1)
  · funext i
    fin_cases i
    · simpa using realBottSplitIsometry_snd_zero 1 0 v
    · simpa using realBottSplitIsometry_snd_one 1 0 v

/-- The matrix coordinates of a generator in the split model of `Cl(2,1)`. -/
@[simp]
theorem realCliffordTwoOneEquivMatrixProd_ι (v : Fin (2 + 1) → ℝ) :
    realCliffordTwoOneEquivMatrixProd (CliffordAlgebra.ι _ v) =
      (!![v 1, v 0 + v 2; v 0 - v 2, -v 1],
        !![v 1, -v 0 + v 2; -v 0 - v 2, -v 1]) := by
  simp only [realCliffordTwoOneEquivMatrixProd, AlgEquiv.trans_apply,
    realCliffordBottEquiv_ι, map_add, Algebra.TensorProduct.congr_apply,
    Algebra.TensorProduct.map_tmul, map_one, prodTensorMatrixEquiv]
  rw [realBottSplitIsometry_one_zero_apply]
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Algebra.TensorProduct.prodRight_tmul] <;> ring

private theorem realCliffordTwoOneEquivMatrixProd_ι_trace
    (v : Fin (2 + 1) → ℝ) :
    (realCliffordTwoOneEquivMatrixProd (CliffordAlgebra.ι _ v)).1.trace = 0 ∧
      (realCliffordTwoOneEquivMatrixProd (CliffordAlgebra.ι _ v)).2.trace = 0 := by
  simp [Matrix.trace, Fin.sum_univ_two]

/-- In the split matrix model of `Cl(2,1)`, Clifford conjugation is matrix adjugation in each
factor. -/
@[simp]
theorem realCliffordTwoOneEquivMatrixProd_star
    (x : CliffordAlgebra (realCliffordForm 2 1)) :
    realCliffordTwoOneEquivMatrixProd (star x) =
      (Matrix.adjugate (realCliffordTwoOneEquivMatrixProd x).1,
        Matrix.adjugate (realCliffordTwoOneEquivMatrixProd x).2) := by
  induction x using CliffordAlgebra.induction with
  | algebraMap r =>
      ext i j <;> fin_cases i <;> fin_cases j <;>
        simp [Algebra.algebraMap_eq_smul_one,
          Matrix.adjugate_fin_two_eq_trace_smul_one_sub, Matrix.trace] <;> ring
  | ι v =>
      rw [CliffordAlgebra.star_ι, map_neg]
      obtain ⟨h₁, h₂⟩ := realCliffordTwoOneEquivMatrixProd_ι_trace v
      rw [Matrix.adjugate_fin_two_eq_trace_smul_one_sub,
        Matrix.adjugate_fin_two_eq_trace_smul_one_sub, h₁, h₂]
      simp
  | add x y hx hy =>
      simp only [star_add, map_add, hx, hy, Prod.fst_add, Prod.snd_add]
      apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;> simp <;> ring
  | mul x y hx hy =>
      simp only [star_mul, map_mul, hx, hy, Prod.fst_mul, Prod.snd_mul,
        Matrix.adjugate_mul_distrib]
      rfl

private def realCliffordZeroOneNegativeSqIsometry :
    (realCliffordForm 0 1).IsometryEquiv
      ((↑(-1 : ℝˣ) : ℝ) • QuadraticMap.sq) where
  toLinearEquiv := LinearEquiv.funUnique (Fin 1) ℝ ℝ
  map_app' v := by
    simp [realCliffordForm_zero_one_apply, QuadraticMap.sq_apply]

private noncomputable def realCliffordTwoTwoAugmentedIsometry :
    (realCliffordForm 2 2).IsometryEquiv
      ((realCliffordForm 2 1).prod ((↑(-1 : ℝˣ) : ℝ) • QuadraticMap.sq)) :=
  (realCliffordSplitIsometry 2 0 1 1).trans
    ((QuadraticMap.IsometryEquiv.refl (realCliffordForm 2 1)).prod
      realCliffordZeroOneNegativeSqIsometry)

private theorem realCliffordTwoTwoAugmentedIsometry_apply (v : Fin (2 + 2) → ℝ) :
    realCliffordTwoTwoAugmentedIsometry v = (![v 0, v 1, v 2], v 3) := by
  apply Prod.ext
  · funext i
    fin_cases i
    · -- Expose the shared signature splitter hidden by the composed isometry.
      change (realCliffordSplitIsometry 2 0 1 1 v).1 0 = v 0
      convert realCliffordSplitIsometry_fst_pos 2 0 1 1 v (0 : Fin 2) using 1 <;> simp
    · -- Expose the shared signature splitter hidden by the composed isometry.
      change (realCliffordSplitIsometry 2 0 1 1 v).1 1 = v 1
      convert realCliffordSplitIsometry_fst_pos 2 0 1 1 v (1 : Fin 2) using 1 <;> simp
    · -- Expose the shared signature splitter hidden by the composed isometry.
      change (realCliffordSplitIsometry 2 0 1 1 v).1 2 = v 2
      convert realCliffordSplitIsometry_fst_neg 2 0 1 1 v (0 : Fin 1) using 1 <;> simp
  · -- Expose the one-dimensional isometry and the last coordinate of the signature splitter.
    change (realCliffordSplitIsometry 2 0 1 1 v).2 0 = v 3
    convert realCliffordSplitIsometry_snd_neg 2 0 1 1 v (0 : Fin 1) using 1 <;> simp

private def realCliffordTwoOneScaleIsometry :
    (-(↑(-1 : ℝˣ)⁻¹ : ℝ) • realCliffordForm 2 1).IsometryEquiv
      (realCliffordForm 2 1) where
  toLinearEquiv := LinearEquiv.refl ℝ _
  map_app' v := by norm_num

@[simp]
private theorem realCliffordTwoOneScaleIsometry_apply (v : Fin (2 + 1) → ℝ) :
    realCliffordTwoOneScaleIsometry v = v := rfl

private noncomputable def realCliffordTwoTwoEvenEquivTwoOne :
    CliffordAlgebra.even (realCliffordForm 2 2) ≃ₐ[ℝ]
      CliffordAlgebra (realCliffordForm 2 1) :=
  (CliffordAlgebra.evenEquivOfIsometry realCliffordTwoTwoAugmentedIsometry).trans <|
    (CliffordAlgebra.evenProdSMulSqEquiv (realCliffordForm 2 1) (-1)).trans <|
      CliffordAlgebra.equivOfIsometry realCliffordTwoOneScaleIsometry

private theorem realCliffordTwoTwoEvenEquivTwoOne_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 2 2)) :
    realCliffordTwoTwoEvenEquivTwoOne
        (CliffordAlgebra.reverseEven (realCliffordForm 2 2) x) =
      star (realCliffordTwoTwoEvenEquivTwoOne x) := by
  simp only [realCliffordTwoTwoEvenEquivTwoOne, AlgEquiv.trans_apply]
  rw [CliffordAlgebra.evenEquivOfIsometry_reverseEven,
    CliffordAlgebra.evenProdSMulSqEquiv_reverseEven,
    CliffordAlgebra.equivOfIsometry_apply, CliffordAlgebra.map_star]
  rfl

/-- The split even-algebra model `Cl⁺(2,2) ≃ M₂(ℝ) × M₂(ℝ)`. -/
noncomputable def realCliffordTwoTwoEvenEquivMatrixProd :
    CliffordAlgebra.even (realCliffordForm 2 2) ≃ₐ[ℝ]
      Matrix (Fin 2) (Fin 2) ℝ × Matrix (Fin 2) (Fin 2) ℝ :=
  realCliffordTwoTwoEvenEquivTwoOne.trans realCliffordTwoOneEquivMatrixProd

/-- The matrix coordinates of a product of two generators in the split model of `Cl⁺(2,2)`. -/
@[simp]
theorem realCliffordTwoTwoEvenEquivMatrixProd_ι (m n : Fin (2 + 2) → ℝ) :
    realCliffordTwoTwoEvenEquivMatrixProd
        ((CliffordAlgebra.even.ι (realCliffordForm 2 2)).bilin m n) =
      (!![m 1 + m 3, m 0 + m 2; m 0 - m 2, -m 1 + m 3] *
          !![n 1 - n 3, n 0 + n 2; n 0 - n 2, -n 1 - n 3],
        !![m 1 + m 3, -m 0 + m 2; -m 0 - m 2, -m 1 + m 3] *
          !![n 1 - n 3, -n 0 + n 2; -n 0 - n 2, -n 1 - n 3]) := by
  simp only [realCliffordTwoTwoEvenEquivMatrixProd, AlgEquiv.trans_apply,
    realCliffordTwoTwoEvenEquivTwoOne, CliffordAlgebra.evenEquivOfIsometry_ι,
    realCliffordTwoTwoAugmentedIsometry_apply,
    CliffordAlgebra.evenProdSMulSqEquiv_ι, map_smul,
    CliffordAlgebra.equivOfIsometry_apply]
  apply Prod.ext <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [Algebra.algebraMap_eq_smul_one, Matrix.mul_apply, Fin.sum_univ_two]

/-- In the split matrix model of `Cl⁺(2,2)`, Clifford reversal is matrix adjugation in each
factor. -/
@[simp]
theorem realCliffordTwoTwoEvenEquivMatrixProd_reverseEven
    (x : CliffordAlgebra.even (realCliffordForm 2 2)) :
    realCliffordTwoTwoEvenEquivMatrixProd
        (CliffordAlgebra.reverseEven (realCliffordForm 2 2) x) =
      (Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).1,
        Matrix.adjugate (realCliffordTwoTwoEvenEquivMatrixProd x).2) := by
  rw [realCliffordTwoTwoEvenEquivMatrixProd, AlgEquiv.trans_apply,
    realCliffordTwoTwoEvenEquivTwoOne_reverseEven,
    realCliffordTwoOneEquivMatrixProd_star]
  rfl

/-- In the split matrix model of `Cl⁺(2,2)`, the reverse norm-one equation is determinant one in
both matrix factors. This concrete computation precedes generic multiplicative simplification. -/
@[simp high]
theorem realCliffordTwoTwo_reverseEven_mul_self_eq_one_iff_det_eq_one
    (x : CliffordAlgebra.even (realCliffordForm 2 2)) :
    CliffordAlgebra.reverseEven (realCliffordForm 2 2) x * x = 1 ↔
      (realCliffordTwoTwoEvenEquivMatrixProd x).1.det = 1 ∧
        (realCliffordTwoTwoEvenEquivMatrixProd x).2.det = 1 := by
  let A := (realCliffordTwoTwoEvenEquivMatrixProd x).1
  let B := (realCliffordTwoTwoEvenEquivMatrixProd x).2
  rw [← Matrix.adjugate_mul_self_eq_one_iff_det_eq_one A,
    ← Matrix.adjugate_mul_self_eq_one_iff_det_eq_one B]
  constructor
  · intro h
    have hm := congrArg realCliffordTwoTwoEvenEquivMatrixProd h
    rw [map_mul, map_one, realCliffordTwoTwoEvenEquivMatrixProd_reverseEven] at hm
    exact ⟨congrArg Prod.fst hm, congrArg Prod.snd hm⟩
  · rintro ⟨hA, hB⟩
    apply realCliffordTwoTwoEvenEquivMatrixProd.injective
    rw [map_mul, map_one, realCliffordTwoTwoEvenEquivMatrixProd_reverseEven]
    exact Prod.ext hA hB

end TauCeti
