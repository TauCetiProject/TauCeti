/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.GradedModuleCat.Betti.Cartan
public import TauCeti.RepresentationTheory.Quiver.Kronecker.A2.Basic
public import TauCeti.RepresentationTheory.Quiver.PathAlgebra.GradedExtEuler.Pairing
import TauCeti.Algebra.Polynomial.Laurent.Coeff

/-!
# Graded Cartan, Betti, and Euler conventions for the one-arrow quiver

Give the path algebra of `1 ⟶ 2` its path-length grading and order the vertices source first.
Its graded Cartan matrix is `[1, 0; q, 1]`: the source projective has a degree-zero source
simple and a degree-one target simple. The categorical q-Euler matrix of the vertex simples
is `[1, -q⁻¹; 0, 1]`, not `[1, -q; 0, 1]`, because the pairing is q-antilinear in its first
variable. These matrices are inverse conjugate transposes.

In the vertex-projective basis, the linear first-arrow resolutions `0 ⟶ P₂{1} ⟶ P₁ ⟶ S₁ ⟶ 0`
and `0 ⟶ 0 ⟶ P₂ ⟶ S₂ ⟶ 0` assemble into the Betti Poincaré matrix `[1, 0; qt, 1]`, supported on
the Koszul diagonal `d = n`. Evaluating at `t = -1` produces `[1, 0; -q, 1]`, the direct inverse
of `[1, 0; q, 1]` under `C(q) · B(q, -1) = I`.

The results below identify these displayed matrices with the actual Laurent Grothendieck-group
and Betti Poincaré constructions, compute the two columns of the graded Cartan map, and recover
the ordinary Cartan and Euler matrices by evaluation at `q = 1`. The Euler-form identification
uses the finite-support Ext computation from the first-arrow resolutions, not a totalized
infinite sum.

## References

* I. Assem, D. Simson and A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras I*, Chapter III, Sections 2--3, for the projective resolutions and Cartan conventions.
* Z. Dancso and A. Licata, *Koszul algebras and flow lattices*, Section 2.2, for the graded
  Cartan matrix and the q-antilinear convention for the Euler form.
* A. Beilinson, V. Ginzburg and W. Soergel, *Koszul duality patterns in representation theory*,
  *Journal of the AMS* **9** (1996), Sections 1.2 and 2.11, for linear resolutions and `B(q, t)`.
-/

public section

noncomputable section

namespace TauCeti.Quiver.Kronecker

open CategoryTheory LaurentPolynomial
open scoped Matrix

universe u v

/-- The path-length-graded Cartan matrix of `1 ⟶ 2`, with simples in the rows and projectives
in the columns, in source-first order. -/
def gradedCartanMatrixA2 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, 0; T 1, 1]

/-- The entries of the graded Cartan matrix of `1 ⟶ 2`. -/
@[simp]
theorem gradedCartanMatrixA2_apply (i j : Fin 2) :
    gradedCartanMatrixA2 i j = !![1, 0; T 1, 1] i j := by
  rw [gradedCartanMatrixA2]

/-- The q-Euler matrix of `1 ⟶ 2`, q-antilinear in the row variable and q-linear in the
column variable, in source-first order. -/
def gradedEulerMatrixA2 : Matrix (Fin 2) (Fin 2) (LaurentPolynomial ℤ) :=
  !![1, -T (-1); 0, 1]

/-- The entries of the q-Euler matrix of `1 ⟶ 2`. -/
@[simp]
theorem gradedEulerMatrixA2_apply (i j : Fin 2) :
    gradedEulerMatrixA2 i j = !![1, -T (-1); 0, 1] i j := by
  rw [gradedEulerMatrixA2]

/-- The graded Betti Poincaré matrix `[1, 0; qt, 1]` of the vertex simples of `1 ⟶ 2` in the
vertex-projective basis, in source-first order. -/
def bettiPoincareMatrixA2 :
    Matrix (Fin 2) (Fin 2) (PowerSeries (LaurentPolynomial ℤ)) :=
  !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1]

/-- The entries of the graded Betti Poincaré matrix of `1 ⟶ 2`. -/
@[simp]
theorem bettiPoincareMatrixA2_apply (i j : Fin 2) :
    bettiPoincareMatrixA2 i j = !![1, 0; PowerSeries.C (T 1) * PowerSeries.X, 1] i j := by
  rw [bettiPoincareMatrixA2]

/-- Every nonzero coefficient of `bettiPoincareMatrixA2` lies on the Koszul diagonal `d = n`. -/
theorem coeff_coeff_bettiPoincareMatrixA2_eq_zero_of_ne (i j : Fin 2) {n : ℕ} {d : ℤ}
    (hd : d ≠ n) : (PowerSeries.coeff n (bettiPoincareMatrixA2 i j)).coeff d = 0 := by
  have hT1 : (T 1 : LaurentPolynomial ℤ).coeff d = if d - 1 = 0 then 1 else 0 := by
    rw [← mul_one (T 1 : LaurentPolynomial ℤ), coeff_T_mul, coeff_one]
  fin_cases i <;> fin_cases j <;> rcases n with _ | (_ | n) <;>
    simp [PowerSeries.coeff_zero_eq_constantCoeff, PowerSeries.coeff_X, hT1] <;> omega

/-- The conjugate transpose of the graded Cartan matrix is a left inverse of the q-Euler
matrix. The coefficient involution is `LaurentPolynomial.invert`. -/
@[simp]
theorem gradedCartanMatrixA2_map_invert_transpose_mul_gradedEulerMatrixA2 :
    (gradedCartanMatrixA2.map (invert (R := ℤ)))ᵀ * gradedEulerMatrixA2 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

/-- The q-Euler matrix is also a left inverse of the conjugate-transposed graded Cartan
matrix. -/
@[simp]
theorem gradedEulerMatrixA2_mul_gradedCartanMatrixA2_map_invert_transpose :
    gradedEulerMatrixA2 * (gradedCartanMatrixA2.map (invert (R := ℤ)))ᵀ = 1 :=
  mul_eq_one_comm.mp gradedCartanMatrixA2_map_invert_transpose_mul_gradedEulerMatrixA2

/-- Setting `q = 1` in the graded Cartan matrix gives the ordinary Cartan matrix. -/
@[simp]
theorem map_laurentEval_one_gradedCartanMatrixA2 :
    gradedCartanMatrixA2.map (laurentEval (1 : ℤˣ)) = cartanMatrixA2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- Setting `q = 1` in the q-Euler matrix gives the ordinary Euler matrix. -/
@[simp]
theorem map_laurentEval_one_gradedEulerMatrixA2 :
    gradedEulerMatrixA2.map (laurentEval (1 : ℤˣ)) = eulerMatrixA2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp

variable {A : Type v} [Unique A] (k : Type u) [Field k]

/-- The categorical graded Cartan matrix of the one-arrow path algebra is `[1, 0; q, 1]`.
In particular, the off-diagonal multiplicity is a positive, not a negative, internal shift. -/
theorem submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 :
    (gradedCartanMatrix (PathAlgebra.integerGrade k (Kronecker A))
      (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A))).submatrix
        ![src, tgt] ![src, tgt] = gradedCartanMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  -- Read the two rows of the path-counting identity `(1 - q Aᵀ) C = 1`. Keep the
  -- categorical matrix opaque to simp, so that only this triangular system is solved.
  have h := PathAlgebra.one_sub_T_smul_transpose_mul_gradedCartanMatrix_eq_one k (Kronecker A)
  refine Matrix.ext fun i j => ?_
  have hs := congrFun₂ h src (![src, tgt] j)
  have ht := congrFun₂ h tgt (![src, tgt] j)
  fin_cases i <;> fin_cases j <;>
    simp [-gradedCartanMatrix_apply, Matrix.mul_apply, Matrix.one_apply,
      sum_univ, Nat.card_eq_fintype_card, Function.swap] at hs ht ⊢ <;>
    simp_all [-gradedCartanMatrix_apply]
  -- Only entry (1, 0) remains: `ht` gives its value via `-q + C₁₀ = 0`.
  -- Simplification does not rearrange this additive equation, so solve it linearly.
  linear_combination ht

/-- Each graded vertex-projective class maps to the corresponding column of the graded
Cartan matrix, expressed in the source-first vertex-simple basis. -/
theorem gradedCartanMap_gradedVertexProjectiveClass (j : Fin 2) :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) (![src, tgt] j)) =
      gradedCartanMatrixA2 0 j •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) src +
        gradedCartanMatrixA2 1 j •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
  have h := gradedCartanMap_basis_apply_eq_sum (PathAlgebra.integerGrade k (Kronecker A))
    (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
    (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A)) (![src, tgt] j)
  rw [PathAlgebra.gradedVertexProjectiveClassBasis_apply] at h
  rw [h]
  have hs := congrFun₂ (submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 (A := A) k) 0 j
  have ht := congrFun₂ (submatrix_gradedCartanMatrix_eq_gradedCartanMatrixA2 (A := A) k) 1 j
  simp only [Matrix.submatrix_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at hs ht
  rw [sum_univ, hs, ht]

/-- The graded Cartan map sends the source projective to `[S₁] + q[S₂]`. This is an equality
of classes in the actual Laurent Grothendieck group of finite graded path-algebra modules. -/
theorem gradedCartanMap_gradedVertexProjectiveClass_src :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) src) =
      PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) src +
        (T 1 : LaurentPolynomial ℤ) •
          PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  simpa using gradedCartanMap_gradedVertexProjectiveClass (A := A) k 0

/-- The graded Cartan map sends the target projective to `[S₂]`, without an internal shift. -/
theorem gradedCartanMap_gradedVertexProjectiveClass_tgt :
    gradedCartanMap (PathAlgebra.integerGrade k (Kronecker A))
        (PathAlgebra.gradedVertexProjectiveClass k (Kronecker A) tgt) =
      PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) tgt := by
  simpa using gradedCartanMap_gradedVertexProjectiveClass (A := A) k 1

private instance uniqueArrowFromSrc : Unique ((j : Kronecker A) × ((src : Kronecker A) ⟶ j)) where
  default := ⟨tgt, arrow default⟩
  uniq := fun ⟨b, f⟩ => by
    cases b with
    | src => exact ((inferInstance : IsEmpty ((src : Kronecker A) ⟶ src)).false f).elim
    | tgt => congr; rw [arrow_def]; exact Unique.eq_default f

private instance isEmptyArrowFromTgt :
    IsEmpty ((j : Kronecker A) × ((tgt : Kronecker A) ⟶ j)) where
  false := fun ⟨b, f⟩ => (isEmpty_hom_from_tgt b).false f

/-- In homological degree `1`, the Betti polynomial of the source vertex simple is `q` along `P₂`
and `0` along `P₁`. -/
private theorem coeff_one_bettiPoincareSeries_src (i : Fin 2) :
    let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
    let _ : Fintype A := Unique.fintype
    PowerSeries.coeff 1
      ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A) src).bettiPoincareSeries
        (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A)) (![src, tgt] i)) =
      PowerSeries.coeff 1 (bettiPoincareMatrixA2 i 0) := by
  let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
  let _ : Fintype A := Unique.fintype
  dsimp only
  rw [GradedProjectiveResolution.coeff_bettiPoincareSeries]
  let Ptgt : (gradedFiniteProjectiveModules
      (PathAlgebra.integerGrade k (Kronecker A))).FullSubcategory :=
    ⟨PathAlgebra.gradedVertexProjective k (Kronecker A) tgt,
      PathAlgebra.gradedFiniteProjectiveModules_gradedVertexProjective _ _ _⟩
  let eArrow : PathAlgebra.gradedArrowSum k (Kronecker A) src ≅ Ptgt.obj.shiftObj 1 :=
    GradedModuleCat.directSumObjIsoOfUnique fun a : (x : Kronecker A) × (src ⟶ x) =>
      (PathAlgebra.gradedVertexProjective k (Kronecker A) a.1).shiftObj 1
  let eTerm : ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
      src).finiteProjectiveTerm 1) ≅
      ⟨Ptgt.obj.shiftObj 1, gradedFiniteProjectiveModules_shiftObj Ptgt.property 1⟩ :=
    ObjectProperty.isoMk _ (eqToIso
      (((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
        src).finiteProjectiveTerm_obj 1).trans
        (PathAlgebra.gradedVertexSimpleProjectiveResolution_termObj_one _ _ _)) ≪≫ eArrow)
  rw [LaurentK0.of_congr.{max u v} _ eTerm, laurentK0_projective_of_shiftObj,
    ← PathAlgebra.gradedVertexProjectiveClass_eq,
    ← PathAlgebra.gradedVertexProjectiveClassBasis_apply, LinearEquiv.map_smul,
    Module.Basis.repr_self]
  fin_cases i <;> simp [src_ne_tgt]

/-- **The Betti Poincaré matrix of the vertex simples of `1 ⟶ 2` is `[1, 0; qt, 1]`.**
This computes `B(q, t)` directly from the linear first-arrow resolutions in the vertex-projective
basis, ordered source first, without assuming `HasExt`. -/
theorem submatrix_bettiPoincareMatrix_eq_bettiPoincareMatrixA2 :
    let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
    let _ : Fintype A := Unique.fintype
    (bettiPoincareMatrix (PathAlgebra.gradedVertexProjectiveClassBasis k (Kronecker A))
      (fun v : Kronecker A =>
        PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A) v)).submatrix
        ![src, tgt] ![src, tgt] = bettiPoincareMatrixA2 := by
  let _ := PathAlgebra.integerGradedAlgebra k (Kronecker A)
  let _ : Fintype A := Unique.fintype
  have : Finite A := Finite.of_fintype A
  refine Matrix.ext fun (i : Fin 2) (j : Fin 2) => PowerSeries.ext fun n => ?_
  rw [Matrix.submatrix_apply, bettiPoincareMatrix_apply]
  match n with
  | 0 =>
    rw [GradedProjectiveResolution.coeff_bettiPoincareSeries]
    have h0 : ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
        (![src, tgt] j)).finiteProjectiveTerm 0) =
        ⟨PathAlgebra.gradedVertexProjective k (Kronecker A) (![src, tgt] j),
          PathAlgebra.gradedFiniteProjectiveModules_gradedVertexProjective _ _ _⟩ :=
      ObjectProperty.FullSubcategory.ext
        (((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
          (![src, tgt] j)).finiteProjectiveTerm_obj 0).trans
          (PathAlgebra.gradedVertexSimpleProjectiveResolution_termObj_zero _ _ _))
    rw [h0, ← PathAlgebra.gradedVertexProjectiveClass_eq,
      ← PathAlgebra.gradedVertexProjectiveClassBasis_apply, Module.Basis.repr_self]
    fin_cases i <;> fin_cases j <;>
      simp [PowerSeries.coeff_zero_eq_constantCoeff, src_ne_tgt]
  | 1 =>
    rcases j with ⟨_ | ⟨_ | j⟩, hj⟩
    · exact coeff_one_bettiPoincareSeries_src k i
    · have htgt : (![src, tgt] ⟨1, hj⟩ : Kronecker A) = tgt := rfl
      have hsub : Subsingleton ((PathAlgebra.gradedVertexSimpleProjectiveResolution k (Kronecker A)
          tgt).X 1) :=
        PathAlgebra.gradedVertexSimpleProjectiveResolution_X_one k (Kronecker A) tgt ▸
          inferInstanceAs (Subsingleton
            (DirectSum ((x : Kronecker A) × ((tgt : Kronecker A) ⟶ x)) _))
      rw [htgt, GradedProjectiveResolution.coeff_bettiPoincareSeries_eq_zero_of_subsingleton
        _ _ _ hsub]
      fin_cases i <;> simp
    · omega
  | n + 2 =>
    have hsub := PathAlgebra.subsingleton_gradedVertexSimpleProjectiveResolution_X_of_two_le
      k (Kronecker A) (![src, tgt] j) (n := n + 2) (by omega)
    rw [GradedProjectiveResolution.coeff_bettiPoincareSeries_eq_zero_of_subsingleton _ _ _ hsub]
    fin_cases i <;> fin_cases j <;> simp

/-- **The alternating Cartan–Betti identity `C(q) · B(q, -1) = I` on `1 ⟶ 2`.** Evaluating
`bettiPoincareMatrixA2` at `t = -1` produces `[1, 0; -q, 1]`, which inverts `gradedCartanMatrixA2`
directly (without taking a conjugate transpose). -/
theorem gradedCartanMatrixA2_mul_alternatingBettiA2 :
    gradedCartanMatrixA2 *
      (Matrix.of fun i j : Fin 2 =>
        ∑ n ∈ Finset.range 2,
          (-1 : LaurentPolynomial ℤ) ^ n * PowerSeries.coeff n (bettiPoincareMatrixA2 i j)) =
      1 := by
  refine Matrix.ext fun i j => ?_
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Finset.sum_range_succ,
      PowerSeries.coeff_zero_eq_constantCoeff]

variable [HasExt.{max u v}
  (GradedModuleCat.{max u v} (PathAlgebra.integerGrade k (Kronecker A)))]

/-- The categorical q-Euler form of the vertex-simple classes has matrix `[1, -q⁻¹; 0, 1]`.
This computes the pairing from the graded Ext groups, with their proved finiteness and support. -/
theorem gradedExtEulerForm_A2_eq :
    (fun i j : Fin 2 ↦ PathAlgebra.gradedExtEulerForm k (Kronecker A)
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) (![src, tgt] i))
      (PathAlgebra.gradedVertexSimpleClassBasis k (Kronecker A) (![src, tgt] j))) =
        gradedEulerMatrixA2 := by
  let _ : Fintype A := Unique.fintype
  ext i j
  rw [PathAlgebra.gradedExtEulerForm_basis]
  fin_cases i <;> fin_cases j <;> simp [Nat.card_eq_fintype_card]

end TauCeti.Quiver.Kronecker
