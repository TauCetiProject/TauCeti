/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Wentao Li
-/
module

public import TauCeti.NumberTheory.IntegralLattice.Binary.NormForm
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
public import TauCeti.LinearAlgebra.IntegralLattice.PosDef.Minimum
import TauCeti.LinearAlgebra.IntegralLattice.StandardCoordinates

/-!
# The binary lattice of determinant 23

The lattice with Gram matrix `!![4, 1; 1, 6]` has minimum four and precisely two minimal
vectors, the first basis vector and its negative. Preserving these vectors and the pairing with
the second basis vector forces every integral automorphism to be the identity or negation.
Both preserve orientation. Thus its full and special orthogonal groups have order two.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, Section 2.
-/

public section

open Module Matrix

namespace TauCeti.IntegralLattice

private def determinant23Matrix : Matrix (Fin 2) (Fin 2) ℤ := !![4, 1; 1, 6]

private theorem determinant23Matrix_isSymm : determinant23Matrix.IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  fin_cases i <;> fin_cases j <;> rfl

/-- The integral binary lattice with Gram matrix `!![4, 1; 1, 6]`. -/
noncomputable def binaryDeterminant23 : IntegralLattice (Fin 2 → ℚ) :=
  ofGramMatrix (Pi.basisFun ℚ (Fin 2)) determinant23Matrix determinant23Matrix_isSymm

/-- The standard integral basis of the determinant-23 lattice. -/
noncomputable def binaryDeterminant23Basis : Basis (Fin 2) ℤ binaryDeterminant23 :=
  ofGramMatrix.basis (Pi.basisFun ℚ (Fin 2)) determinant23Matrix determinant23Matrix_isSymm

/-- The carrier basis is the standard coordinate basis. -/
@[simp] theorem coe_binaryDeterminant23Basis (i : Fin 2) :
    (binaryDeterminant23Basis i : Fin 2 → ℚ) = Pi.single i 1 := by
  exact (ofGramMatrix.coe_basis (Pi.basisFun ℚ (Fin 2)) determinant23Matrix
    determinant23Matrix_isSymm i).trans (Pi.basisFun_apply ℚ (Fin 2) i)

/-- The displayed matrix is the Gram matrix in the standard integral basis. -/
@[simp] theorem gramMatrix_binaryDeterminant23Basis :
    binaryDeterminant23.gramMatrix binaryDeterminant23Basis = !![4, 1; 1, 6] :=
  gramMatrix_ofGramMatrix _ _ _

/-- Vectors of the determinant-23 lattice have integral coordinates. -/
theorem mem_binaryDeterminant23_carrier_iff (x : Fin 2 → ℚ) :
    x ∈ binaryDeterminant23.carrier ↔ ∀ i, ∃ n : ℤ, (n : ℚ) = x i :=
  mem_ofGramMatrix_basisFun_carrier_iff _ _ x

/-- The bilinear form of the determinant-23 lattice in coordinates. -/
theorem binaryDeterminant23_form_apply (x y : Fin 2 → ℚ) :
    binaryDeterminant23.form x y =
      4 * x 0 * y 0 + x 0 * y 1 + x 1 * y 0 + 6 * x 1 * y 1 := by
  rw [binaryDeterminant23, form_ofGramMatrix_basisFun_apply]
  simp [determinant23Matrix, Fin.sum_univ_two]
  ring

/-- Its norm form is `4x² + 2xy + 6y²`. -/
@[simp] theorem binaryDeterminant23_binaryNormForm :
    binaryDeterminant23.binaryNormForm binaryDeterminant23Basis = ⟨4, 2, 6⟩ := by
  ext <;> simp only [binaryNormForm_a, binaryNormForm_b, binaryNormForm_c,
    gramMatrix_binaryDeterminant23Basis] <;> norm_num

/-- Its primitive norm form is `2x² + xy + 3y²`. -/
theorem binaryDeterminant23_primPart :
    (binaryDeterminant23.binaryNormForm binaryDeterminant23Basis).primPart = ⟨2, 1, 3⟩ := by
  rw [binaryDeterminant23_binaryNormForm]
  ext <;> norm_num [BinaryQuadraticForm.primPart_a, BinaryQuadraticForm.primPart_b,
    BinaryQuadraticForm.primPart_c, BinaryQuadraticForm.content_def]

/-- Its primitive discriminant is minus 23. -/
@[simp] theorem binaryDeterminant23_binaryDiscriminant :
    binaryDeterminant23.binaryDiscriminant (by simp) = -23 := by
  rw [binaryDiscriminant_eq_discrim_primPart _ binaryDeterminant23Basis,
    binaryDeterminant23_primPart]
  norm_num [BinaryQuadraticForm.discrim_def, discrim]

/-- Its Gram determinant is 23. -/
@[simp] theorem binaryDeterminant23_determinant : binaryDeterminant23.determinant = 23 := by
  rw [determinant_eq_gramDet _ binaryDeterminant23Basis, gramDet_def,
    gramMatrix_binaryDeterminant23Basis]
  norm_num [Matrix.det_fin_two]

/-- The lattice is nondegenerate. -/
instance : binaryDeterminant23.IsNondegenerate :=
  ⟨binaryDeterminant23.determinant_ne_zero_iff.mp (by simp)⟩

/-- The lattice is positive definite. -/
theorem binaryDeterminant23_isPosDef : binaryDeterminant23.IsPosDef := by
  rw [isPosDef_iff]
  intro x hx
  rw [binaryDeterminant23_form_apply]
  have hx' : x 0 ≠ 0 ∨ x 1 ≠ 0 := by
    by_contra! h
    apply hx
    ext i
    fin_cases i <;> simp [h]
  rcases hx' with h | h
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 1)]
  · have := sq_pos_of_ne_zero h
    nlinarith [sq_nonneg (x 0 + x 1), sq_nonneg (x 0)]

private theorem norm_four_iff (x y : ℤ) :
    4 * x ^ 2 + 2 * x * y + 6 * y ^ 2 = 4 ↔
      (x = 1 ∨ x = -1) ∧ y = 0 := by
  constructor
  · intro h
    have hy : y ^ 2 < 1 := by nlinarith [sq_nonneg (2 * x + y)]
    have hy₀ : y ^ 2 = 0 := by have := sq_nonneg y; omega
    have hy' := sq_eq_zero_iff.mp hy₀
    subst y
    have hx : x ^ 2 = 1 := by nlinarith [h]
    exact ⟨sq_eq_one_iff.mp hx, rfl⟩
  · rintro ⟨h | h, rfl⟩ <;> simp [h]

/-- The integral norm in the standard carrier coordinates. -/
theorem binaryDeterminant23_integralNorm (x : binaryDeterminant23) :
    binaryDeterminant23.integralNorm x =
      4 * (binaryDeterminant23Basis.repr x 0) ^ 2 +
        2 * binaryDeterminant23Basis.repr x 0 * binaryDeterminant23Basis.repr x 1 +
        6 * (binaryDeterminant23Basis.repr x 1) ^ 2 := by
  have hx := binaryDeterminant23Basis.sum_repr x
  rw [Fin.sum_univ_two] at hx
  conv_lhs => rw [← hx, ← eval_binaryNormForm, binaryDeterminant23_binaryNormForm,
    BinaryQuadraticForm.eval_mk]

/-- The only norm-four vectors are the first basis vector and its negative. -/
theorem binaryDeterminant23_integralNorm_eq_four_iff (x : binaryDeterminant23) :
    binaryDeterminant23.integralNorm x = 4 ↔
      x = binaryDeterminant23Basis 0 ∨ x = -binaryDeterminant23Basis 0 := by
  rw [binaryDeterminant23_integralNorm, norm_four_iff]
  constructor
  · rintro ⟨h | h, h₁⟩
    · left
      apply binaryDeterminant23Basis.repr.injective
      ext i
      fin_cases i <;> simp [h, h₁]
    · right
      apply binaryDeterminant23Basis.repr.injective
      ext i
      fin_cases i <;> simp [h, h₁]
  · rintro (rfl | rfl) <;> simp

/-- The norm-four shell is the pair consisting of the first basis vector and its negative. -/
theorem binaryDeterminant23_vectorsOfNorm_four :
    binaryDeterminant23.vectorsOfNorm 4 =
      {binaryDeterminant23Basis 0, -binaryDeterminant23Basis 0} := by
  ext x
  have h := binaryDeterminant23.mem_vectorsOfNorm_intCast (n := 4) (x := x)
  norm_num only [Int.cast_ofNat] at h
  rw [h,
    binaryDeterminant23_integralNorm_eq_four_iff, Set.mem_insert_iff, Set.mem_singleton_iff]

/-- Every nonzero lattice vector has norm at least four. -/
theorem binaryDeterminant23_four_le_integralNorm {x : binaryDeterminant23} (hx : x ≠ 0) :
    4 ≤ binaryDeterminant23.integralNorm x := by
  rw [binaryDeterminant23_integralNorm]
  let m := binaryDeterminant23Basis.repr x 0
  let n := binaryDeterminant23Basis.repr x 1
  -- Fold the carrier coordinates into the local names used by the case split.
  change 4 ≤ 4 * m ^ 2 + 2 * m * n + 6 * n ^ 2
  by_cases hn : n = 0
  · have hm : m ≠ 0 := by
      intro hm
      apply hx
      apply binaryDeterminant23Basis.repr.injective
      ext i
      fin_cases i <;> simp_all [m, n]
    have hm' : 1 ≤ m ^ 2 := by have := sq_pos_of_ne_zero hm; omega
    simp only [hn, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero]
    linarith
  · have hn' : 1 ≤ n ^ 2 := by have := sq_pos_of_ne_zero hn; omega
    nlinarith [sq_nonneg m, sq_nonneg (m + n)]

/-- The minimum of the determinant-23 lattice is four. -/
@[simp] theorem binaryDeterminant23_minimum : binaryDeterminant23.minimum = 4 := by
  have : Nontrivial binaryDeterminant23 :=
    ⟨⟨binaryDeterminant23Basis 0, 0, binaryDeterminant23Basis.ne_zero 0⟩⟩
  have hp := binaryDeterminant23_isPosDef.isPosSemidef
  obtain ⟨x, hx, hmin⟩ := hp.exists_ne_zero_integralNorm_eq_minimum
  have hlo := binaryDeterminant23_four_le_integralNorm hx
  rw [hmin] at hlo
  have hhi := hp.minimum_le_integralNorm (binaryDeterminant23Basis.ne_zero 0)
  have hnorm := (binaryDeterminant23_integralNorm_eq_four_iff
    (binaryDeterminant23Basis 0)).mpr (Or.inl rfl)
  rw [hnorm] at hhi
  omega

/-- The minimal shell consists exactly of the two opposite first basis vectors. -/
theorem binaryDeterminant23_vectorsOfNorm_minimum :
    binaryDeterminant23.vectorsOfNorm binaryDeterminant23.minimum =
      {binaryDeterminant23Basis 0, -binaryDeterminant23Basis 0} := by
  rw [binaryDeterminant23_minimum]
  exact binaryDeterminant23_vectorsOfNorm_four

private theorem integralForm_first (x : binaryDeterminant23) :
    binaryDeterminant23.integralForm (binaryDeterminant23Basis 0) x =
      4 * binaryDeterminant23Basis.repr x 0 + binaryDeterminant23Basis.repr x 1 := by
  have hx := binaryDeterminant23Basis.sum_repr x
  rw [Fin.sum_univ_two] at hx
  conv_lhs => rw [← hx]
  simp only [map_add, map_smul, smul_eq_mul, ← gramMatrix_apply,
    gramMatrix_binaryDeterminant23Basis]
  norm_num
  ring

private theorem isometry_eq_one_of_first_basis
    (e : Isometry binaryDeterminant23 binaryDeterminant23)
    (he : e.carrierEquiv (binaryDeterminant23Basis 0) = binaryDeterminant23Basis 0) : e = 1 := by
  let x := e.carrierEquiv (binaryDeterminant23Basis 1)
  let m := binaryDeterminant23Basis.repr x 0
  let n := binaryDeterminant23Basis.repr x 1
  have hp : 4 * m + n = 1 := by
    rw [← integralForm_first, ← he, Isometry.carrierEquiv_map_integralForm]
    norm_num [← gramMatrix_apply, gramMatrix_binaryDeterminant23Basis]
  have hN : 4 * m ^ 2 + 2 * m * n + 6 * n ^ 2 = 6 := by
    rw [← binaryDeterminant23_integralNorm]
    simp only [x, integralNorm_apply, Isometry.carrierEquiv_map_integralForm]
    norm_num [← gramMatrix_apply, gramMatrix_binaryDeterminant23Basis]
  have hn : n = 1 - 4 * m := by linarith
  have hm : m = 0 := by
    have hprod : m * (2 * m - 1) = 0 := by rw [hn] at hN; nlinarith [hN]
    rcases mul_eq_zero.mp hprod with hm | hm
    · exact hm
    · omega
  have hn' : n = 1 := by omega
  have hx : x = binaryDeterminant23Basis 1 := by
    apply binaryDeterminant23Basis.repr.injective
    ext i
    fin_cases i <;> simp_all [m, n]
  apply Isometry.carrierEquiv_injective
  apply binaryDeterminant23Basis.ext'
  rw [Fin.forall_fin_two]
  simp only [Isometry.one_def, Isometry.carrierEquiv_refl, LinearEquiv.refl_apply]
  exact ⟨he, hx⟩

/-- The full integral isometry group consists of the identity and negation. -/
theorem binaryDeterminant23_isometry_eq (e : Isometry binaryDeterminant23 binaryDeterminant23) :
    e = 1 ∨ e = Isometry.neg binaryDeterminant23 := by
  have hN : binaryDeterminant23.integralNorm
      (e.carrierEquiv (binaryDeterminant23Basis 0)) = 4 := by
    simp only [integralNorm_apply, Isometry.carrierEquiv_map_integralForm]
    norm_num [← gramMatrix_apply, gramMatrix_binaryDeterminant23Basis]
  rcases (binaryDeterminant23_integralNorm_eq_four_iff _).mp hN with h | h
  · exact Or.inl (isometry_eq_one_of_first_basis e h)
  · right
    have he : Isometry.neg binaryDeterminant23 * e = 1 := by
      apply isometry_eq_one_of_first_basis
      simp only [Isometry.mul_def, Isometry.carrierEquiv_trans, LinearEquiv.trans_apply,
        Isometry.carrierEquiv_neg, LinearEquiv.neg_apply, h, neg_neg]
    exact mul_left_cancel (he.trans (Isometry.neg_mul_neg binaryDeterminant23).symm)

/-- The full integral isometry group of the determinant-23 lattice has order two. -/
theorem card_isometry_binaryDeterminant23 :
    Nat.card (Isometry binaryDeterminant23 binaryDeterminant23) = 2 := by
  refine Nat.card_eq_two_iff.mpr ⟨1, Isometry.neg binaryDeterminant23, ?_, ?_⟩
  · intro h
    have h' := congrArg (fun e : Isometry binaryDeterminant23 binaryDeterminant23 ↦
      e (binaryDeterminant23Basis 0 : Fin 2 → ℚ) 0) h
    norm_num [coe_binaryDeterminant23Basis, Pi.single_apply] at h'
  · ext e
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    exact binaryDeterminant23_isometry_eq e

/-- All automorphisms of the determinant-23 lattice preserve orientation. -/
theorem specialOrthogonalGroup_binaryDeterminant23_eq_top :
    specialOrthogonalGroup binaryDeterminant23 = ⊤ := by
  apply top_unique
  intro e _
  rw [mem_specialOrthogonalGroup_iff]
  rcases binaryDeterminant23_isometry_eq e with rfl | rfl
  · exact (Isometry.det binaryDeterminant23).map_one
  · rw [Isometry.det_neg, finrank_carrier]
    norm_num

/-- The special orthogonal group of the determinant-23 lattice has order two. -/
theorem card_specialOrthogonalGroup_binaryDeterminant23 :
    Nat.card (specialOrthogonalGroup binaryDeterminant23) = 2 := by
  rw [specialOrthogonalGroup_binaryDeterminant23_eq_top, Subgroup.card_top]
  exact card_isometry_binaryDeterminant23

/-- Its special orthogonal group has index one in the full isometry group. -/
theorem index_specialOrthogonalGroup_binaryDeterminant23 :
    (specialOrthogonalGroup binaryDeterminant23).index = 1 := by
  rw [specialOrthogonalGroup_binaryDeterminant23_eq_top, Subgroup.index_top]

end TauCeti.IntegralLattice
