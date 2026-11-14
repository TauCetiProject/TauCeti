/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.StarOrder
import TauCeti.Algebra.Star.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module

/-!
# Positivity in matrix C⋆-algebras by quadratic forms

For a non-unital C⋆-algebra `A` and a finite type `n`, Mathlib makes `CStarMatrix n n A` a
C⋆-algebra and orders it by the spectral order. This file proves that a matrix `M` is positive in
this order exactly when its finite quadratic forms are positive in `A`:

`0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j`.

No self-adjointness hypothesis is needed for the converse: positivity of all the quadratic forms
already forces `M` to be self-adjoint, by polarization over `ℂ`. The criterion is the standard way
to recognise positive matrices over a C⋆-algebra, for instance Gram matrices of vectors in a
Hilbert C⋆-module. Specializing `A` to `H →L[ℂ] H` for a complex Hilbert space `H` characterizes
positivity of operator matrices by nonnegativity of all vector quadratic forms
`∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ`.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an
  ordinary matrix respects multiplication and sends `star` to the conjugate transpose.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint. This is purely algebraic, and holds over any complex
  star-algebra whose star is proper.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity.
* `CStarMatrix.norm_sq_smul_sub_mulLeft_nonneg`: positivity of the matrix
  `(‖c‖ ^ 2 • (star (a i) * a j) - star (c * a i) * (c * a j))`.
* `CStarMatrix.nonneg_iff_forall_sum_inner_nonneg`: the vector quadratic-form criterion for
  positivity of operator matrices in `CStarMatrix n n (H →L[ℂ] H)`.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
* V. Paulsen, *Completely Bounded Maps and Operator Algebras*, Lemma 3.1.
-/

public section

open Matrix

namespace CStarMatrix

section Algebraic

variable {n R A : Type*}

/-- Scalars commute past matrix multiplication on the left, as for `Matrix`. -/
instance instIsScalarTowerSelf [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [IsScalarTower R A A] :
    IsScalarTower R (CStarMatrix n n A) (CStarMatrix n n A) :=
  ⟨fun r M N => smul_mul r M N⟩

/-- Scalars commute past matrix multiplication on the right, as for `Matrix`. -/
instance instSMulCommClassSelf [Fintype n] [Monoid R] [NonUnitalNonAssocSemiring A]
    [DistribMulAction R A] [SMulCommClass R A A] :
    SMulCommClass R (CStarMatrix n n A) (CStarMatrix n n A) :=
  ⟨fun r M N => (mul_smul M r N).symm⟩

/-- Reading a C⋆-matrix as an ordinary matrix respects multiplication. -/
@[simp]
lemma ofMatrix_symm_mul [Fintype n] [Mul A] [AddCommMonoid A] (M N : CStarMatrix n n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)

/-- A matrix over a complex star-algebra with proper star all of whose quadratic forms are
self-adjoint is self-adjoint. -/
theorem isSelfAdjoint_of_forall_isSelfAdjoint_sum [Fintype n] [NonUnitalRing A] [StarRing A]
    [Module ℂ A] [IsScalarTower ℂ A A] [SMulCommClass ℂ A A] [StarModule ℂ A] [IsProperStar A]
    {M : CStarMatrix n n A}
    (hM : ∀ x : n → A, IsSelfAdjoint (∑ i, ∑ j, star (x i) * M i j * x j)) :
    IsSelfAdjoint M := by
  classical
  replace hM (x : n → A) : IsSelfAdjoint (star x ⬝ᵥ (ofMatrix.symm M *ᵥ x)) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    exact hM x
  -- Polarization: the sesquilinear form `P x y` satisfies `star (P x y) = P y x`.
  have hP (x y : n → A) :
      star (star x ⬝ᵥ (ofMatrix.symm M *ᵥ y)) = star y ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    have h₁ := (hM (x + y)).star_eq
    have h₂ := (hM (x + Complex.I • y)).star_eq
    simp only [star_add, star_smul, star_neg, Complex.star_def, Complex.conj_I, mulVec_add,
      mulVec_smul, add_dotProduct, dotProduct_add, neg_dotProduct, smul_dotProduct,
      dotProduct_smul, neg_smul, (hM x).star_eq, (hM y).star_eq] at h₁ h₂
    linear_combination (norm := match_scalars) (1 / 2 : ℂ) • h₁ + (Complex.I / 2) • h₂ <;>
      simp [Complex.ext_iff] <;> norm_num
  refine ext fun i j => ?_
  apply sub_eq_zero.mp
  refine TauCeti.eq_zero_of_forall_star_mul_mul_eq_zero fun c d => ?_
  have := hP (Pi.single j c) (Pi.single i d)
  simp only [← Pi.single_star, single_dotProduct, mulVec_single, Pi.smul_apply, col_apply,
    MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op, star_mul, star_star,
    ofMatrix_symm_apply] at this
  rw [star_apply, mul_sub, sub_mul, this, mul_assoc, sub_self]

end Algebraic

section Nonneg

variable {n A : Type*} [Fintype n] [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-! The real continuous functional calculus of the C⋆-algebra `CStarMatrix n n A` is not found by
instance search, because the real scalar action on `CStarMatrix n n A` is the entrywise one rather
than the restriction of the complex action through which the general C⋆-algebra instances are
stated. The two actions agree definitionally, so we register the instances directly. -/

instance instNonUnitalContinuousFunctionalCalculusReal :
    NonUnitalContinuousFunctionalCalculus ℝ (CStarMatrix n n A) IsSelfAdjoint :=
  IsSelfAdjoint.instNonUnitalContinuousFunctionalCalculus

instance instNonnegSpectrumClassReal : NonnegSpectrumClass ℝ (CStarMatrix n n A) :=
  CStarAlgebra.instNonnegSpectrumClass'

/-- A matrix over a C⋆-algebra is positive exactly when all its finite quadratic forms are
positive. -/
theorem nonneg_iff_forall_sum_nonneg {M : CStarMatrix n n A} :
    0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j := by
  -- For `R`, the quadratic form of `star R * R` at `x` is `star (R x) ⬝ᵥ R x`.
  have key (R : CStarMatrix n n A) (x : n → A) :
      star x ⬝ᵥ (ofMatrix.symm (star R * R) *ᵥ x) =
        star (ofMatrix.symm R *ᵥ x) ⬝ᵥ (ofMatrix.symm R *ᵥ x) := by
    rw [ofMatrix_symm_mul, ofMatrix_symm_star, ← mulVec_mulVec, dotProduct_mulVec, star_mulVec]
  have hform (x : n → A) :
      ∑ i, ∑ j, star (x i) * M i j * x j = star x ⬝ᵥ (ofMatrix.symm M *ᵥ x) := by
    rw [dot_mulVec_eq_sum_sum, Finset.sum_comm]
    rfl
  simp_rw [hform]
  refine ⟨fun hM x => ?_, fun hQ => ?_⟩
  · obtain ⟨R, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hM
    rw [key]
    exact dotProduct_star_self_nonneg _
  have hsa : IsSelfAdjoint M := isSelfAdjoint_of_forall_isSelfAdjoint_sum fun x => by
    rw [hform]
    exact .of_nonneg (hQ x)
  -- It remains to show that the negative part `N` of `M` vanishes.
  refine CStarAlgebra.nonneg_iff_isSelfAdjoint_and_negPart_eq_zero.mpr ⟨hsa, ?_⟩
  set N := M⁻
  have hN : 0 ≤ N := CFC.negPart_nonneg M
  obtain ⟨R, hR⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hN
  have hMN : M * N = -(star R * R * N) := by
    conv_lhs => rw [← CFC.posPart_sub_negPart M hsa]
    rw [sub_mul, CFC.posPart_mul_negPart, zero_sub, ← hR]
  -- Evaluating the quadratic form at `N y` shows `R N y = 0` for every `y`.
  have hRN : R * N = 0 := by
    classical
    have hv (y : n → A) : ofMatrix.symm (R * N) *ᵥ y = 0 := by
      have hneg : ofMatrix.symm (-(star R * R * N)) = -ofMatrix.symm (star R * R * N) :=
        ofMatrix.symm_apply_eq.mpr (by rw [← neg_of, Equiv.apply_symm_apply])
      have h := hQ (ofMatrix.symm N *ᵥ y)
      rw [mulVec_mulVec, ← ofMatrix_symm_mul, hMN, hneg, neg_mulVec, dotProduct_neg,
        ofMatrix_symm_mul, ← mulVec_mulVec, key, Left.nonneg_neg_iff] at h
      rw [ofMatrix_symm_mul, ← mulVec_mulVec]
      exact dotProduct_star_self_eq_zero.mp (le_antisymm h (dotProduct_star_self_nonneg _))
    refine ext fun i j => ?_
    have h := congrFun (hv (Pi.single j (star ((R * N) i j)))) i
    simp only [mulVec_single, Pi.smul_apply, col_apply, MulOpposite.smul_eq_mul_unop,
      MulOpposite.unop_op, ofMatrix_symm_apply, Pi.zero_apply, mul_star_self_eq_zero] at h
    rw [h, zero_apply]
  rw [← star_mul_self_eq_zero, hN.star_eq]
  calc N * N = star R * (R * N) := by rw [← mul_assoc, ← hR]
    _ = 0 := by rw [hRN, mul_zero]

/-- For any `c : A` and finite family `a : n → A`, the matrix with `(i, j)`-entry
`‖c‖ ^ 2 • (star (a i) * a j) - star (c * a i) * (c * a j)` is positive in `CStarMatrix n n A`. -/
theorem norm_sq_smul_sub_mulLeft_nonneg (c : A) (a : n → A) :
    0 ≤ ofMatrix (Matrix.of fun i j =>
      ((‖c‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j) - star (c * a i) * (c * a j)) := by
  rw [nonneg_iff_forall_sum_nonneg]
  intro y
  let z : A := ∑ i, a i * y i
  have hsum₁ :
      ∑ i, ∑ j, star (y i) * (((‖c‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j)) * y j =
        (‖c‖ ^ 2 : ℝ) • (star z * z) := by
    simp only [z, ← Complex.coe_smul, mul_smul_comm, smul_mul_assoc, ← Finset.smul_sum,
      star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hsum₂ :
      ∑ i, ∑ j, star (y i) * (star (c * a i) * (c * a j)) * y j =
        star z * (star c * c) * z := by
    simp only [z, star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, mul_assoc]
    rw [Finset.sum_comm]
  have hident :
      ∑ i, ∑ j, star (y i) *
        (((‖c‖ ^ 2 : ℝ) : ℂ) • (star (a i) * a j) - star (c * a i) * (c * a j)) * y j =
        (‖c‖ ^ 2 : ℝ) • (star z * z) - star z * (star c * c) * z := by
    simp_rw [mul_sub, sub_mul, Finset.sum_sub_distrib, hsum₁, hsum₂]
  simp only [ofMatrix_apply, of_apply]
  rw [hident, sub_nonneg, sq, ← CStarRing.norm_star_mul_self (x := c)]
  exact CStarAlgebra.star_left_conjugate_le_norm_smul z (star c * c)

end Nonneg

section HilbertSpace

open scoped ComplexOrder InnerProductSpace

variable {n H : Type*} [Fintype n] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H]

/-- An operator matrix in `CStarMatrix n n (H →L[ℂ] H)` is positive if and only if all its vector
quadratic forms `∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ` are nonnegative in `ℂ`. -/
theorem nonneg_iff_forall_sum_inner_nonneg {M : CStarMatrix n n (H →L[ℂ] H)} :
    0 ≤ M ↔ ∀ ξ : n → H, 0 ≤ ∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ := by
  have hsum (X : n → (H →L[ℂ] H)) (v : H) :
      ⟪v, (∑ i, ∑ j, star (X i) * M i j * X j) v⟫_ℂ =
        ∑ i, ∑ j, ⟪X i v, M i j (X j v)⟫_ℂ := by
    simp only [FunLike.coe_sum, Finset.sum_apply, inner_sum, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right]
  rw [nonneg_iff_forall_sum_nonneg]
  refine ⟨fun hM ξ => ?_, fun hξ X => ?_⟩
  · by_cases hv : ∃ v : H, v ≠ 0
    · obtain ⟨v, hv⟩ := hv
      set u : H := (‖v‖⁻¹ : ℝ) • v
      have hu : ‖u‖ = 1 := by simp [u, norm_smul, norm_eq_zero.not.mpr hv]
      let X : n → (H →L[ℂ] H) := fun i => (innerSL ℂ u).smulRight (ξ i)
      have hXu (i : n) : X i u = ξ i := by simp [X, hu]
      have hpos := (ContinuousLinearMap.nonneg_iff_isPositive.mp (hM X)).inner_nonneg_right u
      rw [hsum X u] at hpos
      simpa only [hXu] using hpos
    · simp only [not_exists, not_not] at hv
      simp [hv]
  · set T : H →L[ℂ] H := ∑ i, ∑ j, star (X i) * M i j * X j
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_iff_complex]
    intro v
    have hz : 0 ≤ ⟪v, T v⟫_ℂ := by
      rw [hsum]
      exact hξ fun i => X i v
    obtain ⟨hre, him⟩ := Complex.nonneg_iff.mp hz
    have hTv : ⟪T v, v⟫_ℂ = ⟪v, T v⟫_ℂ :=
      (inner_conj_symm (T v) v).symm.trans (IsSelfAdjoint.of_nonneg hz).star_eq
    rw [hTv]
    exact ⟨by apply Complex.ext <;> simp [← him], by simpa using hre⟩

/-- Every vector quadratic form of a positive operator matrix in `CStarMatrix n n (H →L[ℂ] H)` is
nonnegative in `ℂ`. -/
theorem sum_inner_nonneg {M : CStarMatrix n n (H →L[ℂ] H)} (hM : 0 ≤ M) (ξ : n → H) :
    0 ≤ ∑ i, ∑ j, ⟪ξ i, M i j (ξ j)⟫_ℂ :=
  nonneg_iff_forall_sum_inner_nonneg.mp hM ξ

end HilbertSpace

end CStarMatrix
