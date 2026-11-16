/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Trace
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.PosPart.Basic
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import TauCeti.Algebra.Star.Basic
import TauCeti.LinearAlgebra.Matrix.Trace.Duality

/-!
# Positivity, trace duality, and Euclidean operators on matrix C⋆-algebras

For a non-unital C⋆-algebra `A` and a finite type `n`, Mathlib makes `CStarMatrix n n A` a
C⋆-algebra and orders it by the spectral order. This file proves that a matrix `M` is positive in
this order exactly when its finite quadratic forms are positive in `A`:

`0 ≤ M ↔ ∀ x : n → A, 0 ≤ ∑ i, ∑ j, star (x i) * M i j * x j`.

No self-adjointness hypothesis is needed for the converse: positivity of all the quadratic forms
already forces `M` to be self-adjoint, by polarization over `ℂ`. The criterion is the standard way
to recognise positive matrices over a C⋆-algebra, for instance Gram matrices of vectors in a
Hilbert C⋆-module. We also show that a diagonal matrix in `CStarMatrix n n A` has operator norm
equal to the supremum norm of its diagonal, expose linear trace duality on `CStarMatrix`, and
construct the isometric `⋆`-algebra isomorphism `CStarMatrix.toEuclideanCLM` between
`CStarMatrix n n ℂ` and `EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n`.

## Main declarations

* `CStarMatrix.instNonUnitalContinuousFunctionalCalculusReal`: the real continuous functional
  calculus of `CStarMatrix n n A`, which instance search does not find on its own.
* `CStarMatrix.ofMatrix_symm_zero`, `CStarMatrix.ofMatrix_symm_smul`,
  `CStarMatrix.ofMatrix_symm_mul`, `CStarMatrix.ofMatrix_symm_star`: reading a C⋆-matrix as an
  ordinary matrix respects algebraic operations and sends `star` to the conjugate transpose.
* `CStarMatrix.traceLinearMap`, `CStarMatrix.existsUnique_trace_mul_eq`,
  `CStarMatrix.existsUnique_sum_trace_mul_eq`: trace linear map and trace duality on `CStarMatrix`.
* `CStarMatrix.isSelfAdjoint_of_forall_isSelfAdjoint_sum`: a matrix all of whose quadratic forms
  are self-adjoint is self-adjoint. This is purely algebraic, and holds over any complex
  star-algebra whose star is proper.
* `CStarMatrix.nonneg_iff_forall_sum_nonneg`: the quadratic-form criterion for positivity.
* `CStarMatrix.norm_ofMatrix_diagonal`: `‖ofMatrix (diagonal d)‖ = ‖d‖` over any non-unital
  C⋆-algebra.
* `CStarMatrix.toEuclideanCLM`, `CStarMatrix.norm_toEuclideanCLM`,
  `CStarMatrix.trace_toEuclideanCLM`: the isometric, trace-preserving `⋆`-algebra isomorphism with
  Euclidean endomorphisms.

## References

* E. C. Lance, *Hilbert C⋆-Modules: A Toolkit for Operator Algebraists*, Lemma 4.1.
-/

public section

open Matrix

namespace CStarMatrix

section Algebraic

variable {m n R A : Type*}

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

/-- `ofMatrixₗ` agrees with `ofMatrix` on underlying matrices. -/
@[simp] lemma ofMatrixₗ_apply [AddCommMonoid A] [Semiring R] [Module R A] (M : Matrix m n A) :
    ofMatrixₗ (R := R) M = ofMatrix M := (rfl)

/-- `ofMatrixₗ.symm` agrees with `ofMatrix.symm` on underlying C⋆-matrices. -/
@[simp] lemma ofMatrixₗ_symm_apply [AddCommMonoid A] [Semiring R] [Module R A]
    (M : CStarMatrix m n A) : (ofMatrixₗ (R := R)).symm M = ofMatrix.symm M := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `0` to `0`. -/
@[simp] lemma ofMatrix_symm_zero [Zero A] : ofMatrix.symm (0 : CStarMatrix m n A) = 0 := by
  rw [← of_zero, Equiv.symm_apply_apply]

/-- Reading a C⋆-matrix as an ordinary matrix respects scalar multiplication. -/
@[simp] lemma ofMatrix_symm_smul [SMul R A] (r : R) (M : CStarMatrix m n A) :
    ofMatrix.symm (r • M) = r • ofMatrix.symm M := by
  rw [ofMatrix.symm_apply_eq, ← smul_of, Equiv.apply_symm_apply]

/-- Reading a C⋆-matrix as an ordinary matrix respects multiplication. -/
@[simp]
lemma ofMatrix_symm_mul [Fintype n] [Mul A] [AddCommMonoid A] (M N : CStarMatrix n n A) :
    ofMatrix.symm (M * N) = ofMatrix.symm M * ofMatrix.symm N := (rfl)

/-- Reading a C⋆-matrix as an ordinary matrix sends `star` to the conjugate transpose. -/
@[simp]
lemma ofMatrix_symm_star [Star A] (M : CStarMatrix n n A) :
    ofMatrix.symm (star M) = (ofMatrix.symm M)ᴴ := (rfl)

/-- The matrix trace of a C⋆-matrix bundled as a linear map. -/
def traceLinearMap (n R A : Type*) [Fintype n] [AddCommMonoid A] [Semiring R] [Module R A] :
    CStarMatrix n n A →ₗ[R] A :=
  (Matrix.traceLinearMap n R A).comp (ofMatrixₗ (R := R)).symm.toLinearMap

@[simp] theorem traceLinearMap_apply [Fintype n] [AddCommMonoid A] [Semiring R] [Module R A]
    (M : CStarMatrix n n A) : traceLinearMap n R A M = Matrix.trace (ofMatrix.symm M) := (rfl)

/-- **Trace duality on `CStarMatrix`.** Every linear functional on `CStarMatrix n n R` is
`M ↦ tr(ρ * M)` for a unique `ρ : CStarMatrix n n R`. -/
theorem existsUnique_trace_mul_eq [Fintype n] [CommSemiring R] (φ : CStarMatrix n n R →ₗ[R] R) :
    ∃! ρ : CStarMatrix n n R, ∀ M, φ M = Matrix.trace (ofMatrix.symm (ρ * M)) := by
  obtain ⟨ρ, hρ, huniq⟩ := (φ.comp (ofMatrixₗ (R := R)).toLinearMap).existsUnique_trace_mul_eq
  refine ⟨ofMatrix ρ, fun M => by simpa [ofMatrix_symm_mul] using hρ (ofMatrix.symm M),
    fun ρ' hρ' => ofMatrix.symm.injective <| by
      rw [Equiv.symm_apply_apply]
      exact huniq (ofMatrix.symm ρ') fun M => by simpa [ofMatrix_symm_mul] using hρ' (ofMatrix M)⟩

/-- **Trace duality on finite families of `CStarMatrix`.** Every linear functional on
`ι → CStarMatrix n n R` is `b ↦ ∑ k, tr(x k * b k)` for a unique family `x`. -/
theorem existsUnique_sum_trace_mul_eq {ι : Type*} [Fintype ι] [Fintype n] [CommSemiring R]
    (φ : (ι → CStarMatrix n n R) →ₗ[R] R) :
    ∃! x : ι → CStarMatrix n n R, ∀ b, φ b = ∑ k, Matrix.trace (ofMatrix.symm (x k * b k)) := by
  classical
  let emb (k : ι) := LinearMap.single R (fun _ : ι => CStarMatrix n n R) k
  choose x hx huniq using fun k => existsUnique_trace_mul_eq (φ.comp (emb k))
  refine ⟨x, fun b => ?_, fun y hy => funext fun k => huniq k (y k) fun M => ?_⟩
  · conv_lhs => rw [← Finset.univ_sum_single b]
    rw [map_sum]; exact Finset.sum_congr rfl fun k _ => hx k (b k)
  · have h := hy (Pi.single k M)
    rw [Finset.sum_eq_single k (fun j _ hj => by simp [Pi.single_eq_of_ne hj])
      (fun hk => absurd (Finset.mem_univ k) hk)] at h
    simpa [emb] using h

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

/-- The operator norm of a diagonal matrix in `CStarMatrix n n A` equals `‖d‖`. -/
@[simp]
theorem norm_ofMatrix_diagonal [DecidableEq n] (d : n → A) : ‖ofMatrix (diagonal d)‖ = ‖d‖ := by
  refine le_antisymm ?_ ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => by
    simpa using norm_entry_le_norm (M := ofMatrix (diagonal d)) (i := i) (j := i))
  rw [norm_def]
  refine (toCLM (ofMatrix (diagonal d))).opNorm_le_bound (norm_nonneg d) fun v => ?_
  refine (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg d) (norm_nonneg v))).mp ?_
  rw [WithCStarModule.pi_norm_sq, mul_pow, WithCStarModule.pi_norm_sq]
  have hsum : ∑ j, inner A (toCLM (ofMatrix (diagonal d)) v j) (toCLM (ofMatrix (diagonal d)) v j) ≤
      ‖d‖ ^ 2 • ∑ j, inner A (v j) (v j) := by
    rw [Finset.smul_sum]
    refine Finset.sum_le_sum fun j _ => ?_
    have happly : toCLM (ofMatrix (diagonal d)) v j = v j * d j := by
      simp [toCLM_apply_eq_sum, diagonal_apply]
    rw [WithCStarModule.inner_def, WithCStarModule.inner_def, happly]
    calc (v j * d j) * star (v j * d j)
        = v j * (d j * star (d j)) * star (v j) := by simp [mul_assoc]
      _ ≤ ‖d j * star (d j)‖ • (v j * star (v j)) :=
          CStarAlgebra.star_right_conjugate_le_norm_smul (v j) (d j * star (d j))
      _ ≤ ‖d‖ ^ 2 • (v j * star (v j)) := by
          rw [CStarRing.norm_self_mul_star, ← sq]
          exact smul_le_smul_of_nonneg_right
            (pow_le_pow_left₀ (norm_nonneg _) (norm_le_pi_norm d j) 2) (mul_star_self_nonneg _)
  simpa only [norm_smul, Real.norm_of_nonneg (sq_nonneg _)] using
    CStarAlgebra.norm_le_norm_of_le_of_nonneg hsum
      (Finset.sum_nonneg fun _ _ => CStarModule.inner_self_nonneg)

section Euclidean

open scoped ComplexOrder

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- The natural `⋆`-algebra equivalence `CStarMatrix m m ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ m →L[ℂ] _)`. -/
noncomputable def toEuclideanCLM :
    CStarMatrix m m ℂ ≃⋆ₐ[ℂ] (EuclideanSpace ℂ m →L[ℂ] EuclideanSpace ℂ m) :=
  ofMatrixStarAlgEquiv.symm.trans (Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ))

/-- `toEuclideanCLM` acts on an underlying matrix via `Matrix.toEuclideanCLM`. -/
theorem toEuclideanCLM_apply (x : CStarMatrix m m ℂ) :
    toEuclideanCLM x = Matrix.toEuclideanCLM (n := m) (𝕜 := ℂ) (ofMatrix.symm x) := (rfl)

/-- `toEuclideanCLM` is isometric between the C⋆-matrix norm and Euclidean operator norm. -/
@[simp]
theorem norm_toEuclideanCLM (x : CStarMatrix m m ℂ) : ‖toEuclideanCLM x‖ = ‖x‖ :=
  StarAlgEquiv.norm_map toEuclideanCLM x

/-- The operator trace of `toEuclideanCLM x` equals the matrix trace of `x`. -/
@[simp]
theorem trace_toEuclideanCLM (x : CStarMatrix m m ℂ) :
    LinearMap.trace ℂ (EuclideanSpace ℂ m) (toEuclideanCLM x).toLinearMap =
      Matrix.trace (ofMatrix.symm x) := by
  rw [toEuclideanCLM_apply, Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal, Matrix.trace_toLin_eq]

end Euclidean

end CStarMatrix
