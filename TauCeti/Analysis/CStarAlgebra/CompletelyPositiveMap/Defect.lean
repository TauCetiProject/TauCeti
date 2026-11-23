/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.Stinespring.Basic
public import TauCeti.Analysis.CStarAlgebra.Matrix.Trace
public import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.InnerProductSpace.Positive

/-!
# Multiplicativity defects of completely positive contractions into matrices

For a completely positive contraction (c.p.c.) `φ : A → M_k` from a possibly nonunital
C⋆-algebra, the *2-norm defect* and the *norm defect* at `a` are
`d₂(φ, a) = Re tr_k(φ(a⋆a) - φ(a)⋆φ(a))` (`CompletelyPositiveMap.twoNormDefect`) and
`d_∞(φ, a) = ‖φ(a⋆a) - φ(a)⋆φ(a)‖` (`CompletelyPositiveMap.normDefect`). The matrix
`φ(a⋆a) - φ(a)⋆φ(a)` is positive by the Kadison–Schwarz inequality for c.p.c. maps,
`CompletelyPositiveMap.star_map_mul_map_le_map_star_mul`, so both defects are nonnegative and
`d₂ ≤ d_∞`.

The estimates come from a Stinespring dilation. Identify `M_k` with the operators on
`ℂᵏ = EuclideanSpace ℂ n` through `CStarMatrix.toEuclideanCLM`, and dilate `φ = V⋆π(·)V` with
`‖V‖ ≤ 1`. With `S = (1 - VV⋆)^{1/2}`, the *defect operator* `T(a) = Sπ(a)V` satisfies
`φ(a⋆b) - φ(a)⋆φ(b) = T(a)⋆T(b)`, so `d_∞(φ, a) = ‖T(a)‖²` and `d₂(φ, a)` is the squared
normalized Hilbert–Schmidt norm of `T(a)`. Since `T` is linear, `‖T(a)‖ ≤ ‖a‖`, and
`T(ab) = T(a)φ(b) + Sπ(a)S T(b)`, this gives, for `d = d₂` and for `d = d_∞`:

* the product estimates `‖φ(ab) - φ(a)φ(b)‖ ≤ ‖a‖ d(φ, b)^{1/2}` and
  `‖φ(ab) - φ(a)φ(b)‖ ≤ d(φ, a⋆)^{1/2} ‖b‖`, in the norm and in the 2-norm
  (`CompletelyPositiveMap.norm_map_mul_sub_le`,
  `CompletelyPositiveMap.normalizedTwoNorm_map_mul_sub_le` and their `'` versions);
* subadditivity `d(φ, a + b)^{1/2} ≤ d(φ, a)^{1/2} + d(φ, b)^{1/2}`, the product rule
  `d(φ, ab)^{1/2} ≤ ‖b‖ d(φ, a)^{1/2} + ‖a‖ d(φ, b)^{1/2}` and the Lipschitz bound
  `|d(φ, a)^{1/2} - d(φ, b)^{1/2}| ≤ ‖a - b‖`.

Finally `d₂(φ, a) ≤ ‖φ(a⋆a) - φ(a⋆)φ(a)‖₂`, and star homomorphisms have zero defects.

## References

* N. P. Brown, *Invariant means and finite representation theory of C⋆-algebras*, Mem. Amer.
  Math. Soc. 184 (2006), Lemma 3.1.5 and the proof of Theorem 3.1.6.
-/

public section

noncomputable section

open scoped CStarAlgebra ComplexOrder InnerProductSpace

namespace CStarMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The star algebra isomorphism between `CStarMatrix n n ℂ` and the operators on
`EuclideanSpace ℂ n`, through `Matrix.toEuclideanCLM`. -/
def toEuclideanCLM : CStarMatrix n n ℂ ≃⋆ₐ[ℂ]
    (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  (ofMatrixStarAlgEquiv (n := n) (A := ℂ)).symm.trans Matrix.toEuclideanCLM

/-- `toEuclideanCLM` is `Matrix.toEuclideanCLM` on the underlying matrix. -/
theorem toEuclideanCLM_apply (x : CStarMatrix n n ℂ) :
    toEuclideanCLM x = Matrix.toEuclideanCLM (n := n) (𝕜 := ℂ) (ofMatrix.symm x) :=
  (rfl)

/-- The diagonal entries of a matrix are the diagonal matrix coefficients of its operator. -/
theorem inner_single_toEuclideanCLM_single (x : CStarMatrix n n ℂ) (i : n) :
    ⟪EuclideanSpace.single i 1, toEuclideanCLM x (EuclideanSpace.single i 1)⟫_ℂ = x i i := by
  simp [toEuclideanCLM_apply, EuclideanSpace.inner_single_left]

/-- `toEuclideanCLM` preserves norms. -/
@[simp]
theorem norm_toEuclideanCLM (x : CStarMatrix n n ℂ) : ‖toEuclideanCLM x‖ = ‖x‖ :=
  NonUnitalStarAlgHom.norm_map toEuclideanCLM toEuclideanCLM.injective x

/-- `toEuclideanCLM` preserves and reflects the order. -/
@[simp]
theorem toEuclideanCLM_le_toEuclideanCLM_iff {x y : CStarMatrix n n ℂ} :
    toEuclideanCLM x ≤ toEuclideanCLM y ↔ x ≤ y :=
  NonUnitalStarAlgHom.map_le_map_iff toEuclideanCLM toEuclideanCLM.injective

/-- `toEuclideanCLM` turns adjoints of operators into adjoints of matrices. -/
theorem symm_adjoint_comp (U W : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    toEuclideanCLM.symm (U.adjoint ∘L W) =
      star (toEuclideanCLM.symm U) * toEuclideanCLM.symm W := by
  rw [StarAlgEquiv.symm_apply_eq, map_mul, map_star, StarAlgEquiv.apply_symm_apply,
    StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.mul_def]

end CStarMatrix

namespace CompletelyPositiveMap

open CStarMatrix

variable {n : Type*} [Fintype n]

section HilbertSchmidt

variable [DecidableEq n]

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-- The columns `(T eᵢ)ᵢ` of an operator on `ℂᵏ`, as a vector in `ℓ²(n, K)`. -/
private def columns : (EuclideanSpace ℂ n →L[ℂ] K) →ₗ[ℂ] PiLp 2 (fun _ : n => K) where
  toFun T := WithLp.toLp 2 fun i => T (EuclideanSpace.single i 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The normalized Hilbert–Schmidt norm `(k⁻¹ Σᵢ ‖T eᵢ‖²)^{1/2}` of an operator on `ℂᵏ`. -/
private def hsNorm (T : EuclideanSpace ℂ n →L[ℂ] K) : ℝ :=
  Real.sqrt (Fintype.card n : ℝ)⁻¹ * ‖columns T‖

private theorem hsNorm_nonneg (T : EuclideanSpace ℂ n →L[ℂ] K) : 0 ≤ hsNorm T := by
  unfold hsNorm; positivity

private theorem hsNorm_add_le (T U : EuclideanSpace ℂ n →L[ℂ] K) :
    hsNorm (T + U) ≤ hsNorm T + hsNorm U := by
  unfold hsNorm
  rw [map_add, ← mul_add]
  gcongr
  exact norm_add_le _ _

private theorem abs_hsNorm_sub_hsNorm_le (T U : EuclideanSpace ℂ n →L[ℂ] K) :
    |hsNorm T - hsNorm U| ≤ max (hsNorm (T - U)) (hsNorm (U - T)) := by
  rw [abs_sub_le_iff]
  constructor
  · have := hsNorm_add_le (T - U) U
    rw [sub_add_cancel] at this
    linarith [le_max_left (hsNorm (T - U)) (hsNorm (U - T))]
  · have := hsNorm_add_le (U - T) T
    rw [sub_add_cancel] at this
    linarith [le_max_right (hsNorm (T - U)) (hsNorm (U - T))]

private theorem hsNorm_comp_le {L : Type*} [NormedAddCommGroup L] [InnerProductSpace ℂ L]
    (R : K →L[ℂ] L) (T : EuclideanSpace ℂ n →L[ℂ] K) : hsNorm (R ∘L T) ≤ ‖R‖ * hsNorm T := by
  unfold hsNorm
  rw [mul_left_comm]
  gcongr
  rw [← sq_le_sq₀ (norm_nonneg _) (by positivity), mul_pow, PiLp.norm_sq_eq_of_L2,
    PiLp.norm_sq_eq_of_L2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (R.le_opNorm _) 2

variable [CompleteSpace K]

/-- The normalized trace of `T⋆T` is the squared normalized Hilbert–Schmidt norm of `T`. -/
private theorem normalizedTrace_symm_adjoint_comp_self (T : EuclideanSpace ℂ n →L[ℂ] K) :
    normalizedTrace (toEuclideanCLM.symm (T.adjoint ∘L T)) = ((hsNorm T ^ 2 : ℝ) : ℂ) := by
  rw [normalizedTrace_eq_sum, hsNorm, mul_pow, Real.sq_sqrt (by positivity),
    PiLp.norm_sq_eq_of_L2]
  push_cast
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← inner_single_toEuclideanCLM_single (toEuclideanCLM.symm (T.adjoint ∘L T)) i,
    StarAlgEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, inner_self_eq_norm_sq_to_K]
  rfl

/-- Operators with the same `T⋆T` have the same normalized Hilbert–Schmidt norm. -/
private theorem hsNorm_eq_of_adjoint_comp_self_eq {L : Type*} [NormedAddCommGroup L]
    [InnerProductSpace ℂ L] [CompleteSpace L] {T : EuclideanSpace ℂ n →L[ℂ] K}
    {U : EuclideanSpace ℂ n →L[ℂ] L} (h : T.adjoint ∘L T = U.adjoint ∘L U) :
    hsNorm T = hsNorm U := by
  have hT := normalizedTrace_symm_adjoint_comp_self T
  rw [h, normalizedTrace_symm_adjoint_comp_self, Complex.ofReal_inj] at hT
  exact (pow_left_inj₀ (hsNorm_nonneg _) (hsNorm_nonneg _) two_ne_zero).mp hT.symm

/-- The normalized 2-norm of a matrix is the normalized Hilbert–Schmidt norm of its operator. -/
private theorem normalizedTwoNorm_symm (Z : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :
    normalizedTwoNorm (toEuclideanCLM.symm Z) = hsNorm Z := by
  rw [normalizedTwoNorm_def, ← symm_adjoint_comp, normalizedTrace_symm_adjoint_comp_self,
    Complex.ofReal_re, Real.sqrt_sq (hsNorm_nonneg Z)]

/-- `‖TY‖_HS ≤ ‖T‖_HS ‖Y‖`. -/
private theorem hsNorm_comp_right_le (T : EuclideanSpace ℂ n →L[ℂ] K)
    (Y : EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) : hsNorm (T ∘L Y) ≤ hsNorm T * ‖Y‖ := by
  obtain ⟨R, hRdef⟩ : ∃ R, R = CFC.sqrt (T.adjoint ∘L T) := ⟨_, rfl⟩
  have hR : R.adjoint ∘L R = T.adjoint ∘L T := by
    rw [hRdef, (CFC.sqrt_nonneg (T.adjoint ∘L T)).isSelfAdjoint.adjoint_eq,
      ← ContinuousLinearMap.mul_def]
    exact CFC.sqrt_mul_sqrt_self _
      ((ContinuousLinearMap.nonneg_iff_isPositive).mpr T.isPositive_adjoint_comp_self)
  have hRY : (R ∘L Y).adjoint ∘L (R ∘L Y) = (T ∘L Y).adjoint ∘L (T ∘L Y) := by
    simp only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
    rw [← ContinuousLinearMap.comp_assoc R.adjoint, hR, ContinuousLinearMap.comp_assoc]
  have hY := norm_toEuclideanCLM (toEuclideanCLM.symm Y)
  rw [StarAlgEquiv.apply_symm_apply] at hY
  rw [← hsNorm_eq_of_adjoint_comp_self_eq hRY, ← hsNorm_eq_of_adjoint_comp_self_eq hR,
    ← normalizedTwoNorm_symm, ← normalizedTwoNorm_symm, hY]
  calc normalizedTwoNorm (toEuclideanCLM.symm (R ∘L Y))
      = normalizedTwoNorm (toEuclideanCLM.symm R * toEuclideanCLM.symm Y) := by
        rw [← map_mul, ContinuousLinearMap.mul_def]
    _ ≤ normalizedTwoNorm (toEuclideanCLM.symm R) * ‖toEuclideanCLM.symm Y‖ :=
        normalizedTwoNorm_mul_le_normalizedTwoNorm_mul_norm _ _

end HilbertSchmidt

variable {A : Type*} [NonUnitalCStarAlgebra A] [PartialOrder A] [StarOrderedRing A]

/-- The **norm defect** `d_∞(φ, a) = ‖φ(a⋆a) - φ(a)⋆φ(a)‖` of a completely positive map into
matrices. -/
def normDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) : ℝ :=
  ‖φ (star a * a) - star (φ a) * φ a‖

/-- Unfolding lemma for `normDefect`. -/
theorem normDefect_def (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.normDefect a = ‖φ (star a * a) - star (φ a) * φ a‖ :=
  (rfl)

/-- The **2-norm defect** `d₂(φ, a) = Re tr_k(φ(a⋆a) - φ(a)⋆φ(a))` of a completely positive map
into matrices. -/
def twoNormDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) : ℝ :=
  (normalizedTrace (φ (star a * a) - star (φ a) * φ a)).re

/-- Unfolding lemma for `twoNormDefect`. -/
theorem twoNormDefect_def (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a = (normalizedTrace (φ (star a * a) - star (φ a) * φ a)).re :=
  (rfl)

/-- The norm defect is nonnegative. -/
theorem normDefect_nonneg (φ : A →CP CStarMatrix n n ℂ) (a : A) : 0 ≤ φ.normDefect a :=
  norm_nonneg _

/-- `d₂(φ, a) ≤ d_∞(φ, a)`, as `|tr_k(x)| ≤ ‖x‖`. -/
theorem twoNormDefect_le_normDefect (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a ≤ φ.normDefect a :=
  (Complex.re_le_norm _).trans (norm_normalizedTrace_le_norm _)

/-- A completely positive map preserves adjoints. -/
private theorem map_star_eq (φ : A →CP CStarMatrix n n ℂ) (a : A) : φ (star a) = star (φ a) :=
  by simpa only [coe_toPositiveLinearMap] using map_star φ.toPositiveLinearMap a

/-- `d₂(φ, a) ≤ ‖φ(a⋆a) - φ(a⋆)φ(a)‖₂`, as `|tr_k(x)| ≤ ‖x‖₂`. -/
theorem twoNormDefect_le_normalizedTwoNorm (φ : A →CP CStarMatrix n n ℂ) (a : A) :
    φ.twoNormDefect a ≤ normalizedTwoNorm (φ (star a * a) - φ (star a) * φ a) := by
  rw [map_star_eq]
  exact (Complex.re_le_norm _).trans (norm_normalizedTrace_le_normalizedTwoNorm _)

/-- Star homomorphisms have zero norm defect. -/
@[simp]
theorem normDefect_toCompletelyPositiveLinearMap (ρ : A →⋆ₙₐ[ℂ] CStarMatrix n n ℂ) (a : A) :
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ).normDefect a = 0 := by
  change ‖ρ (star a * a) - star (ρ a) * ρ a‖ = 0
  simp [map_star ρ]

/-- Star homomorphisms have zero 2-norm defect. -/
@[simp]
theorem twoNormDefect_toCompletelyPositiveLinearMap (ρ : A →⋆ₙₐ[ℂ] CStarMatrix n n ℂ) (a : A) :
    (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap ρ).twoNormDefect a = 0 := by
  change (normalizedTrace (ρ (star a * a) - star (ρ a) * ρ a)).re = 0
  simp [map_star ρ]

section Dilation

variable [DecidableEq n] (φ : A →CP CStarMatrix n n ℂ)

/-- `φ` as a completely positive map into the operators on `ℂᵏ`. -/
private def toOp : A →CP (EuclideanSpace ℂ n →L[ℂ] EuclideanSpace ℂ n) :=
  (CompletelyPositiveMapClass.toCompletelyPositiveLinearMap
    (toEuclideanCLM (n := n))).comp φ

private theorem toOp_apply (a : A) : toOp φ a = toEuclideanCLM (φ a) := by
  simp [toOp]

/-- The operator `1 - VV⋆` on the Stinespring space. -/
private def defectProj : (toOp φ).Stinespring →L[ℂ] (toOp φ).Stinespring :=
  1 - (toOp φ).stinespringOp ∘L (toOp φ).stinespringOp.adjoint

/-- The operator `S = (1 - VV⋆)^{1/2}` on the Stinespring space. -/
private def defectSqrt : (toOp φ).Stinespring →L[ℂ] (toOp φ).Stinespring :=
  CFC.sqrt (defectProj φ)

/-- The defect operator `T(a) = Sπ(a)V`. -/
private def defectOp : A →ₗ[ℂ] (EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) where
  toFun a := defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L (toOp φ).stinespringOp
  map_add' a b := by simp [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add]
  map_smul' c a := by simp [ContinuousLinearMap.smul_comp]

private theorem defectOp_apply (a : A) :
    defectOp φ a = defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L (toOp φ).stinespringOp :=
  (rfl)

private theorem adjoint_defectSqrt : (defectSqrt φ).adjoint = defectSqrt φ := by
  rw [defectSqrt]
  exact (CFC.sqrt_nonneg (defectProj φ)).isSelfAdjoint.adjoint_eq

private theorem stinespring_eq' (c : A) :
    toEuclideanCLM (φ c) =
      (toOp φ).stinespringOp.adjoint ∘L (toOp φ).stinespringHom c ∘L (toOp φ).stinespringOp := by
  rw [← toOp_apply]
  exact ((toOp φ).stinespring_eq c).symm

variable {φ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

private theorem norm_stinespringOp_toOp_le : ‖(toOp φ).stinespringOp‖ ≤ 1 := by
  have h1 : ‖(toOp φ).toContinuousLinearMap‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun a => by
      simpa [toOp_apply] using hφ a
  have h2 := (toOp φ).norm_stinespringOp_sq
  nlinarith [norm_nonneg (toOp φ).stinespringOp]

private theorem defectProj_nonneg : 0 ≤ defectProj φ := by
  set V := (toOp φ).stinespringOp
  have hpos : 0 ≤ V ∘L V.adjoint :=
    (ContinuousLinearMap.nonneg_iff_isPositive).mpr V.isPositive_self_comp_adjoint
  have hnorm : ‖V ∘L V.adjoint‖ ≤ 1 := by
    have h := ContinuousLinearMap.norm_adjoint_comp_self V.adjoint
    rw [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint.norm_map] at h
    rw [h]
    have := norm_stinespringOp_toOp_le hφ
    nlinarith [norm_nonneg V]
  rw [defectProj, sub_nonneg]
  exact (CStarAlgebra.norm_le_one_iff_of_nonneg _ hpos).mp hnorm

/-- `S⋆S = 1 - VV⋆`. -/
private theorem adjoint_defectSqrt_comp_self :
    (defectSqrt φ).adjoint ∘L defectSqrt φ = defectProj φ := by
  rw [adjoint_defectSqrt, ← ContinuousLinearMap.mul_def, defectSqrt]
  exact CFC.sqrt_mul_sqrt_self _ (defectProj_nonneg hφ)

/-- `‖S‖ ≤ 1`. -/
private theorem norm_defectSqrt_le : ‖defectSqrt φ‖ ≤ 1 := by
  have hP : ‖defectProj φ‖ ≤ 1 := by
    rw [CStarAlgebra.norm_le_one_iff_of_nonneg _ (defectProj_nonneg hφ), defectProj,
      sub_le_self_iff, ContinuousLinearMap.nonneg_iff_isPositive]
    exact (toOp φ).stinespringOp.isPositive_self_comp_adjoint
  have h := ContinuousLinearMap.norm_adjoint_comp_self (defectSqrt φ)
  rw [adjoint_defectSqrt_comp_self hφ] at h
  nlinarith [norm_nonneg (defectSqrt φ)]

private theorem norm_defectSqrt_comp_le (a : A) :
    ‖defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L defectSqrt φ‖ ≤ ‖a‖ := by
  calc _ ≤ ‖defectSqrt φ‖ * (‖(toOp φ).stinespringHom a‖ * ‖defectSqrt φ‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · exact norm_defectSqrt_le hφ
        · exact NonUnitalStarAlgHom.norm_apply_le _ a
        · exact norm_defectSqrt_le hφ
    _ = ‖a‖ := by ring

private theorem norm_defectOp_le (a : A) : ‖defectOp φ a‖ ≤ ‖a‖ := by
  rw [defectOp_apply]
  calc _ ≤ ‖defectSqrt φ‖ * (‖(toOp φ).stinespringHom a‖ * ‖(toOp φ).stinespringOp‖) :=
        (ContinuousLinearMap.opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_left (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _))
    _ ≤ 1 * (‖a‖ * 1) := by
        gcongr
        · exact norm_defectSqrt_le hφ
        · exact NonUnitalStarAlgHom.norm_apply_le _ a
        · exact norm_stinespringOp_toOp_le hφ
    _ = ‖a‖ := by ring

/-- The defect identity `φ(a⋆b) - φ(a)⋆φ(b) = T(a)⋆T(b)`. -/
private theorem toEuclideanCLM_map_star_mul_sub (a b : A) :
    toEuclideanCLM (φ (star a * b) - star (φ a) * φ b) =
      (defectOp φ a).adjoint ∘L defectOp φ b := by
  set V := (toOp φ).stinespringOp
  set π := (toOp φ).stinespringHom
  calc toEuclideanCLM (φ (star a * b) - star (φ a) * φ b)
      = V.adjoint ∘L π (star a) ∘L π b ∘L V -
          (V.adjoint ∘L π (star a) ∘L V) ∘L (V.adjoint ∘L π b ∘L V) := by
        rw [← map_star_eq, map_sub, map_mul toEuclideanCLM, stinespring_eq', stinespring_eq',
          stinespring_eq', map_mul π, ContinuousLinearMap.mul_def, ContinuousLinearMap.mul_def]
        simp only [ContinuousLinearMap.comp_assoc]
        rfl
    _ = V.adjoint ∘L (π a).adjoint ∘L ((defectSqrt φ).adjoint ∘L defectSqrt φ) ∘L π b ∘L V := by
        rw [adjoint_defectSqrt_comp_self hφ, defectProj, map_star,
          ContinuousLinearMap.star_eq_adjoint]
        simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
          ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc]
        rfl
    _ = (defectOp φ a).adjoint ∘L defectOp φ b := by
        simp only [defectOp_apply, ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.comp_assoc]
        rfl

private theorem map_star_mul_sub_eq (a b : A) :
    φ (star a * b) - star (φ a) * φ b =
      toEuclideanCLM.symm ((defectOp φ a).adjoint ∘L defectOp φ b) := by
  rw [← toEuclideanCLM_map_star_mul_sub hφ, StarAlgEquiv.symm_apply_apply]

/-- The product rule for the defect operator: `T(ab) = T(a)φ(b) + Sπ(a)S T(b)`. -/
private theorem defectOp_mul (a b : A) :
    defectOp φ (a * b) = defectOp φ a ∘L toEuclideanCLM (φ b) +
      (defectSqrt φ ∘L (toOp φ).stinespringHom a ∘L defectSqrt φ) ∘L defectOp φ b := by
  have hS : defectSqrt φ ∘L defectSqrt φ =
      1 - (toOp φ).stinespringOp ∘L (toOp φ).stinespringOp.adjoint := by
    have h := adjoint_defectSqrt_comp_self hφ
    rwa [adjoint_defectSqrt] at h
  rw [stinespring_eq']
  simp only [defectOp_apply, map_mul (toOp φ).stinespringHom, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_assoc]
  rw [← ContinuousLinearMap.comp_assoc (defectSqrt φ) (defectSqrt φ), hS]
  simp only [ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub,
    ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_assoc]
  abel

private theorem sqrt_normDefect_eq (a : A) : √(φ.normDefect a) = ‖defectOp φ a‖ := by
  rw [normDefect_def, ← norm_toEuclideanCLM, toEuclideanCLM_map_star_mul_sub hφ,
    ContinuousLinearMap.norm_adjoint_comp_self, Real.sqrt_mul_self (norm_nonneg _)]

private theorem twoNormDefect_eq (a : A) : φ.twoNormDefect a = hsNorm (defectOp φ a) ^ 2 := by
  rw [twoNormDefect_def, map_star_mul_sub_eq hφ, normalizedTrace_symm_adjoint_comp_self,
    Complex.ofReal_re]

private theorem sqrt_twoNormDefect_eq (a : A) :
    √(φ.twoNormDefect a) = hsNorm (defectOp φ a) := by
  rw [twoNormDefect_eq hφ, Real.sqrt_sq (hsNorm_nonneg _)]

/-- `φ(ab) - φ(a)φ(b) = T(a⋆)⋆T(b)`. -/
private theorem map_mul_sub_eq (a b : A) :
    φ (a * b) - φ a * φ b =
      toEuclideanCLM.symm ((defectOp φ (star a)).adjoint ∘L defectOp φ b) := by
  have h := map_star_mul_sub_eq hφ (star a) b
  rwa [star_star, ← map_star_eq, star_star] at h

end Dilation

variable {φ : A →CP CStarMatrix n n ℂ} (hφ : ∀ a, ‖φ a‖ ≤ ‖a‖)
include hφ

/-- **Kadison–Schwarz inequality** for a completely positive contraction into matrices:
`φ(a)⋆φ(a) ≤ φ(a⋆a)`. -/
theorem star_map_mul_map_le_map_star_mul (a : A) : star (φ a) * φ a ≤ φ (star a * a) := by
  classical
  rw [← sub_nonneg, ← toEuclideanCLM_le_toEuclideanCLM_iff, map_zero,
    toEuclideanCLM_map_star_mul_sub hφ, ContinuousLinearMap.nonneg_iff_isPositive]
  exact (defectOp φ a).isPositive_adjoint_comp_self

/-- The 2-norm defect is nonnegative. -/
theorem twoNormDefect_nonneg (a : A) : 0 ≤ φ.twoNormDefect a := by
  classical
  rw [twoNormDefect_eq hφ]
  positivity

/-- The norm product estimate `‖φ(ab) - φ(a)φ(b)‖ ≤ ‖a‖ d_∞(φ, b)^{1/2}`. -/
theorem norm_map_mul_sub_le (a b : A) :
    ‖φ (a * b) - φ a * φ b‖ ≤ ‖a‖ * √(φ.normDefect b) := by
  classical
  rw [map_mul_sub_eq hφ, ← norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
    sqrt_normDefect_eq hφ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_defectOp_le hφ (star a)) (norm_nonneg _)

/-- The norm product estimate `‖φ(ab) - φ(a)φ(b)‖ ≤ d_∞(φ, a⋆)^{1/2} ‖b‖`. -/
theorem norm_map_mul_sub_le' (a b : A) :
    ‖φ (a * b) - φ a * φ b‖ ≤ √(φ.normDefect (star a)) * ‖b‖ := by
  classical
  rw [map_mul_sub_eq hφ, ← norm_toEuclideanCLM, StarAlgEquiv.apply_symm_apply,
    sqrt_normDefect_eq hφ]
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_left (norm_defectOp_le hφ b) (norm_nonneg _)

/-- The 2-norm product estimate `‖φ(ab) - φ(a)φ(b)‖₂ ≤ ‖a‖ d₂(φ, b)^{1/2}`. -/
theorem normalizedTwoNorm_map_mul_sub_le (a b : A) :
    normalizedTwoNorm (φ (a * b) - φ a * φ b) ≤ ‖a‖ * √(φ.twoNormDefect b) := by
  classical
  rw [map_mul_sub_eq hφ, normalizedTwoNorm_symm, sqrt_twoNormDefect_eq hφ]
  refine (hsNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (by simpa using norm_defectOp_le hφ (star a))
    (hsNorm_nonneg _)

/-- The 2-norm product estimate `‖φ(ab) - φ(a)φ(b)‖₂ ≤ d₂(φ, a⋆)^{1/2} ‖b‖`. -/
theorem normalizedTwoNorm_map_mul_sub_le' (a b : A) :
    normalizedTwoNorm (φ (a * b) - φ a * φ b) ≤ √(φ.twoNormDefect (star a)) * ‖b‖ := by
  classical
  have h : star (φ (a * b) - φ a * φ b) = φ (star b * star a) - star (φ b) * φ (star a) := by
    rw [← star_mul, map_star_eq, map_star_eq, star_sub, star_mul]
  rw [← normalizedTwoNorm_star, h, map_star_mul_sub_eq hφ, normalizedTwoNorm_symm,
    sqrt_twoNormDefect_eq hφ, mul_comm (hsNorm _)]
  refine (hsNorm_comp_le _ _).trans ?_
  rw [ContinuousLinearMap.adjoint.norm_map]
  exact mul_le_mul_of_nonneg_right (norm_defectOp_le hφ b) (hsNorm_nonneg _)

/-- Subadditivity of `d_∞(φ, ·)^{1/2}`. -/
theorem sqrt_normDefect_add_le (a b : A) :
    √(φ.normDefect (a + b)) ≤ √(φ.normDefect a) + √(φ.normDefect b) := by
  classical
  simp only [sqrt_normDefect_eq hφ, map_add]
  exact norm_add_le (E := EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) _ _

/-- Subadditivity of `d₂(φ, ·)^{1/2}`. -/
theorem sqrt_twoNormDefect_add_le (a b : A) :
    √(φ.twoNormDefect (a + b)) ≤ √(φ.twoNormDefect a) + √(φ.twoNormDefect b) := by
  classical
  simp only [sqrt_twoNormDefect_eq hφ, map_add]
  exact hsNorm_add_le _ _

/-- The product rule `d_∞(φ, ab)^{1/2} ≤ ‖b‖ d_∞(φ, a)^{1/2} + ‖a‖ d_∞(φ, b)^{1/2}`. -/
theorem sqrt_normDefect_mul_le (a b : A) :
    √(φ.normDefect (a * b)) ≤ ‖b‖ * √(φ.normDefect a) + ‖a‖ * √(φ.normDefect b) := by
  classical
  simp only [sqrt_normDefect_eq hφ]
  rw [defectOp_mul hφ]
  refine (norm_add_le (E := EuclideanSpace ℂ n →L[ℂ] (toOp φ).Stinespring) _ _).trans
    (add_le_add ?_ ?_)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    rw [norm_toEuclideanCLM, mul_comm ‖b‖]
    exact mul_le_mul_of_nonneg_left (hφ b) (norm_nonneg _)
  · refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_defectSqrt_comp_le hφ a) (norm_nonneg _)

/-- The product rule `d₂(φ, ab)^{1/2} ≤ ‖b‖ d₂(φ, a)^{1/2} + ‖a‖ d₂(φ, b)^{1/2}`. -/
theorem sqrt_twoNormDefect_mul_le (a b : A) :
    √(φ.twoNormDefect (a * b)) ≤ ‖b‖ * √(φ.twoNormDefect a) + ‖a‖ * √(φ.twoNormDefect b) := by
  classical
  simp only [sqrt_twoNormDefect_eq hφ]
  rw [defectOp_mul hφ]
  refine (hsNorm_add_le _ _).trans (add_le_add ?_ ?_)
  · refine (hsNorm_comp_right_le _ _).trans ?_
    rw [norm_toEuclideanCLM, mul_comm ‖b‖]
    exact mul_le_mul_of_nonneg_left (hφ b) (hsNorm_nonneg _)
  · refine (hsNorm_comp_le _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (norm_defectSqrt_comp_le hφ a) (hsNorm_nonneg _)

/-- `d_∞(φ, a)^{1/2} ≤ ‖a‖`. -/
theorem sqrt_normDefect_le (a : A) : √(φ.normDefect a) ≤ ‖a‖ := by
  classical
  rw [sqrt_normDefect_eq hφ]
  exact norm_defectOp_le hφ a

/-- `d₂(φ, a)^{1/2} ≤ ‖a‖`. -/
theorem sqrt_twoNormDefect_le (a : A) : √(φ.twoNormDefect a) ≤ ‖a‖ :=
  (Real.sqrt_le_sqrt (φ.twoNormDefect_le_normDefect a)).trans (sqrt_normDefect_le hφ a)

/-- The Lipschitz bound `|d_∞(φ, a)^{1/2} - d_∞(φ, b)^{1/2}| ≤ ‖a - b‖`. -/
theorem abs_sqrt_normDefect_sub_le (a b : A) :
    |√(φ.normDefect a) - √(φ.normDefect b)| ≤ ‖a - b‖ := by
  classical
  simp only [sqrt_normDefect_eq hφ]
  refine (abs_norm_sub_norm_le (defectOp φ a) (defectOp φ b)).trans ?_
  rw [← map_sub]
  exact norm_defectOp_le hφ _

/-- The Lipschitz bound `|d₂(φ, a)^{1/2} - d₂(φ, b)^{1/2}| ≤ ‖a - b‖`. -/
theorem abs_sqrt_twoNormDefect_sub_le (a b : A) :
    |√(φ.twoNormDefect a) - √(φ.twoNormDefect b)| ≤ ‖a - b‖ := by
  classical
  have h (c d : A) : hsNorm (defectOp φ c - defectOp φ d) ≤ ‖c - d‖ := by
    rw [← map_sub, ← sqrt_twoNormDefect_eq hφ]
    exact sqrt_twoNormDefect_le hφ _
  simp only [sqrt_twoNormDefect_eq hφ]
  refine (abs_hsNorm_sub_hsNorm_le _ _).trans (max_le (h a b) ?_)
  rw [norm_sub_rev]
  exact h b a

end CompletelyPositiveMap
