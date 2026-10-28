/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Analysis.Matrix.FunctionalCalculus
public import TauCeti.Analysis.InnerProductSpace.MoorePenrose
import TauCeti.Topology.Instances.Matrix

/-!
# The pseudoinverse of a covariance matrix

`Matrix.covariancePseudoInverse` inverts the nonzero eigenvalues of a real positive-semidefinite
matrix and vanishes on its kernel. Invalid covariance matrices give zero. This is the inverse
needed to condition a Gaussian vector on an observed block with singular covariance.

The construction uses Mathlib's finite-spectrum continuous functional calculus. Its Euclidean
operator is the existing `LinearMap.moorePenroseInverse`, so uniqueness follows from the four
Penrose equations rather than a choice of eigenbasis.

## References

* R. Penrose, *A generalized inverse for matrices*, Proc. Cambridge Philos. Soc. **51** (1955),
  406–413.
* T. W. Anderson, *An Introduction to Multivariate Statistical Analysis*, 3rd ed., Wiley (2003).
-/

public section

noncomputable section

open Filter Topology
open scoped MatrixOrder

namespace Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Invert the nonzero eigenvalues of a positive-semidefinite covariance matrix, sending zero
eigenvalues to zero. For a matrix that is not positive semidefinite, return zero. -/
def covariancePseudoInverse (C : Matrix ι ι ℝ) : Matrix ι ι ℝ :=
  open Classical in
  if C.PosSemidef then cfc (fun x : ℝ ↦ x⁻¹) C else 0

/-- The positive-semidefinite branch of the covariance pseudoinverse. -/
theorem covariancePseudoInverse_of_posSemidef {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    C.covariancePseudoInverse = cfc (fun x : ℝ ↦ x⁻¹) C := by
  simp [covariancePseudoInverse, hC]

/-- An invalid covariance has zero pseudoinverse. -/
@[simp]
theorem covariancePseudoInverse_of_not_posSemidef {C : Matrix ι ι ℝ}
    (hC : ¬ C.PosSemidef) : C.covariancePseudoInverse = 0 := by
  simp [covariancePseudoInverse, hC]

/-- The pseudoinverse of zero is zero, also in dimension zero. -/
@[simp]
theorem covariancePseudoInverse_zero : (0 : Matrix ι ι ℝ).covariancePseudoInverse = 0 := by
  simp [covariancePseudoInverse, PosSemidef.zero]

/-- Every covariance pseudoinverse is positive semidefinite, including the invalid branch. -/
theorem posSemidef_covariancePseudoInverse (C : Matrix ι ι ℝ) :
    C.covariancePseudoInverse.PosSemidef := by
  by_cases hC : C.PosSemidef
  · rw [covariancePseudoInverse_of_posSemidef hC, ← nonneg_iff_posSemidef]
    exact cfc_nonneg fun x hx ↦ inv_nonneg.mpr (spectrum_nonneg_of_nonneg hC.nonneg hx)
  · simp [hC, PosSemidef.zero]

/-- A covariance matrix commutes with its pseudoinverse. -/
theorem commute_covariancePseudoInverse (C : Matrix ι ι ℝ) :
    Commute C C.covariancePseudoInverse := by
  by_cases hC : C.PosSemidef
  · rw [covariancePseudoInverse_of_posSemidef hC]
    simpa only [cfc_id' ℝ C hC.isHermitian.isSelfAdjoint] using
      cfc_commute_cfc (fun x : ℝ ↦ x) (fun x ↦ x⁻¹) C
  · simp [hC]

/-- The first Penrose equation for a positive-semidefinite matrix. -/
theorem mul_covariancePseudoInverse_mul {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    C * C.covariancePseudoInverse * C = C := by
  rw [covariancePseudoInverse_of_posSemidef hC]
  rw [hC.isHermitian.mul_cfc, hC.isHermitian.cfc_mul]
  calc
    _ = cfc (fun x : ℝ ↦ x) C := cfc_congr fun x _ ↦ mul_inv_mul_cancel x
    _ = C := cfc_id' ℝ C hC.isHermitian.isSelfAdjoint

/-- The second Penrose equation for a positive-semidefinite matrix. -/
theorem covariancePseudoInverse_mul_self_mul {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    C.covariancePseudoInverse * C * C.covariancePseudoInverse = C.covariancePseudoInverse := by
  rw [covariancePseudoInverse_of_posSemidef hC]
  rw [hC.isHermitian.cfc_mul,
    ← cfc_mul _ _ _ (C.finite_real_spectrum.continuousOn _)
      (C.finite_real_spectrum.continuousOn _)]
  exact cfc_congr fun x _ ↦ by simpa only [inv_inv] using mul_inv_mul_cancel x⁻¹

/-- The product of a covariance and its pseudoinverse is symmetric. -/
theorem isHermitian_mul_covariancePseudoInverse (C : Matrix ι ι ℝ) :
    (C * C.covariancePseudoInverse).IsHermitian := by
  by_cases hC : C.PosSemidef
  · rw [covariancePseudoInverse_of_posSemidef hC]
    rw [hC.isHermitian.mul_cfc]
    exact IsSelfAdjoint.isHermitian (IsSelfAdjoint.cfc)
  · simp [hC]

/-- The product of a covariance pseudoinverse and its covariance is symmetric. -/
theorem isHermitian_covariancePseudoInverse_mul (C : Matrix ι ι ℝ) :
    (C.covariancePseudoInverse * C).IsHermitian := by
  rw [← (commute_covariancePseudoInverse C).eq]
  exact isHermitian_mul_covariancePseudoInverse C

/-- The functional-calculus construction satisfies all four Moore–Penrose equations. -/
theorem isMoorePenroseInverse_covariancePseudoInverse {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    C.toEuclideanLin.IsMoorePenroseInverse C.covariancePseudoInverse.toEuclideanLin :=
  isMoorePenroseInverse_toEuclideanLin_of_penrose (mul_covariancePseudoInverse_mul hC)
    (covariancePseudoInverse_mul_self_mul hC) (isHermitian_mul_covariancePseudoInverse C)
    (isHermitian_covariancePseudoInverse_mul C)

/-- The four matrix Penrose equations characterize the covariance pseudoinverse. -/
theorem eq_covariancePseudoInverse_of_penrose {C D : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (h₁ : C * D * C = C) (h₂ : D * C * D = D)
    (h₃ : (C * D).IsHermitian) (h₄ : (D * C).IsHermitian) :
    D = C.covariancePseudoInverse :=
  toEuclideanLin.injective ((isMoorePenroseInverse_toEuclideanLin_of_penrose h₁ h₂ h₃ h₄).unique
    (isMoorePenroseInverse_covariancePseudoInverse hC))

/-- The covariance construction agrees with the existing Moore–Penrose inverse of the
Euclidean operator. -/
theorem toEuclideanLin_covariancePseudoInverse {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    C.covariancePseudoInverse.toEuclideanLin = C.toEuclideanLin.moorePenroseInverse :=
  (LinearMap.isMoorePenroseInverse_iff_eq_moorePenroseInverse _).mp
    (isMoorePenroseInverse_covariancePseudoInverse hC)

/-- At positive-definite covariance, the pseudoinverse is the ordinary inverse. -/
theorem covariancePseudoInverse_of_posDef {C : Matrix ι ι ℝ} (hC : C.PosDef) :
    C.covariancePseudoInverse = C⁻¹ := by
  rw [covariancePseudoInverse_of_posSemidef hC.posSemidef, nonsing_inv_eq_ringInverse]
  exact cfc_ringInverse_id C hC.isUnit hC.isHermitian.isSelfAdjoint

/-- Inverting the covariance pseudoinverse recovers every valid covariance. -/
@[simp]
theorem covariancePseudoInverse_covariancePseudoInverse {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) : C.covariancePseudoInverse.covariancePseudoInverse = C := by
  apply toEuclideanLin.injective
  exact (isMoorePenroseInverse_covariancePseudoInverse
    (posSemidef_covariancePseudoInverse C)).unique
      (isMoorePenroseInverse_covariancePseudoInverse hC).symm

/-- Multiplication by a covariance and its pseudoinverse is the orthogonal projection onto
its Euclidean range. `Submodule.starProjection` is the ambient inclusion composed with
`Submodule.orthogonalProjectionOnto`. -/
theorem toEuclideanLin_mul_covariancePseudoInverse {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    (C * C.covariancePseudoInverse).toEuclideanLin = C.toEuclideanLin.range.starProjection := by
  let f := C.toEuclideanLin
  let g := C.covariancePseudoInverse.toEuclideanLin
  have h := isMoorePenroseInverse_covariancePseudoInverse hC
  have hp : (f ∘ₗ g).IsSymmetricProjection := by
    refine ⟨?_, h.isSymmetric_comp⟩
    exact LinearMap.ext fun x ↦ h.apply_apply_apply (g x)
  have hr : LinearMap.range (f ∘ₗ g) = f.range := by
    apply le_antisymm (LinearMap.range_comp_le_range _ _)
    rintro _ ⟨x, rfl⟩
    exact ⟨f x, h.apply_apply_apply x⟩
  rw [toLpLin_mul_same]
  exact hp.ext (Submodule.isSymmetricProjection_starProjection f.range) (by simpa using hr)

/-- Multiplication by a covariance pseudoinverse and its covariance is the orthogonal
projection onto the covariance's Euclidean range. -/
theorem toEuclideanLin_covariancePseudoInverse_mul {C : Matrix ι ι ℝ}
    (hC : C.PosSemidef) :
    (C.covariancePseudoInverse * C).toEuclideanLin = C.toEuclideanLin.range.starProjection := by
  rw [← (commute_covariancePseudoInverse C).eq]
  exact toEuclideanLin_mul_covariancePseudoInverse hC

/-- For symmetric `C` and positive `ε`, `(C² + ε I)⁻¹ C` is the functional calculus of
`x ↦ x / (x² + ε)` at `C`, including when `C` is singular. -/
theorem inv_sq_add_smul_mul_eq_cfc {C : Matrix ι ι ℝ} (hC : C.IsHermitian)
    {ε : ℝ} (hε : 0 < ε) :
    (C ^ 2 + ε • 1)⁻¹ * C = cfc (fun x : ℝ ↦ x / (x ^ 2 + ε)) C := by
  have hcont (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ C) := C.finite_real_spectrum.continuousOn f
  have hden : ∀ x ∈ spectrum ℝ C, x ^ 2 + ε ≠ 0 := fun x _ ↦ by positivity
  have hquot : (fun x : ℝ ↦ x / (x ^ 2 + ε)) =
      fun x ↦ (x ^ 2 + ε)⁻¹ * x := by ext x; simp [div_eq_mul_inv, mul_comm]
  rw [hquot, cfc_mul _ _ _ (hcont _) (hcont _),
    cfc_inv (fun x : ℝ ↦ x ^ 2 + ε) C hden (hcont _) hC.isSelfAdjoint,
    cfc_add C (fun x : ℝ ↦ x ^ 2) (fun _ ↦ ε) (hcont _) (hcont _),
    cfc_pow_id C 2 hC.isSelfAdjoint, cfc_const ε C hC.isSelfAdjoint,
    cfc_id' ℝ C hC.isSelfAdjoint, Algebra.algebraMap_eq_smul_one,
    ← nonsing_inv_eq_ringInverse]

private theorem tendsto_pseudoinverse_regularization (x : ℝ) :
    Tendsto (fun ε : ℝ ↦ x / (x ^ 2 + ε)) (𝓝[>] 0) (𝓝 x⁻¹) := by
  by_cases hx : x = 0
  · simp [hx]
  · have he : Tendsto (fun ε : ℝ ↦ ε) (𝓝[>] 0) (𝓝 0) :=
      continuousWithinAt_id.tendsto
    convert (tendsto_const_nhds (x := x)).div
      ((tendsto_const_nhds (x := x ^ 2)).add he)
      (by simpa using pow_ne_zero 2 hx) using 1
    simp [div_eq_mul_inv, pow_two, hx]

/-- The covariance pseudoinverse is the limit of `(C² + ε I)⁻¹ C` as positive `ε` tends to zero.
The limit includes zero covariance and empty coordinate types. -/
theorem tendsto_inv_sq_add_smul_mul {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    Tendsto (fun ε : ℝ ↦ (C ^ 2 + ε • 1)⁻¹ * C)
      (nhdsWithin 0 (Set.Ioi 0)) (𝓝 C.covariancePseudoInverse) := by
  rw [covariancePseudoInverse_of_posSemidef hC]
  refine (TauCeti.tendsto_matrix_cfc_fun tendsto_pseudoinverse_regularization C).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  exact (inv_sq_add_smul_mul_eq_cfc hC.isHermitian hε).symm

/-- The totalized covariance pseudoinverse is Borel measurable in all matrix entries. -/
@[fun_prop]
theorem measurable_covariancePseudoInverse :
    Measurable (covariancePseudoInverse : Matrix ι ι ℝ → Matrix ι ι ℝ) := by
  classical
  exact Measurable.ite posSemidef_is_closed.measurableSet
    (TauCeti.measurable_matrix_cfc_of_tendsto
      (F := fun k x ↦ x / (x ^ 2 + 1 / (k + 1)))
      (fun _ ↦ continuous_id.div ((continuous_id.pow 2).add continuous_const)
        (fun _ ↦ by positivity))
      (fun x ↦ (tendsto_pseudoinverse_regularization x).comp
        (tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun _ ↦ Nat.one_div_pos_of_nat⟩)))
    measurable_const

end Matrix
