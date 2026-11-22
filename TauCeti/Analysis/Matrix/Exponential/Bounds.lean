/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.L2OpNorm
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.Normed.Algebra.Exponential
import TauCeti.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.ExpLog
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Deterministic Loewner and norm bounds for the matrix exponential

Deterministic order and operator-norm bounds for the matrix exponential `exp A` over any `RCLike`
scalar field `𝕜` (`ℝ` or `ℂ`):

* `TauCeti.isHermitian_of_le`, `TauCeti.isHermitian_of_le_smul_one`: Loewner domination by a
  Hermitian matrix or real scalar multiple of the identity implies Hermitianness.
* `Matrix.IsHermitian.smul_one_add_smul_eq_cfc`,
  `Matrix.IsHermitian.smul_one_add_smul_add_smul_mul_self_eq_cfc`: affine and quadratic
  functional-calculus normalizations for Hermitian matrices.
* `Matrix.IsHermitian.one_add_le_exp`: `1 + A ≤ exp A` for Hermitian `A`.
* `Matrix.IsHermitian.exp_neg_smul_one_le_exp_and_exp_le_exp_smul_one`: two-sided scalar Loewner
  bounds for `exp A` from `‖A‖ ≤ M`.
* `TauCeti.exp_le_exp_smul_one`: `exp A ≤ exp M • 1` from the one-sided bound `A ≤ M • 1`.
* `TauCeti.l2_opNorm_exp_le_exp_of_le`: `‖exp A‖ ≤ exp M` from `‖A‖ ≤ M`.
* `TauCeti.exp_smul_le_one_add_add_mul_self`: deterministic operator Bernstein bound from
  `A ≤ L • 1` (`0 ≤ L`, `0 ≤ θ`, `θ * L < 3`).

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math.
  **12** (2012), 389–434, Sections 3 and 6.
-/

public section

noncomputable section

open NormedSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜]

/-- If `B` is Hermitian and `A ≤ B` in the Loewner order, then `A` is Hermitian. -/
theorem isHermitian_of_le {A B : Matrix n n 𝕜} (hB : B.IsHermitian) (hle : A ≤ B) :
    A.IsHermitian := by
  simpa only [sub_sub_cancel] using hB.sub (Matrix.le_iff.1 hle).isHermitian

/-- Any matrix bounded above by a real scalar multiple of the identity in the Loewner order is
Hermitian. -/
theorem isHermitian_of_le_smul_one [DecidableEq n] {A : Matrix n n 𝕜} {c : ℝ}
    (hU : A ≤ c • (1 : Matrix n n 𝕜)) : A.IsHermitian :=
  isHermitian_of_le (Matrix.isHermitian_one.smul (IsSelfAdjoint.all c)) hU

end TauCeti

namespace Matrix

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- Normalization of `a • 1 + b • A` as a functional calculus expression for Hermitian `A`. -/
theorem IsHermitian.smul_one_add_smul_eq_cfc {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (a b : ℝ) :
    a • (1 : Matrix n n 𝕜) + b • A = cfc (fun x : ℝ ↦ a + b * x) A := by
  have hfin := A.finite_real_spectrum
  rw [cfc_add A (fun _ : ℝ ↦ a) (fun x : ℝ ↦ b * x) (hfin.continuousOn _) (hfin.continuousOn _),
    cfc_const_mul b (fun x : ℝ ↦ x) A (hfin.continuousOn _), cfc_id' ℝ A hA.isSelfAdjoint,
    ← Algebra.algebraMap_eq_smul_one a, cfc_const a A hA.isSelfAdjoint]

/-- Normalization of `a • 1 + b • A + c • (A * A)` as a functional calculus expression for
Hermitian `A`. -/
theorem IsHermitian.smul_one_add_smul_add_smul_mul_self_eq_cfc {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (a b c : ℝ) :
    a • (1 : Matrix n n 𝕜) + b • A + c • (A * A) =
      cfc (fun x : ℝ ↦ a + b * x + c * x ^ 2) A := by
  have hfin := A.finite_real_spectrum
  rw [cfc_add A (fun x : ℝ ↦ a + b * x) (fun x : ℝ ↦ c * x ^ 2)
      (hfin.continuousOn _) (hfin.continuousOn _),
    hA.smul_one_add_smul_eq_cfc a b,
    cfc_const_mul c (fun x : ℝ ↦ x ^ 2) A (hfin.continuousOn _),
    cfc_pow_id A 2 hA.isSelfAdjoint, sq]

/-- For a Hermitian matrix `A`, `1 + A ≤ exp A` in the Loewner order. -/
theorem IsHermitian.one_add_le_exp {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    1 + A ≤ exp A := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint]
  have h1A : (1 : Matrix n n 𝕜) + A = cfc (fun x : ℝ ↦ 1 + x) A := by
    simpa only [one_smul, one_mul] using hA.smul_one_add_smul_eq_cfc 1 1
  exact h1A ▸ cfc_mono fun x _ ↦ by linarith [Real.add_one_le_exp x]

/-- For a Hermitian matrix with `‖A‖ ≤ M`, `exp (-M) • 1 ≤ exp A ≤ exp M • 1` in the Loewner
order. -/
theorem IsHermitian.exp_neg_smul_one_le_exp_and_exp_le_exp_smul_one {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) {M : ℝ} (hbdd : ‖A‖ ≤ M) :
    Real.exp (-M) • (1 : Matrix n n 𝕜) ≤ exp A ∧
      exp A ≤ Real.exp M • (1 : Matrix n n 𝕜) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hspec (x : ℝ) (hx : x ∈ spectrum ℝ A) : -M ≤ x ∧ x ≤ M := by
    rw [hA.spectrum_real_eq_range_eigenvalues] at hx
    obtain ⟨i, rfl⟩ := hx
    have h := norm_le_pi_norm hA.eigenvalues i
    rw [Real.norm_eq_abs, ← hA.l2_opNorm_eq_norm_eigenvalues] at h
    exact abs_le.1 (h.trans hbdd)
  have hconst (r : ℝ) : r • (1 : Matrix n n 𝕜) = cfc (fun _ : ℝ ↦ r) A := by
    rw [← Algebra.algebraMap_eq_smul_one, cfc_const r A hA.isSelfAdjoint]
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hconst, hconst]
  exact ⟨cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).1,
    cfc_mono fun x hx ↦ Real.exp_le_exp.2 (hspec x hx).2⟩

end Matrix

namespace TauCeti

variable {𝕜 n : Type*} [RCLike 𝕜] [Fintype n] [DecidableEq n]

/-- If `A ≤ M • 1` in the Loewner order, then `exp A ≤ exp M • 1`. -/
theorem exp_le_exp_smul_one {A : Matrix n n 𝕜} {M : ℝ} (hU : A ≤ M • (1 : Matrix n n 𝕜)) :
    exp A ≤ Real.exp M • (1 : Matrix n n 𝕜) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hA : A.IsHermitian := isHermitian_of_le_smul_one hU
  have hconst : Real.exp M • (1 : Matrix n n 𝕜) = cfc (fun _ : ℝ ↦ Real.exp M) A := by
    rw [← Algebra.algebraMap_eq_smul_one, cfc_const (Real.exp M) A hA.isSelfAdjoint]
  rw [← CFC.real_exp_eq_normedSpace_exp hA.isSelfAdjoint, hconst]
  refine cfc_mono fun x hx ↦ Real.exp_le_exp.2 ?_
  exact (le_algebraMap_iff_spectrum_le (ha := hA.isSelfAdjoint)).1
    (by simpa [Algebra.algebraMap_eq_smul_one] using hU) x hx

/-- For any square matrix with `‖A‖ ≤ M`, `‖exp A‖ ≤ exp M`. -/
theorem l2_opNorm_exp_le_exp_of_le {A : Matrix n n 𝕜} {M : ℝ} (hbdd : ‖A‖ ≤ M) :
    ‖exp A‖ ≤ Real.exp M := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  exact (TauCeti.norm_exp_le_exp_norm Matrix.l2_opNorm_one_le A).trans (Real.exp_le_exp.2 hbdd)

/-- **Deterministic operator Bernstein bound.** For `A ≤ L • 1` with `0 ≤ L`, `0 ≤ θ`, and
`θ * L < 3`, `exp (θ • A) ≤ 1 + θ • A + (θ ^ 2 / (2 * (1 - θ * L / 3))) • (A * A)`. -/
theorem exp_smul_le_one_add_add_mul_self {A : Matrix n n 𝕜} {L θ : ℝ} (hL : 0 ≤ L)
    (hU : A ≤ L • (1 : Matrix n n 𝕜)) (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    exp (θ • A) ≤ (1 : Matrix n n 𝕜) + θ • A + (θ ^ 2 / (2 * (1 - θ * L / 3))) • (A * A) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hA : A.IsHermitian := isHermitian_of_le_smul_one hU
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hexp_cfc : exp (θ • A) = cfc (fun x : ℝ ↦ Real.exp (θ * x)) A := by
    rw [← CFC.real_exp_eq_normedSpace_exp (hA.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
      ← cfc_comp_const_mul θ Real.exp A Real.continuous_exp.continuousOn hA.isSelfAdjoint]
  have hpoly_cfc : (1 : Matrix n n 𝕜) + θ • A + c • (A * A) =
      cfc (fun x : ℝ ↦ 1 + θ * x + c * x ^ 2) A := by
    simpa only [one_smul, one_mul] using hA.smul_one_add_smul_add_smul_mul_self_eq_cfc 1 θ c
  rw [hexp_cfc, hpoly_cfc]
  refine cfc_mono fun x hx ↦ ?_
  have hxL : x ≤ L := (le_algebraMap_iff_spectrum_le (ha := hA.isSelfAdjoint)).1
    (by simpa [Algebra.algebraMap_eq_smul_one] using hU) x hx
  have hbern := Real.exp_le_one_add_add_sq_div_of_le
    (mul_le_mul_of_nonneg_left hxL hθ) (mul_nonneg hθ hL) hθL
  have hc_eq : (θ * x) ^ 2 / (2 * (1 - θ * L / 3)) = c * x ^ 2 := by
    dsimp only [c]; ring
  linarith

end TauCeti
