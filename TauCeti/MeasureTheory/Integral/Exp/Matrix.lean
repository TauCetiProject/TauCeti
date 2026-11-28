/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Analysis.Matrix.Order
public import TauCeti.Analysis.Matrix.Exponential.TraceInequalities
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Matrix.Trace.Basic
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.MeasureTheory.Integral.Matrix
import TauCeti.MeasureTheory.Integral.PosSemidef

/-!
# Integrability and expectations of matrix exponentials

Integrability, positive definiteness, and cumulant generating function (CGF) helpers for random
matrix exponentials `ω ↦ exp (Z ω)` under almost-everywhere scalar Loewner upper bounds
`Z ω ≤ M • 1`.

## Main results

* `AEMeasurable.integrable_exp_of_ae_le_smul_one`,
  `AEMeasurable.integrable_exp_apply_of_ae_le_smul_one`,
  `AEMeasurable.integrable_re_trace_exp_of_ae_le_smul_one`,
  `AEMeasurable.integrable_re_trace_exp`: Bochner, entrywise, and real-trace integrability of
  `exp (Z ω)`.
* `AEMeasurable.posDef_integral_exp`: positive definiteness of `E[exp X]` under an a.e. scalar
  Loewner upper bound.
* `AEMeasurable.cfc_log_integral_exp_le_of_le_one_add` and
  `TauCeti.re_trace_exp_sum_cfc_log_le_of_sum_le`: shared CGF comparison and trace-CGF summing
  helpers for matrix concentration inequalities.
-/

public section

open MeasureTheory Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace AEMeasurable

section

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]
  [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- Under `Matrix.Norms.L2Operator`, `ω ↦ exp (Z ω)` is Bochner integrable whenever `Z` is
a.e. measurable and satisfies an a.e. upper Loewner bound `Z ≤ M • 1`. -/
theorem integrable_exp_of_ae_le_smul_one [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜)) :
    Integrable (fun ω ↦ NormedSpace.exp (Z ω)) P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  refine Integrable.of_bound
    ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable
      hmeas).aestronglyMeasurable
    (Real.exp M) (hupper.mono fun ω hU ↦ ?_)
  have hH := TauCeti.isHermitian_of_le_smul_one hU
  exact hH.posDef_exp.posSemidef.l2_opNorm_le_of_le_smul_one (Real.exp_pos M).le
    (TauCeti.exp_le_exp_smul_one hU)

/-- Entrywise integrability of `ω ↦ exp (Z ω)` under an a.e. upper Loewner bound `Z ≤ M • 1`. -/
theorem integrable_exp_apply_of_ae_le_smul_one [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜))
    (i j : n) :
    Integrable (fun ω ↦ (NormedSpace.exp (Z ω)) i j) P :=
  (TauCeti.integrable_l2Op_matrix_iff.1 (hmeas.integrable_exp_of_ae_le_smul_one hupper)) i j

/-- Integrability of `ω ↦ Re Tr (exp (Z ω))` under an a.e. upper Loewner bound `Z ≤ M • 1`. -/
theorem integrable_re_trace_exp_of_ae_le_smul_one [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜)) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (Z ω)).trace) P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hcont := TauCeti.continuous_re_trace.comp (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜))
  refine Integrable.of_bound (hcont.measurable.comp_aemeasurable hmeas).aestronglyMeasurable
    ((Fintype.card n : ℝ) * Real.exp M) (hupper.mono fun ω hU ↦ ?_)
  have hH := TauCeti.isHermitian_of_le_smul_one hU
  rw [Real.norm_eq_abs, abs_of_nonneg hH.re_trace_exp_nonneg]
  exact TauCeti.re_trace_exp_le_card_mul_exp hU

/-- Integrability of `ω ↦ Re Tr (exp (Z ω))` for an a.e. operator-norm bounded Hermitian random
matrix. -/
theorem integrable_re_trace_exp [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) (hherm : ∀ᵐ ω ∂P, (Z ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ M) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (Z ω)).trace) P :=
  hmeas.integrable_re_trace_exp_of_ae_le_smul_one
    ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ h1.le_smul_one_of_l2_opNorm_le h2)

/-- Under a nonzero finite measure, the entrywise expectation of `exp X` for a random matrix
satisfying an a.e. scalar Loewner upper bound `X ≤ M • 1` is positive definite. -/
theorem posDef_integral_exp [IsFiniteMeasure P] [NeZero P] {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ M • (1 : Matrix n n 𝕜)) :
    (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P).PosDef :=
  TauCeti.posDef_integral
    (hupper.mono fun _ hU ↦ (TauCeti.isHermitian_of_le_smul_one hU).posDef_exp)
    (hmeas.integrable_exp_apply_of_ae_le_smul_one hupper)

/-- Shared matrix CGF step: if `Z` satisfies an a.e. scalar Loewner upper bound `Z ≤ M • 1`, `B`
is Hermitian, and `E[exp Z] ≤ 1 + B`, then `log E[exp Z] ≤ B`. -/
theorem cfc_log_integral_exp_le_of_le_one_add [IsFiniteMeasure P] [NeZero P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (hEB : Matrix.of (fun i j ↦ ∫ ω, (NormedSpace.exp (Z ω)) i j ∂P) ≤ (1 : Matrix n n 𝕜) + B) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (Z ω)) i j ∂P) ≤ B :=
  ((hmeas.posDef_integral_exp hupper).cfc_log_le_cfc_log (hEB.trans hB.one_add_le_exp)).trans_eq
    hB.cfc_log_exp

end

end AEMeasurable

namespace TauCeti

/-- Shared trace-CGF summing step: given `log E[exp (X k)] ≤ B k` for `k ∈ s` and
`∑ k ∈ s, B k ≤ b • 1`, we have `Re Tr exp (∑ k ∈ s, log E[exp (X k)]) ≤ card n * exp b`. -/
theorem re_trace_exp_sum_cfc_log_le_of_sum_le {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [RCLike 𝕜] [Fintype n] [DecidableEq n] (s : Finset ι)
    {X : ι → Ω → Matrix n n 𝕜} {B : ι → Matrix n n 𝕜}
    (hcgf : ∀ k ∈ s,
      cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X k ω)) i j ∂P) ≤ B k)
    {b : ℝ} (hb : ∑ k ∈ s, B k ≤ b • (1 : Matrix n n 𝕜)) :
    RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X k ω)) i j ∂P))).trace ≤
      (Fintype.card n : ℝ) * Real.exp b :=
  re_trace_exp_le_card_mul_exp ((Finset.sum_le_sum hcgf).trans hb)

end TauCeti
