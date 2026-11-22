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

* `TauCeti.integrable_exp_of_ae_le_smul_one`, `TauCeti.integrable_exp_apply_of_ae_le_smul_one`,
  `TauCeti.integrable_re_trace_exp_of_ae_le_smul_one`, `TauCeti.integrable_re_trace_exp`:
  Bochner, entrywise, and real-trace integrability of `exp (Z ω)`.
* `TauCeti.posDef_integral_exp`: positive definiteness of `E[exp X]` under an a.e. scalar Loewner
  upper bound.
* `TauCeti.cfc_log_integral_exp_le_of_le_one_add` and
  `TauCeti.re_trace_exp_sum_cfc_log_le_of_sum_le`: shared CGF comparison and trace-CGF summing
  helpers for matrix concentration inequalities.
-/

public section

open MeasureTheory Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

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
  have hH := isHermitian_of_le_smul_one hU
  exact hH.posDef_exp.posSemidef.l2_opNorm_le_of_le_smul_one (Real.exp_pos M).le
    (exp_le_exp_smul_one hU)

/-- Entrywise integrability of `ω ↦ exp (Z ω)` under an a.e. upper Loewner bound `Z ≤ M • 1`. -/
theorem integrable_exp_apply_of_ae_le_smul_one [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜))
    (i j : n) :
    Integrable (fun ω ↦ (NormedSpace.exp (Z ω)) i j) P :=
  (integrable_l2Op_matrix_iff.1 (integrable_exp_of_ae_le_smul_one hmeas hupper)) i j

/-- Integrability of `ω ↦ Re Tr (exp (Z ω))` under an a.e. upper Loewner bound `Z ≤ M • 1`. -/
theorem integrable_re_trace_exp_of_ae_le_smul_one [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜)) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (Z ω)).trace) P := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  have hcont := continuous_re_trace.comp (NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜))
  refine Integrable.of_bound (hcont.measurable.comp_aemeasurable hmeas).aestronglyMeasurable
    ((Fintype.card n : ℝ) * Real.exp M) (hupper.mono fun ω hU ↦ ?_)
  have hH := isHermitian_of_le_smul_one hU
  rw [Real.norm_eq_abs, abs_of_nonneg hH.re_trace_exp_nonneg]
  exact re_trace_exp_le_card_mul_exp hU

/-- Integrability of `ω ↦ Re Tr (exp (Z ω))` for an a.e. operator-norm bounded Hermitian random
matrix. -/
theorem integrable_re_trace_exp [IsFiniteMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) (hherm : ∀ᵐ ω ∂P, (Z ω).IsHermitian)
    {M : ℝ} (hbdd : ∀ᵐ ω ∂P, ‖Z ω‖ ≤ M) :
    Integrable (fun ω ↦ RCLike.re (NormedSpace.exp (Z ω)).trace) P :=
  integrable_re_trace_exp_of_ae_le_smul_one hmeas
    ((hherm.and hbdd).mono fun _ ⟨h1, h2⟩ ↦ h1.le_smul_one_of_l2_opNorm_le h2)

/-- Under a probability measure, the entrywise expectation of `exp X` for a random matrix
satisfying an a.e. scalar Loewner upper bound `X ≤ M • 1` is positive definite. -/
theorem posDef_integral_exp [IsProbabilityMeasure P] {X : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable X P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ M • (1 : Matrix n n 𝕜)) :
    (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P).PosDef := by
  have hint := integrable_exp_apply_of_ae_le_smul_one hmeas hupper
  have hherm : ∀ᵐ ω ∂P, (NormedSpace.exp (X ω)).IsHermitian :=
    hupper.mono fun _ hU ↦ (isHermitian_of_le_smul_one hU).posDef_exp.isHermitian
  refine Matrix.PosDef.of_dotProduct_mulVec_pos
    (isHermitian_integral_of_ae_isHermitian hherm) fun c hc ↦ ?_
  have hquad : star c ⬝ᵥ ((Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (X ω)) i j ∂P) *ᵥ c) =
      ∫ ω, star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c) ∂P := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
    rw [integral_finsetSum _ fun i _ ↦
      (integrable_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)).const_mul _]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [integral_const_mul, integral_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)]
    simp only [integral_mul_const]
  have hquad_int : Integrable (fun ω ↦ star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) P := by
    simp only [dotProduct, Matrix.mulVec]
    exact integrable_finsetSum _ fun i _ ↦
      (integrable_finsetSum _ fun j _ ↦ (hint i j).mul_const (c j)).const_mul _
  have hpos_ae : ∀ᵐ ω ∂P, 0 < RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) :=
    hupper.mono fun ω hU ↦ by
      have hP := (isHermitian_of_le_smul_one hU).posDef_exp
      exact (RCLike.pos_iff.1 (hP.dotProduct_mulVec_pos hc)).1
  have him_ae : ∀ᵐ ω ∂P, RCLike.im (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) = 0 :=
    hupper.mono fun ω hU ↦ by
      have hP := (isHermitian_of_le_smul_one hU).posDef_exp
      exact (RCLike.pos_iff.1 (hP.dotProduct_mulVec_pos hc)).2
  have hre_pos : 0 < RCLike.re (∫ ω, star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c) ∂P) := by
    rw [← RCLike.reCLM_apply, ← RCLike.reCLM.integral_comp_comm hquad_int]
    refine (integral_pos_iff_support_of_nonneg_ae (hpos_ae.mono fun _ h ↦ h.le)
      (RCLike.reCLM.integrable_comp hquad_int)).2 ?_
    have hsup : {ω | RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) = 0} ≤ᵐ[P]
        (∅ : Set Ω) :=
      hpos_ae.mono fun _ h h0 ↦ h.ne' h0
    have hP0 : P {ω | RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) = 0} = 0 :=
      nonpos_iff_eq_zero.1 ((measure_mono_ae hsup).trans (by simp))
    have hunion : P Set.univ ≤
        P (Function.support fun ω ↦ RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c))) +
          P {ω | RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) = 0} := by
      refine (measure_mono fun ω _ ↦ ?_).trans (measure_union_le _ _)
      by_cases h0 : RCLike.re (star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c)) = 0
      · exact Or.inr h0
      · exact Or.inl h0
    rw [measure_univ, hP0, add_zero] at hunion
    exact lt_of_lt_of_le zero_lt_one hunion
  have him_zero : RCLike.im (∫ ω, star c ⬝ᵥ (NormedSpace.exp (X ω) *ᵥ c) ∂P) = 0 := by
    rw [← RCLike.imCLM_apply, ← RCLike.imCLM.integral_comp_comm hquad_int]
    exact integral_eq_zero_of_ae him_ae
  rw [hquad]
  exact RCLike.pos_iff.2 ⟨hre_pos, him_zero⟩

/-- Shared matrix CGF step: if `Z` satisfies an a.e. scalar Loewner upper bound `Z ≤ M • 1`, `B`
is Hermitian, and `E[exp Z] ≤ 1 + B`, then `log E[exp Z] ≤ B`. -/
theorem cfc_log_integral_exp_le_of_le_one_add [IsProbabilityMeasure P] {Z : Ω → Matrix n n 𝕜}
    (hmeas : AEMeasurable Z P) {M : ℝ} (hupper : ∀ᵐ ω ∂P, Z ω ≤ M • (1 : Matrix n n 𝕜))
    {B : Matrix n n 𝕜} (hB : B.IsHermitian)
    (hEB : Matrix.of (fun i j ↦ ∫ ω, (NormedSpace.exp (Z ω)) i j ∂P) ≤ (1 : Matrix n n 𝕜) + B) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (Z ω)) i j ∂P) ≤ B :=
  ((posDef_integral_exp hmeas hupper).cfc_log_le_cfc_log (hEB.trans hB.one_add_le_exp)).trans_eq
    hB.cfc_log_exp

end

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
