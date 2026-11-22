/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Matrix.Laplace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Exponential.Bounds
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Matrix.Spectrum
import TauCeti.MeasureTheory.Integral.Exp.Matrix
import TauCeti.MeasureTheory.Integral.Matrix
import TauCeti.MeasureTheory.Integral.PosSemidef

/-!
# Matrix Chernoff inequalities

Tropp's matrix Chernoff inequalities for finite sums of independent random positive semidefinite
matrices over any `RCLike` field `𝕜` (`ℝ` or `ℂ`):

* `TauCeti.cfc_log_integral_exp_smul_le_of_posSemidef`: Chernoff matrix CGF bound (Tropp 2012,
  Lemma 5.8).
* `ProbabilityTheory.iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_posSemidef` and
  `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_posSemidef`: upper eigenvalue
  and operator-norm Chernoff tails (Tropp 2012, Theorem 1.1(i)).
* `ProbabilityTheory.iIndepFun.measureReal_sInf_spectrum_sum_le_le_of_posSemidef`: lower
  eigenvalue Chernoff tail for `δ ∈ [0, 1]` including `δ = 1` (Tropp 2012, Theorem 1.1(ii)).
* `ProbabilityTheory.measureReal_sSup_spectrum_sum_ge_eq_zero_of_le_zero`,
  `ProbabilityTheory.measureReal_l2_opNorm_sum_ge_eq_zero_of_le_zero`, and
  `ProbabilityTheory.measureReal_sInf_spectrum_sum_le_eq_zero_of_le_zero`: degenerate `L = 0`
  bounds.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, Theorem 1.1 and Section 5.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- **Chernoff matrix cumulant generating function bound** (Tropp 2012, Lemma 5.8). Let `Y` be a
random positive semidefinite matrix over `𝕜` (`ℝ` or `ℂ`) satisfying `Y ≤ L • 1` almost everywhere
with `0 < L`. Then for every real `θ`,
`log E[exp (θ Y)] ≤ ((exp (θ * L) - 1) / L) • E[Y]`. -/
theorem cfc_log_integral_exp_smul_le_of_posSemidef [IsProbabilityMeasure P]
    {Y : Ω → Matrix n n 𝕜} (hmeas : AEMeasurable Y P)
    (hpsd : ∀ᵐ ω ∂P, (Y ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ᵐ ω ∂P, Y ω ≤ L • (1 : Matrix n n 𝕜)) (θ : ℝ) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y ω)) i j ∂P) ≤
      ((Real.exp (θ * L) - 1) / L) • (Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set c : ℝ := (Real.exp (θ * L) - 1) / L
  -- Scalar convexity bound `exp (θ x) ≤ 1 + c * x` for `0 ≤ x ≤ L`, lifted via CFC.
  have hpt : ∀ᵐ ω ∂P, NormedSpace.exp (θ • Y ω) ≤ (1 : Matrix n n 𝕜) + c • Y ω := by
    refine (hpsd.and hupper).mono fun ω ⟨hP, hU⟩ ↦ ?_
    have hpoly : (1 : Matrix n n 𝕜) + c • Y ω = cfc (fun x : ℝ ↦ 1 + c * x) (Y ω) := by
      simpa only [one_smul] using hP.1.smul_one_add_smul_eq_cfc 1 c
    rw [← CFC.real_exp_eq_normedSpace_exp (hP.1.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
      ← cfc_comp_const_mul θ Real.exp (Y ω) Real.continuous_exp.continuousOn hP.1.isSelfAdjoint,
      hpoly]
    refine cfc_mono fun x hx ↦ ?_
    have hx0 := (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hP.1.isSelfAdjoint).1 hP.nonneg x hx
    have hxL := (le_algebraMap_iff_spectrum_le (ha := hP.1.isSelfAdjoint)).1
      (by simpa [Algebra.algebraMap_eq_smul_one] using hU) x hx
    have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * L))
      (sub_nonneg.2 ((div_le_one hL).2 hxL)) (div_nonneg hx0 hL.le) (sub_add_cancel 1 (x / L))
    have harg : (1 - x / L) • (0 : ℝ) + (x / L) • (θ * L) = θ * x := by
      simp only [smul_eq_mul]; field_simp [hL.ne']; ring
    have hval : (1 - x / L) • Real.exp 0 + (x / L) • Real.exp (θ * L) = 1 + c * x := by
      simp only [smul_eq_mul, Real.exp_zero, c]; field_simp [hL.ne']; ring
    rwa [harg, hval] at hconv
  have hY_bdd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ L :=
    (hpsd.and hupper).mono fun _ ⟨hP, hU⟩ ↦ hP.l2_opNorm_le_of_le_smul_one hL.le hU
  have hY_int : Integrable Y P := integrable_l2Op_of_ae_l2_opNorm_le hmeas hY_bdd
  have hY1_int : Integrable (fun ω ↦ (1 : Matrix n n 𝕜) + c • Y ω) P :=
    (integrable_const (1 : Matrix n n 𝕜)).add (hY_int.smul c)
  have hθY_meas := (continuous_const_smul θ).measurable.comp_aemeasurable hmeas
  have hθY_upper : ∀ᵐ ω ∂P, θ • Y ω ≤ (|θ| * L) • (1 : Matrix n n 𝕜) :=
    (hpsd.and hY_bdd).mono fun _ ⟨hP, hbdd⟩ ↦
      (hP.1.smul (IsSelfAdjoint.all θ)).le_smul_one_of_l2_opNorm_le <| by
        simpa only [norm_smul, Real.norm_eq_abs] using mul_le_mul_of_nonneg_left hbdd (abs_nonneg θ)
  have hE_le := integral_le_integral_of_ae_le hpt
    (integrable_exp_apply_of_ae_le_smul_one hθY_meas hθY_upper)
    (integrable_l2Op_matrix_iff.1 hY1_int)
  have hE_rhs : (Matrix.of fun i j ↦ ∫ ω, ((1 : Matrix n n 𝕜) + c • Y ω) i j ∂P) =
      (1 : Matrix n n 𝕜) + c • (Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P) := by
    have hadd := integral_add (f := fun _ ↦ (1 : Matrix n n 𝕜)) (g := fun ω ↦ c • Y ω)
      (integrable_const _) (hY_int.smul c)
    rw [← integral_l2Op_matrix_eq_of hY1_int, hadd, integral_const, probReal_univ, one_smul,
      integral_smul, integral_l2Op_matrix_eq_of hY_int]
  rw [hE_rhs] at hE_le
  have hcM_herm : (c • (Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P)).IsHermitian :=
    (isHermitian_integral_of_ae_isHermitian (hpsd.mono fun _ h ↦ h.1)).smul (IsSelfAdjoint.all c)
  exact cfc_log_integral_exp_le_of_le_one_add hθY_meas hθY_upper hcM_herm hE_le

end TauCeti

namespace ProbabilityTheory

section PositiveBound

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- Common CGF trace bound for independent bounded PSD matrices: given
`((exp (θ * L) - 1) / L) • ∑ E[Y k] ≤ b • 1`, we have
`Re Tr exp (∑ log E[exp (θ Y k)]) ≤ card n * exp b`. -/
private theorem re_trace_exp_sum_cfc_log_le_of_posSemidef [IsProbabilityMeasure P]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hmeas : ∀ k ∈ s, AEMeasurable (Y k) P)
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ L • (1 : Matrix n n 𝕜))
    (θ : ℝ) {b : ℝ}
    (hb : ((Real.exp (θ * L) - 1) / L) • (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P) ≤
      b • (1 : Matrix n n 𝕜)) :
    RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P))).trace ≤
      (Fintype.card n : ℝ) * Real.exp b := by
  have hsum_eq : ∑ k ∈ s, ((Real.exp (θ * L) - 1) / L) •
        (Matrix.of fun i j ↦ ∫ ω, Y k ω i j ∂P) =
      ((Real.exp (θ * L) - 1) / L) • (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P) := by
    rw [← Finset.smul_sum]
    ext; simp
  exact TauCeti.re_trace_exp_sum_cfc_log_le_of_sum_le s
    (fun k hk ↦ TauCeti.cfc_log_integral_exp_smul_le_of_posSemidef
      (hmeas k hk) (hpsd k hk) hL (hupper k hk) θ)
    (hsum_eq ▸ hb)

/-- **Matrix Chernoff upper tail bound** (Tropp 2012, Theorem 1.1(i)). Let `Y k` (`k ∈ s`) be
independent random positive semidefinite matrices over `𝕜` (`ℝ` or `ℂ`) on a nonempty index type
`n`, satisfying `Y k ≤ L • 1` almost everywhere (`0 < L`), and suppose
`∑ k ∈ s, E[Y k] ≤ μ_max • 1`. Then for every `δ ≥ 0`,
`P {λ_max (∑ k ∈ s, Y k) ≥ (1 + δ) * μ_max} ≤ card n * (exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L)`.
-/
theorem iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_posSemidef [IsProbabilityMeasure P]
    [Nonempty n] {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun Y P)
    (hmeas : ∀ k ∈ s, AEMeasurable (Y k) P)
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ L • (1 : Matrix n n 𝕜))
    {μ_max : ℝ}
    (hM : (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P) ≤ μ_max • (1 : Matrix n n 𝕜))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    P.real {ω | (1 + δ) * μ_max ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} ≤
      (Fintype.card n : ℝ) * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L) := by
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [add_zero, Real.exp_zero, Real.one_rpow, div_one, mul_one]
    exact measureReal_le_one.trans (by exact_mod_cast Fintype.card_pos (α := n))
  have h1δ : 0 < 1 + δ := by linarith
  set θ : ℝ := Real.log (1 + δ) / L
  have hlap := hindep.measureReal_sSup_spectrum_sum_ge_le hmeas
    (fun k hk ↦ ⟨L, hupper k hk⟩) (θ := θ) (t := (1 + δ) * μ_max)
    (div_pos (Real.log_pos (by linarith)) hL)
  have hexpθL : (Real.exp (θ * L) - 1) / L = δ / L := by
    have hθL : θ * L = Real.log (1 + δ) := div_mul_cancel₀ _ hL.ne'
    rw [hθL, Real.exp_log h1δ, add_sub_cancel_left]
  have htr_le := re_trace_exp_sum_cfc_log_le_of_posSemidef hmeas hpsd hL hupper θ
    (b := δ * μ_max / L) (by
      rw [hexpθL]
      exact (smul_le_smul_of_nonneg_left hM (div_nonneg hδ.le hL.le)).trans_eq
        (by rw [smul_smul, div_mul_eq_mul_div]))
  have hrhs_eq : Real.exp (-θ * ((1 + δ) * μ_max) + δ * μ_max / L) =
      (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L) := by
    rw [Real.rpow_def_of_pos (div_pos (Real.exp_pos δ) (Real.rpow_pos_of_pos h1δ _)),
      Real.log_div (Real.exp_pos δ).ne' (Real.rpow_pos_of_pos h1δ _).ne',
      Real.log_exp, Real.log_rpow h1δ]
    congr 1; dsimp only [θ]; ring
  calc
    P.real {ω | (1 + δ) * μ_max ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))}
        ≤ Real.exp (-θ * ((1 + δ) * μ_max)) *
            ((Fintype.card n : ℝ) * Real.exp (δ * μ_max / L)) :=
          hlap.trans (mul_le_mul_of_nonneg_left htr_le (Real.exp_pos _).le)
    _ = (Fintype.card n : ℝ) * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L) := by
          rw [← hrhs_eq, Real.exp_add]; ring

/-- **Matrix Chernoff operator-norm upper tail bound** (Tropp 2012, Theorem 1.1(i)). Let `Y k`
(`k ∈ s`) be independent random positive semidefinite matrices over `𝕜` (`ℝ` or `ℂ`) on a nonempty
index type `n`, satisfying `Y k ≤ L • 1` almost everywhere (`0 < L`), and let
`μ_max = ‖∑ k ∈ s, E[Y k]‖`. Then for every `δ ≥ 0`,
`P {‖∑ k ∈ s, Y k‖ ≥ (1 + δ) * μ_max} ≤ card n * (exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L)`. -/
theorem iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_posSemidef [IsProbabilityMeasure P]
    [Nonempty n] {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun Y P)
    (hmeas : ∀ k ∈ s, AEMeasurable (Y k) P)
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ L • (1 : Matrix n n 𝕜))
    {δ : ℝ} (hδ : 0 ≤ δ) :
    P.real {ω | (1 + δ) * ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P‖ ≤
        ‖∑ k ∈ s, Y k ω‖} ≤
      (Fintype.card n : ℝ) * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P‖ / L) := by
  set M : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P
  have hM_split : M = ∑ k ∈ s, Matrix.of fun i j ↦ ∫ ω, Y k ω i j ∂P := by ext; simp [M]
  have hM_psd : M.PosSemidef := hM_split ▸ Matrix.posSemidef_sum s fun k hk ↦
    TauCeti.posSemidef_integral (hpsd k hk)
      (TauCeti.integrable_apply_of_ae_l2_opNorm_le (hmeas k hk)
        (((hpsd k hk).and (hupper k hk)).mono fun _ ⟨hP, hU⟩ ↦
          hP.l2_opNorm_le_of_le_smul_one hL.le hU))
  refine (ENNReal.toReal_mono (measure_ne_top P _) <| measure_mono_ae <|
    (TauCeti.ae_posSemidef_finsetSum hpsd).mono fun ω hω hge ↦ by
      simp only [Set.mem_ofPred_eq] at hge ⊢
      rwa [hω.1.sSup_spectrum_real_eq_eigenvalues₀_zero, ← hω.l2_opNorm_eq_eigenvalues₀_zero]).trans
    (hindep.measureReal_sSup_spectrum_sum_ge_le_of_posSemidef hmeas hpsd hL hupper
      hM_psd.le_l2_opNorm_smul_one hδ)

/-- **Matrix Chernoff lower tail bound** (Tropp 2012, Theorem 1.1(ii)). Let `Y k` (`k ∈ s`) be
independent random positive semidefinite matrices over `𝕜` (`ℝ` or `ℂ`) on a nonempty index type
`n`, satisfying `Y k ≤ L • 1` almost everywhere (`0 < L`), and suppose
`μ_min • 1 ≤ ∑ k ∈ s, E[Y k]`. Then for every `δ ∈ [0, 1]`,
`P {λ_min (∑ k ∈ s, Y k) ≤ (1 - δ) * μ_min}` is bounded by
`card n * (exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μ_min / L)`. At the endpoint `δ = 1`,
`0 ^ (0 : ℝ) = 1` reduces the right-hand side to `card n * exp (-μ_min / L)`. -/
theorem iIndepFun.measureReal_sInf_spectrum_sum_le_le_of_posSemidef [IsProbabilityMeasure P]
    [Nonempty n] {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun Y P)
    (hmeas : ∀ k ∈ s, AEMeasurable (Y k) P)
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ L • (1 : Matrix n n 𝕜))
    {μ_min : ℝ}
    (hM : μ_min • (1 : Matrix n n 𝕜) ≤ Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P)
    {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) :
    P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ (1 - δ) * μ_min} ≤
      (Fintype.card n : ℝ) * (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μ_min / L) := by
  rcases hδ0.eq_or_lt with rfl | hδ0
  · simp only [sub_zero, neg_zero, Real.exp_zero, Real.one_rpow, div_one, mul_one]
    exact measureReal_le_one.trans (by exact_mod_cast Fintype.card_pos (α := n))
  -- Common Laplace + Chernoff-CGF upper bound valid for every `θ > 0` and every `t : ℝ`.
  have hparam (θ : ℝ) (hθ : 0 < θ) (t : ℝ) :
      P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} ≤
        (Fintype.card n : ℝ) * Real.exp (θ * t + ((Real.exp (-θ * L) - 1) / L) * μ_min) := by
    have hlap := hindep.measureReal_sInf_spectrum_sum_le_le hmeas
      (fun k hk ↦ ⟨0, (hpsd k hk).mono fun _ h ↦ by simpa only [zero_smul] using h.nonneg⟩)
      (t := t) hθ
    have htr_le := re_trace_exp_sum_cfc_log_le_of_posSemidef hmeas hpsd hL hupper (-θ)
      (b := ((Real.exp (-θ * L) - 1) / L) * μ_min)
      ((smul_le_smul_of_nonpos_left hM (div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.2 (Real.exp_le_one_iff.2 (by nlinarith))) hL.le)).trans_eq (smul_smul _ _ _))
    exact (hlap.trans (mul_le_mul_of_nonneg_left htr_le (Real.exp_pos _).le)).trans_eq
      (by rw [Real.exp_add]; ring)
  -- Endpoint `δ = 1`: pass to the limit `θ → +∞`.
  rcases hδ1.eq_or_lt with rfl | hδ1
  · simp only [sub_self, zero_mul, Real.rpow_zero, div_one]
    have hexp_rpow : (Real.exp (-1)) ^ (μ_min / L) = Real.exp (-μ_min / L) := by
      rw [← Real.exp_mul]; ring_nf
    rw [hexp_rpow]
    have hexp0 : Tendsto (fun θ : ℝ ↦ Real.exp (-θ * L)) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp <| by
        simpa [Function.comp_def, neg_mul] using
          tendsto_neg_atTop_atBot.comp (tendsto_id.atTop_mul_const hL)
    have harg_val : (0 - 1) / L * μ_min = -μ_min / L := by ring
    have harg : Tendsto (fun θ : ℝ ↦ ((Real.exp (-θ * L) - 1) / L) * μ_min) atTop
        (𝓝 (-μ_min / L)) := by
      simpa only [harg_val] using ((hexp0.sub_const 1).div_const L).mul_const μ_min
    refine ge_of_tendsto ((Real.continuous_exp.tendsto _ |>.comp harg).const_mul _) ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    simpa only [Function.comp_apply, mul_zero, zero_add] using hparam θ hθ 0
  -- Interior case `0 < δ < 1`: choose `θ = -log (1 - δ) / L > 0`.
  have h1δ : 0 < 1 - δ := by linarith
  set θ : ℝ := -Real.log (1 - δ) / L
  have hstep := hparam θ (div_pos (neg_pos.2 (Real.log_neg h1δ (by linarith))) hL) ((1 - δ) * μ_min)
  have hexpθL : (Real.exp (-θ * L) - 1) / L = -δ / L := by
    have hnegθL : -θ * L = Real.log (1 - δ) := by dsimp only [θ]; field_simp [hL.ne']
    rw [hnegθL, Real.exp_log h1δ]; ring
  have hrhs_eq : Real.exp (θ * ((1 - δ) * μ_min) + ((Real.exp (-θ * L) - 1) / L) * μ_min) =
      (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μ_min / L) := by
    rw [hexpθL, Real.rpow_def_of_pos (div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1δ _)),
      Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1δ _).ne',
      Real.log_exp, Real.log_rpow h1δ]
    congr 1; dsimp only [θ]; ring
  rwa [hrhs_eq] at hstep

end PositiveBound

section Degenerate

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

private theorem measureReal_eq_zero_of_posSemidef_of_le_zero {s : Finset ι}
    {Y : ι → Ω → Matrix n n 𝕜} (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {p : Matrix n n 𝕜 → Prop} (hp : ¬ p 0) :
    P.real {ω | p (∑ k ∈ s, Y k ω)} = 0 := by
  have hsum0 := TauCeti.ae_sum_eq_zero_of_ae_posSemidef_of_ae_le_zero hpsd hupper
  have hae_empty : {ω | p (∑ k ∈ s, Y k ω)} =ᵐ[P] (∅ : Set Ω) :=
    hsum0.mono fun ω hω ↦ ⟨fun h ↦ hp (hω ▸ h), False.elim⟩
  rw [measureReal_congr hae_empty, measureReal_empty]

/-- Degenerate `L = 0` upper real-spectrum tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`,
then `P {sSup (spectrum ℝ (∑ k ∈ s, Y k)) ≥ t} = 0` for every `t > 0` (the largest-eigenvalue
event when `n` is nonempty). -/
theorem measureReal_sSup_spectrum_sum_ge_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} = 0 :=
  measureReal_eq_zero_of_posSemidef_of_le_zero hpsd hupper (p := fun A ↦ t ≤ sSup (spectrum ℝ A))
    (by rw [TauCeti.sSup_spectrum_real_zero]; exact not_le_of_gt ht)

/-- Degenerate `L = 0` operator-norm tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`, then
`P {‖∑ k ∈ s, Y k‖ ≥ t} = 0` for every `t > 0`. -/
theorem measureReal_l2_opNorm_sum_ge_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, Y k ω‖} = 0 :=
  measureReal_eq_zero_of_posSemidef_of_le_zero hpsd hupper (p := fun A ↦ t ≤ ‖A‖)
    (by rw [norm_zero]; exact not_le_of_gt ht)

/-- Degenerate `L = 0` lower real-spectrum tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`,
then `P {sInf (spectrum ℝ (∑ k ∈ s, Y k)) ≤ t} = 0` for every `t < 0` (the smallest-eigenvalue
event when `n` is nonempty). -/
theorem measureReal_sInf_spectrum_sum_le_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : t < 0) :
    P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} = 0 :=
  measureReal_eq_zero_of_posSemidef_of_le_zero hpsd hupper (p := fun A ↦ sInf (spectrum ℝ A) ≤ t)
    (by rw [TauCeti.sInf_spectrum_real_zero]; exact not_le_of_gt ht)

end Degenerate

end ProbabilityTheory
