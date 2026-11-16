/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Concentration.Matrix.Laplace
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Normed.Algebra.Basic

/-!
# Matrix Chernoff inequalities

This file establishes Tropp's matrix Chernoff inequalities for finite sums of independent random
positive semidefinite matrices over any `RCLike` scalar field `𝕜` (`ℝ` or `ℂ`):

* **Chernoff matrix CGF bound** (`Matrix.cfc_log_of_integral_exp_smul_le_of_posSemidef`,
  Tropp 2012, Lemma 5.8): for a random positive semidefinite matrix `Y` with `Y ≤ L • 1` almost
  everywhere (`0 < L`) and any real `θ`,
  `log E[exp (θ Y)] ≤ ((exp (θ * L) - 1) / L) • E[Y]`.
* **Matrix Chernoff upper tail** (Tropp 2012, Theorem 1.1(i);
  `ProbabilityTheory.iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_posSemidef` and
  `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_posSemidef`): if
  `∑ k ∈ s, E[Y k] ≤ μ_max • 1` and `δ ≥ 0`, then
  `P {λ_max (∑ k ∈ s, Y k) ≥ (1 + δ) * μ_max} ≤ card n * (exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L)`.
* **Matrix Chernoff lower tail** (Tropp 2012, Theorem 1.1(ii);
  `ProbabilityTheory.iIndepFun.measureReal_sInf_spectrum_sum_le_le_of_posSemidef`): if
  `μ_min • 1 ≤ ∑ k ∈ s, E[Y k]` and `δ ∈ [0, 1]` (including the endpoint `δ = 1`, where
  `0 ^ (0 : ℝ) = 1` gives `card n * exp (-μ_min / L)`), then
  `P {λ_min (∑ k ∈ s, Y k) ≤ (1 - δ) * μ_min}` is bounded by
  `card n * (exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μ_min / L)`.
* **Degenerate `L = 0` bounds**
  (`TauCeti.Probability.measureReal_sSup_spectrum_sum_ge_eq_zero_of_le_zero`,
  `TauCeti.Probability.measureReal_l2_opNorm_sum_ge_eq_zero_of_le_zero`, and
  `TauCeti.Probability.measureReal_sInf_spectrum_sum_le_eq_zero_of_le_zero`): when every summand
  satisfies `0 ≤ Y k ≤ 0` almost everywhere, the sum vanishes almost everywhere and every strict
  upper or lower tail has probability `0`.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, Theorem 1.1 and Section 5.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter Topology
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- **Chernoff matrix cumulant generating function bound** (Tropp 2012, Lemma 5.8). Let `Y` be a
random positive semidefinite matrix over `𝕜` (`ℝ` or `ℂ`) satisfying `Y ≤ L • 1` almost everywhere
with `0 < L`. Then for every real `θ`,
`log E[exp (θ Y)] ≤ ((exp (θ * L) - 1) / L) • E[Y]`. -/
theorem cfc_log_of_integral_exp_smul_le_of_posSemidef [IsProbabilityMeasure P]
    {Y : Ω → Matrix n n 𝕜} (hmeas : AEMeasurable Y P)
    (hpsd : ∀ᵐ ω ∂P, (Y ω).PosSemidef)
    {L : ℝ} (hL : 0 < L) (hupper : ∀ᵐ ω ∂P, Y ω ≤ L • (1 : Matrix n n 𝕜)) (θ : ℝ) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y ω)) i j ∂P) ≤
      ((Real.exp (θ * L) - 1) / L) • (Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  set c : ℝ := (Real.exp (θ * L) - 1) / L
  -- Scalar convexity bound: `exp (θ x) ≤ 1 + c * x` for `0 ≤ x ≤ L`.
  have hscalar (x : ℝ) (hx0 : 0 ≤ x) (hxL : x ≤ L) :
      Real.exp (θ * x) ≤ 1 + c * x := by
    have ha : 0 ≤ 1 - x / L := sub_nonneg.2 ((div_le_one hL).2 hxL)
    have hb : 0 ≤ x / L := div_nonneg hx0 hL.le
    have hab : (1 - x / L) + x / L = 1 := sub_add_cancel 1 (x / L)
    have hconv := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (θ * L)) ha hb hab
    have hL' : L ≠ 0 := hL.ne'
    have harg : (1 - x / L) • (0 : ℝ) + (x / L) • (θ * L) = θ * x := by
      simp only [smul_eq_mul]
      field_simp [hL']
      ring
    have hrhs : (1 - x / L) • Real.exp 0 + (x / L) • Real.exp (θ * L) = 1 + c * x := by
      simp only [smul_eq_mul, Real.exp_zero, c]
      field_simp [hL']
      ring
    rwa [harg, hrhs] at hconv
  -- Pointwise operator bound: `exp (θ Y) ≤ 1 + c • Y`.
  have hpt : ∀ᵐ ω ∂P, NormedSpace.exp (θ • Y ω) ≤ (1 : Matrix n n 𝕜) + c • Y ω := by
    refine (hpsd.and hupper).mono fun ω ⟨hP, hU⟩ ↦ ?_
    have hexp_cfc : NormedSpace.exp (θ • Y ω) =
        cfc (fun x : ℝ ↦ Real.exp (θ * x)) (Y ω) := by
      rw [← CFC.real_exp_eq_normedSpace_exp (hP.1.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
        ← cfc_comp_const_mul θ Real.exp (Y ω) Real.continuous_exp.continuousOn hP.1.isSelfAdjoint]
    have hlin_cfc : (1 : Matrix n n 𝕜) + c • Y ω = cfc (fun x : ℝ ↦ 1 + c * x) (Y ω) := by
      have hfin := (Y ω).finite_real_spectrum
      rw [cfc_add (Y ω) (fun _ : ℝ ↦ 1) (fun x : ℝ ↦ c * x)
          (hfin.continuousOn _) (hfin.continuousOn _),
        cfc_const_one ℝ (Y ω) hP.1.isSelfAdjoint,
        cfc_const_mul c (fun x : ℝ ↦ x) (Y ω) (hfin.continuousOn _),
        cfc_id' ℝ (Y ω) hP.1.isSelfAdjoint]
    rw [hexp_cfc, hlin_cfc]
    refine cfc_mono fun x hx ↦ hscalar x ?_ ?_
    · exact (StarOrderedRing.nonneg_iff_spectrum_nonneg _ hP.1.isSelfAdjoint).1 hP.nonneg x hx
    · exact (le_algebraMap_iff_spectrum_le (ha := hP.1.isSelfAdjoint)).1
        (by simpa [Algebra.algebraMap_eq_smul_one] using hU) x hx
  -- Entrywise integrability and norm bounds.
  have hY_bdd : ∀ᵐ ω ∂P, ‖Y ω‖ ≤ L :=
    (hpsd.and hupper).mono fun _ ⟨hP, hU⟩ ↦ hP.l2_opNorm_le_of_le_smul_one hL.le hU
  have hθY_meas : AEMeasurable (fun ω ↦ θ • Y ω) P :=
    (continuous_const_smul θ).measurable.comp_aemeasurable hmeas
  have hθY_herm : ∀ᵐ ω ∂P, (θ • Y ω).IsHermitian :=
    hpsd.mono fun _ h ↦ h.1.smul (IsSelfAdjoint.all θ)
  have hθY_bdd : ∀ᵐ ω ∂P, ‖θ • Y ω‖ ≤ |θ| * L :=
    hY_bdd.mono fun ω hω ↦ by
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hω (abs_nonneg θ)
  have hexp_int : ∀ i j, Integrable (fun ω ↦ (NormedSpace.exp (θ • Y ω)) i j) P :=
    integrable_apply_of_ae_l2_opNorm_le
      ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hθY_meas)
      ((hθY_herm.and hθY_bdd).mono fun _ ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2)
  have hY_int : ∀ i j, Integrable (fun ω ↦ Y ω i j) P :=
    integrable_apply_of_ae_l2_opNorm_le hmeas hY_bdd
  have hrhs_fun (i j : n) :
      (fun ω ↦ ((1 : Matrix n n 𝕜) + c • Y ω) i j) =
        fun ω ↦ (1 : Matrix n n 𝕜) i j + c • Y ω i j := rfl
  have hrhs_int : ∀ i j, Integrable (fun ω ↦ ((1 : Matrix n n 𝕜) + c • Y ω) i j) P := fun i j ↦ by
    rw [hrhs_fun]
    exact (integrable_const _).add ((hY_int i j).smul c)
  have hE_le := of_integral_le_of_integral_of_ae_le hpt hexp_int hrhs_int
  set M : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∫ ω, Y ω i j ∂P
  have hrhs_eq :
      (Matrix.of fun i j ↦ ∫ ω, ((1 : Matrix n n 𝕜) + c • Y ω) i j ∂P) =
        (1 : Matrix n n 𝕜) + c • M := by
    ext i j
    simp only [of_apply]
    have hint2 : Integrable (fun ω ↦ c • Y ω i j) P := (hY_int i j).smul c
    rw [hrhs_fun, integral_add (integrable_const _) hint2, integral_const, probReal_univ, one_smul,
      integral_smul]
    rfl
  rw [hrhs_eq] at hE_le
  have hM_herm : M.IsHermitian := isHermitian_of_integral (hpsd.mono fun _ h ↦ h.1)
  have hcM_herm : (c • M).IsHermitian := hM_herm.smul (IsSelfAdjoint.all c)
  have hE_pos : (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y ω)) i j ∂P).PosDef :=
    posDef_of_integral_exp hθY_meas hθY_herm hθY_bdd
  exact (hE_pos.cfc_log_le_cfc_log (hE_le.trans hcM_herm.one_add_le_exp)).trans_eq
    hcM_herm.cfc_log_exp

end Matrix

namespace ProbabilityTheory

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

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
  -- Degenerate case `δ = 0`: RHS is `card n ≥ 1 ≥ P.real _`.
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [add_zero, Real.exp_zero, Real.one_rpow, div_one, mul_one]
    have hcard : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
    have hprob : P.real {ω | 1 * μ_max ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} ≤ 1 :=
      (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
    exact hprob.trans hcard
  -- Main case `δ > 0`: choose `θ = log (1 + δ) / L > 0`.
  have h1δ : 0 < 1 + δ := by linarith
  set θ : ℝ := Real.log (1 + δ) / L
  have hθ : 0 < θ := div_pos (Real.log_pos (by linarith)) hL
  have hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian :=
    fun k hk ↦ (hpsd k hk).mono fun _ h ↦ h.1
  have hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ M := fun k hk ↦
    ⟨L, ((hpsd k hk).and (hupper k hk)).mono fun _ ⟨hP, hU⟩ ↦
      hP.l2_opNorm_le_of_le_smul_one hL.le hU⟩
  have hlap := hindep.measureReal_sSup_spectrum_sum_ge_le hmeas hherm hbdd
    (t := (1 + δ) * μ_max) hθ
  have hexpθL : (Real.exp (θ * L) - 1) / L = δ / L := by
    have hθL : θ * L = Real.log (1 + δ) := div_mul_cancel₀ _ hL.ne'
    rw [hθL, Real.exp_log h1δ, add_sub_cancel_left]
  set M : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P
  have hcgf_le : (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P)) ≤
      (δ / L) • M := by
    have hsum_M : ∑ k ∈ s, (δ / L) • (Matrix.of fun i j ↦ ∫ ω, Y k ω i j ∂P) = (δ / L) • M := by
      rw [← Finset.smul_sum]
      congr 1
      ext i j
      simp [M]
    rw [← hsum_M]
    refine Finset.sum_le_sum fun k hk ↦ ?_
    simpa only [hexpθL] using
      cfc_log_of_integral_exp_smul_le_of_posSemidef (hmeas k hk) (hpsd k hk) hL (hupper k hk) θ
  have hcgf_smul : (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P)) ≤
      (δ * μ_max / L) • (1 : Matrix n n 𝕜) := by
    calc
      (∑ k ∈ s, cfc Real.log
            (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P))
          ≤ (δ / L) • M := hcgf_le
      _ ≤ (δ / L) • (μ_max • (1 : Matrix n n 𝕜)) :=
          smul_le_smul_of_nonneg_left hM (div_nonneg hδ.le hL.le)
      _ = (δ * μ_max / L) • (1 : Matrix n n 𝕜) := by rw [smul_smul, div_mul_eq_mul_div]
  have hsum_herm : (∑ k ∈ s, cfc Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P)).IsHermitian :=
    Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero fun _ _ ↦
      IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
  have htr_le := hsum_herm.re_trace_exp_le_card_mul_exp hcgf_smul
  have hbase_pos : 0 < Real.exp δ / (1 + δ) ^ (1 + δ) :=
    div_pos (Real.exp_pos δ) (Real.rpow_pos_of_pos h1δ _)
  have hrhs_eq :
      Real.exp (-θ * ((1 + δ) * μ_max) + δ * μ_max / L) =
        (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L) := by
    rw [Real.rpow_def_of_pos hbase_pos,
      Real.log_div (Real.exp_pos δ).ne' (Real.rpow_pos_of_pos h1δ _).ne',
      Real.log_exp, Real.log_rpow h1δ]
    congr 1
    dsimp only [θ]
    ring
  calc
    P.real {ω | (1 + δ) * μ_max ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))}
        ≤ Real.exp (-θ * ((1 + δ) * μ_max)) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
            (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • Y k ω)) i j ∂P))).trace := hlap
    _ ≤ Real.exp (-θ * ((1 + δ) * μ_max)) *
          ((Fintype.card n : ℝ) * Real.exp (δ * μ_max / L)) :=
        mul_le_mul_of_nonneg_left htr_le (Real.exp_pos _).le
    _ = (Fintype.card n : ℝ) * Real.exp (-θ * ((1 + δ) * μ_max) + δ * μ_max / L) := by
        rw [Real.exp_add]; ring
    _ = (Fintype.card n : ℝ) * (Real.exp δ / (1 + δ) ^ (1 + δ)) ^ (μ_max / L) := by
        rw [hrhs_eq]

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
  have hM_psd : M.PosSemidef := by
    have hsplit : M = ∑ k ∈ s, Matrix.of fun i j ↦ ∫ ω, Y k ω i j ∂P := by
      ext i j; simp [M]
    rw [hsplit]
    refine Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) PosSemidef.zero fun k hk ↦ ?_
    have hY_bdd : ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ L :=
      ((hpsd k hk).and (hupper k hk)).mono fun _ ⟨hP, hU⟩ ↦
        hP.l2_opNorm_le_of_le_smul_one hL.le hU
    exact posSemidef_of_integral (hpsd k hk)
      (integrable_apply_of_ae_l2_opNorm_le (hmeas k hk) hY_bdd)
  have hsum_psd : ∀ᵐ ω ∂P, (∑ k ∈ s, Y k ω).PosSemidef := by
    have hall : ∀ᵐ ω ∂P, ∀ k ∈ s, (Y k ω).PosSemidef := (ae_ball_iff s.countable_toSet).2 hpsd
    exact hall.mono fun ω hω ↦
      Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) PosSemidef.zero hω
  have hsub : {ω | (1 + δ) * ‖M‖ ≤ ‖∑ k ∈ s, Y k ω‖} ≤ᵐ[P]
      {ω | (1 + δ) * ‖M‖ ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} :=
    hsum_psd.mono fun ω hω hge ↦ by
      simp only [Set.mem_ofPred_eq] at hge ⊢
      rwa [hω.1.sSup_spectrum_real_eq_eigenvalues₀_zero, ← hω.l2_opNorm_eq_eigenvalues₀_zero]
  have hle : P.real {ω | (1 + δ) * ‖M‖ ≤ ‖∑ k ∈ s, Y k ω‖} ≤
      P.real {ω | (1 + δ) * ‖M‖ ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} :=
    ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
  exact hle.trans <|
    hindep.measureReal_sSup_spectrum_sum_ge_le_of_posSemidef hmeas hpsd hL hupper
      hM_psd.le_l2_opNorm_smul_one hδ

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
  -- Degenerate case `δ = 0`: RHS is `card n ≥ 1 ≥ P.real _`.
  rcases hδ0.eq_or_lt with rfl | hδ0
  · simp only [sub_zero, neg_zero, Real.exp_zero, Real.one_rpow, div_one, mul_one]
    have hcard : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
    have hprob : P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ 1 * μ_min} ≤ 1 :=
      (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
    exact hprob.trans hcard
  -- Common Laplace + Chernoff-CGF upper bound valid for every `θ > 0` and every `t : ℝ`.
  have hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).IsHermitian :=
    fun k hk ↦ (hpsd k hk).mono fun _ h ↦ h.1
  have hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖Y k ω‖ ≤ M := fun k hk ↦
    ⟨L, ((hpsd k hk).and (hupper k hk)).mono fun _ ⟨hP, hU⟩ ↦
      hP.l2_opNorm_le_of_le_smul_one hL.le hU⟩
  set M : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, Y k ω i j ∂P
  have hparam (θ : ℝ) (hθ : 0 < θ) (t : ℝ) :
      P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} ≤
        (Fintype.card n : ℝ) *
          Real.exp (θ * t + ((Real.exp (-θ * L) - 1) / L) * μ_min) := by
    have hlap := hindep.measureReal_sInf_spectrum_sum_le_le hmeas hherm hbdd (t := t) hθ
    set c : ℝ := (Real.exp (-θ * L) - 1) / L
    have hc_nonpos : c ≤ 0 := by
      dsimp only [c]
      have h1 : Real.exp (-θ * L) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 h1) hL.le
    have hcgf_le : (∑ k ∈ s, cfc Real.log
          (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • Y k ω)) i j ∂P)) ≤ c • M := by
      have hsum_M : ∑ k ∈ s, c • (Matrix.of fun i j ↦ ∫ ω, Y k ω i j ∂P) = c • M := by
        rw [← Finset.smul_sum]
        congr 1
        ext i j
        simp [M]
      rw [← hsum_M]
      exact Finset.sum_le_sum fun k hk ↦
        cfc_log_of_integral_exp_smul_le_of_posSemidef (hmeas k hk) (hpsd k hk) hL (hupper k hk) (-θ)
    have hcgf_smul : (∑ k ∈ s, cfc Real.log
          (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • Y k ω)) i j ∂P)) ≤
        (c * μ_min) • (1 : Matrix n n 𝕜) := by
      calc
        (∑ k ∈ s, cfc Real.log
              (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • Y k ω)) i j ∂P))
            ≤ c • M := hcgf_le
        _ ≤ c • (μ_min • (1 : Matrix n n 𝕜)) := smul_le_smul_of_nonpos_left hM hc_nonpos
        _ = (c * μ_min) • (1 : Matrix n n 𝕜) := smul_smul c μ_min 1
    have hsum_herm : (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • Y k ω)) i j ∂P)).IsHermitian :=
      Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero fun _ _ ↦
        IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
    have htr_le := hsum_herm.re_trace_exp_le_card_mul_exp hcgf_smul
    calc
      P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t}
          ≤ Real.exp (θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
              (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp ((-θ) • Y k ω)) i j ∂P))).trace := hlap
      _ ≤ Real.exp (θ * t) * ((Fintype.card n : ℝ) * Real.exp (c * μ_min)) :=
          mul_le_mul_of_nonneg_left htr_le (Real.exp_pos _).le
      _ = (Fintype.card n : ℝ) * Real.exp (θ * t + c * μ_min) := by
          rw [Real.exp_add]; ring
  -- Endpoint `δ = 1`: pass to the limit `θ → +∞`.
  rcases hδ1.eq_or_lt with rfl | hδ1
  · simp only [sub_self, zero_mul, Real.rpow_zero, div_one]
    have hrpow : (Real.exp (-1)) ^ (μ_min / L) = Real.exp (-μ_min / L) := by
      rw [← Real.exp_mul]; ring_nf
    rw [hrpow]
    have htend : Tendsto
        (fun θ : ℝ ↦ (Fintype.card n : ℝ) * Real.exp (((Real.exp (-θ * L) - 1) / L) * μ_min))
        atTop (𝓝 ((Fintype.card n : ℝ) * Real.exp (-μ_min / L))) := by
      have hexp0 : Tendsto (fun θ : ℝ ↦ Real.exp (-θ * L)) atTop (𝓝 0) := by
        have hneg : Tendsto (fun θ : ℝ ↦ -θ * L) atTop atBot := by
          have := tendsto_id.atTop_mul_const hL
          have hneg' := tendsto_neg_atTop_atBot.comp this
          simpa [Function.comp_def, neg_mul] using hneg'
        exact Real.tendsto_exp_atBot.comp hneg
      have harg : Tendsto (fun θ : ℝ ↦ ((Real.exp (-θ * L) - 1) / L) * μ_min) atTop
          (𝓝 (-μ_min / L)) := by
        have h1 := (((hexp0.sub_const 1).div_const L).mul_const μ_min)
        have hlim : (0 - 1) / L * μ_min = -μ_min / L := by ring
        rwa [hlim] at h1
      exact (Real.continuous_exp.tendsto _ |>.comp harg).const_mul _
    refine ge_of_tendsto htend ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with θ hθ
    simpa only [mul_zero, zero_add] using hparam θ hθ 0
  -- Interior case `0 < δ < 1`: choose `θ = -log (1 - δ) / L > 0`.
  have h1δ : 0 < 1 - δ := by linarith
  set θ : ℝ := -Real.log (1 - δ) / L
  have hθ : 0 < θ := div_pos (neg_pos.2 (Real.log_neg h1δ (by linarith))) hL
  have hstep := hparam θ hθ ((1 - δ) * μ_min)
  have hexpθL : (Real.exp (-θ * L) - 1) / L = -δ / L := by
    have hθL : -θ * L = Real.log (1 - δ) := by
      dsimp only [θ]
      field_simp [hL.ne']
    rw [hθL, Real.exp_log h1δ]
    ring
  have hbase_pos : 0 < Real.exp (-δ) / (1 - δ) ^ (1 - δ) :=
    div_pos (Real.exp_pos _) (Real.rpow_pos_of_pos h1δ _)
  have hrhs_eq :
      Real.exp (θ * ((1 - δ) * μ_min) + ((Real.exp (-θ * L) - 1) / L) * μ_min) =
        (Real.exp (-δ) / (1 - δ) ^ (1 - δ)) ^ (μ_min / L) := by
    rw [hexpθL, Real.rpow_def_of_pos hbase_pos,
      Real.log_div (Real.exp_pos _).ne' (Real.rpow_pos_of_pos h1δ _).ne',
      Real.log_exp, Real.log_rpow h1δ]
    congr 1
    dsimp only [θ]
    ring
  rwa [hrhs_eq] at hstep

end ProbabilityTheory

namespace TauCeti.Probability

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

/-- If positive semidefinite random matrices `Y k` (`k ∈ s`) satisfy `Y k ≤ 0` almost everywhere,
then their sum vanishes almost everywhere. -/
private theorem ae_sum_eq_zero_of_posSemidef_of_le_zero {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) :
    ∀ᵐ ω ∂P, ∑ k ∈ s, Y k ω = 0 := by
  have hall : ∀ᵐ ω ∂P, ∀ k ∈ s, (Y k ω).PosSemidef ∧ Y k ω ≤ 0 :=
    (ae_ball_iff s.countable_toSet).2 fun k hk ↦ (hpsd k hk).and (hupper k hk)
  refine hall.mono fun ω hω ↦ Finset.sum_eq_zero fun k hk ↦ ?_
  exact le_antisymm (hω k hk).2 (hω k hk).1.nonneg

/-- Degenerate `L = 0` upper eigenvalue tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`, then
`P {λ_max (∑ k ∈ s, Y k) ≥ t} = 0` for every `t > 0`. -/
theorem measureReal_sSup_spectrum_sum_ge_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} = 0 := by
  have hsum0 := ae_sum_eq_zero_of_posSemidef_of_le_zero hpsd hupper
  have hspec0 : sSup (spectrum ℝ (0 : Matrix n n 𝕜)) = 0 := by
    simpa only [zero_smul, zero_mul] using
      Matrix.sSup_spectrum_real_smul_of_nonneg (0 : Matrix n n 𝕜) le_rfl
  have hempty : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} ≤ᵐ[P] (∅ : Set Ω) :=
    hsum0.mono fun ω hω hge ↦ by
      simp only [Set.mem_ofPred_eq] at hge
      rw [hω, hspec0] at hge
      exact not_le_of_gt ht hge
  have hle : P {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, Y k ω))} ≤ P ∅ := measure_mono_ae hempty
  simp only [measure_empty, nonpos_iff_eq_zero] at hle
  simp [Measure.real, hle]

/-- Degenerate `L = 0` operator-norm tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`, then
`P {‖∑ k ∈ s, Y k‖ ≥ t} = 0` for every `t > 0`. -/
theorem measureReal_l2_opNorm_sum_ge_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, Y k ω‖} = 0 := by
  have hsum0 := ae_sum_eq_zero_of_posSemidef_of_le_zero hpsd hupper
  have hempty : {ω | t ≤ ‖∑ k ∈ s, Y k ω‖} ≤ᵐ[P] (∅ : Set Ω) :=
    hsum0.mono fun ω hω hge ↦ by
      simp only [Set.mem_ofPred_eq] at hge
      rw [hω, norm_zero] at hge
      exact not_le_of_gt ht hge
  have hle : P {ω | t ≤ ‖∑ k ∈ s, Y k ω‖} ≤ P ∅ := measure_mono_ae hempty
  simp only [measure_empty, nonpos_iff_eq_zero] at hle
  simp [Measure.real, hle]

/-- Degenerate `L = 0` lower eigenvalue tail: if `0 ≤ Y k ≤ 0` almost everywhere for `k ∈ s`, then
`P {λ_min (∑ k ∈ s, Y k) ≤ t} = 0` for every `t < 0`. -/
theorem measureReal_sInf_spectrum_sum_le_eq_zero_of_le_zero [Fintype n] [DecidableEq n]
    {s : Finset ι} {Y : ι → Ω → Matrix n n 𝕜}
    (hpsd : ∀ k ∈ s, ∀ᵐ ω ∂P, (Y k ω).PosSemidef)
    (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, Y k ω ≤ 0) {t : ℝ} (ht : t < 0) :
    P.real {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} = 0 := by
  have hsum0 := ae_sum_eq_zero_of_posSemidef_of_le_zero hpsd hupper
  have hspec0 : sInf (spectrum ℝ (0 : Matrix n n 𝕜)) = 0 := by
    have hsup0 : sSup (spectrum ℝ (0 : Matrix n n 𝕜)) = 0 := by
      simpa only [zero_smul, zero_mul] using
        Matrix.sSup_spectrum_real_smul_of_nonneg (0 : Matrix n n 𝕜) le_rfl
    have hneg := Matrix.sSup_spectrum_real_neg (0 : Matrix n n 𝕜)
    rw [neg_zero, hsup0] at hneg
    linarith
  have hempty : {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} ≤ᵐ[P] (∅ : Set Ω) :=
    hsum0.mono fun ω hω hle' ↦ by
      simp only [Set.mem_ofPred_eq] at hle'
      rw [hω, hspec0] at hle'
      exact not_le_of_gt ht hle'
  have hle : P {ω | sInf (spectrum ℝ (∑ k ∈ s, Y k ω)) ≤ t} ≤ P ∅ := measure_mono_ae hempty
  simp only [measure_empty, nonpos_iff_eq_zero] at hle
  simp [Measure.real, hle]

end TauCeti.Probability
