/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.Probability.Independence.Basic
public import TauCeti.Probability.Concentration.Matrix.Laplace
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Frobenius
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.Analysis.Normed.Algebra.Basic
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Matrix Bernstein inequalities

This file establishes Tropp's matrix Bernstein inequalities for finite sums of independent centered
random matrices over any `RCLike` scalar field `𝕜` (`ℝ` or `ℂ`):

* **Bernstein matrix CGF bound** (`Matrix.cfc_log_of_integral_exp_smul_le`): for a centered,
  a.e. bounded Hermitian random matrix `X` with `X ≤ L • 1` almost everywhere and `0 ≤ θ`,
  `θ * L < 3`,
  `log E[exp (θ X)] ≤ (θ ^ 2 / (2 * (1 - θ * L / 3))) • E[X * X]`.
* **One-sided Hermitian Matrix Bernstein** (Tropp 2012, Theorem 1.4;
  `ProbabilityTheory.iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_le`): for independent
  centered a.e. bounded Hermitian random matrices `X k ≤ L • 1` on a nonempty index type `n` with
  matrix variance `V = ∑ k ∈ s, E[X k * X k]`,
  `P {λ_max (∑ k ∈ s, X k) ≥ t} ≤ card n * exp (-(t ^ 2 / 2) / (‖V‖ + L * t / 3))` for all `t ≥ 0`.
* **Two-sided Hermitian Matrix Bernstein** (Tropp 2012, Theorem 1.4;
  `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_isHermitian`): applying the
  one-sided bound to `X` and `-X` bounds `P {‖∑ k ∈ s, X k‖ ≥ t}` with factor `2 * card n` for all
  `t > 0`, with no nonemptiness assumption on `n` and no sign assumption on `L`.
* **Rectangular Matrix Bernstein** (Tropp 2012, Theorem 1.6;
  `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le`): applying the one-sided Hermitian
  bound to the Hermitian dilation `fromBlocks 0 Z Zᴴ 0` of independent centered rectangular
  `m × p` random matrices `Z k` with `‖Z k‖ ≤ L` yields the sharp dimensional factor
  `card m + card p` and variance parameter
  `max ‖∑ k ∈ s, E[Z k * (Z k)ᴴ]‖ ‖∑ k ∈ s, E[(Z k)ᴴ * Z k]‖`.

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, Theorems 1.4 and 1.6 and Section 6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace Matrix

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- **Bernstein matrix cumulant generating function bound** (Tropp 2012, Lemma 6.7). Let `X` be a
centered, a.e. bounded random Hermitian matrix over `𝕜` (`ℝ` or `ℂ`) satisfying `X ≤ L • 1` almost
everywhere. Then for every `θ ≥ 0` with `θ * L < 3`,
`log E[exp (θ X)] ≤ (θ ^ 2 / (2 * (1 - θ * L / 3))) • E[X * X]`. -/
theorem cfc_log_of_integral_exp_smul_le [IsProbabilityMeasure P]
    {X : Ω → Matrix n n 𝕜} (hmeas : AEMeasurable X P)
    (hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ L • (1 : Matrix n n 𝕜))
    (hbdd : ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X ω‖ ≤ M)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X ω)) i j ∂P) ≤
      (θ ^ 2 / (2 * (1 - θ * L / 3))) •
        (Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P) := by
  by_cases hn : IsEmpty n
  · exact le_of_eq (Subsingleton.elim _ _)
  obtain ⟨i₀⟩ := not_isEmpty_iff.1 hn
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  let : NormedAlgebra ℚ (Matrix n n 𝕜) := TauCeti.normedAlgebraRatOfReal
  obtain ⟨M, hM⟩ := hbdd
  have hX_int : ∀ i j, Integrable (fun ω ↦ X ω i j) P :=
    integrable_apply_of_ae_l2_opNorm_le hmeas hM
  have hL : 0 ≤ L := by
    have hle : (0 : Matrix n n 𝕜) ≤ L • (1 : Matrix n n 𝕜) := by
      have hzero : (0 : Matrix n n 𝕜) = Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P := by
        ext i j; simp [hmean]
      have hconst : L • (1 : Matrix n n 𝕜) =
          Matrix.of fun i j ↦ ∫ _ω, (L • (1 : Matrix n n 𝕜)) i j ∂P := by
        ext i j; simp
      rw [hzero, hconst]
      exact of_integral_le_of_integral_of_ae_le hupper hX_int (fun _ _ ↦ integrable_const _)
    have hdiag := (le_iff.1 hle).diag_nonneg (i := i₀)
    rw [RCLike.nonneg_iff] at hdiag
    simpa [RCLike.smul_re] using hdiag.1
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  -- Pointwise operator Bernstein bound: `exp (θ X) ≤ 1 + θ X + c X²`.
  have hpt : ∀ᵐ ω ∂P,
      NormedSpace.exp (θ • X ω) ≤
        (1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω) := by
    refine (hherm.and hupper).mono fun ω ⟨hH, hU⟩ ↦ ?_
    have hexp_cfc : NormedSpace.exp (θ • X ω) =
        cfc (fun x : ℝ ↦ Real.exp (θ * x)) (X ω) := by
      rw [← CFC.real_exp_eq_normedSpace_exp (hH.smul (IsSelfAdjoint.all θ)).isSelfAdjoint,
        ← cfc_comp_const_mul θ Real.exp (X ω) Real.continuous_exp.continuousOn hH.isSelfAdjoint]
    have hpoly_cfc : (1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω) =
        cfc (fun x : ℝ ↦ 1 + θ * x + c * x ^ 2) (X ω) := by
      have hfin := (X ω).finite_real_spectrum
      rw [cfc_add (X ω) (fun x : ℝ ↦ 1 + θ * x) (fun x : ℝ ↦ c * x ^ 2)
          (hfin.continuousOn _) (hfin.continuousOn _),
        cfc_add (X ω) (fun _ : ℝ ↦ 1) (fun x : ℝ ↦ θ * x)
          (hfin.continuousOn _) (hfin.continuousOn _),
        cfc_const_one ℝ (X ω) hH.isSelfAdjoint,
        cfc_const_mul θ (fun x : ℝ ↦ x) (X ω) (hfin.continuousOn _),
        cfc_id' ℝ (X ω) hH.isSelfAdjoint,
        cfc_const_mul c (fun x : ℝ ↦ x ^ 2) (X ω) (hfin.continuousOn _),
        cfc_pow (fun x : ℝ ↦ x) 2 (X ω) (hfin.continuousOn _),
        cfc_id' ℝ (X ω) hH.isSelfAdjoint, sq]
    rw [hexp_cfc, hpoly_cfc]
    refine cfc_mono fun x hx ↦ ?_
    have hxL : x ≤ L := (le_algebraMap_iff_spectrum_le (ha := hH.isSelfAdjoint)).1
      (by simpa [Algebra.algebraMap_eq_smul_one] using hU) x hx
    have hbern := Real.exp_le_one_add_add_sq_div_of_le
      (mul_le_mul_of_nonneg_left hxL hθ) (mul_nonneg hθ hL) hθL
    have heq : (θ * x) ^ 2 / (2 * (1 - θ * L / 3)) = c * x ^ 2 := by
      dsimp only [c]; ring
    linarith
  -- Entrywise integrability of `exp (θ X)` and `X * X`.
  have hθX_meas : AEMeasurable (fun ω ↦ θ • X ω) P :=
    (continuous_const_smul θ).measurable.comp_aemeasurable hmeas
  have hθX_herm : ∀ᵐ ω ∂P, (θ • X ω).IsHermitian :=
    hherm.mono fun _ h ↦ h.smul (IsSelfAdjoint.all θ)
  have hθX_bdd : ∀ᵐ ω ∂P, ‖θ • X ω‖ ≤ θ * M :=
    hM.mono fun ω hω ↦ by
      rw [norm_smul, Real.norm_of_nonneg hθ]
      exact mul_le_mul_of_nonneg_left hω hθ
  have hexp_int : ∀ i j, Integrable (fun ω ↦ (NormedSpace.exp (θ • X ω)) i j) P :=
    integrable_apply_of_ae_l2_opNorm_le
      ((NormedSpace.exp_continuous (𝔸 := Matrix n n 𝕜)).measurable.comp_aemeasurable hθX_meas)
      ((hθX_herm.and hθX_bdd).mono fun _ ⟨h1, h2⟩ ↦ h1.l2_opNorm_exp_le h2)
  have hXsq_meas : AEMeasurable (fun ω ↦ X ω * X ω) P :=
    continuous_mul.measurable.comp_aemeasurable (hmeas.prodMk hmeas)
  have hXsq_bdd : ∀ᵐ ω ∂P, ‖X ω * X ω‖ ≤ (max M 0) ^ 2 :=
    hM.mono fun ω hω ↦ by
      have h1 : ‖X ω‖ ≤ max M 0 := hω.trans (le_max_left M 0)
      calc ‖X ω * X ω‖ ≤ ‖X ω‖ * ‖X ω‖ := norm_mul_le _ _
        _ ≤ max M 0 * max M 0 := mul_le_mul h1 h1 (norm_nonneg _) (le_max_right M 0)
        _ = (max M 0) ^ 2 := (sq _).symm
  have hXsq_int : ∀ i j, Integrable (fun ω ↦ (X ω * X ω) i j) P :=
    integrable_apply_of_ae_l2_opNorm_le hXsq_meas hXsq_bdd
  have hrhs_fun (i j : n) :
      (fun ω ↦ ((1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω)) i j) =
        fun ω ↦ (1 : Matrix n n 𝕜) i j + θ • X ω i j + c • (X ω * X ω) i j := rfl
  have hrhs_int : ∀ i j,
      Integrable (fun ω ↦ ((1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω)) i j) P := fun i j ↦ by
    rw [hrhs_fun]
    exact ((integrable_const _).add ((hX_int i j).smul θ)).add ((hXsq_int i j).smul c)
  -- Take entrywise expectation, then apply `1 + c • V ≤ exp (c • V)` and monotonicity of `log`.
  have hE_le := of_integral_le_of_integral_of_ae_le hpt hexp_int hrhs_int
  set V : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P
  have hrhs_eq :
      (Matrix.of fun i j ↦ ∫ ω, ((1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω)) i j ∂P) =
        (1 : Matrix n n 𝕜) + c • V := by
    ext i j
    simp only [of_apply]
    have hint1 : Integrable (fun ω ↦ (1 : Matrix n n 𝕜) i j + θ • X ω i j) P :=
      (integrable_const _).add ((hX_int i j).smul θ)
    have hint2 : Integrable (fun ω ↦ c • (X ω * X ω) i j) P := (hXsq_int i j).smul c
    have hint3 : Integrable (fun ω ↦ θ • X ω i j) P := (hX_int i j).smul θ
    rw [hrhs_fun, integral_add hint1 hint2, integral_add (integrable_const _) hint3,
      integral_const, probReal_univ, one_smul, integral_smul, integral_smul,
      hmean i j, smul_zero, add_zero]
    rfl
  rw [hrhs_eq] at hE_le
  have hV_herm : V.IsHermitian :=
    isHermitian_of_integral (hherm.mono fun ω hω ↦ by
      simpa only [hω.eq] using isHermitian_conjTranspose_mul_self (X ω))
  have hcV_herm : (c • V).IsHermitian := hV_herm.smul (IsSelfAdjoint.all c)
  have hE_pos : (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X ω)) i j ∂P).PosDef :=
    posDef_of_integral_exp hθX_meas hθX_herm hθX_bdd
  exact (hE_pos.cfc_log_le_cfc_log (hE_le.trans hcV_herm.one_add_le_exp)).trans_eq
    hcV_herm.cfc_log_exp

end Matrix

namespace ProbabilityTheory

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- If the sum of expected squares `∑ k ∈ s, E[X k * X k]` of a.e. bounded Hermitian random matrices
vanishes, then each `X k` (`k ∈ s`) vanishes almost everywhere. -/
private theorem ae_eq_zero_of_sum_integral_mul_self_eq_zero [IsFiniteMeasure P]
    [Fintype n] [DecidableEq n] {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M)
    (hV0 : (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P) = 0) :
    ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω = 0 := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have htr_each (k : ι) (hk : k ∈ s) :
      RCLike.re (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P).trace =
        ∫ ω, ∑ i, ∑ j, ‖X k ω i j‖ ^ 2 ∂P := by
    obtain ⟨Mk, hMk⟩ := hbdd k hk
    have hXsq_int : ∀ i j, Integrable (fun ω ↦ (X k ω * X k ω) i j) P := by
      refine integrable_apply_of_ae_l2_opNorm_le (M := (max Mk 0) ^ 2)
        (continuous_mul.measurable.comp_aemeasurable ((hmeas k hk).prodMk (hmeas k hk)))
        (hMk.mono fun ω hω ↦ ?_)
      have h1 : ‖X k ω‖ ≤ max Mk 0 := hω.trans (le_max_left Mk 0)
      calc ‖X k ω * X k ω‖ ≤ ‖X k ω‖ * ‖X k ω‖ := norm_mul_le _ _
        _ ≤ max Mk 0 * max Mk 0 := mul_le_mul h1 h1 (norm_nonneg _) (le_max_right Mk 0)
        _ = (max Mk 0) ^ 2 := (sq _).symm
    have htr_int : Integrable (fun ω ↦ (X k ω * X k ω).trace) P :=
      integrable_finsetSum _ fun i _ ↦ hXsq_int i i
    calc
      RCLike.re (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P).trace
          = RCLike.re (∫ ω, (X k ω * X k ω).trace ∂P) := by
            congr 1
            simp only [trace, diag_apply, of_apply]
            exact (integral_finsetSum _ fun i _ ↦ hXsq_int i i).symm
      _ = ∫ ω, RCLike.re (X k ω * X k ω).trace ∂P := by
            simpa only [RCLike.reCLM_apply] using (RCLike.reCLM.integral_comp_comm htr_int).symm
      _ = ∫ ω, ∑ i, ∑ j, ‖X k ω i j‖ ^ 2 ∂P := by
            refine integral_congr_ae ((hherm k hk).mono fun ω hω ↦ ?_)
            dsimp only
            have hmul : X k ω * X k ω = X k ω * (X k ω)ᴴ := by rw [hω.eq]
            rw [hmul]
            exact re_trace_mul_conjTranspose_self (X k ω)
  have hsum_zero : ∑ k ∈ s, ∫ ω, ∑ i, ∑ j, ‖X k ω i j‖ ^ 2 ∂P = 0 := by
    have hre0 : RCLike.re
        (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P).trace = 0 := by
      rw [hV0, trace_zero, map_zero]
    rw [← hre0]
    have hsplit : RCLike.re (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P).trace =
        ∑ k ∈ s, RCLike.re (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P).trace := by
      simp only [trace, diag_apply, of_apply, map_sum]
      rw [Finset.sum_comm]
    rw [hsplit]
    exact Finset.sum_congr rfl fun k hk ↦ (htr_each k hk).symm
  have hnonneg : ∀ k ∈ s, 0 ≤ ∫ ω, ∑ i, ∑ j, ‖X k ω i j‖ ^ 2 ∂P :=
    fun _ _ ↦ integral_nonneg fun _ ↦ Finset.sum_nonneg fun _ _ ↦
      Finset.sum_nonneg fun _ _ ↦ sq_nonneg _
  have heach_zero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum_zero
  intro k hk
  obtain ⟨Mk, hMk⟩ := hbdd k hk
  have hf_int : Integrable (fun ω ↦ ∑ i, ∑ j, ‖X k ω i j‖ ^ 2) P := by
    refine integrable_finsetSum _ fun i _ ↦ integrable_finsetSum _ fun j _ ↦ ?_
    have hij_meas : AEMeasurable (fun ω ↦ ‖X k ω i j‖ ^ 2) P :=
      ((continuous_pow 2).comp continuous_norm).measurable.comp_aemeasurable
        (Matrix.measurable_apply.comp_aemeasurable (hmeas k hk))
    refine Integrable.of_bound hij_meas.aestronglyMeasurable ((max Mk 0) ^ 2)
      (hMk.mono fun ω hω ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hle : ‖X k ω i j‖ ≤ max Mk 0 :=
      (Matrix.norm_apply_le_l2_opNorm (X k ω) i j).trans (hω.trans (le_max_left Mk 0))
    exact pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hae0 : (fun ω ↦ ∑ i, ∑ j, ‖X k ω i j‖ ^ 2) =ᵐ[P] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall fun _ ↦ Finset.sum_nonneg fun _ _ ↦
        Finset.sum_nonneg fun _ _ ↦ sq_nonneg _) hf_int).1 (heach_zero k hk)
  refine hae0.mono fun ω hω ↦ ?_
  ext i j
  have hrow : ∑ j', ‖X k ω i j'‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ sq_nonneg _).1
      hω i (Finset.mem_univ i)
  have hentry : ‖X k ω i j‖ ^ 2 = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun _ _ ↦ sq_nonneg _).1 hrow j (Finset.mem_univ j)
  exact norm_eq_zero.1 (sq_eq_zero_iff.1 hentry)

/-- **One-sided Hermitian Matrix Bernstein inequality** (Tropp 2012, Theorem 1.4). Let `X k`
(`k ∈ s`) be independent, centered, a.e. bounded Hermitian random matrices over `𝕜` (`ℝ` or `ℂ`)
with `X k ≤ L • 1` almost everywhere, and let `V = ∑ k ∈ s, E[X k * X k]` be the matrix variance
statistic. Then for every `t ≥ 0`,
`P {λ_max (∑ k ∈ s, X k) ≥ t} ≤ card n * exp (-(t ^ 2 / 2) / (‖V‖ + L * t / 3))`. -/
theorem iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_le [IsProbabilityMeasure P]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω ≤ L • (1 : Matrix n n 𝕜))
    (hbdd : ∀ k ∈ s, ∃ M : ℝ, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ M)
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤
      (Fintype.card n : ℝ) * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  set V : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P
  set v : ℝ := ‖V‖
  -- Degenerate case `t = 0`: RHS is `card n ≥ 1 ≥ P.real _`.
  rcases ht.eq_or_lt with rfl | ht
  · simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_div, neg_zero,
      mul_zero, add_zero, Real.exp_zero, mul_one]
    have hcard : (1 : ℝ) ≤ (Fintype.card n : ℝ) := by exact_mod_cast Fintype.card_pos (α := n)
    have hprob : P.real {ω | 0 ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ 1 :=
      (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
    exact hprob.trans hcard
  -- Degenerate case `v = 0`: each `X k` (`k ∈ s`) is a.e. zero, so the tail probability is `0`.
  rcases (norm_nonneg V).eq_or_lt with hv | hv
  · have hV0 : V = 0 := norm_eq_zero.1 hv.symm
    have hae0 := ae_eq_zero_of_sum_integral_mul_self_eq_zero hmeas hherm hbdd hV0
    have hsum0 : ∀ᵐ ω ∂P, ∑ k ∈ s, X k ω = 0 := by
      have hall : ∀ᵐ ω ∂P, ∀ k ∈ s, X k ω = 0 := (ae_ball_iff s.countable_toSet).2 hae0
      exact hall.mono fun ω hω ↦ Finset.sum_eq_zero hω
    have hspec0 : sSup (spectrum ℝ (0 : Matrix n n 𝕜)) = 0 := by
      have h := Matrix.sSup_spectrum_real_smul_of_nonneg (0 : Matrix n n 𝕜) le_rfl
      simpa only [zero_smul, zero_mul] using h
    have hempty : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ᵐ[P] (∅ : Set Ω) :=
      hsum0.mono fun ω hω hge ↦ by
        simp only [Set.mem_ofPred_eq] at hge
        rw [hω, hspec0] at hge
        exact not_le_of_gt ht hge
    have hprob0 : P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} = 0 := by
      have hle : P {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ≤ P ∅ := measure_mono_ae hempty
      simp only [measure_empty, nonpos_iff_eq_zero] at hle
      simp [Measure.real, hle]
    rw [hprob0]
    positivity
  -- Main case `0 < t` and `0 < v`: deduce `s.Nonempty` and `0 ≤ L`.
  have hsne : s.Nonempty := by
    by_contra hemp
    have hV0 : V = 0 := by ext i j; simp [V, Finset.not_nonempty_iff_eq_empty.1 hemp]
    exact hv.ne' (by simp [hV0])
  have hL : 0 ≤ L := by
    obtain ⟨k, hk⟩ := hsne
    obtain ⟨Mk, hMk⟩ := hbdd k hk
    have hle : (0 : Matrix n n 𝕜) ≤ L • (1 : Matrix n n 𝕜) := by
      have hzero : (0 : Matrix n n 𝕜) = Matrix.of fun i j ↦ ∫ ω, X k ω i j ∂P := by
        ext i j; simp [hmean k hk]
      have hconst : L • (1 : Matrix n n 𝕜) =
          Matrix.of fun i j ↦ ∫ _ω, (L • (1 : Matrix n n 𝕜)) i j ∂P := by
        ext i j; simp
      rw [hzero, hconst]
      exact of_integral_le_of_integral_of_ae_le (hupper k hk)
        (integrable_apply_of_ae_l2_opNorm_le (hmeas k hk) hMk) (fun _ _ ↦ integrable_const _)
    have hdiag := (le_iff.1 hle).diag_nonneg (i := Classical.arbitrary n)
    rw [RCLike.nonneg_iff] at hdiag
    simpa [RCLike.smul_re] using hdiag.1
  -- Optimize the Laplace parameter `θ = t / (v + L * t / 3)`.
  have hden : 0 < v + L * t / 3 := by positivity
  set θ : ℝ := t / (v + L * t / 3)
  have hθ : 0 < θ := div_pos ht hden
  have hθL : θ * L < 3 := by
    dsimp only [θ]
    rw [div_mul_eq_mul_div, div_lt_iff₀ hden]
    linarith
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hc_nonneg : 0 ≤ c := by
    dsimp only [c]
    have h1 : 0 < 1 - θ * L / 3 := by linarith
    positivity
  have hlap := hindep.measureReal_sSup_spectrum_sum_ge_le hmeas hherm hbdd (t := t) hθ
  -- Bound each CGF summand by `c • E[X k * X k]` and sum over `k ∈ s`.
  have hcgf_le : (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P)) ≤ c • V := by
    have hsum_V : ∑ k ∈ s, c • (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P) = c • V := by
      rw [← Finset.smul_sum]
      congr 1
      ext i j
      simp [V]
    rw [← hsum_V]
    refine Finset.sum_le_sum fun k hk ↦
      cfc_log_of_integral_exp_smul_le (hmeas k hk) (hherm k hk) (hmean k hk)
        (hupper k hk) (hbdd k hk) hθ.le hθL
  have hV_psd : V.PosSemidef := by
    have hsplit : V = ∑ k ∈ s, Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P := by
      ext i j; simp [V]
    rw [hsplit]
    refine Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) PosSemidef.zero fun k hk ↦ ?_
    obtain ⟨Mk, hMk⟩ := hbdd k hk
    have hXsq_int : ∀ i j, Integrable (fun ω ↦ (X k ω * X k ω) i j) P := by
      refine integrable_apply_of_ae_l2_opNorm_le (M := (max Mk 0) ^ 2)
        (continuous_mul.measurable.comp_aemeasurable ((hmeas k hk).prodMk (hmeas k hk)))
        (hMk.mono fun ω hω ↦ ?_)
      have h1 : ‖X k ω‖ ≤ max Mk 0 := hω.trans (le_max_left Mk 0)
      calc ‖X k ω * X k ω‖ ≤ ‖X k ω‖ * ‖X k ω‖ := norm_mul_le _ _
        _ ≤ max Mk 0 * max Mk 0 := mul_le_mul h1 h1 (norm_nonneg _) (le_max_right Mk 0)
        _ = (max Mk 0) ^ 2 := (sq _).symm
    exact posSemidef_of_integral
      ((hherm k hk).mono fun ω hω ↦ by
        simpa only [hω.eq] using posSemidef_conjTranspose_mul_self (X k ω))
      hXsq_int
  have hcgf_smul : (∑ k ∈ s, cfc Real.log
        (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P)) ≤
      (c * v) • (1 : Matrix n n 𝕜) := by
    calc
      (∑ k ∈ s, cfc Real.log
            (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))
          ≤ c • V := hcgf_le
      _ ≤ c • (v • (1 : Matrix n n 𝕜)) :=
          smul_le_smul_of_nonneg_left hV_psd.le_l2_opNorm_smul_one hc_nonneg
      _ = (c * v) • (1 : Matrix n n 𝕜) := smul_smul c v 1
  have hsum_herm : (∑ k ∈ s, cfc Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P)).IsHermitian :=
    Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero fun k _ ↦
      IsSelfAdjoint.isHermitian (cfc_predicate Real.log _)
  have htr_le := hsum_herm.re_trace_exp_le_card_mul_exp hcgf_smul
  have hden' : v + L * t / 3 ≠ 0 := hden.ne'
  have hv' : v ≠ 0 := hv.ne'
  have h1 : 1 - θ * L / 3 = v / (v + L * t / 3) := by
    dsimp only [θ]
    rw [div_mul_eq_mul_div, div_div, one_sub_div (by positivity : (v + L * t / 3) * 3 ≠ 0)]
    field_simp [hden']
    ring
  have hcv : c * v = t ^ 2 / (2 * (v + L * t / 3)) := by
    dsimp only [c]
    rw [h1]
    dsimp only [θ]
    field_simp [hv', hden']
  have hexp_eq : -θ * t + c * v = -(t ^ 2 / 2) / (v + L * t / 3) := by
    rw [hcv]
    dsimp only [θ]
    field_simp [hden']
    ring
  calc
    P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))}
        ≤ Real.exp (-θ * t) * RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
            (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))).trace := hlap
    _ ≤ Real.exp (-θ * t) * ((Fintype.card n : ℝ) * Real.exp (c * v)) :=
        mul_le_mul_of_nonneg_left htr_le (Real.exp_pos _).le
    _ = (Fintype.card n : ℝ) * Real.exp (-θ * t + c * v) := by
        rw [Real.exp_add]; ring
    _ = (Fintype.card n : ℝ) * Real.exp (-(t ^ 2 / 2) / (v + L * t / 3)) := by
        rw [hexp_eq]

/-- **Two-sided Hermitian Matrix Bernstein inequality** (Tropp 2012, Theorem 1.4). Let `X k`
(`k ∈ s`) be independent, centered Hermitian random matrices over `𝕜` (`ℝ` or `ℂ`) satisfying
`‖X k‖ ≤ L` almost everywhere. Then for every `t > 0`,
`P {‖∑ k ∈ s, X k‖ ≥ t} ≤ 2 * card n * exp (-(t ^ 2 / 2) / (‖∑ k ∈ s, E[X k * X k]‖ + L * t / 3))`.
-/
theorem iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_isHermitian [IsProbabilityMeasure P]
    [Fintype n] [DecidableEq n] {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0)
    {L : ℝ} (hbdd : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖X k ω‖ ≤ L)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤
      2 * (Fintype.card n : ℝ) * Real.exp (-(t ^ 2 / 2) /
        (‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖ + L * t / 3)) := by
  by_cases hn : Nonempty n
  · let : Nonempty n := hn
    have hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω ≤ L • (1 : Matrix n n 𝕜) := fun k hk ↦
      ((hherm k hk).and (hbdd k hk)).mono fun _ ⟨h1, h2⟩ ↦ h1.le_smul_one_of_l2_opNorm_le h2
    have hpos := hindep.measureReal_sSup_spectrum_sum_ge_le_of_le hmeas hherm hmean hupper
      (fun k hk ↦ ⟨L, hbdd k hk⟩) ht.le
    have hneg_indep : iIndepFun (fun k ω ↦ -X k ω) P :=
      hindep.comp (fun _ A ↦ -A) fun _ ↦ continuous_neg.measurable
    have hneg_meas : ∀ k ∈ s, AEMeasurable (fun ω ↦ -X k ω) P :=
      fun k hk ↦ continuous_neg.measurable.comp_aemeasurable (hmeas k hk)
    have hneg_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (-X k ω).IsHermitian :=
      fun k hk ↦ (hherm k hk).mono fun _ h ↦ h.neg
    have hneg_mean : ∀ k ∈ s, ∀ i j, ∫ ω, (-X k ω) i j ∂P = 0 := fun k hk i j ↦ by
      simp [integral_neg, hmean k hk i j]
    have hneg_bdd : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖-X k ω‖ ≤ L :=
      fun k hk ↦ (hbdd k hk).mono fun _ h ↦ by simpa using h
    have hneg_upper : ∀ k ∈ s, ∀ᵐ ω ∂P, -X k ω ≤ L • (1 : Matrix n n 𝕜) := fun k hk ↦
      ((hneg_herm k hk).and (hneg_bdd k hk)).mono fun _ ⟨h1, h2⟩ ↦ h1.le_smul_one_of_l2_opNorm_le h2
    have hneg := hneg_indep.measureReal_sSup_spectrum_sum_ge_le_of_le hneg_meas hneg_herm
      hneg_mean hneg_upper (fun k hk ↦ ⟨L, hneg_bdd k hk⟩) ht.le
    simp only [neg_mul_neg] at hneg
    have hsum_herm : ∀ᵐ ω ∂P, (∑ k ∈ s, X k ω).IsHermitian := by
      have hall : ∀ᵐ ω ∂P, ∀ k ∈ s, (X k ω).IsHermitian :=
        (ae_ball_iff s.countable_toSet).2 hherm
      exact hall.mono fun ω hω ↦
        Finset.sum_induction _ _ (fun _ _ h₁ h₂ ↦ h₁.add h₂) isHermitian_zero hω
    have hsub : {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤ᵐ[P]
        {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ∪
          {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} := by
      refine hsum_herm.mono fun ω hω hge ↦ ?_
      simp only [Set.mem_ofPred_eq] at hge
      rw [hω.l2_opNorm_eq_max_sSup_spectrum_real, le_max_iff] at hge
      simpa only [Set.mem_union, Set.mem_ofPred_eq, Finset.sum_neg_distrib] using hge
    have hunion : P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤
        P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} +
          P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} := by
      calc
        P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖}
            ≤ P.real ({ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ∪
                {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))}) :=
              ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)
        _ ≤ P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} +
              P.real {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} :=
              measureReal_union_le _ _
    linarith
  · have : IsEmpty n := not_nonempty_iff.1 hn
    have hemp : {ω | t ≤ ‖∑ k ∈ s, X k ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have h0 : ∑ k ∈ s, X k ω = 0 := Subsingleton.elim _ _
      rwa [h0, norm_zero]
    rw [hemp, measureReal_empty]
    positivity

/-- **Rectangular Matrix Bernstein inequality** (Tropp 2012, Theorem 1.6). Let `Z k` (`k ∈ s`) be
independent, centered random `m × p` matrices over `𝕜` (`ℝ` or `ℂ`) satisfying `‖Z k‖ ≤ L` almost
everywhere, and let
`v = max ‖∑ k ∈ s, E[Z k * (Z k)ᴴ]‖ ‖∑ k ∈ s, E[(Z k)ᴴ * Z k]‖`.
Then for every `t > 0`,
`P {‖∑ k ∈ s, Z k‖ ≥ t} ≤ (card m + card p) * exp (-(t ^ 2 / 2) / (v + L * t / 3))`. -/
theorem iIndepFun.measureReal_l2_opNorm_sum_ge_le [IsProbabilityMeasure P]
    {m p : Type*} [Fintype m] [Fintype p] [DecidableEq m] [DecidableEq p]
    {s : Finset ι} {Z : ι → Ω → Matrix m p 𝕜}
    (hindep : iIndepFun Z P)
    (hmeas : ∀ k ∈ s, AEMeasurable (Z k) P)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, Z k ω i j ∂P = 0)
    {L : ℝ} (hbdd : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ L)
    {t : ℝ} (ht : 0 < t) :
    P.real {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} ≤
      ((Fintype.card m : ℝ) + (Fintype.card p : ℝ)) * Real.exp (-(t ^ 2 / 2) /
        (max ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (Z k ω * (Z k ω)ᴴ) i j ∂P‖
            ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, ((Z k ω)ᴴ * Z k ω) i j ∂P‖ +
          L * t / 3)) := by
  by_cases hmp : Nonempty (m ⊕ p)
  · let : Nonempty (m ⊕ p) := hmp
    -- Apply one-sided Hermitian Matrix Bernstein to the Hermitian dilation `fromBlocks 0 Z Zᴴ 0`.
    let dil : Matrix m p 𝕜 → Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fun A ↦ fromBlocks 0 A Aᴴ 0
    have hdil_cont : Continuous dil := by
      refine continuous_pi fun i ↦ continuous_pi fun j ↦ ?_
      cases i with
      | inl i =>
        cases j with
        | inl j => simpa [dil] using continuous_const
        | inr j => exact (continuous_apply j).comp (continuous_apply i)
      | inr i =>
        cases j with
        | inl j => exact continuous_star.comp ((continuous_apply i).comp (continuous_apply j))
        | inr j => simpa [dil] using continuous_const
    let D : ι → Ω → Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fun k ω ↦ dil (Z k ω)
    have hD_indep : iIndepFun D P := hindep.comp (fun _ ↦ dil) (fun _ ↦ hdil_cont.measurable)
    have hD_meas : ∀ k ∈ s, AEMeasurable (D k) P :=
      fun k hk ↦ hdil_cont.measurable.comp_aemeasurable (hmeas k hk)
    have hD_herm : ∀ k ∈ s, ∀ᵐ ω ∂P, (D k ω).IsHermitian :=
      fun _ _ ↦ Eventually.of_forall fun _ ↦ isHermitian_zero.fromBlocks rfl isHermitian_zero
    have hD_mean : ∀ k ∈ s, ∀ i j, ∫ ω, D k ω i j ∂P = 0 := by
      intro k hk i j
      cases i with
      | inl i =>
        cases j with
        | inl j => simp [D, dil]
        | inr j => simpa [D, dil] using hmean k hk i j
      | inr i =>
        cases j with
        | inl j =>
          simp only [D, dil, fromBlocks_apply₂₁, conjTranspose_apply, RCLike.star_def]
          rw [integral_conj, hmean k hk j i, map_zero]
        | inr j => simp [D, dil]
    have hD_bdd : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖D k ω‖ ≤ L := fun k hk ↦
      (hbdd k hk).mono fun ω hω ↦ by rwa [l2_opNorm_fromBlocks_zero_conjTranspose]
    have hD_upper : ∀ k ∈ s, ∀ᵐ ω ∂P, D k ω ≤ L • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) := fun k hk ↦
      ((hD_herm k hk).and (hD_bdd k hk)).mono fun _ ⟨h1, h2⟩ ↦ h1.le_smul_one_of_l2_opNorm_le h2
    have hbound := hD_indep.measureReal_sSup_spectrum_sum_ge_le_of_le hD_meas hD_herm hD_mean
      hD_upper (fun k hk ↦ ⟨L, hD_bdd k hk⟩) ht.le
    have hsum_dil (ω : Ω) : ∑ k ∈ s, D k ω = dil (∑ k ∈ s, Z k ω) := by
      ext i j
      cases i <;> cases j <;> simp [D, dil]
    have hset : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, D k ω))} = {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} := by
      ext ω
      rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, hsum_dil,
        sSup_spectrum_real_fromBlocks_zero_conjTranspose]
    have hvar :
        (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (D k ω * D k ω) i j ∂P) =
          fromBlocks
            (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (Z k ω * (Z k ω)ᴴ) i j ∂P) 0 0
            (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, ((Z k ω)ᴴ * Z k ω) i j ∂P) := by
      have hsq (k : ι) (ω : Ω) :
          D k ω * D k ω = fromBlocks (Z k ω * (Z k ω)ᴴ) 0 0 ((Z k ω)ᴴ * Z k ω) := by
        simp [D, dil, fromBlocks_multiply]
      ext i j
      cases i <;> cases j <;> simp [hsq]
    rw [hset, hvar, l2_opNorm_fromBlocks_diagonal, Fintype.card_sum, Nat.cast_add] at hbound
    exact hbound
  · have : IsEmpty m := ⟨fun i ↦ hmp ⟨Sum.inl i⟩⟩
    have : IsEmpty p := ⟨fun j ↦ hmp ⟨Sum.inr j⟩⟩
    have hemp : {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} = ∅ := by
      ext ω
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
      have h0 : ∑ k ∈ s, Z k ω = 0 := Subsingleton.elim _ _
      rwa [h0, norm_zero]
    rw [hemp, measureReal_empty]
    positivity

end ProbabilityTheory
