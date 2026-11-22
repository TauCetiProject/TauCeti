/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Concentration.Matrix.Laplace
import TauCeti.Analysis.Matrix.Eigenvalues.OperatorNorm
import TauCeti.Analysis.Matrix.Exponential.Bounds
import TauCeti.Analysis.Matrix.L2OpNorm
import TauCeti.Analysis.Matrix.Order
import TauCeti.MeasureTheory.Integral.Exp.Matrix
import TauCeti.MeasureTheory.Integral.Matrix
import TauCeti.MeasureTheory.Integral.PosSemidef

/-!
# Matrix Bernstein inequalities

Tropp's matrix Bernstein inequalities for finite sums of independent centered random matrices over
any `RCLike` field `𝕜` (`ℝ` or `ℂ`):

* `TauCeti.cfc_log_integral_exp_smul_le`: Bernstein matrix CGF bound for square-integrable
  matrices bounded above in Loewner order (Tropp 2012, Lemma 6.7).
* `ProbabilityTheory.iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_le`: one-sided Hermitian
  Matrix Bernstein for square-integrable summands bounded above by `L • 1` (Tropp 2012,
  Theorem 1.4).
* `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le_of_isHermitian`: two-sided Hermitian
  Matrix Bernstein (Tropp 2012, Theorem 1.4).
* `ProbabilityTheory.iIndepFun.measureReal_l2_opNorm_sum_ge_le`: rectangular Matrix Bernstein via
  the Hermitian dilation `Matrix.hermitianDilation` (Tropp 2012, Theorem 1.6).

## References

* J. A. Tropp, *User-friendly tail bounds for sums of random matrices*, Found. Comput. Math. 12
  (2012), 389–434, Theorems 1.4 and 1.6 and Section 6.
-/

public section

open MeasureTheory ProbabilityTheory Matrix Filter
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

namespace TauCeti

variable {Ω 𝕜 n : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  [RCLike 𝕜] [MeasurableSpace 𝕜] [BorelSpace 𝕜] [Fintype n] [DecidableEq n]

/-- **Bernstein matrix cumulant generating function bound** (Tropp 2012, Lemma 6.7). Let `X` be a
centered, square-integrable random matrix over `𝕜` (`ℝ` or `ℂ`) satisfying `X ≤ L • 1` almost
everywhere. Then for every `θ ≥ 0` with `θ * L < 3`,
`log E[exp (θ X)] ≤ (θ ^ 2 / (2 * (1 - θ * L / 3))) • E[X * X]`. -/
theorem cfc_log_integral_exp_smul_le [IsProbabilityMeasure P]
    {X : Ω → Matrix n n 𝕜} (hmeas : AEMeasurable X P)
    (hmean : ∀ i j, ∫ ω, X ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ᵐ ω ∂P, X ω ≤ L • (1 : Matrix n n 𝕜))
    (hsq : Integrable (fun ω ↦ ‖X ω‖ ^ 2) P)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    cfc Real.log (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X ω)) i j ∂P) ≤
      (θ ^ 2 / (2 * (1 - θ * L / 3))) •
        (Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P) := by
  by_cases hn : IsEmpty n
  · exact le_of_eq (Subsingleton.elim _ _)
  have : Nonempty n := not_isEmpty_iff.1 hn
  let : NormedAlgebra ℝ (Matrix n n 𝕜) := Matrix.l2OpNormedAlgebraReal
  have hherm : ∀ᵐ ω ∂P, (X ω).IsHermitian := hupper.mono fun _ ↦ isHermitian_of_le_smul_one
  have hX_apply_int := integrable_apply_of_integrable_l2_opNorm_sq hmeas hsq
  have hX_int : Integrable X P := integrable_l2Op_matrix_iff.2 hX_apply_int
  have hL : 0 ≤ L := nonneg_of_integral_eq_zero_of_ae_le_smul_one hX_apply_int hmean hupper
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hpt : ∀ᵐ ω ∂P,
      NormedSpace.exp (θ • X ω) ≤ (1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω) :=
    hupper.mono fun _ hU ↦ exp_smul_le_one_add_add_mul_self hL hU hθ hθL
  have hθX_meas := (continuous_const_smul θ).measurable.comp_aemeasurable hmeas
  have hθX_upper : ∀ᵐ ω ∂P, θ • X ω ≤ (θ * L) • (1 : Matrix n n 𝕜) :=
    hupper.mono fun _ h ↦ (smul_le_smul_of_nonneg_left h hθ).trans_eq (smul_smul _ _ _)
  have hXsq_apply_int := integrable_mul_self_apply hmeas hsq
  have hXsq_int : Integrable (fun ω ↦ X ω * X ω) P := integrable_l2Op_matrix_iff.2 hXsq_apply_int
  have hRHS_int : Integrable (fun ω ↦ (1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω)) P :=
    ((integrable_const (1 : Matrix n n 𝕜)).add (hX_int.smul θ)).add (hXsq_int.smul c)
  have hE_le := integral_le_integral_of_ae_le hpt
    (integrable_exp_apply_of_ae_le_smul_one hθX_meas hθX_upper)
    (integrable_l2Op_matrix_iff.1 hRHS_int)
  set V : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∫ ω, (X ω * X ω) i j ∂P
  have hE_rhs : (Matrix.of fun i j ↦
        ∫ ω, ((1 : Matrix n n 𝕜) + θ • X ω + c • (X ω * X ω)) i j ∂P) =
      (1 : Matrix n n 𝕜) + c • V := by
    have hadd₁ := integral_add
      (f := fun ω ↦ (1 : Matrix n n 𝕜) + θ • X ω) (g := fun ω ↦ c • (X ω * X ω))
      ((integrable_const (1 : Matrix n n 𝕜)).add (hX_int.smul θ)) (hXsq_int.smul c)
    have hadd₂ := integral_add (f := fun _ ↦ (1 : Matrix n n 𝕜)) (g := fun ω ↦ θ • X ω)
      (integrable_const _) (hX_int.smul θ)
    have hmean0 : (Matrix.of fun i j ↦ ∫ ω, X ω i j ∂P) = 0 := by ext; simp [hmean]
    rw [← integral_l2Op_matrix_eq_of hRHS_int, hadd₁, hadd₂, integral_const, probReal_univ,
      one_smul, integral_smul, integral_smul, integral_l2Op_matrix_eq_of hX_int,
      integral_l2Op_matrix_eq_of hXsq_int, hmean0, smul_zero, add_zero]
  rw [hE_rhs] at hE_le
  have hcV_herm : (c • V).IsHermitian :=
    (isHermitian_integral_of_ae_isHermitian (hherm.mono fun ω hω ↦ by
      simpa only [hω.eq] using isHermitian_conjTranspose_mul_self (X ω))).smul (IsSelfAdjoint.all c)
  exact cfc_log_integral_exp_le_of_le_one_add hθX_meas hθX_upper hcV_herm hE_le

/-- Optimal Bernstein exponent identity: for `θ = t / (v + L * t / 3)` and
`c = θ ^ 2 / (2 * (1 - θ * L / 3))`, `-θ * t + c * v = -(t ^ 2 / 2) / (v + L * t / 3)`. -/
private theorem bernstein_exponent_eq {v L t : ℝ} (hv : 0 < v) (hL : 0 ≤ L) (ht : 0 < t) :
    let θ := t / (v + L * t / 3);
    -θ * t + (θ ^ 2 / (2 * (1 - θ * L / 3))) * v = -(t ^ 2 / 2) / (v + L * t / 3) := by
  intro θ
  have hden : 0 < v + L * t / 3 := by positivity
  have h1 : 1 - θ * L / 3 = v / (v + L * t / 3) := by
    dsimp only [θ]; field_simp [hden.ne']; ring
  rw [h1]; dsimp only [θ]; field_simp [hv.ne', hden.ne']; ring

/-- Bernstein CGF trace bound: summing `TauCeti.cfc_log_integral_exp_smul_le` over `k ∈ s` and
bounding the matrix variance `V` by `‖V‖ • 1` yields
`Re Tr exp (∑ log E[exp (θ X k)]) ≤ card n * exp (c * ‖V‖)`. -/
private theorem re_trace_exp_sum_cfc_log_le_bernstein {ι : Type*} [IsProbabilityMeasure P]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω ≤ L • (1 : Matrix n n 𝕜))
    (hsq : ∀ k ∈ s, Integrable (fun ω ↦ ‖X k ω‖ ^ 2) P)
    {θ : ℝ} (hθ : 0 ≤ θ) (hθL : θ * L < 3) :
    RCLike.re (NormedSpace.exp (∑ k ∈ s, cfc Real.log
      (Matrix.of fun i j ↦ ∫ ω, (NormedSpace.exp (θ • X k ω)) i j ∂P))).trace ≤
      (Fintype.card n : ℝ) * Real.exp ((θ ^ 2 / (2 * (1 - θ * L / 3))) *
        ‖Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P‖) := by
  set V : Matrix n n 𝕜 := Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (X k ω * X k ω) i j ∂P
  set c : ℝ := θ ^ 2 / (2 * (1 - θ * L / 3))
  have hc_nonneg : 0 ≤ c := by
    have : 0 < 1 - θ * L / 3 := by linarith
    positivity
  have hV_split : V = ∑ k ∈ s, Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P := by ext; simp [V]
  have hV_psd : V.PosSemidef := hV_split ▸ Matrix.posSemidef_sum s fun k hk ↦
    posSemidef_integral ((hupper k hk).mono fun ω hU ↦ by
      have hω := isHermitian_of_le_smul_one hU
      simpa only [hω.eq] using posSemidef_conjTranspose_mul_self (X k ω))
      (integrable_mul_self_apply (hmeas k hk) (hsq k hk))
  have hsum_V :
      (∑ k ∈ s, c • (Matrix.of fun i j ↦ ∫ ω, (X k ω * X k ω) i j ∂P)) = c • V := by
    rw [← Finset.smul_sum, ← hV_split]
  exact re_trace_exp_sum_cfc_log_le_of_sum_le s
    (fun k hk ↦ cfc_log_integral_exp_smul_le (hmeas k hk) (hmean k hk) (hupper k hk)
      (hsq k hk) hθ hθL)
    (hsum_V ▸ (smul_le_smul_of_nonneg_left hV_psd.le_l2_opNorm_smul_one hc_nonneg).trans_eq
      (smul_smul c ‖V‖ 1))

end TauCeti

namespace ProbabilityTheory

variable {Ω 𝕜 n ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [RCLike 𝕜]

/-- Shared empty-index operator-norm tail vanish helper: when either `m` or `p` is empty, a
sum of `m × p` matrices is `0`, so its positive-threshold norm tail event is empty and has zero
probability. -/
private theorem measureReal_l2_opNorm_sum_ge_le_of_subsingleton {m p : Type*}
    [Fintype m] [Fintype p] [DecidableEq p]
    [Subsingleton (Matrix m p 𝕜)] {s : Finset ι} {Z : ι → Ω → Matrix m p 𝕜}
    {t : ℝ} (ht : 0 < t) {rhs : ℝ} (hrhs : 0 ≤ rhs) :
    P.real {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} ≤ rhs := by
  have hevent : {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} = ∅ := by
    ext ω
    simp [Subsingleton.elim (∑ k ∈ s, Z k ω) 0, not_le.2 ht]
  rw [hevent, measureReal_empty]
  exact hrhs

section

variable [MeasurableSpace 𝕜] [BorelSpace 𝕜]

/-- **One-sided Hermitian Matrix Bernstein inequality** (Tropp 2012, Theorem 1.4). Let `X k`
(`k ∈ s`) be independent, centered, square-integrable random matrices over `𝕜` (`ℝ` or `ℂ`) with
`X k ≤ L • 1` almost everywhere, and let `V = ∑ k ∈ s, E[X k * X k]` be the matrix variance
statistic. Then for every `t ≥ 0`,
`P {λ_max (∑ k ∈ s, X k) ≥ t} ≤ card n * exp (-(t ^ 2 / 2) / (‖V‖ + L * t / 3))`. -/
theorem iIndepFun.measureReal_sSup_spectrum_sum_ge_le_of_le [IsProbabilityMeasure P]
    [Fintype n] [DecidableEq n] [Nonempty n]
    {s : Finset ι} {X : ι → Ω → Matrix n n 𝕜}
    (hindep : iIndepFun X P)
    (hmeas : ∀ k ∈ s, AEMeasurable (X k) P)
    (hmean : ∀ k ∈ s, ∀ i j, ∫ ω, X k ω i j ∂P = 0)
    {L : ℝ} (hupper : ∀ k ∈ s, ∀ᵐ ω ∂P, X k ω ≤ L • (1 : Matrix n n 𝕜))
    (hsq : ∀ k ∈ s, Integrable (fun ω ↦ ‖X k ω‖ ^ 2) P)
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
    exact measureReal_le_one.trans (by exact_mod_cast Fintype.card_pos (α := n))
  -- Degenerate case `v = 0`: each `X k` (`k ∈ s`) is a.e. zero, so the tail probability is `0`.
  rcases (norm_nonneg V).eq_or_lt with hv | hv
  · have hherm : ∀ k ∈ s, ∀ᵐ ω ∂P, (X k ω).IsHermitian :=
      fun k hk ↦ (hupper k hk).mono fun _ ↦ TauCeti.isHermitian_of_le_smul_one
    have hsum0 : ∀ᵐ ω ∂P, ∑ k ∈ s, X k ω = 0 :=
      ((ae_ball_iff s.countable_toSet).2
        (TauCeti.ae_eq_zero_of_sum_integral_mul_self_eq_zero hherm
          (fun k hk i ↦ TauCeti.integrable_mul_self_apply (hmeas k hk) (hsq k hk) i i)
          (norm_eq_zero.1 hv.symm))).mono fun _ ↦ Finset.sum_eq_zero
    have hae_empty : {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} =ᵐ[P] (∅ : Set Ω) :=
      hsum0.mono fun ω hω ↦
        ⟨fun hge ↦ not_le_of_gt ht (by simpa [hω, TauCeti.sSup_spectrum_real_zero] using hge),
          False.elim⟩
    rw [measureReal_congr hae_empty, measureReal_empty]
    positivity
  -- Main case `0 < t` and `0 < v`: deduce `s.Nonempty` and `0 ≤ L`.
  have hL : 0 ≤ L := by
    have hsne : s.Nonempty := by
      by_contra hemp
      have hV0 : V = 0 := by ext; simp [V, Finset.not_nonempty_iff_eq_empty.1 hemp]
      exact hv.ne' (by simp [hV0])
    obtain ⟨k, hk⟩ := hsne
    exact TauCeti.nonneg_of_integral_eq_zero_of_ae_le_smul_one
      (TauCeti.integrable_apply_of_integrable_l2_opNorm_sq (hmeas k hk) (hsq k hk))
      (hmean k hk) (hupper k hk)
  -- Combine the master Laplace bound and the Bernstein CGF bound at `θ = t / (v + L * t / 3)`.
  have hden : 0 < v + L * t / 3 := by positivity
  set θ : ℝ := t / (v + L * t / 3)
  have hθ : 0 < θ := div_pos ht hden
  have hθL : θ * L < 3 := by dsimp only [θ]; rw [div_mul_eq_mul_div, div_lt_iff₀ hden]; linarith
  have hlap := hindep.measureReal_sSup_spectrum_sum_ge_le hmeas
    (fun k hk ↦ ⟨L, hupper k hk⟩) (t := t) hθ
  have hcgf := TauCeti.re_trace_exp_sum_cfc_log_le_bernstein hmeas hmean hupper hsq hθ.le hθL
  exact (hlap.trans (mul_le_mul_of_nonneg_left hcgf (Real.exp_pos _).le)).trans_eq
    (by rw [← TauCeti.bernstein_exponent_eq hv hL ht, Real.exp_add]; ring)

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
    have hsq := fun k hk ↦ TauCeti.integrable_l2_opNorm_sq_of_ae_le (hmeas k hk) (hbdd k hk)
    have hpos := hindep.measureReal_sSup_spectrum_sum_ge_le_of_le hmeas hmean
      (fun k hk ↦ ((hherm k hk).and (hbdd k hk)).mono fun _ ⟨h1, h2⟩ ↦
        h1.le_smul_one_of_l2_opNorm_le h2) hsq ht.le
    have hneg := (hindep.comp (fun _ A ↦ -A) fun _ ↦
        continuous_neg.measurable).measureReal_sSup_spectrum_sum_ge_le_of_le
      (fun k hk ↦ continuous_neg.measurable.comp_aemeasurable (hmeas k hk))
      (fun k hk i j ↦ by simp [integral_neg, hmean k hk i j])
      (fun k hk ↦ ((hherm k hk).and (hbdd k hk)).mono fun _ ⟨h1, h2⟩ ↦
        h1.neg.le_smul_one_of_l2_opNorm_le (by simpa using h2))
      (fun k hk ↦ by simpa using hsq k hk) ht.le
    simp only [Function.comp_apply, neg_mul_neg] at hneg
    have hsub : {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤ᵐ[P]
        {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, X k ω))} ∪
          {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, -X k ω))} :=
      (TauCeti.ae_isHermitian_finsetSum hherm).mono fun _ hω hge ↦ by
        simp only [Set.mem_ofPred_eq] at hge
        rw [hω.l2_opNorm_eq_max_sSup_spectrum_real, le_max_iff] at hge
        simpa only [Set.mem_union, Set.mem_ofPred_eq, Finset.sum_neg_distrib] using hge
    have hunion : P.real {ω | t ≤ ‖∑ k ∈ s, X k ω‖} ≤ _ :=
      (ENNReal.toReal_mono (measure_ne_top P _) (measure_mono_ae hsub)).trans
        (measureReal_union_le _ _)
    linarith
  · have : IsEmpty n := not_nonempty_iff.1 hn
    exact measureReal_l2_opNorm_sum_ge_le_of_subsingleton ht (by positivity)

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
    -- Apply one-sided Hermitian Matrix Bernstein to the Hermitian dilation `Z.hermitianDilation`.
    let D : ι → Ω → Matrix (m ⊕ p) (m ⊕ p) 𝕜 := fun k ω ↦ (Z k ω).hermitianDilation
    have hD_meas := fun k hk ↦
      Matrix.continuous_hermitianDilation.measurable.comp_aemeasurable (hmeas k hk)
    have hD_bdd : ∀ k ∈ s, ∀ᵐ ω ∂P, ‖D k ω‖ ≤ L := fun k hk ↦
      (hbdd k hk).mono fun _ h ↦ by simpa [D] using h
    have hD_upper : ∀ k ∈ s, ∀ᵐ ω ∂P, D k ω ≤ L • (1 : Matrix (m ⊕ p) (m ⊕ p) 𝕜) :=
      fun k hk ↦ (hD_bdd k hk).mono fun _ h ↦
        (Matrix.isHermitian_hermitianDilation _).le_smul_one_of_l2_opNorm_le h
    have hD_sq : ∀ k ∈ s, Integrable (fun ω ↦ ‖D k ω‖ ^ 2) P :=
      fun k hk ↦ TauCeti.integrable_l2_opNorm_sq_of_ae_le (hD_meas k hk) (hD_bdd k hk)
    have hD_mean : ∀ k ∈ s, ∀ i j, ∫ ω, D k ω i j ∂P = 0 := fun k hk i j ↦ by
      cases i <;> cases j <;> simp [D, Matrix.hermitianDilation_def, hmean k hk,
        conjTranspose_apply, RCLike.star_def, integral_conj]
    have hbound := (hindep.comp (fun _ ↦ Matrix.hermitianDilation)
        (fun _ ↦ Matrix.continuous_hermitianDilation.measurable))
      |>.measureReal_sSup_spectrum_sum_ge_le_of_le hD_meas hD_mean hD_upper hD_sq ht.le
    simp only [Function.comp_apply] at hbound
    have hset :
        {ω | t ≤ sSup (spectrum ℝ (∑ k ∈ s, D k ω))} = {ω | t ≤ ‖∑ k ∈ s, Z k ω‖} := by
      ext ω
      simp only [Set.mem_ofPred_eq, D, ← Matrix.hermitianDilation_sum,
        Matrix.sSup_spectrum_real_hermitianDilation]
    have hvar : (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (D k ω * D k ω) i j ∂P) =
        fromBlocks (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, (Z k ω * (Z k ω)ᴴ) i j ∂P) 0 0
          (Matrix.of fun i j ↦ ∑ k ∈ s, ∫ ω, ((Z k ω)ᴴ * Z k ω) i j ∂P) := by
      ext i j; cases i <;> cases j <;> simp [D, Matrix.hermitianDilation_mul_self]
    rwa [hset, hvar, Matrix.l2_opNorm_fromBlocks_zero₁₂_zero₂₁, Fintype.card_sum,
      Nat.cast_add] at hbound
  · have : IsEmpty m := ⟨fun i ↦ hmp ⟨Sum.inl i⟩⟩
    have : IsEmpty p := ⟨fun j ↦ hmp ⟨Sum.inr j⟩⟩
    exact measureReal_l2_opNorm_sum_ge_le_of_subsingleton ht (by positivity)

end

end ProbabilityTheory
