/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
public import TauCeti.Analysis.Fredholm.Proper
public import TauCeti.Analysis.ODE.EnergyEstimate.Fredholm

/-!
# A degenerate limit destroys the Fredholm property of the trajectory operator

Let `A : ℝ → End(E)` be an essentially bounded family of operators on a real Banach space `E`.
This file proves that the trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, E) → L²(ℝ, E)`

(`TauCeti.WeakDerivStep.trajectoryOperator`, for an `L∞` class of `A`) is **not** Fredholm as
soon as `A s v → 0` for some nonzero vector `v` as `s → +∞` or as `s → -∞`; in particular, as soon
as `A` has a limit at one end which is not injective. Combined with
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator`, this shows that for a `C¹` family of
symmetric operators on a finite-dimensional space, with limits at both ends and derivative
tending to zero, `D_A` is Fredholm exactly when both limits are invertible
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`).

The obstruction is a sequence of approximate kernel elements escaping to infinity. Take smooth
plateaus `ψₙ`, equal to one on an interval of length `2 (n + 1)` and supported in the interval
of length `2 (n + 2)` with the same centre, the centres moving off to the end at which `A s v`
tends to zero. Their derivatives are bounded independently of `n` and supported on two intervals
of length one (`TauCeti.exists_forall_contDiff_plateau`), so after rescaling `v` to a unit vector,
the normalized paths `uₙ = ψₙ v / ‖ψₙ v‖_{L²}` satisfy

`‖D_A uₙ‖²_{L²} ≤ 2 ‖ψₙ'‖² / ‖ψₙ‖² + 2 sup_{supp ψₙ} ‖A s v‖² → 0`,

while `‖uₙ‖_{L²} = 1` and `uₙ` stays bounded in `W^{1,2}`. A Fredholm operator is proper on
bounded sets (`ContinuousLinearMap.tendsto_subseq_of_isBounded`), so some subsequence would
converge in `W^{1,2}`, hence in `L²`. But an `L²` limit of paths whose supports leave every
bounded set vanishes almost everywhere, contradicting `‖uₙ‖_{L²} = 1`.

## Main declarations

* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atBot`: if `A s v → 0` for
  some `v ≠ 0` at one end, then `D_A` is not Fredholm.
* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atBot`: the
  same when `A` converges at that end to an operator which is not injective.
* `TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff`: for a `C¹` family of symmetric
  operators on a finite-dimensional space with limits at both ends and derivative tending to
  zero, `D_A` is Fredholm if and only if both limits are injective.

## References

* M. Schwarz, *Morse Homology*, Chapter 2 (the trajectory operator is Fredholm precisely for
  hyperbolic limits).
* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc. 27
  (1995) (the operator `d/ds + A(s)` is Fredholm if and only if the limits are invertible).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter Metric
open scoped ENNReal Topology Distributions

namespace TauCeti.WeakDerivStep

variable {E : Type*} [NormedAddCommGroup E]

section Complete

variable [NormedSpace ℝ E] [CompleteSpace E] {A : ℝ → E →L[ℝ] E}

/-- The path `φ v` of a test function `φ` and a unit vector `v` has `L²` norm `‖φ‖_{L²}` and
`W^{1,2}` norm `‖φ‖_{W^{1,2}}`. -/
private theorem norm_sq_smulRightW1pL_ofTestFunctionₗ {v : E} (hv : ‖v‖ = 1)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ‖prev _ (smulRightW1pL v (W1p.ofTestFunctionₗ volume ⊤ 2 φ))‖ ^ 2 = ∫ s, φ s ^ 2 ∧
      ‖smulRightW1pL v (W1p.ofTestFunctionₗ volume ⊤ 2 φ)‖ ^ 2 =
        (∫ s, φ s ^ 2) + ∫ s, deriv φ s ^ 2 := by
  have hu := prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (mu := volume) (p := 2) v φ
  have hC1 : ContDiff ℝ 1 fun s ↦ φ s • v :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).smul contDiff_const
  have hprev : ‖prev _ (smulRightW1pL v (W1p.ofTestFunctionₗ volume ⊤ 2 φ))‖ ^ 2 =
      ∫ s, φ s ^ 2 := by
    rw [norm_prev_sq_eq_integral hu]
    simp [norm_smul, hv]
  refine ⟨hprev, ?_⟩
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, hprev,
    norm_weakFDeriv_sq_eq_integral hC1 hu]
  simp [deriv_smul_const ((φ.contDiff.differentiable (by simp)) _), norm_smul, hv]

/-- If `‖A s v‖ ≤ ε` on the support of a test function `φ`, for a unit vector `v`, then
`‖D_A (φ v)‖² ≤ 2 ‖φ'‖² + 2 ε² ‖φ‖²` in `L²`. -/
private theorem norm_trajectoryOperator_smulRightW1pL_ofTestFunctionₗ_sq_le
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {v : E} (hv : ‖v‖ = 1)
    (φ : 𝓓((⊤ : Opens ℝ), ℝ)) {ε : ℝ} (hε : ∀ s ∈ tsupport φ, ‖A s v‖ ≤ ε) :
    ‖trajectoryOperator (p := 2) AL (smulRightW1pL v (W1p.ofTestFunctionₗ volume ⊤ 2 φ))‖ ^ 2 ≤
      2 * (∫ s, deriv φ s ^ 2) + 2 * ε ^ 2 * ∫ s, φ s ^ 2 := by
  have hC1 : ContDiff ℝ 1 fun s ↦ φ s • v :=
    (φ.contDiff.of_le (by exact_mod_cast le_top)).smul contDiff_const
  have hderiv (s : ℝ) : deriv (fun s ↦ φ s • v) s = deriv φ s • v :=
    deriv_smul_const ((φ.contDiff.differentiable (by simp)) s) v
  have hint : Integrable (fun s ↦ φ s ^ 2) :=
    Continuous.integrable_of_hasCompactSupport (by fun_prop)
      (φ.hasCompactSupport.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num))
  have hdint : Integrable (fun s ↦ deriv φ s ^ 2) :=
    Continuous.integrable_of_hasCompactSupport
      ((φ.contDiff.continuous_deriv (by simp)).pow 2)
      (φ.hasCompactSupport.deriv.comp_left (g := fun x : ℝ ↦ x ^ 2) (by norm_num))
  rw [norm_trajectoryOperator_sq_eq_integral hC1
    (prev_smulRightW1pL_ofTestFunctionₗ_ae_eq v φ) AL hAL]
  -- The pointwise bound `‖φ' v + φ A v‖² ≤ 2 φ'² + 2 ε² φ²`.
  have hpt (s : ℝ) : ‖deriv (fun s ↦ φ s • v) s + A s (φ s • v)‖ ^ 2 ≤
      2 * deriv φ s ^ 2 + 2 * ε ^ 2 * φ s ^ 2 := by
    rw [hderiv, map_smul]
    have h1 : ‖deriv φ s • v‖ = |deriv φ s| := by simp [norm_smul, hv]
    have h2 : ‖φ s • A s v‖ ≤ |φ s| * ε := by
      rw [norm_smul, Real.norm_eq_abs]
      by_cases hs : s ∈ tsupport φ
      · exact mul_le_mul_of_nonneg_left (hε s hs) (abs_nonneg _)
      · simp [image_eq_zero_of_notMem_tsupport hs]
    have h3 := (norm_add_le _ _).trans (add_le_add h1.le h2)
    calc _ ≤ (|deriv φ s| + |φ s| * ε) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h3 2
      _ ≤ 2 * |deriv φ s| ^ 2 + 2 * (|φ s| * ε) ^ 2 := by
        nlinarith [sq_nonneg (|deriv φ s| - |φ s| * ε)]
      _ = _ := by rw [sq_abs, mul_pow, sq_abs]; ring
  calc _ ≤ ∫ s, (2 * deriv φ s ^ 2 + 2 * ε ^ 2 * φ s ^ 2) :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _)
          ((hdint.const_mul 2).add (hint.const_mul _)) (Eventually.of_forall hpt)
    _ = _ := by
        simp only [integral_add (hdint.const_mul 2) (hint.const_mul _), integral_const_mul]

/-- **Escaping approximate kernels.** If for every `ε > 0` the nonzero vector `v` satisfies
`‖A s v‖ ≤ ε` on the intervals `closedBall (c n) (n + 2)` for all large `n`, and these intervals
eventually leave every bounded set, then `D_A` is not Fredholm. -/
private theorem not_isFredholm_trajectoryOperator_of_forall_mem_closedBall
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {v : E} (hv : v ≠ 0)
    (c : ℕ → ℝ) (hfar : ∀ R, ∀ᶠ n in atTop, ∀ s ∈ closedBall (c n) (n + 2), R < |s|)
    (hsmall : ∀ ε > 0, ∀ᶠ n in atTop, ∀ s ∈ closedBall (c n) (n + 2), ‖A s v‖ ≤ ε) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  -- Reduce to a unit vector.
  wlog hv1 : ‖v‖ = 1 generalizing v
  · have hv' : 0 < ‖v‖ := norm_pos_iff.2 hv
    refine this (v := ‖v‖⁻¹ • v) (smul_ne_zero (inv_ne_zero hv'.ne') hv) (fun ε hε ↦ ?_) ?_
    · filter_upwards [hsmall (ε * ‖v‖) (by positivity)] with n hn s hs
      rw [map_smul, norm_smul, norm_inv, norm_norm, inv_mul_le_iff₀ hv', mul_comm]
      exact hn s hs
    · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hv'.ne']
  intro hT
  obtain ⟨C, hC⟩ := exists_forall_contDiff_plateau
  have hC' (n : ℕ) : ∃ ψ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ tsupport ψ ⊆ closedBall (c n) (n + 2) ∧
      2 * (n + 1) ≤ ∫ s, ψ s ^ 2 ∧ ∫ s, deriv ψ s ^ 2 ≤ C := by
    simpa only [add_assoc, one_add_one_eq_two] using hC (c n) (r := n + 1) (by positivity)
  choose ψ hψ hψt hI hJ using hC'
  -- The paths `uₙ = ψₙ v` of `W^{1,2}(ℝ, E)`.
  let φ (n : ℕ) : 𝓓((⊤ : Opens ℝ), ℝ) :=
    ⟨ψ n, hψ n, (isCompact_closedBall _ _).of_isClosed_subset (isClosed_tsupport _) (hψt n),
      by simp⟩
  let u (n : ℕ) := smulRightW1pL v (W1p.ofTestFunctionₗ volume ⊤ 2 (φ n))
  have hzero (n : ℕ) {s : ℝ} (hs : s ∉ closedBall (c n) (n + 2)) : ψ n s = 0 :=
    image_eq_zero_of_notMem_tsupport fun h ↦ hs (hψt n h)
  have hIpos (n : ℕ) : 0 < ∫ s, ψ n s ^ 2 := lt_of_lt_of_le (by positivity) (hI n)
  have hprev (n : ℕ) : ‖prev _ (u n)‖ ^ 2 = ∫ s, ψ n s ^ 2 :=
    (norm_sq_smulRightW1pL_ofTestFunctionₗ hv1 (φ n)).1
  have hnorm (n : ℕ) : ‖u n‖ ^ 2 = (∫ s, ψ n s ^ 2) + ∫ s, deriv (ψ n) s ^ 2 :=
    (norm_sq_smulRightW1pL_ofTestFunctionₗ hv1 (φ n)).2
  have hTu (n : ℕ) {ε : ℝ} (hn : ∀ s ∈ closedBall (c n) (n + 2), ‖A s v‖ ≤ ε) :
      ‖trajectoryOperator (p := 2) AL (u n)‖ ^ 2 ≤
        2 * (∫ s, deriv (ψ n) s ^ 2) + 2 * ε ^ 2 * ∫ s, ψ n s ^ 2 :=
    norm_trajectoryOperator_smulRightW1pL_ofTestFunctionₗ_sq_le AL hAL hv1 (φ n)
      fun s hs ↦ hn s (hψt n hs)
  -- Normalize: `xₙ = uₙ / ‖uₙ‖_{L²}`.
  let x (n : ℕ) := (√(∫ s, ψ n s ^ 2))⁻¹ • u n
  have hscale (n : ℕ) : (√(∫ s, ψ n s ^ 2))⁻¹ ^ 2 * (∫ s, ψ n s ^ 2) = 1 := by
    rw [inv_pow, Real.sq_sqrt (hIpos n).le, inv_mul_cancel₀ (hIpos n).ne']
  have hxprev (n : ℕ) : ‖prev _ (x n)‖ = 1 := by
    have h : ‖prev _ (x n)‖ ^ 2 * (∫ s, ψ n s ^ 2) = ‖prev _ (u n)‖ ^ 2 := by
      simp only [x, prev_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [mul_right_comm, hscale, one_mul]
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1
      (mul_right_cancel₀ (hIpos n).ne' (h.trans ((hprev n).trans (one_mul _).symm)))
  have hC0 : 0 ≤ C := (integral_nonneg fun _ ↦ sq_nonneg _).trans (hJ 0)
  have hbdd : Bornology.IsBounded (range x) := by
    refine isBounded_iff_forall_norm_le.2 ⟨1 + C, ?_⟩
    rintro _ ⟨n, rfl⟩
    have h : ‖x n‖ ^ 2 * (∫ s, ψ n s ^ 2) = (∫ s, ψ n s ^ 2) + ∫ s, deriv (ψ n) s ^ 2 := by
      rw [← hnorm]
      simp only [x, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [mul_right_comm, hscale, one_mul]
    have h1 : ‖x n‖ ^ 2 ≤ 1 + C := by
      refine le_of_mul_le_mul_right ?_ (hIpos n)
      nlinarith [hI n, hJ n, mul_le_mul_of_nonneg_left (hI n) hC0]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    nlinarith
  -- `D_A xₙ → 0`.
  have hTx : Tendsto (fun n ↦ trajectoryOperator (p := 2) AL (x n)) atTop (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun δ hδ ↦ ?_
    filter_upwards [hsmall (δ / 2) (by positivity),
      tendsto_natCast_atTop_atTop.eventually_gt_atTop (2 * C / δ ^ 2)] with n hn hnC
    rw [dist_zero_right]
    refine (pow_lt_pow_iff_left₀ (norm_nonneg _) hδ.le two_ne_zero).1 ?_
    have h : ‖trajectoryOperator (p := 2) AL (x n)‖ ^ 2 * (∫ s, ψ n s ^ 2) =
        ‖trajectoryOperator (p := 2) AL (u n)‖ ^ 2 := by
      simp only [x, map_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
      rw [mul_right_comm, hscale, one_mul]
    have hT2 := hTu n hn
    rw [div_lt_iff₀ (by positivity)] at hnC
    refine lt_of_mul_lt_mul_right ?_ (hIpos n).le
    nlinarith [hJ n, mul_le_mul_of_nonneg_left (hI n) (sq_nonneg δ)]
  -- A Fredholm operator would give a convergent subsequence.
  obtain ⟨y, φ', hφ', hy⟩ := ContinuousLinearMap.tendsto_subseq_of_isBounded
    hT.isClosed_range hT.finite_ker hT.closedComplemented_ker hbdd hTx
  have hprevy : Tendsto (fun k ↦ prev _ (x (φ' k))) atTop (𝓝 (prev _ y)) := by
    simpa [Function.comp_def] using ((prevL _).continuous.tendsto y).comp hy
  have hnorm1 : ‖prev _ y‖ = 1 :=
    tendsto_nhds_unique ((continuous_norm.tendsto _).comp hprevy) (by
      simp only [Function.comp_def, hxprev]
      exact tendsto_const_nhds)
  -- Its limit vanishes almost everywhere, since the supports escape to infinity.
  have hrep : ∀ᵐ s ∂volume.restrict ((⊤ : Opens ℝ) : Set ℝ),
      ∀ n, prev _ (x n) s = (√(∫ s, ψ n s ^ 2))⁻¹ • ψ n s • v :=
    ae_all_iff.2 fun n ↦ by
      filter_upwards [Lp.coeFn_smul (√(∫ s, ψ n s ^ 2))⁻¹ (prev _ (u n)),
        prev_smulRightW1pL_ofTestFunctionₗ_ae_eq (p := 2) v (φ n)] with s h1 h2
      simp only [x, prev_smul, h1, Pi.smul_apply]
      exact congrArg _ h2
  obtain ⟨ns, hns, hae⟩ := (tendstoInMeasure_of_tendsto_Lp hprevy).exists_seq_tendsto_ae
  have hy0 : ⇑(prev _ y) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] 0 := by
    filter_upwards [hae, hrep] with s hs hr
    refine tendsto_nhds_unique hs (tendsto_const_nhds.congr' ?_)
    filter_upwards [((hφ'.comp hns).tendsto_atTop).eventually (hfar |s|)] with i hi
    rw [hr, hzero (φ' (ns i)) fun h ↦ (hi s h).false]
    simp
  rw [(Lp.eq_zero_iff_ae_eq_zero).2 hy0, norm_zero] at hnorm1
  exact zero_ne_one hnorm1

/-- **A degenerate limit at `+∞` destroys the Fredholm property.** If `A s v → 0` as `s → +∞` for
some nonzero vector `v`, then the trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)` is not Fredholm. The coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atTop
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {v : E} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atTop (𝓝 0)) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  refine not_isFredholm_trajectoryOperator_of_forall_mem_closedBall AL hAL hv
    (fun n ↦ 2 * n + 4) (fun R ↦ ?_) fun ε hε ↦ ?_
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop R] with n hn s hs
    rw [Real.closedBall_eq_Icc] at hs
    rw [abs_of_pos (by linarith [hs.1])]
    linarith [hs.1]
  · obtain ⟨S, hS⟩ := eventually_atTop.1 (hAv.eventually (closedBall_mem_nhds 0 hε))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop S] with n hn s hs
    rw [Real.closedBall_eq_Icc] at hs
    exact mem_closedBall_zero_iff.1 (hS s (by linarith [hs.1]))

/-- **A degenerate limit at `-∞` destroys the Fredholm property.** If `A s v → 0` as `s → -∞` for
some nonzero vector `v`, then the trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to
`L²(ℝ, E)` is not Fredholm. The coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atBot
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {v : E} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atBot (𝓝 0)) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  refine not_isFredholm_trajectoryOperator_of_forall_mem_closedBall AL hAL hv
    (fun n ↦ -(2 * n + 4)) (fun R ↦ ?_) fun ε hε ↦ ?_
  · filter_upwards [tendsto_natCast_atTop_atTop.eventually_gt_atTop R] with n hn s hs
    rw [Real.closedBall_eq_Icc] at hs
    rw [abs_of_neg (by linarith [hs.2])]
    linarith [hs.2]
  · obtain ⟨S, hS⟩ := eventually_atBot.1 (hAv.eventually (closedBall_mem_nhds 0 hε))
    filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (-S)] with n hn s hs
    rw [Real.closedBall_eq_Icc] at hs
    exact mem_closedBall_zero_iff.1 (hS s (by linarith [hs.2]))

/-- **A noninjective limit at `+∞` destroys the Fredholm property.** If `A` converges at `+∞` to
an operator which is not injective, then the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aplus : E →L[ℝ] E}
    (htop : Tendsto A atTop (𝓝 Aplus)) (hinj : ¬ Function.Injective Aplus) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨v, hAv, hv⟩ : ∃ v : E, _ ∧ v ≠ 0 := by simpa [injective_iff_map_eq_zero] using hinj
  refine not_isFredholm_trajectoryOperator_of_tendsto_atTop AL hAL hv ?_
  simpa [Function.comp_def, hAv] using
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto Aplus).comp htop

/-- **A noninjective limit at `-∞` destroys the Fredholm property.** If `A` converges at `-∞` to
an operator which is not injective, then the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atBot
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aminus : E →L[ℝ] E}
    (hbot : Tendsto A atBot (𝓝 Aminus)) (hinj : ¬ Function.Injective Aminus) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨v, hAv, hv⟩ : ∃ v : E, _ ∧ v ≠ 0 := by simpa [injective_iff_map_eq_zero] using hinj
  refine not_isFredholm_trajectoryOperator_of_tendsto_atBot AL hAL hv ?_
  simpa [Function.comp_def, hAv] using
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto Aminus).comp hbot

end Complete

/-- **The trajectory operator is Fredholm exactly for invertible limits.** For a `C¹` family of
symmetric operators on a finite-dimensional real inner product space, with limits `A±` at `±∞`
and derivative tending to zero at both ends, the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is Fredholm if and only if both limits are injective, that is,
invertible. The coefficient of the operator is any `L∞` class `AL` of `A`. -/
theorem isFredholm_trajectoryOperator_iff [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    {A : ℝ → E →L[ℝ] E} (hA : ContDiff ℝ 1 A) (hsym : ∀ s, (A s).toLinearMap.IsSymmetric)
    {Aminus Aplus : E →L[ℝ] E}
    (hbot : Tendsto A atBot (𝓝 Aminus)) (htop : Tendsto A atTop (𝓝 Aplus))
    (hdbot : Tendsto (deriv A) atBot (𝓝 0)) (hdtop : Tendsto (deriv A) atTop (𝓝 0))
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    (trajectoryOperator (p := 2) AL).IsFredholm ↔
      Function.Injective Aminus ∧ Function.Injective Aplus := by
  refine ⟨fun h ↦ ⟨by_contra fun hm ↦
    not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atBot AL hAL hbot hm h,
    by_contra fun hp ↦
    not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop AL hAL htop hp h⟩,
    fun ⟨hm, hp⟩ ↦ ?_⟩
  -- On a finite-dimensional space an injective operator is bounded below.
  have hbelow {T : E →L[ℝ] E} (hT : Function.Injective T) : ∃ c > 0, ∀ v, c * ‖v‖ ≤ ‖T v‖ := by
    obtain ⟨K, -, hK⟩ := (T : E →ₗ[ℝ] E).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hT)
    exact antilipschitzWith_iff_exists_mul_le_norm.1 ⟨K, hK⟩
  obtain ⟨cm, hcm, hcm'⟩ := hbelow hm
  obtain ⟨cp, hcp, hcp'⟩ := hbelow hp
  exact isFredholm_trajectoryOperator hA hsym (lt_min hcm hcp)
    (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg v)).trans (hcm' v))
    (fun v ↦ (mul_le_mul_of_nonneg_right (min_le_right _ _) (norm_nonneg v)).trans (hcp' v))
    hbot htop hdbot hdtop AL hAL

end TauCeti.WeakDerivStep
