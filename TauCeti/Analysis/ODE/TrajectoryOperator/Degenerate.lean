/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Fredholm.Basic
public import TauCeti.Analysis.ODE.TrajectoryOperator
import TauCeti.Analysis.Calculus.BumpFunction.Escaping
import TauCeti.Analysis.Normed.Operator.ClosedRange
import TauCeti.Analysis.ODE.TrajectoryOperator.Kernel
import TauCeti.MeasureTheory.Function.LocallyIntegrable
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The trajectory operator with a degenerate limit is not Fredholm

Let `A : ℝ → End(F)` be an essentially bounded family of operators on a real Banach space `F`.
Suppose that some `C¹` path `e : ℝ → F`, bounded with bounded derivative and bounded away from
`0`, solves `e' + A e = 0` approximately at `+∞` (or at `-∞`): `e'(s) + A(s) e(s) → 0`. Then the
trajectory operator

`D_A u = u' + A u : W^{1,2}(ℝ, F) → L²(ℝ, F)`

is not Fredholm. Two cases matter. A constant `e = v` with `A(s) v → 0`, for instance because `A`
has a limit `A⁺` with `A⁺ v = 0`, shows that a limit with a nonzero kernel destroys the Fredholm
property. A rotating `e(s) = cos (ω s) • v + sin (ω s) • w`, where `A⁺ v = -ω • w` and
`A⁺ w = ω • v`, does the same for a limit with a purely imaginary eigenvalue
(`TauCeti.Analysis.ODE.TrajectoryOperator.DegenerateLimit`). Together with
`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_of_hasLyapunovForm`, this shows that for a
continuous family of operators on a finite-dimensional inner product space with limits `A±`,
`D_A` is Fredholm exactly when both limits are hyperbolic
(`TauCeti.WeakDerivStep.isFredholm_trajectoryOperator_iff_forall_eq_zero`, in
`TauCeti.Analysis.ODE.EnergyEstimate.Lyapunov`).

The proof constructs an escaping approximate kernel. Take smooth compactly supported profiles
`φₙ` on `ℝ` with `∫ φₙ² = 1`, `∫ φₙ'² → 0` and pairwise disjoint supports, escaping so far out
that `‖e'(s) + A(s) e(s)‖ ≤ 1 / (n + 1)` on the support of `φₙ`
(`TauCeti.exists_seq_contDiff_hasCompactSupport_escaping_atTop`), and put `uₙ = φₙ • e`. Then
`‖uₙ‖_{W^{1,2}}` is bounded, `‖D_A uₙ‖_{L²} → 0`, and `‖uₙ - uₘ‖²_{L²} ≥ 2 m²` for `n ≠ m`, where
`m > 0` bounds `‖e‖` below.
A Fredholm operator has closed range and a finite-dimensional complemented kernel, so a bounded
sequence on which it tends to zero has a convergent subsequence
(`ContinuousLinearMap.tendsto_subseq_of_cauchySeq_comp`), so its terms cannot stay a fixed distance
apart (`ContinuousLinearMap.not_cauchySeq_comp_of_le_dist`). The terms of `uₙ` do.

## Main declarations

* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atBot`: an
  approximate solution `e` of `e' + A e = 0` at `+∞` or at `-∞`, bounded and bounded away from
  `0`, shows that `D_A` is not Fredholm.
* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atTop` and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_tendsto_atBot`: the constant case,
  `A(s) v → 0` at `+∞` or at `-∞` for some `v ≠ 0`.

## References

* J. Robbin and D. Salamon, *The spectral flow and the Maslov index*, Bull. London Math. Soc.
  **27** (1995), 1--33, Theorem A (the operator `d/ds + A(s)` is Fredholm exactly when the limits
  are invertible).
* M. Schwarz, *Morse Homology*, Chapter 2 (linearized trajectory operators).
-/

public section

noncomputable section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

/-! ### The escaping approximate kernel -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {e : ℝ → F} {φ ψ : ℝ → ℝ}

private theorem contDiff_profile_smul (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (he : ContDiff ℝ 1 e) :
    ContDiff ℝ 1 fun s ↦ φ s • e s :=
  (hφ.of_le (by exact_mod_cast le_top)).smul he

private theorem deriv_profile_smul (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (he : ContDiff ℝ 1 e) (s : ℝ) :
    deriv (fun s ↦ φ s • e s) s = φ s • deriv e s + deriv φ s • e s :=
  deriv_smul ((hφ.differentiable (by simp)) s) (he.differentiable one_ne_zero s)

variable [CompleteSpace F] {A : ℝ → F →L[ℝ] F}

variable {u u' : WeakDerivStep volume ⊤ 2
  (ContinuousLinearMap.id ℝ (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))}

/-- Paths `φ • e` and `ψ • e` along `e` for profiles with unit `L²` norm and disjoint supports are
at distance at least `√2 m` in `L²`, where `m` bounds `‖e‖` below. -/
private theorem two_mul_sq_le_norm_prev_sub_sq (he : Continuous e) {m : ℝ} (hm : 0 ≤ m)
    (hlow : ∀ s, m ≤ ‖e s‖) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ1 : ∫ s, φ s ^ 2 = 1) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψc : HasCompactSupport ψ)
    (hψ1 : ∫ s, ψ s ^ 2 = 1) (hdisj : ∀ s, φ s * ψ s = 0)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ φ s • e s)
    (hu' : ⇑(prev _ u') =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ ψ s • e s) :
    2 * m ^ 2 ≤ ‖prev _ u - prev _ u'‖ ^ 2 := by
  rw [← Lp.integral_norm_sq_eq_norm_sq]
  have hae : (fun s ↦ ‖(prev _ u - prev _ u') s‖ ^ 2)
      =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)]
        fun s ↦ φ s ^ 2 * ‖e s‖ ^ 2 + ψ s ^ 2 * ‖e s‖ ^ 2 := by
    filter_upwards [Lp.coeFn_sub (prev _ u) (prev _ u'), hu, hu'] with s hs hs1 hs2
    rw [hs, Pi.sub_apply, hs1, hs2, ← sub_smul, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    linear_combination (-2 * ‖e s‖ ^ 2) * hdisj s
  have hg : Continuous fun s ↦ ‖e s‖ ^ 2 := by fun_prop
  have hφsq : Continuous fun s ↦ φ s ^ 2 := hφ.continuous.pow 2
  have hψsq : Continuous fun s ↦ ψ s ^ 2 := hψ.continuous.pow 2
  have hφsqc : HasCompactSupport fun s ↦ φ s ^ 2 := hφc.comp_left (g := (· ^ 2)) (by simp)
  have hψsqc : HasCompactSupport fun s ↦ ψ s ^ 2 := hψc.comp_left (g := (· ^ 2)) (by simp)
  have hint := hφ.continuous.integrable_sq_of_hasCompactSupport (μ := volume) hφc
  have hintψ := hψ.continuous.integrable_sq_of_hasCompactSupport (μ := volume) hψc
  rw [integral_congr_ae hae, Opens.coe_top, Measure.restrict_univ]
  calc 2 * m ^ 2 = ∫ s, (φ s ^ 2 * m ^ 2 + ψ s ^ 2 * m ^ 2) := by
        rw [integral_add (hint.mul_const _) (hintψ.mul_const _), integral_mul_const,
          integral_mul_const, hφ1, hψ1]
        ring
    _ ≤ _ := integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
        ((hφsq.integrable_mul_of_continuousOn hφsqc (subset_univ _) hg.continuousOn).add
          (hψsq.integrable_mul_of_continuousOn hψsqc (subset_univ _) hg.continuousOn))
        (.of_forall fun s ↦ by
          have := pow_le_pow_left₀ hm (hlow s) 2
          simp only [Pi.add_apply]
          gcongr)

/-- The squared `W^{1,2}` norm of a path `φ • e` along `e`, for a profile `φ` with unit `L²` norm,
is bounded in terms of a common bound `M` on `‖e‖` and `‖e'‖`. -/
private theorem norm_sq_le_of_prev_ae_eq (he : ContDiff ℝ 1 e) {M : ℝ} (hup : ∀ s, ‖e s‖ ≤ M)
    (hdup : ∀ s, ‖deriv e s‖ ≤ M) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ1 : ∫ s, φ s ^ 2 = 1)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ φ s • e s) :
    ‖u‖ ^ 2 ≤ 3 * M ^ 2 + 2 * M ^ 2 * ∫ s, deriv φ s ^ 2 := by
  rw [norm_sq_eq_norm_prev_sq_add_norm_weakFDeriv_sq, norm_prev_sq_eq_integral hu,
    norm_weakFDeriv_sq_eq_integral (contDiff_profile_smul hφ he) hu]
  have hint := hφ.continuous.integrable_sq_of_hasCompactSupport (μ := volume) hφc
  have hintd := hφ.integrable_deriv_sq_of_hasCompactSupport (μ := volume) hφc (by simp)
  have h₁ : ∫ s, ‖φ s • e s‖ ^ 2 ≤ M ^ 2 := by
    calc _ ≤ ∫ s, M ^ 2 * φ s ^ 2 :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
            (hint.const_mul _) (.of_forall fun s ↦ by
              dsimp only
              rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
              have := pow_le_pow_left₀ (norm_nonneg _) (hup s) 2
              nlinarith [sq_nonneg (φ s)])
      _ = M ^ 2 := by rw [integral_const_mul, hφ1, mul_one]
  have h₂ : ∫ s, ‖deriv (fun s ↦ φ s • e s) s‖ ^ 2 ≤
      2 * M ^ 2 + 2 * M ^ 2 * ∫ s, deriv φ s ^ 2 := by
    calc _ ≤ ∫ s, (2 * M ^ 2 * φ s ^ 2 + 2 * M ^ 2 * deriv φ s ^ 2) :=
          integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
            ((hint.const_mul _).add (hintd.const_mul _)) (.of_forall fun s ↦ by
              rw [deriv_profile_smul hφ he]
              refine ((pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
                add_sq_le).trans ?_
              simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
              have := pow_le_pow_left₀ (norm_nonneg _) (hdup s) 2
              have := pow_le_pow_left₀ (norm_nonneg _) (hup s) 2
              nlinarith [sq_nonneg (φ s), sq_nonneg (deriv φ s)])
      _ = _ := by
          rw [integral_add (hint.const_mul _) (hintd.const_mul _), integral_const_mul,
            integral_const_mul, hφ1, mul_one]
  linarith

/-- `D_A` is small on a path `φ • e` along `e`, for a profile `φ` with unit `L²` norm, where
`‖e' + A e‖ ≤ ε` on the support of `φ`. -/
private theorem norm_trajectoryOperator_sq_le_of_prev_ae_eq (he : ContDiff ℝ 1 e) {M : ℝ}
    (hup : ∀ s, ‖e s‖ ≤ M) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ)
    (hφ1 : ∫ s, φ s ^ 2 = 1) {ε : ℝ} (hA : ∀ s, φ s ≠ 0 → ‖deriv e s + A s (e s)‖ ≤ ε)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A)
    (hu : ⇑(prev _ u) =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] fun s ↦ φ s • e s) :
    ‖trajectoryOperator AL u‖ ^ 2 ≤ 2 * M ^ 2 * (∫ s, deriv φ s ^ 2) + 2 * ε ^ 2 := by
  rw [norm_trajectoryOperator_sq_eq_integral (contDiff_profile_smul hφ he) hu AL hAL]
  have hint := hφ.continuous.integrable_sq_of_hasCompactSupport (μ := volume) hφc
  have hintd := hφ.integrable_deriv_sq_of_hasCompactSupport (μ := volume) hφc (by simp)
  calc _ ≤ ∫ s, (2 * M ^ 2 * deriv φ s ^ 2 + 2 * ε ^ 2 * φ s ^ 2) :=
        integral_mono_of_nonneg (.of_forall fun _ ↦ by positivity)
          ((hintd.const_mul _).add (hint.const_mul _)) (.of_forall fun s ↦ ?_)
    _ = _ := by
        rw [integral_add (hintd.const_mul _) (hint.const_mul _), integral_const_mul,
          integral_const_mul, hφ1, mul_one]
  -- The integrand is `φ' • e + φ • (e' + A e)`, and the second term vanishes off the support.
  have hsplit : deriv (fun s ↦ φ s • e s) s + A s (φ s • e s) =
      deriv φ s • e s + φ s • (deriv e s + A s (e s)) := by
    rw [deriv_profile_smul hφ he, map_smul, smul_add]
    abel
  have hAs : (φ s * ‖deriv e s + A s (e s)‖) ^ 2 ≤ (φ s * ε) ^ 2 := by
    by_cases h0 : φ s = 0
    · simp [h0]
    · rw [mul_pow, mul_pow]
      have h := hA s h0
      gcongr
  rw [hsplit]
  refine ((pow_le_pow_left₀ (norm_nonneg _) (norm_add_le _ _) 2).trans
    add_sq_le).trans ?_
  simp only [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs] at hAs ⊢
  have := pow_le_pow_left₀ (norm_nonneg _) (hup s) 2
  nlinarith [sq_nonneg (deriv φ s)]

/-- **The escaping approximate kernel.** Let `e` be `C¹` with `m ≤ ‖e‖ ≤ M` and `‖e'‖ ≤ M`, where
`m > 0`. Let `φₙ` be smooth compactly supported functions with `∫ φₙ² = 1`, `∫ φₙ'² → 0` and
pairwise disjoint supports, with `‖e'(s) + A(s) e(s)‖ ≤ εₙ` on the support of `φₙ` and `εₙ → 0`.
The paths `uₙ = φₙ • e` are bounded in `W^{1,2}`, satisfy `D_A uₙ → 0` and stay `√2 m` apart in
`L²`, so `D_A` is not Fredholm. -/
private theorem not_isFredholm_trajectoryOperator_of_seq (he : ContDiff ℝ 1 e)
    {m M : ℝ} (hm : 0 < m) (hlow : ∀ s, m ≤ ‖e s‖) (hup : ∀ s, ‖e s‖ ≤ M)
    (hdup : ∀ s, ‖deriv e s‖ ≤ M) {φ : ℕ → ℝ → ℝ} (hφ : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (φ n))
    (hφc : ∀ n, HasCompactSupport (φ n)) (hφ1 : ∀ n, ∫ s, φ n s ^ 2 = 1)
    (hφ' : Tendsto (fun n ↦ ∫ s, deriv (φ n) s ^ 2) atTop (𝓝 0))
    (hdisj : ∀ m n, m ≠ n → ∀ s, φ m s * φ n s = 0) {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hA : ∀ n s, φ n s ≠ 0 → ‖deriv e s + A s (e s)‖ ≤ ε n)
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  intro hF
  choose x hx using fun n : ℕ ↦ exists_prev_ae_eq_of_contDiff_of_hasCompactSupport (p := 2)
    (contDiff_profile_smul (hφ n) he) (hφc n).smul_right
  obtain ⟨B, hB⟩ := hφ'.bddAbove_range
  have hbdd : Bornology.IsBounded (Set.range x) := by
    refine isBounded_iff_forall_norm_le.2
      ⟨3 * M ^ 2 + 2 * M ^ 2 * B + 1, Set.forall_mem_range.2 fun n ↦ ?_⟩
    have h := norm_sq_le_of_prev_ae_eq he hup hdup (hφ n) (hφc n) (hφ1 n) (hx n)
    have h1 : 2 * M ^ 2 * (∫ s, deriv (φ n) s ^ 2) ≤ 2 * M ^ 2 * B :=
      mul_le_mul_of_nonneg_left (hB (Set.mem_range_self n)) (by positivity)
    nlinarith [norm_nonneg (x n), sq_nonneg (‖x n‖ - 1), sq_nonneg M]
  have hTx : Tendsto (trajectoryOperator AL ∘ x) atTop (𝓝 0) := by
    have hbound : Tendsto (fun n ↦ 2 * M ^ 2 * (∫ s, deriv (φ n) s ^ 2) + 2 * ε n ^ 2)
        atTop (𝓝 0) := by
      simpa using (hφ'.const_mul (2 * M ^ 2)).add ((hε.pow 2).const_mul 2)
    have hsq : Tendsto (fun n ↦ ‖trajectoryOperator AL (x n)‖ ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun _ ↦ by positivity) (fun n ↦
        norm_trajectoryOperator_sq_le_of_prev_ae_eq he hup (hφ n) (hφc n) (hφ1 n) (hA n) AL hAL
          (hx n)) hbound
    rw [tendsto_zero_iff_norm_tendsto_zero]
    simpa [Function.comp_def, Real.sqrt_sq (norm_nonneg _)] using
      (Real.continuous_sqrt.tendsto 0).comp hsq
  -- A Fredholm operator would give a convergent subsequence, but distinct terms are `√2 m` apart.
  have hP := (prevL (ContinuousLinearMap.id ℝ
    (Lp F 2 (volume.restrict ((⊤ : Opens ℝ) : Set ℝ))))).continuous
  refine (trajectoryOperator AL).not_cauchySeq_comp_of_le_dist hF.isClosed_range hF.finite_ker
    hF.closedComplemented_ker hP hbdd hm (fun i j hij ↦ ?_) hTx.cauchySeq
  have hsep := two_mul_sq_le_norm_prev_sub_sq he.continuous hm.le hlow (hφ i) (hφc i) (hφ1 i)
    (hφ j) (hφc j) (hφ1 j) (hdisj i j hij) (hx i) (hx j)
  rw [prevL_apply, prevL_apply, dist_eq_norm]
  exact (pow_le_pow_iff_left₀ hm.le (norm_nonneg _) two_ne_zero).1 (by linarith [sq_nonneg m])

/-- **An approximate solution escaping to `+∞` destroys the Fredholm property.** Let `e` be a
`C¹` path with `m ≤ ‖e s‖ ≤ M` and `‖e' s‖ ≤ M` for all `s`, where `m > 0`, which solves
`e' + A e = 0` asymptotically at `+∞`: `e'(s) + A(s) e(s) → 0` as `s → ∞`. Then
`u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atTop (he : ContDiff ℝ 1 e)
    {m M : ℝ} (hm : 0 < m) (hlow : ∀ s, m ≤ ‖e s‖) (hup : ∀ s, ‖e s‖ ≤ M)
    (hdup : ∀ s, ‖deriv e s‖ ≤ M)
    (hAe : Tendsto (fun s ↦ deriv e s + A s (e s)) atTop (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  have hS (n : ℕ) : ∃ S, ∀ s ≥ S, ‖deriv e s + A s (e s)‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atTop.1 ((tendsto_zero_iff_norm_tendsto_zero.1 hAe).eventually
      (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨φ, hφ, hφc, hφ1, hφ', hφS, hdisj⟩ :=
    exists_seq_contDiff_hasCompactSupport_escaping_atTop S
  exact not_isFredholm_trajectoryOperator_of_seq he hm hlow hup hdup hφ hφc hφ1 hφ' hdisj
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n s hs ↦ hS n s (hφS n s hs)) AL hAL

/-- **An approximate solution escaping to `-∞` destroys the Fredholm property.** Let `e` be a
`C¹` path with `m ≤ ‖e s‖ ≤ M` and `‖e' s‖ ≤ M` for all `s`, where `m > 0`, which solves
`e' + A e = 0` asymptotically at `-∞`: `e'(s) + A(s) e(s) → 0` as `s → -∞`. Then
`u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atBot (he : ContDiff ℝ 1 e)
    {m M : ℝ} (hm : 0 < m) (hlow : ∀ s, m ≤ ‖e s‖) (hup : ∀ s, ‖e s‖ ≤ M)
    (hdup : ∀ s, ‖deriv e s‖ ≤ M)
    (hAe : Tendsto (fun s ↦ deriv e s + A s (e s)) atBot (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  have hS (n : ℕ) : ∃ S, ∀ s ≤ S, ‖deriv e s + A s (e s)‖ ≤ 1 / ((n : ℝ) + 1) :=
    eventually_atBot.1 ((tendsto_zero_iff_norm_tendsto_zero.1 hAe).eventually
      (eventually_le_nhds (by positivity)))
  choose S hS using hS
  obtain ⟨φ, hφ, hφc, hφ1, hφ', hφS, hdisj⟩ :=
    exists_seq_contDiff_hasCompactSupport_escaping_atBot S
  exact not_isFredholm_trajectoryOperator_of_seq he hm hlow hup hdup hφ hφc hφ1 hφ' hdisj
    tendsto_one_div_add_atTop_nhds_zero_nat (fun n s hs ↦ hS n s (hφS n s hs)) AL hAL

/-- **The trajectory operator with a degenerate limit at `+∞` is not Fredholm.** If `A(s) v → 0`
as `s → ∞` for some `v ≠ 0`, for instance because `A` tends to an operator `A⁺` with `A⁺ v = 0`,
then `u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atTop {v : F} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atTop (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm :=
  not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atTop (e := fun _ ↦ v) contDiff_const
    (norm_pos_iff.2 hv) (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun _ ↦ by simp)
    (by simpa using hAv) AL hAL

/-- **The trajectory operator with a degenerate limit at `-∞` is not Fredholm.** If `A(s) v → 0`
as `s → -∞` for some `v ≠ 0`, for instance because `A` tends to an operator `A⁻` with `A⁻ v = 0`,
then `u ↦ u' + A u` from `W^{1,2}(ℝ, F)` to `L²(ℝ, F)` is not Fredholm. The coefficient of the
operator is any `L∞` class `AL` of `A`. -/
theorem not_isFredholm_trajectoryOperator_of_tendsto_atBot {v : F} (hv : v ≠ 0)
    (hAv : Tendsto (fun s ↦ A s v) atBot (𝓝 0))
    (AL : Lp (F →L[ℝ] F) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm :=
  not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atBot (e := fun _ ↦ v) contDiff_const
    (norm_pos_iff.2 hv) (fun _ ↦ le_rfl) (fun _ ↦ le_rfl) (fun _ ↦ by simp)
    (by simpa using hAv) AL hAL

end TauCeti.WeakDerivStep
