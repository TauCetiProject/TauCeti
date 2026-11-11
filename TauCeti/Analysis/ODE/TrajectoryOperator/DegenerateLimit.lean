/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.Degenerate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# Nonhyperbolic limits of trajectory operators

If the coefficient `A` of the trajectory operator `D_A u = u' + A u` converges at `+∞` or at `-∞`
to an operator `B` with a purely imaginary eigenvalue, then `D_A` is not Fredholm. Over the reals
a purely imaginary eigenvalue `± i ω` of `B` is a pair of vectors `v, w`, not both zero, with
`B v = -ω • w` and `B w = ω • v`; the case `ω = 0` is a nonzero kernel. Such a pair gives the
bounded solution `e(s) = cos (ω s) • v + sin (ω s) • w` of `e' + B e = 0`, which never vanishes,
and `e' + A e = (A - B) e` tends to `0` at that end. This is the approximate solution required by
the non-Fredholm criterion of `TauCeti.Analysis.ODE.TrajectoryOperator.Degenerate`.

## Main declarations

* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop`
  and `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atBot`:
  a limit with a nonzero kernel.
* `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_apply_eq_neg_smul_of_tendsto_atTop`
  and
  `TauCeti.WeakDerivStep.not_isFredholm_trajectoryOperator_of_apply_eq_neg_smul_of_tendsto_atBot`:
  a limit with a purely imaginary eigenvalue.
-/

public section

open MeasureTheory TopologicalSpace Set Filter
open scoped ENNReal Topology

namespace TauCeti.WeakDerivStep

section Complete

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {A : ℝ → E →L[ℝ] E}

/-- **A noninjective limit at `+∞` destroys the Fredholm property.** If `A` converges at `+∞` to
an operator which is not injective, then the trajectory operator `D_A u = u' + A u` from
`W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_not_injective_of_tendsto_atTop
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aplus : E →L[ℝ] E}
    (htop : Tendsto A atTop (𝓝 Aplus)) (hinj : ¬ Function.Injective Aplus) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨v, hAv, hv⟩ : ∃ v : E, _ ∧ v ≠ 0 := by simpa [injective_iff_map_eq_zero] using hinj
  refine not_isFredholm_trajectoryOperator_of_tendsto_atTop hv ?_ AL hAL
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
  refine not_isFredholm_trajectoryOperator_of_tendsto_atBot hv ?_ AL hAL
  simpa [Function.comp_def, hAv] using
    ((ContinuousLinearMap.apply ℝ E v).continuous.tendsto Aminus).comp hbot

omit [CompleteSpace E] in
/-- A pair `v, w`, not both zero, with `B v = -ω • w` and `B w = ω • v` gives a `C¹` solution `e` of
`e' = -B e`, bounded with bounded derivative and bounded away from `0`. For `ω = 0` it is constant;
otherwise it is `e(s) = cos (ω s) • v + sin (ω s) • w`, a periodic path which never vanishes. -/
private theorem exists_contDiff_deriv_eq_neg_apply {B : E →L[ℝ] E} {ω : ℝ} {v w : E}
    (hv : B v = -ω • w) (hw : B w = ω • v) (hvw : ¬ (v = 0 ∧ w = 0)) :
    ∃ (e : ℝ → E) (m M : ℝ), ContDiff ℝ 1 e ∧ 0 < m ∧ (∀ s, m ≤ ‖e s‖) ∧
      (∀ s, ‖e s‖ ≤ M) ∧ (∀ s, ‖deriv e s‖ ≤ M) ∧ ∀ s, deriv e s = -B (e s) := by
  rcases eq_or_ne ω 0 with rfl | hω
  · -- A nonzero kernel vector is a constant solution.
    obtain ⟨u, hu, hBu⟩ : ∃ u : E, u ≠ 0 ∧ B u = 0 := by
      by_cases h : v = 0
      · exact ⟨w, fun hw0 ↦ hvw ⟨h, hw0⟩, by simpa using hw⟩
      · exact ⟨v, h, by simpa using hv⟩
    exact ⟨fun _ ↦ u, ‖u‖, ‖u‖, contDiff_const, norm_pos_iff.2 hu, fun _ ↦ le_rfl,
      fun _ ↦ le_rfl, fun _ ↦ by simp, fun _ ↦ by simp [hBu]⟩
  set e : ℝ → E := fun s ↦ Real.cos (ω * s) • v + Real.sin (ω * s) • w with he_def
  have hderiv (s : ℝ) : HasDerivAt e (-B (e s)) s := by
    have h := (((hasDerivAt_id s).const_mul ω).cos.smul_const v).add
      (((hasDerivAt_id s).const_mul ω).sin.smul_const w)
    simp only [id, mul_one] at h
    convert h using 1
    simp only [he_def, map_add, map_smul, hv, hw]
    module
  -- The path never vanishes: at a zero, applying `B` would force `v = w = 0`.
  have hne (s : ℝ) : e s ≠ 0 := by
    intro h0
    set c := Real.cos (ω * s)
    set d := Real.sin (ω * s)
    have h1 : ω • (d • v - c • w) = 0 := by
      have := congrArg B h0
      simp only [he_def, map_add, map_smul, hv, hw, map_zero] at this
      rw [← this]
      module
    have h2 : d • v - c • w = 0 := (smul_eq_zero.1 h1).resolve_left hω
    have hcd : c ^ 2 + d ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq _
    refine hvw ⟨?_, ?_⟩
    · calc v = c • e s + d • (d • v - c • w) := by
            simp only [he_def]
            linear_combination (norm := module) -(hcd • v)
        _ = 0 := by rw [h0, h2, smul_zero, smul_zero, add_zero]
    · calc w = d • e s - c • (d • v - c • w) := by
            simp only [he_def]
            linear_combination (norm := module) -(hcd • w)
        _ = 0 := by rw [h0, h2, smul_zero, smul_zero, sub_zero]
  have hcont : Continuous e := by fun_prop
  -- A periodic nonvanishing path is bounded away from `0`.
  have hper : Function.Periodic e (ω⁻¹ * (2 * Real.pi)) := fun s ↦ by
    simp only [he_def, Real.cos_periodic.const_mul ω s, Real.sin_periodic.const_mul ω s]
  have hperT : Function.Periodic e |ω⁻¹ * (2 * Real.pi)| := by
    rcases abs_choice (ω⁻¹ * (2 * Real.pi)) with h | h <;> rw [h]
    exacts [hper, hper.neg]
  have hT : 0 < |ω⁻¹ * (2 * Real.pi)| := abs_pos.2 (by positivity)
  obtain ⟨s₀, -, hs₀⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hT.le)
    (hcont.norm.continuousOn (s := Icc 0 |ω⁻¹ * (2 * Real.pi)|))
  refine ⟨e, ‖e s₀‖, (1 + ‖B‖) * (‖v‖ + ‖w‖), by fun_prop, norm_pos_iff.2 (hne s₀),
    fun s ↦ ?_, fun s ↦ ?_, fun s ↦ ?_, fun s ↦ (hderiv s).deriv⟩
  · obtain ⟨y, hy, hey⟩ := hperT.exists_mem_Ico₀ hT s
    rw [hey]
    exact hs₀ (Ico_subset_Icc_self hy)
  · have h : ‖e s‖ ≤ ‖v‖ + ‖w‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
        exact mul_le_of_le_one_left (norm_nonneg _) (by simp [Real.abs_cos_le_one,
          Real.abs_sin_le_one])
    nlinarith [norm_nonneg B, norm_nonneg v, norm_nonneg w]
  · rw [(hderiv s).deriv, norm_neg]
    have h : ‖e s‖ ≤ ‖v‖ + ‖w‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_smul] <;>
        exact mul_le_of_le_one_left (norm_nonneg _) (by simp [Real.abs_cos_le_one,
          Real.abs_sin_le_one])
    calc ‖B (e s)‖ ≤ ‖B‖ * ‖e s‖ := B.le_opNorm _
      _ ≤ ‖B‖ * (‖v‖ + ‖w‖) := by gcongr
      _ ≤ _ := by nlinarith [norm_nonneg v, norm_nonneg w]

omit [CompleteSpace E] in
/-- Along a bounded solution `e` of `e' = -B e`, the defect `e' + A e = (A - B) e` tends to `0`
wherever `A` tends to `B`. -/
private theorem tendsto_deriv_add_apply {l : Filter ℝ} {B : E →L[ℝ] E} (hAB : Tendsto A l (𝓝 B))
    {e : ℝ → E} {M : ℝ} (hup : ∀ s, ‖e s‖ ≤ M) (hd : ∀ s, deriv e s = -B (e s)) :
    Tendsto (fun s ↦ deriv e s + A s (e s)) l (𝓝 0) := by
  refine squeeze_zero_norm (a := fun s ↦ ‖A s - B‖ * M) (fun s ↦ ?_) ?_
  · rw [hd, neg_add_eq_sub, ← sub_apply]
    exact ((A s - B).le_opNorm _).trans (by gcongr; exact hup s)
  · simpa using (tendsto_iff_norm_sub_tendsto_zero.1 hAB).mul_const M

/-- **A purely imaginary eigenvalue of the limit at `+∞` destroys the Fredholm property.** If `A`
converges at `+∞` to an operator `A⁺` with `A⁺ v = -ω • w` and `A⁺ w = ω • v` for some `ω` and
some `v, w` not both zero, so that `A⁺` has the eigenvalues `± i ω` on the imaginary axis, then the
trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_apply_eq_neg_smul_of_tendsto_atTop
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aplus : E →L[ℝ] E}
    (htop : Tendsto A atTop (𝓝 Aplus)) {ω : ℝ} {v w : E} (hv : Aplus v = -ω • w)
    (hw : Aplus w = ω • v) (hvw : ¬ (v = 0 ∧ w = 0)) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨e, m, M, he, hm, hlow, hup, hdup, hd⟩ := exists_contDiff_deriv_eq_neg_apply hv hw hvw
  exact not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atTop he hm hlow hup hdup
    (tendsto_deriv_add_apply htop hup hd) AL hAL

/-- **A purely imaginary eigenvalue of the limit at `-∞` destroys the Fredholm property.** If `A`
converges at `-∞` to an operator `A⁻` with `A⁻ v = -ω • w` and `A⁻ w = ω • v` for some `ω` and
some `v, w` not both zero, so that `A⁻` has the eigenvalues `± i ω` on the imaginary axis, then the
trajectory operator `D_A u = u' + A u` from `W^{1,2}(ℝ, E)` to `L²(ℝ, E)` is not Fredholm. -/
theorem not_isFredholm_trajectoryOperator_of_apply_eq_neg_smul_of_tendsto_atBot
    (AL : Lp (E →L[ℝ] E) ∞ (volume.restrict ((⊤ : Opens ℝ) : Set ℝ)))
    (hAL : AL =ᵐ[volume.restrict ((⊤ : Opens ℝ) : Set ℝ)] A) {Aminus : E →L[ℝ] E}
    (hbot : Tendsto A atBot (𝓝 Aminus)) {ω : ℝ} {v w : E} (hv : Aminus v = -ω • w)
    (hw : Aminus w = ω • v) (hvw : ¬ (v = 0 ∧ w = 0)) :
    ¬ (trajectoryOperator (p := 2) AL).IsFredholm := by
  obtain ⟨e, m, M, he, hm, hlow, hup, hdup, hd⟩ := exists_contDiff_deriv_eq_neg_apply hv hw hvw
  exact not_isFredholm_trajectoryOperator_of_tendsto_deriv_add_atBot he hm hlow hup hdup
    (tendsto_deriv_add_apply hbot hup hd) AL hAL

end Complete

end TauCeti.WeakDerivStep
