/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.TrajectoryOperator.Degenerate
import TauCeti.Analysis.ODE.Linear

/-!
# Nonhyperbolic limits of trajectory operators

If the coefficient `A` of the trajectory operator `D_A u = u' + A u` converges at `+∞` or at `-∞`
to an operator `B` with a purely imaginary eigenvalue, then `D_A` is not Fredholm. Over the reals
a purely imaginary eigenvalue `± i ω` of `B` is a pair of vectors `v, w`, not both zero, with
`B v = -ω • w` and `B w = ω • v`. For `ω ≠ 0` such a pair gives the bounded solution
`e(s) = cos (ω s) • v + sin (ω s) • w` of `e' + B e = 0`, which never vanishes; for `ω = 0` a
nonzero member of the pair is a kernel vector of `B`, a constant solution. In both cases
`e' + A e = (A - B) e` tends to `0` at that end (`TauCeti.exists_contDiff_deriv_eq_neg_apply`
and `TauCeti.tendsto_deriv_add_apply`). This is the approximate solution required by
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
