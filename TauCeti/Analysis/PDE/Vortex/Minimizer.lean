/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# A minimizer of Taubes's functional on `H¹(ℂ)`

Let `P` be a complex polynomial of degree `m ≥ 1`. A plane vortex with zero divisor `P` is
obtained from a solution `w` of the reduced equation `Δw = (exp (2w) h - 1) / 8 + g`, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`, and Taubes obtains `w` as a minimizer
of the functional `I` of `TauCeti.Vortex.sobolevReducedFunctional` on `H¹(ℂ) = W^{1,2}(ℂ)`.

This file carries out the direct method of the calculus of variations:

* `TauCeti.Vortex.lowerSemicontinuous_sobolevReducedFunctional`: `I` is lower semicontinuous for
  the weak topology of `H¹(ℂ)`. The Dirichlet energy and the potential are convex integral
  functionals of the weak gradient and of the value, and the linear term is a continuous linear
  functional.
* `TauCeti.Vortex.exists_forall_sobolevReducedFunctional_le`: `I` attains its minimum on
  `H¹(ℂ)`. Its sublevel sets are bounded
  (`TauCeti.Vortex.exists_norm_le_of_sobolevReducedFunctional_le`), and closed balls of the
  Hilbert space `H¹(ℂ)` are weakly compact.

Since `I(0) = 0`, the minimum is at most `0`; in particular the potential of a minimizer is
integrable. The Euler–Lagrange equation of the minimizer and its regularity are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

/-- The vortex potential `∫⁻ h (exp (2v) - 1 - 2v)` is weakly lower semicontinuous on `L²(ν)` for
every measure `ν` equal to Lebesgue measure. This transports
`TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub` to Lebesgue measure
restricted to the whole plane, the measure of the `L²` spaces of `W^{1,2}(ℂ)`. -/
private theorem lowerSemicontinuous_lintegral_potential (P : Polynomial ℂ) {ν : Measure ℂ}
    (hν : ν = volume) :
    LowerSemicontinuous fun v : WeakSpace ℝ (Lp ℝ 2 ν) ↦
      ∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * ((toWeakSpace ℝ (Lp ℝ 2 ν)).symm v z)) - 1 -
          2 * ((toWeakSpace ℝ (Lp ℝ 2 ν)).symm v z))) := by
  subst hν
  exact lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P

/-- Taubes's functional as the sum of an extended nonnegative energy, the Dirichlet energy and the
potential, and the linear term. -/
private theorem sobolevReducedFunctional_eq_add (P : Polynomial ℂ)
    (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u =
      (((∫⁻ z, ENNReal.ofReal (‖W1p.gradient u z‖ ^ 2) ∂(volume : Measure ℂ).restrict
          ((⊤ : Opens ℂ) : Set ℂ)) / 2 +
        (∫⁻ z, ENNReal.ofReal (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z))) / 16 : ℝ≥0∞) : EReal) +
        ((∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z : ℝ) : EReal) := by
  have hgrad : (∫⁻ z, ENNReal.ofReal (‖W1p.gradient u z‖ ^ 2) ∂(volume : Measure ℂ).restrict
      ((⊤ : Opens ℂ) : Set ℂ)) / 2 =
      ENNReal.ofReal (‖W1p.gradient u‖ ^ 2 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal (W1p.integrable_norm_gradient_sq u)
      (ae_of_all _ fun z ↦ sq_nonneg _), Lp.integral_norm_sq_eq_norm_sq,
      ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  rw [sobolevReducedFunctional_def, EReal.coe_ennreal_add, hgrad, EReal.coe_ennreal_ofReal,
    max_eq_left (by positivity), EReal.coe_add, add_right_comm]

/-- **Weak lower semicontinuity of Taubes's functional.** For a complex polynomial `P` of degree
at least one, the functional `TauCeti.Vortex.sobolevReducedFunctional P` is lower semicontinuous
for the weak topology of `H¹(ℂ) = W^{1,2}(ℂ)`. -/
theorem lowerSemicontinuous_sobolevReducedFunctional {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    LowerSemicontinuous fun u : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) ↦
      sobolevReducedFunctional P ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm u) := by
  set e := (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm
  -- The value and the weak gradient are weakly continuous.
  have hval (u : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)) :
      (toWeakSpace ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)))).symm
        (WeakSpace.map W1p.valueL u) = W1p.value (e u) := by
    rw [← W1p.valueL_apply]
    rfl
  have hgrad (u : WeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)) :
      (toWeakSpace ℝ (Lp ℂ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ)))).symm
        (WeakSpace.map W1p.gradientL u) = W1p.gradient (e u) := by
    rw [← W1p.gradientL_apply]
    rfl
  -- The energy is a sum of two weakly lower semicontinuous convex integrals.
  have hpot := (lowerSemicontinuous_lintegral_potential P (by simp)).comp
    (WeakSpace.map (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous
  have hdir := lowerSemicontinuous_lintegral_norm_sq_comp_toWeakSpace_symm.comp
    (WeakSpace.map (W1p.gradientL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous
  simp only [Function.comp_def, hval, hgrad] at hpot hdir
  have hdiv (c : ℝ≥0∞) (hc : c ≠ 0) : Continuous fun x : ℝ≥0∞ ↦ x / c :=
    ENNReal.continuous_div_const c hc
  have hdiv_mono (c : ℝ≥0∞) : Monotone fun x : ℝ≥0∞ ↦ x / c :=
    fun _ _ h ↦ ENNReal.div_le_div_right h c
  have henergy := continuous_coe_ennreal_ereal.comp_lowerSemicontinuous
    (((hdiv 2 two_ne_zero).comp_lowerSemicontinuous hdir (hdiv_mono 2)).add
      ((hdiv 16 (by norm_num)).comp_lowerSemicontinuous hpot (hdiv_mono 16)))
    fun _ _ h ↦ EReal.coe_ennreal_le_coe_ennreal_iff.mpr h
  -- The linear term is a continuous linear functional of the value.
  have hc := (memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm).restrict
    ((⊤ : Opens ℂ) : Set ℂ)
  set ℓ : StrongDual ℝ (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))) :=
    innerSL ℝ (hc.toLp _)
  have hℓ (v : Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))) :
      ℓ v = ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * v z := by
    have h := integral_congr_ae (hc.coeFn_toLp.mono fun z hz ↦ congrArg (· * v z) hz)
    simp only [Opens.coe_top, Measure.restrict_univ] at h
    rw [← h, innerSL_apply_apply, L2.inner_def]
    simp only [Opens.coe_top, Measure.restrict_univ, RCLike.inner_apply, conj_trivial]
    exact integral_congr_ae (ae_of_all _ fun z ↦ mul_comm _ _)
  have hℓc : Continuous fun v : WeakSpace ℝ
      (Lp ℝ 2 ((volume : Measure ℂ).restrict ((⊤ : Opens ℂ) : Set ℂ))) ↦
      ℓ ((toWeakSpace ℝ _).symm v) :=
    WeakBilin.eval_continuous (topDualPairing ℝ _).flip ℓ
  have hlin := (continuous_coe_real_ereal.comp hℓc).comp
    (WeakSpace.map (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous
  simp only [Function.comp_def, hval, hℓ] at hlin
  have hsum := henergy.add' hlin.lowerSemicontinuous fun _ ↦
    EReal.continuousAt_add (Or.inr (EReal.coe_ne_bot _)) (Or.inl (EReal.coe_ennreal_ne_bot _))
  simp only [Function.comp_def] at hsum
  rw [funext fun u ↦ sobolevReducedFunctional_eq_add P (e u)]
  exact hsum

/-- **Existence of a minimizer of Taubes's functional.** For a complex polynomial `P` of degree
at least one, the functional `TauCeti.Vortex.sobolevReducedFunctional P` attains its minimum on
`H¹(ℂ) = W^{1,2}(ℂ)`. -/
theorem exists_forall_sobolevReducedFunctional_le {P : Polynomial ℂ} (hm : 0 < P.natDegree) :
    ∃ u : W1p (volume : Measure ℂ) ⊤ 2,
      ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
  obtain ⟨R, hR⟩ := exists_norm_le_of_sobolevReducedFunctional_le hm 0
  have hR0 : (0 : W1p (volume : Measure ℂ) ⊤ 2) ∈ Metric.closedBall 0 R := by
    rw [mem_closedBall_zero_iff]
    exact hR 0 (by simp)
  have hK : IsCompact (toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2) '' Metric.closedBall 0 R) :=
    isCompact_toWeakSpace_closedBall surjective_inclusionInDoubleDual_of_uniformConvexSpace 0 R
  obtain ⟨a, -, hmin⟩ := (lowerSemicontinuous_sobolevReducedFunctional hm).lowerSemicontinuousOn
    _ |>.exists_isMinOn ⟨_, mem_image_of_mem _ hR0⟩ hK
  refine ⟨(toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a, fun v ↦ ?_⟩
  by_cases hv : ‖v‖ ≤ R
  · have h := isMinOn_iff.mp hmin _ (mem_image_of_mem _ (mem_closedBall_zero_iff.mpr hv))
    simp only [LinearEquiv.symm_apply_apply] at h
    exact h
  · -- Outside the ball the functional is positive, while the minimum on the ball is at most
    -- its value `0` at the origin.
    have h0 :
        sobolevReducedFunctional P ((toWeakSpace ℝ (W1p (volume : Measure ℂ) ⊤ 2)).symm a) ≤ 0 := by
      have h := isMinOn_iff.mp hmin _ (mem_image_of_mem _ hR0)
      simp only [LinearEquiv.symm_apply_apply, sobolevReducedFunctional_zero] at h
      exact h
    refine h0.trans (le_of_lt (not_le.mp fun hv' ↦ hv (hR v ?_)))
    exact_mod_cast hv'

end TauCeti.Vortex
