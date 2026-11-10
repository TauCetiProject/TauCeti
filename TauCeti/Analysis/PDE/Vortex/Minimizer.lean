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
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.W1p
import TauCeti.MeasureTheory.Function.Lp.IntegralFunctional
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The minimizer of Taubes's functional on `H¹(ℂ)`

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

The minimizer is unique. The Dirichlet energy `‖∇u‖₂² / 2` is a quadratic form, the potential is
the integral of the convex function `h (exp (2t) - 1 - 2t)` and the linear term is linear, so at
the midpoint `m` of `u` and `v` the parallelogram law gives

`2 I(m) + ‖∇(u - v)‖₂² / 4 ≤ I(u) + I(v)`

(`TauCeti.Vortex.sobolevReducedFunctional_midpoint_add_add_le`). At a minimizer `u` this becomes
the quadratic growth bound `I(u) + ‖∇(v - u)‖₂² / 4 ≤ I(v)` for every `v`
(`TauCeti.Vortex.sobolevReducedFunctional_add_le_of_forall_le`). Two minimizers therefore have
the same weak gradient, so they differ by a constant, which vanishes because both are square
integrable on the plane (`TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le`,
`TauCeti.Vortex.existsUnique_forall_sobolevReducedFunctional_le`). The solution of the reduced
equation obtained by minimization is thus determined by `P` alone.

Since `I(0) = 0`, the minimum is at most `0`; in particular the potential of a minimizer is
integrable. The weak Euler–Lagrange equation of the minimizer is in
`TauCeti.Analysis.PDE.Vortex.EulerLagrange`; its regularity is not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4. The functional is strictly convex there, which gives uniqueness.
-/

public section

noncomputable section

namespace TauCeti.Vortex

open MeasureTheory Set TopologicalSpace
open scoped ENNReal

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
  have hpot := (lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P _).comp
    (WeakSpace.map (W1p.valueL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous
  have hdir := lowerSemicontinuous_lintegral_norm_sq_comp_toWeakSpace_symm.comp
    (WeakSpace.map (W1p.gradientL (mu := (volume : Measure ℂ)) (Omega := ⊤) (p := 2))).continuous
  simp only [Function.comp_def, hval, hgrad] at hpot hdir
  simp only [Opens.coe_top, Measure.restrict_univ] at hpot
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

/-! ### Uniqueness of the minimizer -/

/-- Taubes's functional on `H¹(ℂ)` never takes the value `⊥`. -/
theorem sobolevReducedFunctional_ne_bot (P : Polynomial ℂ) (u : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u ≠ ⊥ := by
  by_cases hu : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  · rw [sobolevReducedFunctional_eq_coe hu]
    exact EReal.coe_ne_bot _
  · rw [sobolevReducedFunctional_eq_top hu]
    exact top_ne_bot

/-- Midpoint convexity of `t ↦ exp (2t) - 1 - 2t`. -/
private theorem exp_two_mul_midpoint_sub_le (a b : ℝ) :
    Real.exp (2 * ((a + b) / 2)) - 1 - 2 * ((a + b) / 2) ≤
      ((Real.exp (2 * a) - 1 - 2 * a) + (Real.exp (2 * b) - 1 - 2 * b)) / 2 := by
  have hab : Real.exp (2 * ((a + b) / 2)) = Real.exp a * Real.exp b := by
    rw [← Real.exp_add]
    ring_nf
  have ha : Real.exp (2 * a) = Real.exp a ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  have hb : Real.exp (2 * b) = Real.exp b ^ 2 := by
    rw [← Real.exp_nat_mul]
    ring_nf
  rw [hab, ha, hb]
  nlinarith [sq_nonneg (Real.exp a - Real.exp b)]

/-- The value of the midpoint of two elements of `H¹(ℂ)` is almost everywhere the average of
their values. -/
private theorem value_midpoint_ae (u v : W1p (volume : Measure ℂ) ⊤ 2) :
    ∀ᵐ z, W1p.value (midpoint ℝ u v) z = (W1p.value u z + W1p.value v z) / 2 := by
  have hs := W1p.value_smul_ae (⅟2 : ℝ) (u + v)
  have ha := W1p.value_add_ae u v
  simp only [Opens.coe_top, Measure.restrict_univ] at hs ha
  filter_upwards [hs, ha] with z hzs hza
  rw [midpoint_eq_smul_add, hzs, Pi.smul_apply, hza, Pi.add_apply, smul_eq_mul, invOf_eq_inv]
  ring

/-- The squared norm of the weak gradient of a midpoint, by the parallelogram law. -/
private theorem norm_gradient_midpoint_sq (u v : W1p (volume : Measure ℂ) ⊤ 2) :
    ‖W1p.gradient (midpoint ℝ u v)‖ ^ 2 + ‖W1p.gradient (u - v)‖ ^ 2 / 4 =
      (‖W1p.gradient u‖ ^ 2 + ‖W1p.gradient v‖ ^ 2) / 2 := by
  have hm : W1p.gradient (midpoint ℝ u v) = (⅟2 : ℝ) • (W1p.gradient u + W1p.gradient v) := by
    rw [midpoint_eq_smul_add, ← W1p.gradientL_apply, map_smul, W1p.gradientL_apply,
      W1p.gradient_add]
  have hpar := parallelogram_law_with_norm ℝ (W1p.gradient u) (W1p.gradient v)
  rw [hm, norm_smul, W1p.gradient_sub, invOf_eq_inv, Real.norm_of_nonneg (by norm_num)]
  nlinarith [hpar]

/-- **Midpoint convexity of Taubes's functional.** For `u, v ∈ H¹(ℂ)` with midpoint `m`,
`2 I(m) + ‖∇(u - v)‖₂² / 4 ≤ I(u) + I(v)`: the Dirichlet energy is uniformly convex in the weak
gradient, the potential is convex and the linear term is linear. -/
theorem sobolevReducedFunctional_midpoint_add_add_le {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    (u v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P (midpoint ℝ u v) + sobolevReducedFunctional P (midpoint ℝ u v) +
        ((‖W1p.gradient (u - v)‖ ^ 2 / 4 : ℝ) : EReal) ≤
      sobolevReducedFunctional P u + sobolevReducedFunctional P v := by
  set h : ℂ → ℝ := fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) with h_def
  set c : ℂ → ℝ := fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
    (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8 with c_def
  have hh (z : ℂ) : 0 ≤ h z := by positivity
  -- If one of the two potentials is not integrable, the right-hand side is `⊤`.
  by_cases hu : Integrable fun z ↦ h z * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)
  swap
  · rw [sobolevReducedFunctional_eq_top hu, EReal.top_add_of_ne_bot
      (sobolevReducedFunctional_ne_bot P v)]
    exact le_top
  by_cases hv : Integrable fun z ↦ h z * (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)
  swap
  · rw [sobolevReducedFunctional_eq_top hv, EReal.add_top_of_ne_bot
      (sobolevReducedFunctional_ne_bot P u)]
    exact le_top
  -- Pointwise convexity bounds the potential of the midpoint by the average of the potentials.
  have hpot : ∀ᵐ z, h z * (Real.exp (2 * W1p.value (midpoint ℝ u v) z) - 1 -
      2 * W1p.value (midpoint ℝ u v) z) ≤
      (h z * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z) +
        h z * (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z)) / 2 := by
    filter_upwards [value_midpoint_ae u v] with z hz
    rw [hz, ← mul_add, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left (exp_two_mul_midpoint_sub_le _ _) (hh z)
  have hmid : Integrable fun z ↦ h z * (Real.exp (2 * W1p.value (midpoint ℝ u v) z) - 1 -
      2 * W1p.value (midpoint ℝ u v) z) := by
    refine Integrable.mono' ((hu.add hv).div_const 2) ?_ ?_
    · have hΦ : Continuous fun t : ℝ ↦ Real.exp (2 * t) - 1 - 2 * t := by fun_prop
      exact (by fun_prop (disch := intro z; positivity) : Continuous h).aestronglyMeasurable.mul
        (hΦ.comp_aestronglyMeasurable (W1p.memLp_value _).aestronglyMeasurable)
    · filter_upwards [hpot] with z hz
      rw [Real.norm_of_nonneg (mul_nonneg (hh z) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _))]
      exact hz
  -- The linear term is linear in the value.
  have hc := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  have hcu : Integrable fun z ↦ c z * W1p.value u z := hc.integrable_mul (W1p.memLp_value u)
  have hcv : Integrable fun z ↦ c z * W1p.value v z := hc.integrable_mul (W1p.memLp_value v)
  have hlin : 2 * ∫ z, c z * W1p.value (midpoint ℝ u v) z =
      (∫ z, c z * W1p.value u z) + ∫ z, c z * W1p.value v z := by
    rw [← integral_add hcu hcv, ← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [value_midpoint_ae u v] with z hz
    rw [hz]
    ring
  have hpot' : 2 * ∫ z, h z * (Real.exp (2 * W1p.value (midpoint ℝ u v) z) - 1 -
      2 * W1p.value (midpoint ℝ u v) z) ≤
      (∫ z, h z * (Real.exp (2 * W1p.value u z) - 1 - 2 * W1p.value u z)) +
        ∫ z, h z * (Real.exp (2 * W1p.value v z) - 1 - 2 * W1p.value v z) := by
    rw [← integral_add hu hv, ← integral_const_mul]
    refine integral_mono_ae (hmid.const_mul 2) (hu.add hv) ?_
    filter_upwards [hpot] with z hz
    linarith
  have hgrad := norm_gradient_midpoint_sq u v
  rw [sobolevReducedFunctional_eq_coe hu, sobolevReducedFunctional_eq_coe hv,
    sobolevReducedFunctional_eq_coe hmid, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_add,
    EReal.coe_le_coe_iff]
  linarith

/-- The minimum of Taubes's functional is a real number: it lies between `⊥` and `I(0) = 0`. -/
private theorem exists_coe_eq_of_forall_le {P : Polynomial ℂ} {u : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w) :
    ∃ a : ℝ, sobolevReducedFunctional P u = a :=
  ⟨(sobolevReducedFunctional P u).toReal, (EReal.coe_toReal
    (((hu 0).trans_eq sobolevReducedFunctional_zero).trans_lt EReal.zero_lt_top).ne
    (sobolevReducedFunctional_ne_bot P u)).symm⟩

/-- **Quadratic growth of Taubes's functional at its minimizer.** If `u` minimizes Taubes's
functional on `H¹(ℂ)`, then `I(u) + ‖∇(v - u)‖₂² / 4 ≤ I(v)` for every `v ∈ H¹(ℂ)`. -/
theorem sobolevReducedFunctional_add_le_of_forall_le {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    {u : W1p (volume : Measure ℂ) ⊤ 2} (hu : ∀ w, sobolevReducedFunctional P u ≤
      sobolevReducedFunctional P w) (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P u + ((‖W1p.gradient (v - u)‖ ^ 2 / 4 : ℝ) : EReal) ≤
      sobolevReducedFunctional P v := by
  obtain ⟨a, ha⟩ := exists_coe_eq_of_forall_le hu
  have hmid := sobolevReducedFunctional_midpoint_add_add_le hm u v
  have hle := hu (midpoint ℝ u v)
  rw [← norm_neg, ← W1p.gradient_neg, neg_sub] at hmid
  induction hv : sobolevReducedFunctional P v using EReal.rec with
  | bot => exact absurd hv (sobolevReducedFunctional_ne_bot P v)
  | top => exact le_top
  | coe b =>
    rw [ha] at hle hmid ⊢
    rw [hv] at hmid
    induction hm' : sobolevReducedFunctional P (midpoint ℝ u v) using EReal.rec with
    | bot => exact absurd hm' (sobolevReducedFunctional_ne_bot P _)
    | top =>
      rw [hm', EReal.top_add_top, EReal.top_add_of_ne_bot (EReal.coe_ne_bot _)] at hmid
      exact absurd (top_le_iff.mp hmid) (EReal.coe_ne_top _)
    | coe c =>
      rw [hm'] at hle hmid
      norm_cast at hle hmid ⊢
      linarith

/-- **Uniqueness of the minimizer of Taubes's functional.** Two minimizers of Taubes's functional
on `H¹(ℂ)` are equal. -/
theorem eq_of_forall_sobolevReducedFunctional_le {P : Polynomial ℂ} (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    (hv : ∀ w, sobolevReducedFunctional P v ≤ sobolevReducedFunctional P w) : u = v := by
  -- The weak gradient of `v - u` vanishes.
  have hgrad : W1p.gradient (v - u) = 0 := by
    have h := (sobolevReducedFunctional_add_le_of_forall_le hm hu v).trans (hv u)
    obtain ⟨a, ha⟩ := exists_coe_eq_of_forall_le hu
    rw [ha, ← EReal.coe_add, EReal.coe_le_coe_iff] at h
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp (by
      nlinarith [sq_nonneg ‖W1p.gradient (v - u)‖]))
  -- So `v - u` is almost everywhere constant, and a square integrable constant on `ℂ` is `0`.
  obtain ⟨c, hc⟩ := W1p.exists_value_ae_eq_const_of_gradient_eq_zero
    (by simpa using isPreconnected_univ) hgrad
  simp only [Opens.coe_top, Measure.restrict_univ] at hc
  have hconst : MemLp (fun _ : ℂ ↦ c) 2 := (W1p.memLp_value (v - u)).ae_eq hc
  have hc0 : c = 0 := by
    rcases (memLp_const_iff two_ne_zero ENNReal.ofNat_ne_top).mp hconst with h | h
    · exact h
    · exact absurd h (by simp [measure_univ_of_isAddLeftInvariant])
  refine (W1p.ext_value ?_).symm
  rw [← sub_eq_zero, ← W1p.valueL_apply, ← W1p.valueL_apply, ← map_sub, W1p.valueL_apply]
  refine Lp.eq_zero_iff_ae_eq_zero.mpr ?_
  simp only [Opens.coe_top, Measure.restrict_univ]
  filter_upwards [hc] with z hz
  simpa [hc0] using hz

/-- **Existence and uniqueness of the minimizer of Taubes's functional.** For a complex polynomial
`P` of degree at least one, Taubes's functional has exactly one minimizer on `H¹(ℂ)`. -/
theorem existsUnique_forall_sobolevReducedFunctional_le {P : Polynomial ℂ}
    (hm : 0 < P.natDegree) :
    ∃! u : W1p (volume : Measure ℂ) ⊤ 2,
      ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v := by
  obtain ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  exact ⟨u, hu, fun v hv ↦ eq_of_forall_sobolevReducedFunctional_le hm hv hu⟩

end TauCeti.Vortex
