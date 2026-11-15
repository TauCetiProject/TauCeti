/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.Reduced.Functional
public import Mathlib.Topology.Algebra.Module.Spaces.WeakDual
public import Mathlib.Topology.Semicontinuity.Defs
import Mathlib.Analysis.InnerProductSpace.Convex
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.MeasureTheory.Function.Lp.Integral.Functional
import TauCeti.MeasureTheory.Function.Lp.Norm

/-!
# The minimizer of Taubes's functional on `H¹(ℂ)`

Let `P` be a complex polynomial of degree `m ≥ 1`. A plane vortex with zero divisor `P` is
obtained from a solution `w` of the reduced equation `Δw = (exp (2w) h - 1) / 8 + g`, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`, and Taubes obtains `w` as the minimizer
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
integrable.

The minimizer is unique. For `φ(t) = exp (2t) - 1 - 2t` the midpoint defect is explicit,
`(φ(a) + φ(b)) / 2 - φ((a + b) / 2) = (exp a - exp b)² / 2`, so where `I(u)` and `I(v)` are finite

`2 I((u + v) / 2) + (1 / 16) ∫ h (exp u - exp v)² ≤ I(u) + I(v)`

(`TauCeti.Vortex.two_mul_sobolevReducedFunctional_midpoint_add_le`). For two minimizers `u` and
`v`, both `I(u)` and `I(v)` are at most `I((u + v) / 2)`, so `∫ h (exp u - exp v)² ≤ 0` and
`exp u = exp v` wherever `h > 0`, that is off the finitely many zeros of `P`
(`TauCeti.Vortex.eq_of_forall_sobolevReducedFunctional_le`,
`TauCeti.Vortex.existsUnique_forall_sobolevReducedFunctional_le`). The minimizer is therefore a
function of `P`, `TauCeti.Vortex.reducedMinimizer`, characterized by
`TauCeti.Vortex.eq_reducedMinimizer_iff`; it depends on `P` only through `I`
(`TauCeti.Vortex.reducedMinimizer_eq_of_forall_sobolevReducedFunctional_eq`). Its laws under
translations, rotations and constant changes of the line frame are in
`TauCeti.Analysis.PDE.Vortex.Equivariance`.

The weak Euler–Lagrange equation of the minimizer is in
`TauCeti.Analysis.PDE.Vortex.EulerLagrange`; its regularity is not treated here.

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

/-! ### Convexity and uniqueness -/

variable {P : Polynomial ℂ}

/-- **The potential at a midpoint.** Let `a` and `b` be real functions on the plane whose
potentials `h φ(a)` and `h φ(b)`, with `h = ‖P‖² / (1 + ‖P‖²)` and `φ(t) = exp (2t) - 1 - 2t`, are
integrable. Then the defect `D = h (exp a - exp b)²` and the potential of the pointwise midpoint
`(a + b) / 2` are integrable, and the latter integrates to `(∫ h φ(a) + ∫ h φ(b) - ∫ D) / 2`:
pointwise, `(φ(a) + φ(b)) / 2 - φ((a + b) / 2) = (exp a - exp b)² / 2`. -/
private theorem integral_potential_midpoint {a b : ℂ → ℝ} (ha : AEStronglyMeasurable a)
    (hb : AEStronglyMeasurable b)
    (hpa : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * a z) - 1 - 2 * a z))
    (hpb : Integrable fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * b z) - 1 - 2 * b z)) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (a z) - Real.exp (b z)) ^ 2) ∧
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * ((a z + b z) / 2)) - 1 - 2 * ((a z + b z) / 2))) ∧
      ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
          (Real.exp (2 * ((a z + b z) / 2)) - 1 - 2 * ((a z + b z) / 2)) =
        ((∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * a z) - 1 - 2 * a z)) +
          (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * b z) - 1 - 2 * b z)) -
          ∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
            (Real.exp (a z) - Real.exp (b z)) ^ 2) / 2 := by
  set D : ℂ → ℝ := fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
    (Real.exp (a z) - Real.exp (b z)) ^ 2 with hD
  -- `D = h φ(a) + h φ(b) - 2 h φ((a + b) / 2)`, from `exp (2t) = (exp t)²`.
  have hDeq (z : ℂ) : D z =
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * a z) - 1 - 2 * a z) +
      ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * b z) - 1 - 2 * b z) -
      2 * (‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * ((a z + b z) / 2)) - 1 - 2 * ((a z + b z) / 2))) := by
    have hab : Real.exp (2 * ((a z + b z) / 2)) = Real.exp (a z) * Real.exp (b z) := by
      rw [← Real.exp_add]; ring_nf
    simp only [hD, hab, show ∀ t, Real.exp (2 * t) = Real.exp t ^ 2 from fun t ↦ by
      rw [← Real.exp_nat_mul]; ring_nf]
    ring
  have hD0 : 0 ≤ D := fun z ↦ by positivity
  have hmid0 (z : ℂ) : 0 ≤ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (2 * ((a z + b z) / 2)) - 1 - 2 * ((a z + b z) / 2)) :=
    mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)
  have hDm : AEStronglyMeasurable D := by
    have hhc : Continuous fun z : ℂ ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
      fun_prop (disch := intro z; positivity)
    have hF : Continuous fun p : ℝ × ℝ ↦ (Real.exp p.1 - Real.exp p.2) ^ 2 := by fun_prop
    exact (hhc.aestronglyMeasurable.mul (hF.comp_aestronglyMeasurable (ha.prodMk hb))).congr
      (ae_of_all _ fun z ↦ by simp only [hD, Pi.mul_apply])
  -- `0 ≤ D ≤ h φ(a) + h φ(b)`.
  have hDi : Integrable D := by
    refine (hpa.add hpb).mono' hDm (ae_of_all _ fun z ↦ ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (hD0 z), hDeq z]
    simp only [Pi.add_apply]
    linarith [hmid0 z]
  refine ⟨hDi, (((hpa.add hpb).sub hDi).div_const 2).congr (ae_of_all _ fun z ↦ ?_), ?_⟩
  · simp only [Pi.add_apply, Pi.sub_apply, hDeq z]
    ring
  have e := integral_sub (hpa.add hpb) hDi
  simp only [Pi.add_apply] at e
  rw [← integral_add hpa hpb, ← e, ← integral_div]
  exact integral_congr_ae (ae_of_all _ fun z ↦ by simp only [hDeq z]; ring)

/-- **Midpoint convexity of Taubes's functional.** For a complex polynomial `P` of degree at least
one and `u, v ∈ H¹(ℂ)` at which Taubes's functional `I` is finite, the defect
`h (exp u - exp v)²`, `h = ‖P‖² / (1 + ‖P‖²)`, is integrable and

`2 I((u + v) / 2) + (1 / 16) ∫ h (exp u - exp v)² ≤ I(u) + I(v)`. -/
theorem two_mul_sobolevReducedFunctional_midpoint_add_le (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2} (hu : sobolevReducedFunctional P u ≠ ⊤)
    (hv : sobolevReducedFunctional P v ≠ ⊤) :
    Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (W1p.value u z) - Real.exp (W1p.value v z)) ^ 2) ∧
      2 * sobolevReducedFunctional P ((1 / 2 : ℝ) • (u + v)) +
          (((∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
            (Real.exp (W1p.value u z) - Real.exp (W1p.value v z)) ^ 2) / 16 : ℝ) : EReal) ≤
        sobolevReducedFunctional P u + sobolevReducedFunctional P v := by
  have hpu := sobolevReducedFunctional_ne_top_iff.1 hu
  have hpv := sobolevReducedFunctional_ne_top_iff.1 hv
  have hua := W1p.memLp_value u
  have hva := W1p.memLp_value v
  obtain ⟨hDi, hpm, hpot⟩ := integral_potential_midpoint hua.aestronglyMeasurable
    hva.aestronglyMeasurable hpu hpv
  refine ⟨hDi, ?_⟩
  -- The value of the midpoint is the pointwise midpoint of the values.
  have hval : (W1p.value ((1 / 2 : ℝ) • (u + v)) : ℂ → ℝ) =ᵐ[volume]
      fun z ↦ (W1p.value u z + W1p.value v z) / 2 := by
    have h1 := W1p.value_add_ae u v
    have h2 := W1p.value_smul_ae (1 / 2 : ℝ) (u + v)
    simp only [Opens.coe_top, Measure.restrict_univ] at h1 h2
    filter_upwards [h1, h2] with z hz1 hz2
    rw [hz2, Pi.smul_apply, hz1, Pi.add_apply, smul_eq_mul]
    ring
  have hpmeq := hval.mono fun z (hz : W1p.value ((1 / 2 : ℝ) • (u + v)) z = _) ↦
    congrArg (fun t ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * t) - 1 - 2 * t)) hz
  rw [← integral_congr_ae hpmeq] at hpot
  -- The linear term of the midpoint is the mean of those of `u` and `v`.
  have hcL := memLp_two_mul_norm_derivative_eval_sq_div_sub_inv_div_eight hm
  have hcu : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z := hcL.integrable_mul hua
  have hcv : Integrable fun z ↦ (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z := hcL.integrable_mul hva
  have hlin : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value ((1 / 2 : ℝ) • (u + v)) z =
      ((∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value u z) +
      ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
        (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * W1p.value v z) / 2 := by
    rw [← integral_add hcu hcv, ← integral_div]
    exact integral_congr_ae (hval.mono fun z hz ↦ by simp only [hz]; ring)
  -- The Dirichlet energy of the midpoint is at most the mean of those of `u` and `v`.
  have hnorm : ‖W1p.gradient ((1 / 2 : ℝ) • (u + v))‖ ^ 2 ≤
      (‖W1p.gradient u‖ ^ 2 + ‖W1p.gradient v‖ ^ 2) / 2 := by
    rw [← W1p.gradientL_apply, map_smul, map_add, W1p.gradientL_apply, W1p.gradientL_apply,
      norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have htri := norm_add_le (W1p.gradient u) (W1p.gradient v)
    nlinarith [sq_nonneg (‖W1p.gradient u‖ - ‖W1p.gradient v‖),
      norm_nonneg (W1p.gradient u + W1p.gradient v)]
  have h2 : ((2 : ℝ) : EReal) = 2 := rfl
  rw [sobolevReducedFunctional_eq_coe hpu, sobolevReducedFunctional_eq_coe hpv,
    sobolevReducedFunctional_eq_coe ((integrable_congr hpmeq).2 hpm), hpot, hlin, ← h2,
    ← EReal.coe_mul, ← EReal.coe_add, ← EReal.coe_add, EReal.coe_le_coe_iff]
  linarith

/-- **Uniqueness of the minimizer of Taubes's functional.** For a complex polynomial `P` of degree
at least one, two minimizers of `TauCeti.Vortex.sobolevReducedFunctional P` on `H¹(ℂ)` are equal. -/
theorem eq_of_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree)
    {u v : W1p (volume : Measure ℂ) ⊤ 2}
    (hu : ∀ w, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P w)
    (hv : ∀ w, sobolevReducedFunctional P v ≤ sobolevReducedFunctional P w) : u = v := by
  -- Compare both minimizers with their midpoint, using midpoint convexity. Both have finite
  -- functional, at most `I(0) = 0`.
  have hfin {w : W1p (volume : Measure ℂ) ⊤ 2}
      (hw : ∀ w', sobolevReducedFunctional P w ≤ sobolevReducedFunctional P w') :
      sobolevReducedFunctional P w ≠ ⊤ :=
    ((hw 0).trans_lt (by rw [sobolevReducedFunctional_zero]; exact EReal.zero_lt_top)).ne
  have hpu := sobolevReducedFunctional_ne_top_iff.1 (hfin hu)
  have hpv := sobolevReducedFunctional_ne_top_iff.1 (hfin hv)
  obtain ⟨hDi, hle⟩ := two_mul_sobolevReducedFunctional_midpoint_add_le hm (hfin hu) (hfin hv)
  -- The midpoint has finite functional, since `2 I((u + v) / 2)` is at most `I(u) + I(v)`.
  have hmtop : sobolevReducedFunctional P ((1 / 2 : ℝ) • (u + v)) ≠ ⊤ := by
    intro htop
    rw [htop, sobolevReducedFunctional_eq_coe hpu, sobolevReducedFunctional_eq_coe hpv,
      EReal.mul_top_of_pos (by norm_num), EReal.top_add_coe, ← EReal.coe_add, top_le_iff] at hle
    exact EReal.coe_ne_top _ hle
  have hpm := sobolevReducedFunctional_ne_top_iff.1 hmtop
  -- Both values are at most the value at the midpoint, so the defect integrates to zero.
  have hum := hu ((1 / 2 : ℝ) • (u + v))
  have hvm := hv ((1 / 2 : ℝ) • (u + v))
  rw [sobolevReducedFunctional_eq_coe hpu, sobolevReducedFunctional_eq_coe hpm,
    EReal.coe_le_coe_iff] at hum
  rw [sobolevReducedFunctional_eq_coe hpv, sobolevReducedFunctional_eq_coe hpm,
    EReal.coe_le_coe_iff] at hvm
  have h2 : ((2 : ℝ) : EReal) = 2 := rfl
  rw [sobolevReducedFunctional_eq_coe hpu, sobolevReducedFunctional_eq_coe hpv,
    sobolevReducedFunctional_eq_coe hpm, ← h2, ← EReal.coe_mul, ← EReal.coe_add,
    ← EReal.coe_add, EReal.coe_le_coe_iff] at hle
  have hD0 : 0 ≤ fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
      (Real.exp (W1p.value u z) - Real.exp (W1p.value v z)) ^ 2 := fun z ↦ by positivity
  have hDz := (integral_eq_zero_iff_of_nonneg hD0 hDi).1
    (le_antisymm (by linarith) (integral_nonneg hD0))
  -- Off the finitely many zeros of `P` the weight is positive, so the values agree.
  have hroots : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ {z | P.IsRoot z} :=
    measure_eq_zero_iff_ae_notMem.1 ((Polynomial.finite_setOfPred_isRoot
      (Polynomial.ne_zero_of_natDegree_gt hm)).measure_zero _)
  have hae : (W1p.value u : ℂ → ℝ) =ᵐ[volume] W1p.value v := by
    filter_upwards [hDz, hroots] with z hz hzr
    have hpos : 0 < ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
      have : 0 < ‖P.eval z‖ := norm_pos_iff.2 hzr
      positivity
    have hsq : (Real.exp (W1p.value u z) - Real.exp (W1p.value v z)) ^ 2 = 0 :=
      (mul_eq_zero.1 hz).resolve_left hpos.ne'
    exact Real.exp_injective (sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hsq))
  refine W1p.ext_value (Lp.ext ?_)
  simpa only [Opens.coe_top, Measure.restrict_univ] using hae

/-- **Existence and uniqueness of the minimizer of Taubes's functional.** For a complex polynomial
`P` of degree at least one, `TauCeti.Vortex.sobolevReducedFunctional P` has exactly one minimizer
on `H¹(ℂ)`. -/
theorem existsUnique_forall_sobolevReducedFunctional_le (hm : 0 < P.natDegree) :
    ∃! u : W1p (volume : Measure ℂ) ⊤ 2,
      ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v :=
  let ⟨u, hu⟩ := exists_forall_sobolevReducedFunctional_le hm
  ⟨u, hu, fun _ hv ↦ eq_of_forall_sobolevReducedFunctional_le hm hv hu⟩

/-! ### The minimizer -/

variable (P) in
/-- **The minimizer of Taubes's functional** `TauCeti.Vortex.sobolevReducedFunctional P` on
`H¹(ℂ)`. When `P` has degree at least one, it is the unique minimizer
(`TauCeti.Vortex.eq_reducedMinimizer_iff`); its smooth representative corrects the background
amplitude of `P` to the amplitude of a vortex with zero divisor `P`
(`TauCeti.Vortex.exists_contDiff_ae_eq_and_laplacian_eq_of_forall_sobolevReducedFunctional_le`).
For constant `P` it is an arbitrary element of `H¹(ℂ)`. -/
def reducedMinimizer : W1p (volume : Measure ℂ) ⊤ 2 :=
  Classical.epsilon fun u ↦ ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v

/-- The minimizer minimizes Taubes's functional. -/
theorem forall_sobolevReducedFunctional_reducedMinimizer_le (hm : 0 < P.natDegree)
    (v : W1p (volume : Measure ℂ) ⊤ 2) :
    sobolevReducedFunctional P (reducedMinimizer P) ≤ sobolevReducedFunctional P v :=
  Classical.epsilon_spec (exists_forall_sobolevReducedFunctional_le hm) v

/-- An element of `H¹(ℂ)` is the minimizer of Taubes's functional exactly when it minimizes it. -/
theorem eq_reducedMinimizer_iff (hm : 0 < P.natDegree) {u : W1p (volume : Measure ℂ) ⊤ 2} :
    u = reducedMinimizer P ↔ ∀ v, sobolevReducedFunctional P u ≤ sobolevReducedFunctional P v :=
  ⟨fun h ↦ h ▸ forall_sobolevReducedFunctional_reducedMinimizer_le hm,
    fun hu ↦ eq_of_forall_sobolevReducedFunctional_le hm hu
      (forall_sobolevReducedFunctional_reducedMinimizer_le hm)⟩

/-- The minimizer depends on `P` only through Taubes's functional: polynomials with the same
functional have the same minimizer. -/
theorem reducedMinimizer_eq_of_forall_sobolevReducedFunctional_eq {Q : Polynomial ℂ}
    (h : ∀ u, sobolevReducedFunctional Q u = sobolevReducedFunctional P u) :
    reducedMinimizer Q = reducedMinimizer P := by
  simp only [reducedMinimizer, h]

end TauCeti.Vortex
