/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
public import Mathlib.Analysis.LocallyConvex.WeakSpace
public import Mathlib.Topology.Semicontinuity.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Set
import TauCeti.Analysis.SpecialFunctions.Sqrt
import TauCeti.MeasureTheory.Function.Lp.Norm
import TauCeti.MeasureTheory.Integral.Bochner.CauchySchwarz

/-!
# Lower semicontinuity of convex integral functionals on Lp

For a continuous real-valued integrand `Φ`, the extended integral of its positive part is
lower semicontinuous in the norm topology of `Lp`. If `Φ` is convex, it is also lower
semicontinuous in the weak topology. The integral may be taken against any measure absolutely
continuous with respect to the measure defining `Lp`; this includes weighted potentials.

Using an extended nonnegative integral is essential: a nonlinear potential need not be
integrable at every `Lp` function. The proofs use almost-everywhere subsequence convergence,
Fatou's lemma, and the equality of norm and weak closures for convex sets.

In particular the extended integral of the squared norm is weakly lower semicontinuous on `Lp`
(`TauCeti.lowerSemicontinuous_lintegral_norm_sq_comp_toWeakSpace_symm`).

On `L²`, the integral of the modular `√(1 + v²) - 1` over any set is moreover norm continuous
(`TauCeti.continuous_setIntegral_sqrt_one_add_sq_sub_one`). The modular is at most `v² / 2`, and
its local Lipschitz bound with the Cauchy–Schwarz inequality controls differences.
-/

public section

open MeasureTheory Filter Set Topology
open scoped ENNReal

namespace TauCeti

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F]
  {μ ν : Measure α} {p : ℝ≥0∞} {Φ : F → ℝ}

/-- The positive part of a continuous integrand composed with an `Lp` representative is
almost everywhere measurable for any absolutely continuous measure. -/
theorem aemeasurable_ofReal_comp_Lp (hν : ν ≪ μ) (hΦ : Continuous Φ) (u : Lp F p μ) :
    AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (u x))) ν :=
  ((ENNReal.continuous_ofReal.comp hΦ).comp_aestronglyMeasurable
    ((Lp.aestronglyMeasurable u).mono_ac hν)).aemeasurable

/-- The extended integral of the positive part of a continuous integrand is norm lower
semicontinuous on `Lp`. Absolute continuity makes the integral independent of representatives. -/
theorem lowerSemicontinuous_lintegral_ofReal_comp_Lp [Fact (1 ≤ p)]
    (hν : ν ≪ μ) (hΦ : Continuous Φ) :
    LowerSemicontinuous (fun u : Lp F p μ ↦ ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  apply isSeqClosed_iff_isClosed.mp
  intro u v hu huv
  obtain ⟨s, -, hs⟩ := (tendstoInMeasure_of_tendsto_Lp huv).exists_seq_tendsto_ae
  have hsν := hν.ae_le hs
  have hmeas (n : ℕ) : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (u (s n) x))) ν :=
    aemeasurable_ofReal_comp_Lp hν hΦ (u (s n))
  calc
    ∫⁻ x, ENNReal.ofReal (Φ (v x)) ∂ν =
        ∫⁻ x, liminf (fun n ↦ ENNReal.ofReal (Φ (u (s n) x))) atTop ∂ν := by
      apply lintegral_congr_ae
      filter_upwards [hsν] with x hx
      exact ((ENNReal.continuous_ofReal.comp hΦ).continuousAt.tendsto.comp hx).liminf_eq.symm
    _ ≤ liminf (fun n ↦ ∫⁻ x, ENNReal.ofReal (Φ (u (s n) x)) ∂ν) atTop :=
      lintegral_liminf_le' hmeas
    _ ≤ c := liminf_le_of_frequently_le (Frequently.of_forall fun n ↦ hu (s n))

variable [NormedSpace ℝ F]

/-- Sublevels of the extended integral of the positive part of a continuous convex integrand
are convex. No integrability assumption on the integrand is required. -/
theorem convex_setOf_lintegral_ofReal_comp_Lp_le
    (hν : ν ≪ μ) (hcont : Continuous Φ) (hΦ : ConvexOn ℝ univ Φ) (c : ℝ≥0∞) :
    Convex ℝ {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c} := by
  intro u hu v hv a b ha hb hab
  have hmeas (w : Lp F p μ) : AEMeasurable (fun x ↦ ENNReal.ofReal (Φ (w x))) ν :=
    aemeasurable_ofReal_comp_Lp hν hcont w
  have hpoint : ∀ᵐ x ∂ν,
      ENNReal.ofReal (Φ ((a • u + b • v) x)) ≤
        ENNReal.ofReal a * ENNReal.ofReal (Φ (u x)) +
          ENNReal.ofReal b * ENNReal.ofReal (Φ (v x)) := by
    filter_upwards [hν.ae_le (Lp.coeFn_add (a • u) (b • v)),
      hν.ae_le (Lp.coeFn_smul a u), hν.ae_le (Lp.coeFn_smul b v)] with x hx hxu hxv
    simp only [Pi.add_apply, Pi.smul_apply] at hx hxu hxv
    rw [hx, hxu, hxv]
    calc
      ENNReal.ofReal (Φ (a • u x + b • v x)) ≤
          ENNReal.ofReal (a * Φ (u x) + b * Φ (v x)) :=
        ENNReal.ofReal_le_ofReal (hΦ.2 (mem_univ _) (mem_univ _) ha hb hab)
      _ ≤ ENNReal.ofReal (a * Φ (u x)) + ENNReal.ofReal (b * Φ (v x)) :=
        ENNReal.ofReal_add_le
      _ = _ := by rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hb]
  calc
    ∫⁻ x, ENNReal.ofReal (Φ ((a • u + b • v) x)) ∂ν ≤
        ∫⁻ x, ENNReal.ofReal a * ENNReal.ofReal (Φ (u x)) +
          ENNReal.ofReal b * ENNReal.ofReal (Φ (v x)) ∂ν := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal a * (∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν) +
        ENNReal.ofReal b * (∫⁻ x, ENNReal.ofReal (Φ (v x)) ∂ν) := by
      rw [lintegral_add_left' ((hmeas u).const_mul _),
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ENNReal.ofReal a * c + ENNReal.ofReal b * c := by gcongr <;> assumption
    _ = c := by rw [← add_mul, ← ENNReal.ofReal_add ha hb, hab]; simp

/-- A continuous convex potential has weakly lower semicontinuous extended integral on `Lp`.
The value `∞` is allowed, so this applies before the effective domain of the potential has been
identified. The integrating measure can incorporate a nonnegative weight. -/
theorem lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm [Fact (1 ≤ p)]
    (hν : ν ≪ μ) (hΦ : Continuous Φ) (hconv : ConvexOn ℝ univ Φ) :
    LowerSemicontinuous (fun u : WeakSpace ℝ (Lp F p μ) ↦
      ∫⁻ x, ENNReal.ofReal (Φ ((toWeakSpace ℝ (Lp F p μ)).symm u x)) ∂ν) := by
  rw [lowerSemicontinuous_iff_isClosed_preimage]
  intro c
  have hc : IsClosed {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c} :=
    (lowerSemicontinuous_lintegral_ofReal_comp_Lp (p := p) hν hΦ).isClosed_preimage c
  have hcv := convex_setOf_lintegral_ofReal_comp_Lp_le (p := p) hν hΦ hconv c
  have heq := hcv.toWeakSpace_closure ℝ
  rw [hc.closure_eq] at heq
  have hclosed : IsClosed ((toWeakSpace ℝ (Lp F p μ)) ''
      {u : Lp F p μ | ∫⁻ x, ENNReal.ofReal (Φ (u x)) ∂ν ≤ c}) := by
    rw [heq]
    exact isClosed_closure
  rwa [(toWeakSpace ℝ (Lp F p μ)).image_eq_preimage_symm] at hclosed

/-- The extended integral of the squared norm is weakly lower semicontinuous on `Lp`. -/
theorem lowerSemicontinuous_lintegral_norm_sq_comp_toWeakSpace_symm [Fact (1 ≤ p)] :
    LowerSemicontinuous (fun u : WeakSpace ℝ (Lp F p μ) ↦
      ∫⁻ x, ENNReal.ofReal (‖(toWeakSpace ℝ (Lp F p μ)).symm u x‖ ^ 2) ∂μ) :=
  lowerSemicontinuous_lintegral_ofReal_comp_toWeakSpace_symm Measure.AbsolutelyContinuous.rfl
    (by fun_prop) (convexOn_univ_norm.pow (fun x _ ↦ norm_nonneg x) 2)

/-- On `L²`, the integral of the modular `√(1 + v²) - 1` over a set is continuous in `v`. The
modular is at most `v² / 2`, so the integral is finite, and its local Lipschitz bound
`|g(a) - g(b)| ≤ |a - b| (|a| + |b|)` gives `|∫ g(b) - ∫ g(a)| ≤ ‖b - a‖ (‖b‖ + ‖a‖)` by the
Cauchy–Schwarz inequality. -/
theorem continuous_setIntegral_sqrt_one_add_sq_sub_one (t : Set α) :
    Continuous fun v : Lp ℝ 2 ν ↦ ∫ x in t, (√(1 + v x ^ 2) - 1) ∂ν := by
  have hint (v : Lp ℝ 2 ν) : Integrable (fun x ↦ √(1 + v x ^ 2) - 1) ν := by
    refine ((Lp.memLp v).integrable_sq.div_const 2).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (sub_nonneg.mpr (Real.one_le_sqrt_one_add_sq _))]
    exact Real.sqrt_one_add_sq_sub_one_le_sq_div_two _
  -- Cauchy–Schwarz: `∫ ‖f‖ ‖g‖ ≤ ‖f‖₂ ‖g‖₂`.
  have hcs (f g : Lp ℝ 2 ν) : ∫ x, ‖f x‖ * ‖g x‖ ∂ν ≤ ‖f‖ * ‖g‖ := by
    have h := sq_integral_mul_le_integral_sq_mul_integral_sq (Lp.memLp f).norm (Lp.memLp g).norm
    rw [Lp.integral_norm_sq_eq_norm_sq, Lp.integral_norm_sq_eq_norm_sq, ← mul_pow] at h
    exact (abs_le_of_sq_le_sq h (by positivity)).trans' (le_abs_self _)
  have hbound (a b : Lp ℝ 2 ν) :
      dist (∫ x in t, (√(1 + b x ^ 2) - 1) ∂ν) (∫ x in t, (√(1 + a x ^ 2) - 1) ∂ν) ≤
        ‖b - a‖ * ‖b‖ + ‖b - a‖ * ‖a‖ := by
    have hba := (Lp.memLp (b - a)).norm
    have hi1 : Integrable (fun x ↦ ‖(b - a) x‖ * ‖b x‖) ν := hba.integrable_mul (Lp.memLp b).norm
    have hi2 : Integrable (fun x ↦ ‖(b - a) x‖ * ‖a x‖) ν := hba.integrable_mul (Lp.memLp a).norm
    rw [Real.dist_eq, ← integral_sub (hint b).integrableOn
      (hint a).integrableOn]
    calc |∫ x in t, ((√(1 + b x ^ 2) - 1) - (√(1 + a x ^ 2) - 1)) ∂ν|
        ≤ ∫ x in t, (‖(b - a) x‖ * ‖b x‖ + ‖(b - a) x‖ * ‖a x‖) ∂ν := by
          refine abs_integral_le_integral_abs.trans
            (integral_mono_ae ?_ (hi1.add hi2).integrableOn ?_)
          · exact ((hint b).sub
              (hint a)).integrableOn.abs
          · filter_upwards [ae_restrict_of_ae (Lp.coeFn_sub b a)] with x hx
            rw [hx, Pi.sub_apply, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
              sub_sub_sub_cancel_right, ← mul_add]
            exact Real.abs_sqrt_one_add_sq_sub_sqrt_one_add_sq_le _ _
      _ ≤ ∫ x, (‖(b - a) x‖ * ‖b x‖ + ‖(b - a) x‖ * ‖a x‖) ∂ν :=
          setIntegral_le_integral (hi1.add hi2) (ae_of_all _ fun x ↦ by positivity)
      _ ≤ ‖b - a‖ * ‖b‖ + ‖b - a‖ * ‖a‖ := by
          rw [integral_add hi1 hi2]
          exact add_le_add (hcs _ _) (hcs _ _)
  rw [continuous_iff_continuousAt]
  intro a
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun _ ↦ dist_nonneg) (fun b ↦ hbound a b) ?_
  have : Tendsto (fun b : Lp ℝ 2 ν ↦ ‖b - a‖ * ‖b‖ + ‖b - a‖ * ‖a‖) (𝓝 a)
      (𝓝 (‖a - a‖ * ‖a‖ + ‖a - a‖ * ‖a‖)) := by
    have hc : Continuous fun b : Lp ℝ 2 ν ↦ ‖b - a‖ * ‖b‖ + ‖b - a‖ * ‖a‖ := by fun_prop
    exact hc.tendsto a
  simpa using this

end TauCeti
