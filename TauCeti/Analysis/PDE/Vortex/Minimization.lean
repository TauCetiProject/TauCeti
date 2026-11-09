/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Vortex.ReducedFunctional
public import TauCeti.Analysis.Sobolev.WeakDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.Convex
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Convex.Uniform.Basic
import TauCeti.Analysis.Normed.Module.Dual.Reflexive.WeakCompact
import TauCeti.Analysis.Normed.Module.WeakSpace.Bounded
import TauCeti.Analysis.PDE.Vortex.Potential
import TauCeti.Analysis.SpecialFunctions.Exp.Modular
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Function.L2Space
import TauCeti.Topology.Algebra.Module.WeakSpace

/-!
# Weak limits of minimizing sequences of Taubes's functional

Let `P` be a complex polynomial of degree at least one, `h = ‖P‖² / (1 + ‖P‖²)` and
`g = 2 ‖P'‖² / (1 + ‖P‖²)²`. The plane vortex with zero divisor `P` is obtained from a correction
`w` of the background amplitude solving `Δw = (exp (2w) h - 1) / 8 + g`, and Taubes finds `w` as
the minimizer of the functional

`I(w) = ∫ ‖Dw‖² / 2 + (1 / 16) ∫ h (exp (2w) - 1 - 2w) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) w`

(`TauCeti.Vortex.reducedFunctional`) by the direct method of the calculus of variations. The
functional is defined classically on compactly supported `C¹` functions, where it is coercive
(`TauCeti.Vortex.exists_integral_le_of_reducedFunctional_le`). This file passes to the weak limit.

The same expression makes sense for a square-integrable `u` with a weak derivative
`U : ℂ → ℂ →L[ℝ] ℝ` in place of `Dw`: this is `TauCeti.Vortex.weakReducedFunctional P u U`, and
for a `C¹` function with its classical derivative it is `I`
(`TauCeti.Vortex.weakReducedFunctional_fderiv`). Along a minimizing sequence of compactly supported
`C¹` functions, the coercivity estimates bound the `L²` norms of the functions and of their partial
derivatives, so that a subsequence converges weakly in `L²(ℂ)`
(`TauCeti.exists_strictMono_tendsto_toWeakSpace_of_norm_le`, using that Hilbert spaces are
reflexive). The limit `u` is weakly differentiable, its weak derivative being assembled from the
weak limits of the partial derivatives, and each term of the functional passes to the limit: the
Dirichlet energy by weak lower semicontinuity of the norm
(`TauCeti.lowerSemicontinuous_norm_toWeakSpace_symm`), the potential by weak lower
semicontinuity of the convex potential
(`TauCeti.Vortex.lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub`), which also shows that
it is finite, and the linear term by weak continuity. The main result,
`TauCeti.Vortex.exists_hasWeakFDerivOn_weakReducedFunctional_le`, therefore gives a function in
`H¹(ℂ)` with finite potential whose value of the functional is at most `I(w)` for every compactly
supported `C¹` function `w`.

That `u` minimizes the functional among all weakly differentiable functions, its Euler–Lagrange
equation, and the regularity and decay of `u` are not treated here.

## References

* C. H. Taubes, *Arbitrary N-vortex solutions to the first order Ginzburg–Landau equations*,
  Comm. Math. Phys. 72 (1980), 277–292.
* A. Jaffe and C. H. Taubes, *Vortices and Monopoles*, Progress in Physics 2, Birkhäuser, 1980,
  Chapter III, Section 4.
-/

public section

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ContDiff ENNReal

namespace TauCeti.Vortex

variable {P : Polynomial ℂ}

/-- **Taubes's functional at a weakly differentiable function.** For `u : ℂ → ℝ` and a candidate
derivative `U : ℂ → ℂ →L[ℝ] ℝ`, this is
`∫ ‖U‖² / 2 + (1 / 16) ∫ h (exp (2u) - 1 - 2u) + ∫ (g - (1 + ‖P‖²)⁻¹ / 8) u`, with
`h = ‖P‖² / (1 + ‖P‖²)` and `g = 2 ‖P'‖² / (1 + ‖P‖²)²`. It is meant for `u` square integrable
with weak derivative `U`, and for a `C¹` function with its derivative it is Taubes's functional
`TauCeti.Vortex.reducedFunctional` (`TauCeti.Vortex.weakReducedFunctional_fderiv`). -/
def weakReducedFunctional (P : Polynomial ℂ) (u : ℂ → ℝ) (U : ℂ → ℂ →L[ℝ] ℝ) : ℝ :=
  (∫ z, ‖U z‖ ^ 2) / 2 +
    (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * u z) - 1 - 2 * u z)) / 16 +
    ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * u z

/-- The defining formula of `TauCeti.Vortex.weakReducedFunctional`. -/
theorem weakReducedFunctional_def (P : Polynomial ℂ) (u : ℂ → ℝ) (U : ℂ → ℂ →L[ℝ] ℝ) :
    weakReducedFunctional P u U =
      (∫ z, ‖U z‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * u z) - 1 - 2 * u z)) / 16 +
        ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
          (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * u z := (rfl)

/-- At a function with its classical derivative, the functional is Taubes's functional. -/
@[simp]
theorem weakReducedFunctional_fderiv (P : Polynomial ℂ) (w : ℂ → ℝ) :
    weakReducedFunctional P w (fderiv ℝ w) = reducedFunctional P w := by
  rw [weakReducedFunctional_def, reducedFunctional_def]

/-! ### Auxiliary identities -/

/-- The integral of a product with a real square-integrable function is an `L²` inner product. -/
private theorem integral_mul_eq_inner_toLp {f : ℂ → ℝ} (hf : MemLp f 2)
    (g : Lp ℝ 2 (volume : Measure ℂ)) : ∫ z, f z * g z = inner ℝ (hf.toLp f) g := by
  rw [L2.inner_toLp_left]
  simp [mul_comm]

/-- The integral of the square of a real `L²` class is its squared norm. -/
private theorem integral_sq_eq_norm_sq (f : Lp ℝ 2 (volume : Measure ℂ)) :
    ∫ z, f z ^ 2 = ‖f‖ ^ 2 := by
  simp [L2.norm_sq_eq_integral_norm_sq]

/-- The squared norm of `a • re + b • im` is `a ^ 2 + b ^ 2`. -/
private theorem norm_smul_reCLM_add_smul_imCLM_sq (a b : ℝ) :
    ‖a • Complex.reCLM + b • Complex.imCLM‖ ^ 2 = a ^ 2 + b ^ 2 := by
  rw [ContinuousLinearMap.norm_sq_eq_apply_one_sq_add_apply_I_sq]
  simp

/-- **Weak derivatives of weak limits.** Let `w n` be `C¹` functions whose `L²` classes converge
weakly to `u`, while the classes of the partial derivatives `∂₁ w n = Dw n 1` and
`∂₂ w n = Dw n I` converge weakly to `G₁` and `G₂`. Then `z ↦ G₁ z • re + G₂ z • im` is the weak
derivative of `u`. -/
private theorem hasWeakFDerivOn_of_tendsto {w : ℕ → ℂ → ℝ}
    (hw : ∀ n, ContDiff ℝ 1 (w n))
    {W D₁ D₂ : ℕ → Lp ℝ 2 (volume : Measure ℂ)} (hW : ∀ n, W n =ᵐ[volume] w n)
    (hD₁ : ∀ n, D₁ n =ᵐ[volume] fun z ↦ fderiv ℝ (w n) z 1)
    (hD₂ : ∀ n, D₂ n =ᵐ[volume] fun z ↦ fderiv ℝ (w n) z Complex.I)
    {u G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ)}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ _ (W n)) atTop (𝓝 (toWeakSpace ℝ _ u)))
    (hG₁ : Tendsto (fun n ↦ toWeakSpace ℝ _ (D₁ n)) atTop (𝓝 (toWeakSpace ℝ _ G₁)))
    (hG₂ : Tendsto (fun n ↦ toWeakSpace ℝ _ (D₂ n)) atTop (𝓝 (toWeakSpace ℝ _ G₂))) :
    HasWeakFDerivOn volume ⊤ u fun z ↦ G₁ z • Complex.reCLM + G₂ z • Complex.imCLM := by
  have hli (f : Lp ℝ 2 (volume : Measure ℂ)) : LocallyIntegrableOn f ⊤ volume :=
    ((Lp.memLp f).locallyIntegrable one_le_two).locallyIntegrableOn _
  refine hasWeakFDerivOn_iff.2 fun v ↦ ?_
  have hUv : (fun z ↦ (G₁ z • Complex.reCLM + G₂ z • Complex.imCLM) v) =
      fun z ↦ v.re * G₁ z + v.im * G₂ z := by
    funext z; simp [mul_comm]
  have hmemU : MemLp (fun z ↦ v.re * G₁ z + v.im * G₂ z) 2 :=
    ((Lp.memLp G₁).const_mul v.re).add ((Lp.memLp G₂).const_mul v.im)
  rw [hUv, hasWeakLineDerivOn_iff (hli u)
    ((hmemU.locallyIntegrable one_le_two).locallyIntegrableOn _)]
  intro φ hφ hφc _
  have h1 : ContDiff ℝ 1 φ := hφ.of_le (by exact_mod_cast le_top)
  have hφ2 : MemLp φ 2 := hφ.continuous.memLp_of_hasCompactSupport hφc
  have hψ : MemLp (fun z ↦ lineDeriv ℝ φ z v) 2 := by
    have he : (fun z ↦ lineDeriv ℝ φ z v) = fun z ↦ fderiv ℝ φ z v :=
      funext fun z ↦ ((h1.differentiable one_ne_zero) z).lineDeriv_eq_fderiv
    rw [he]
    exact ((h1.continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      (hφc.fderiv_apply (𝕜 := ℝ) v)
  -- Integrals against `φ` of `a G₁ + b G₂`-type combinations are `L²` inner products.
  have hcomb (f₁ f₂ : Lp ℝ 2 (volume : Measure ℂ)) (g : ℂ → ℝ)
      (hg : g =ᵐ[volume] fun z ↦ v.re * f₁ z + v.im * f₂ z) :
      ∫ z, φ z • g z = v.re * inner ℝ (hφ2.toLp φ) f₁ + v.im * inner ℝ (hφ2.toLp φ) f₂ := by
    calc ∫ z, φ z • g z = ∫ z, (v.re * (φ z * f₁ z) + v.im * (φ z * f₂ z)) :=
          integral_congr_ae (by filter_upwards [hg] with z hz; rw [hz, smul_eq_mul]; ring)
      _ = _ := by
        have i₁ : Integrable fun z ↦ φ z * f₁ z := hφ2.integrable_mul (Lp.memLp _)
        have i₂ : Integrable fun z ↦ φ z * f₂ z := hφ2.integrable_mul (Lp.memLp _)
        rw [integral_add (i₁.const_mul _) (i₂.const_mul _), integral_const_mul, integral_const_mul,
          integral_mul_eq_inner_toLp, integral_mul_eq_inner_toLp]
  -- The identity for each `w n`, written through `L²` inner products.
  have hn (n : ℕ) : inner ℝ (hψ.toLp _) (W n) =
      -(v.re * inner ℝ (hφ2.toLp φ) (D₁ n) + v.im * inner ℝ (hφ2.toLp φ) (D₂ n)) := by
    have hwd := ((hw n).locallyLipschitz.locallyLipschitzOn
      (s := ((⊤ : TopologicalSpace.Opens ℂ) : Set ℂ))).hasWeakFDerivOn_fderiv
      (μ := volume) |>.hasWeakLineDerivOn v
    have key := (hasWeakLineDerivOn_iff hwd.locallyIntegrableOn hwd.locallyIntegrableOn_deriv).1
      hwd φ hφ hφc (subset_univ _)
    have hD : (fun z ↦ fderiv ℝ (w n) z v) =ᵐ[volume]
        fun z ↦ v.re * D₁ n z + v.im * D₂ n z := by
      filter_upwards [hD₁ n, hD₂ n] with z h1 h2
      rw [h1, h2, (fderiv ℝ (w n) z).apply_eq_re_smul_one_add_im_smul_I v, smul_eq_mul,
        smul_eq_mul]
    rw [← hcomb _ _ _ hD, ← key, ← integral_mul_eq_inner_toLp]
    exact integral_congr_ae (by filter_upwards [hW n] with z hz; simp [hz])
  -- Pass to the weak limit on both sides.
  have hlim₁ := tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hu (innerSL ℝ (hψ.toLp _))
  have hlim₂ := ((tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hG₁
    (innerSL ℝ (hφ2.toLp φ))).const_mul v.re).add
    ((tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hG₂ (innerSL ℝ (hφ2.toLp φ))).const_mul v.im)
  simp only [innerSL_apply_apply] at hlim₁ hlim₂
  have heq := tendsto_nhds_unique hlim₁ (by simpa only [hn] using hlim₂.neg)
  rw [hcomb G₁ G₂ _ (Eventually.of_forall fun z ↦ rfl), ← heq, ← integral_mul_eq_inner_toLp]
  simp only [smul_eq_mul]

/-- Taubes's functional at a weakly differentiable function `u` with weak derivative
`G₁ • re + G₂ • im`, written through `L²` norms and inner products. -/
private theorem weakReducedFunctional_eq (hc : MemLp (fun z ↦ 2 * ‖P.derivative.eval z‖ ^ 2 /
      (1 + ‖P.eval z‖ ^ 2) ^ 2 - (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) 2)
    (u : ℂ → ℝ) {U : Lp ℝ 2 (volume : Measure ℂ)} (hU : U =ᵐ[volume] u)
    (G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ)) :
    weakReducedFunctional P u (fun z ↦ G₁ z • Complex.reCLM + G₂ z • Complex.imCLM) =
      (‖G₁‖ ^ 2 + ‖G₂‖ ^ 2) / 2 +
        (∫ z, ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * u z) - 1 - 2 * u z)) / 16 +
        inner ℝ (hc.toLp _) U := by
  have hcu : ∫ z, (2 * ‖P.derivative.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) ^ 2 -
      (1 + ‖P.eval z‖ ^ 2)⁻¹ / 8) * u z = inner ℝ (hc.toLp _) U := by
    rw [← integral_mul_eq_inner_toLp]
    exact integral_congr_ae (by filter_upwards [hU] with z hz; rw [hz])
  rw [weakReducedFunctional_def, hcu, ← integral_sq_eq_norm_sq, ← integral_sq_eq_norm_sq,
    ← integral_add (Lp.memLp G₁).integrable_sq (Lp.memLp G₂).integrable_sq]
  simp_rw [norm_smul_reCLM_add_smul_imCLM_sq]

/-- The potential density `h (exp (2f) - 1 - 2f)`, `h = ‖P‖² / (1 + ‖P‖²)`, of Taubes's
functional. -/
private def pot (P : Polynomial ℂ) (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) * (Real.exp (2 * f z) - 1 - 2 * f z)

/-- The potential density is nonnegative, since `exp (2t) ≥ 1 + 2t`. -/
private theorem pot_nonneg (P : Polynomial ℂ) (f : ℂ → ℝ) : 0 ≤ pot P f := fun z ↦
  mul_nonneg (by positivity) (Real.exp_two_mul_sub_one_sub_two_mul_nonneg _)

/-- A continuous compactly supported function has integrable potential density. -/
private theorem integrable_pot {f : ℂ → ℝ} (hf : Continuous f) (hfs : HasCompactSupport f) :
    Integrable (pot P f) :=
  integrable_mul_exp_sub_one_sub P hf hfs

/-- The potential density of an almost everywhere strongly measurable function is almost
everywhere strongly measurable. -/
private theorem aestronglyMeasurable_pot {f : ℂ → ℝ} (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (pot P f) volume := by
  have hh : Continuous fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) := by
    fun_prop (disch := intro z; positivity)
  have hΦ : Continuous fun t : ℝ ↦ Real.exp (2 * t) - 1 - 2 * t := by fun_prop
  exact hh.aestronglyMeasurable.mul (hΦ.comp_aestronglyMeasurable hf)

/-- Taubes's functional only depends on the weak derivative up to null sets, through its
values on `1` and `I`. -/
private theorem weakReducedFunctional_congr_ae (P : Polynomial ℂ) (u : ℂ → ℝ)
    (U : ℂ → ℂ →L[ℝ] ℝ) {G₁ G₂ : ℂ → ℝ} (h₁ : G₁ =ᵐ[volume] fun z ↦ U z 1)
    (h₂ : G₂ =ᵐ[volume] fun z ↦ U z Complex.I) :
    weakReducedFunctional P u (fun z ↦ G₁ z • Complex.reCLM + G₂ z • Complex.imCLM) =
      weakReducedFunctional P u U := by
  rw [weakReducedFunctional_def, weakReducedFunctional_def]
  congr 3
  refine integral_congr_ae ?_
  filter_upwards [h₁, h₂] with z hz₁ hz₂
  rw [norm_smul_reCLM_add_smul_imCLM_sq, hz₁, hz₂,
    ContinuousLinearMap.norm_sq_eq_apply_one_sq_add_apply_I_sq]

/-- **Lower semicontinuity of the potential.** Let `w n` be compactly supported `C¹` functions
with bounded potentials whose `L²` classes converge weakly to `u`. Then `u` has finite potential,
and the potential of `u` is eventually at most that of `w n` plus any given `δ > 0`. -/
private theorem integrable_pot_and_eventually_integral_pot_lt {w : ℕ → ℂ → ℝ}
    (hw : ∀ n, Continuous (w n)) (hws : ∀ n, HasCompactSupport (w n))
    {W : ℕ → Lp ℝ 2 (volume : Measure ℂ)} (hW : ∀ n, W n =ᵐ[volume] w n)
    {u : Lp ℝ 2 (volume : Measure ℂ)}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ _ (W n)) atTop (𝓝 (toWeakSpace ℝ _ u)))
    {B : ℝ} (hB : ∀ n, ∫ z, pot P (w n) z ≤ B) :
    Integrable (pot P u) ∧
      ∀ δ > 0, ∀ᶠ n in atTop, ∫ z, pot P u z < (∫ z, pot P (w n) z) + δ := by
  -- The potential of `w n` as an extended integral of its `L²` class.
  have hEn (n : ℕ) : ∫⁻ z, ENNReal.ofReal (pot P (W n) z) =
      ENNReal.ofReal (∫ z, pot P (w n) z) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_pot (hw n) (hws n))
      (Eventually.of_forall (pot_nonneg _ _))]
    exact lintegral_congr_ae (by filter_upwards [hW n] with z hz; rw [pot, pot, hz])
  -- Weak lower semicontinuity of the extended potential along the sequence.
  have hlsc (a : ℝ≥0∞) (ha : a < ∫⁻ z, ENNReal.ofReal (pot P u z)) :
      ∀ᶠ n in atTop, a < ENNReal.ofReal (∫ z, pot P (w n) z) := by
    have h := hu.eventually ((lowerSemicontinuous_lintegral_ofReal_mul_exp_sub_one_sub P)
      (toWeakSpace ℝ _ u) a (by simpa only [LinearEquiv.symm_apply_apply, pot] using ha))
    filter_upwards [h] with n hn
    rw [← hEn n]
    simpa only [LinearEquiv.symm_apply_apply, pot] using hn
  -- The potential of `u` is finite.
  have hfin : ∫⁻ z, ENNReal.ofReal (pot P u z) ≤ ENNReal.ofReal B := by
    by_contra! h
    obtain ⟨n, hn⟩ := (hlsc _ h).exists
    exact hn.not_ge (ENNReal.ofReal_le_ofReal (hB n))
  have hint : Integrable (pot P u) :=
    (lintegral_ofReal_ne_top_iff_integrable (aestronglyMeasurable_pot (Lp.aestronglyMeasurable u))
      (Eventually.of_forall (pot_nonneg _ _))).1 (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hfin)
  have hEu : ENNReal.ofReal (∫ z, pot P u z) = ∫⁻ z, ENNReal.ofReal (pot P u z) :=
    ofReal_integral_eq_lintegral_ofReal hint (Eventually.of_forall (pot_nonneg _ _))
  refine ⟨hint, fun δ hδ ↦ ?_⟩
  rcases lt_or_ge (∫ z, pot P u z) δ with h | h
  · refine Eventually.of_forall fun n ↦ ?_
    have : (0 : ℝ) ≤ ∫ z, pot P (w n) z := integral_nonneg (pot_nonneg P (w n))
    linarith
  · have ha : ENNReal.ofReal ((∫ z, pot P u z) - δ) < ∫⁻ z, ENNReal.ofReal (pot P u z) := by
      rw [← hEu, ENNReal.ofReal_lt_ofReal_iff']
      exact ⟨sub_lt_self _ hδ, hδ.trans_le h⟩
    filter_upwards [hlsc _ ha] with n hn
    rw [ENNReal.ofReal_lt_ofReal_iff'] at hn
    linarith [hn.1]

/-- **The direct method for Taubes's functional.** Let `w n` be compactly supported `C¹`
functions whose values `I(w n)` are eventually below `t + ε` for every `ε > 0`, with bounded
potentials. If the `L²` classes of `w n` and of its partial derivatives converge weakly to `u`,
`G₁` and `G₂`, then `u` has finite potential and Taubes's functional at `u`, with derivative
`G₁ • re + G₂ • im`, is at most `t`. -/
private theorem integrable_and_weakReducedFunctional_le (hm : 0 < P.natDegree)
    {w : ℕ → ℂ → ℝ} (hw : ∀ n, ContDiff ℝ 1 (w n)) (hws : ∀ n, HasCompactSupport (w n))
    {W D₁ D₂ : ℕ → Lp ℝ 2 (volume : Measure ℂ)} (hW : ∀ n, W n =ᵐ[volume] w n)
    (hD₁ : ∀ n, D₁ n =ᵐ[volume] fun z ↦ fderiv ℝ (w n) z 1)
    (hD₂ : ∀ n, D₂ n =ᵐ[volume] fun z ↦ fderiv ℝ (w n) z Complex.I)
    {u G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ)}
    (hu : Tendsto (fun n ↦ toWeakSpace ℝ _ (W n)) atTop (𝓝 (toWeakSpace ℝ _ u)))
    (hG₁ : Tendsto (fun n ↦ toWeakSpace ℝ _ (D₁ n)) atTop (𝓝 (toWeakSpace ℝ _ G₁)))
    (hG₂ : Tendsto (fun n ↦ toWeakSpace ℝ _ (D₂ n)) atTop (𝓝 (toWeakSpace ℝ _ G₂)))
    {t B : ℝ} (hI : ∀ ε > 0, ∀ᶠ n in atTop, reducedFunctional P (w n) < t + ε)
    (hB : ∀ n, ∫ z, pot P (w n) z ≤ B) :
    Integrable (pot P u) ∧
      weakReducedFunctional P u (fun z ↦ G₁ z • Complex.reCLM + G₂ z • Complex.imCLM) ≤ t := by
  have hc := memLp_reducedFunctional_coefficient hm
  obtain ⟨hint, hpot⟩ :=
    integrable_pot_and_eventually_integral_pot_lt (fun n ↦ (hw n).continuous) hws hW hu hB
  refine ⟨hint, le_of_forall_pos_lt_add fun ε hε ↦ ?_⟩
  have hδ : 0 < ε / 4 := by positivity
  -- The Dirichlet energy is weakly lower semicontinuous, since the norm is.
  have hsq {x : ℕ → Lp ℝ 2 (volume : Measure ℂ)} {y : Lp ℝ 2 (volume : Measure ℂ)}
      (hx : Tendsto (fun n ↦ toWeakSpace ℝ _ (x n)) atTop (𝓝 (toWeakSpace ℝ _ y))) :
      ∀ᶠ n in atTop, ‖y‖ ^ 2 < ‖x n‖ ^ 2 + ε / 4 := by
    have hlsc : LowerSemicontinuous fun a : WeakSpace ℝ (Lp ℝ 2 (volume : Measure ℂ)) ↦
        max ‖(toWeakSpace ℝ _).symm a‖ 0 ^ 2 :=
      (continuous_id.max continuous_const |>.pow 2).comp_lowerSemicontinuous
        lowerSemicontinuous_norm_toWeakSpace_symm
        fun a b hab ↦ pow_le_pow_left₀ (le_max_right _ _) (max_le_max_right 0 hab) 2
    filter_upwards [hx.eventually (hlsc (toWeakSpace ℝ _ y) (‖y‖ ^ 2 - ε / 4) (by simp; linarith))]
      with n hn
    simp only [LinearEquiv.symm_apply_apply, norm_nonneg, max_eq_left] at hn
    linarith
  -- The linear term is weakly continuous.
  have hlin : ∀ᶠ n in atTop, inner ℝ (hc.toLp _) u < inner ℝ (hc.toLp _) (W n) + ε / 4 := by
    have hlim := tendsto_toWeakSpace_iff_forall_eval_tendsto.1 hu (innerSL ℝ (hc.toLp _))
    simp only [innerSL_apply_apply] at hlim
    filter_upwards [hlim.eventually (Ioi_mem_nhds (sub_lt_self _ hδ))] with n hn
    exact sub_lt_iff_lt_add.1 hn
  obtain ⟨n, h₁, h₂, h₃, h₄, h₅⟩ :=
    ((hsq hG₁).and ((hsq hG₂).and ((hpot _ hδ).and (hlin.and (hI (ε / 4) hδ))))).exists
  have hIn := weakReducedFunctional_eq hc (w n) (hW n) (D₁ n) (D₂ n)
  rw [weakReducedFunctional_congr_ae P (w n) (fderiv ℝ (w n)) (hD₁ n) (hD₂ n),
    weakReducedFunctional_fderiv] at hIn
  rw [weakReducedFunctional_eq hc u (Eventually.of_forall fun _ ↦ rfl)]
  simp only [pot] at h₃
  linarith

/-- **Weak compactness in `H¹(ℂ)`.** Compactly supported `C¹` functions `w n` with uniformly
bounded `L²` norms and Dirichlet energies have a subsequence `w ∘ σ` along which the `L²` classes
of the functions and of their partial derivatives `∂₁ = D · 1` and `∂₂ = D · I` converge weakly in
`L²(ℂ)`. -/
private theorem exists_strictMono_tendsto_of_integral_le {w : ℕ → ℂ → ℝ}
    (hw : ∀ n, ContDiff ℝ 1 (w n)) (hws : ∀ n, HasCompactSupport (w n)) {C : ℝ}
    (hC : ∀ n, ∫ z, ‖fderiv ℝ (w n) z‖ ^ 2 ≤ C ∧ ∫ z, w n z ^ 2 ≤ C) :
    ∃ (W D₁ D₂ : ℕ → Lp ℝ 2 (volume : Measure ℂ)) (u G₁ G₂ : Lp ℝ 2 (volume : Measure ℂ))
      (σ : ℕ → ℕ), StrictMono σ ∧ (∀ n, W n =ᵐ[volume] w (σ n)) ∧
      (∀ n, D₁ n =ᵐ[volume] fun z ↦ fderiv ℝ (w (σ n)) z 1) ∧
      (∀ n, D₂ n =ᵐ[volume] fun z ↦ fderiv ℝ (w (σ n)) z Complex.I) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ _ (W n)) atTop (𝓝 (toWeakSpace ℝ _ u)) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ _ (D₁ n)) atTop (𝓝 (toWeakSpace ℝ _ G₁)) ∧
      Tendsto (fun n ↦ toWeakSpace ℝ _ (D₂ n)) atTop (𝓝 (toWeakSpace ℝ _ G₂)) := by
  have hmem (n : ℕ) : MemLp (w n) 2 := (hw n).continuous.memLp_of_hasCompactSupport (hws n)
  have hmemD (n : ℕ) (v : ℂ) : MemLp (fun z ↦ fderiv ℝ (w n) z v) 2 :=
    (((hw n).continuous_fderiv one_ne_zero).clm_apply continuous_const).memLp_of_hasCompactSupport
      ((hws n).fderiv_apply (𝕜 := ℝ) v)
  have hint (n : ℕ) : Integrable fun z ↦ ‖fderiv ℝ (w n) z‖ ^ 2 :=
    ((hw n).continuous_fderiv one_ne_zero).norm.pow 2 |>.integrable_of_hasCompactSupport
      (((hws n).fderiv (𝕜 := ℝ)).norm.mono fun z hz h0 ↦ hz (by simp [h0]))
  -- The `L²` norms of the partial derivatives are bounded by the Dirichlet energy.
  have hDle (n : ℕ) (v : ℂ) (hv : ‖v‖ = 1) : ‖(hmemD n v).toLp _‖ ≤ √C := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← integral_sq_eq_norm_sq]
    calc ∫ z, (hmemD n v).toLp _ z ^ 2 = ∫ z, fderiv ℝ (w n) z v ^ 2 :=
          integral_congr_ae (by filter_upwards [(hmemD n v).coeFn_toLp] with z hz; rw [hz])
      _ ≤ ∫ z, ‖fderiv ℝ (w n) z‖ ^ 2 :=
          integral_mono (hmemD n v).integrable_sq (hint n) fun z ↦ by
            rw [← sq_abs]
            gcongr
            simpa [hv] using (fderiv ℝ (w n) z).le_opNorm v
      _ ≤ C := (hC n).1
  have hWle (n : ℕ) : ‖(hmem n).toLp _‖ ≤ √C := by
    refine Real.le_sqrt_of_sq_le ?_
    rw [← integral_sq_eq_norm_sq]
    calc ∫ z, (hmem n).toLp _ z ^ 2 = ∫ z, w n z ^ 2 :=
          integral_congr_ae (by filter_upwards [(hmem n).coeFn_toLp] with z hz; rw [hz])
      _ ≤ C := (hC n).2
  -- Extract three successive subsequences in the reflexive space `L²(ℂ)`.
  have hE := surjective_inclusionInDoubleDual_of_uniformConvexSpace (𝕜 := ℝ)
    (E := Lp ℝ 2 (volume : Measure ℂ))
  obtain ⟨u, φ₁, hφ₁, hu⟩ := exists_strictMono_tendsto_toWeakSpace_of_norm_le hE hWle
  obtain ⟨G₁, φ₂, hφ₂, hG₁⟩ := exists_strictMono_tendsto_toWeakSpace_of_norm_le hE
    fun n ↦ hDle (φ₁ n) 1 (by simp)
  obtain ⟨G₂, φ₃, hφ₃, hG₂⟩ := exists_strictMono_tendsto_toWeakSpace_of_norm_le hE
    fun n ↦ hDle (φ₁ (φ₂ n)) Complex.I (by simp)
  exact ⟨fun n ↦ (hmem _).toLp _, fun n ↦ (hmemD _ 1).toLp _, fun n ↦ (hmemD _ Complex.I).toLp _,
    u, G₁, G₂, fun n ↦ φ₁ (φ₂ (φ₃ n)), hφ₁.comp (hφ₂.comp hφ₃),
    fun n ↦ (hmem _).coeFn_toLp, fun n ↦ MemLp.coeFn_toLp _, fun n ↦ MemLp.coeFn_toLp _,
    hu.comp (hφ₂.comp hφ₃).tendsto_atTop, hG₁.comp hφ₃.tendsto_atTop, hG₂⟩

/-- **Weak limits of minimizing sequences of Taubes's functional.** For a complex polynomial
`P` of degree at least one there is a square-integrable function `u` with a square-integrable
weak derivative `U` and finite potential `∫ h (exp (2u) - 1 - 2u)`, whose value of Taubes's
functional is at most `I(w)` for every compactly supported `C¹` function `w`. Here `I` is
`TauCeti.Vortex.reducedFunctional P`, and its value at `u` is
`TauCeti.Vortex.weakReducedFunctional P u U`. -/
theorem exists_hasWeakFDerivOn_weakReducedFunctional_le (hm : 0 < P.natDegree) :
    ∃ (u : ℂ → ℝ) (U : ℂ → ℂ →L[ℝ] ℝ), MemLp u 2 ∧ MemLp U 2 ∧ HasWeakFDerivOn volume ⊤ u U ∧
      Integrable (fun z ↦ ‖P.eval z‖ ^ 2 / (1 + ‖P.eval z‖ ^ 2) *
        (Real.exp (2 * u z) - 1 - 2 * u z)) ∧
      ∀ w : ℂ → ℝ, ContDiff ℝ 1 w → HasCompactSupport w →
        weakReducedFunctional P u U ≤ reducedFunctional P w := by
  -- A minimizing sequence among the compactly supported `C¹` functions, below the infimum `t`
  -- plus `1 / (n + 1)`.
  let S := {w : ℂ → ℝ // ContDiff ℝ 1 w ∧ HasCompactSupport w}
  have : Nonempty S := ⟨⟨0, contDiff_const, HasCompactSupport.zero⟩⟩
  obtain ⟨C₀, hC₀⟩ := exists_le_reducedFunctional hm
  have hbdd : BddBelow (range fun w : S ↦ reducedFunctional P w.1) :=
    ⟨C₀, forall_mem_range.2 fun w ↦ hC₀ w.1 w.2.1 w.2.2⟩
  have hlt (n : ℕ) : ∃ w : S, reducedFunctional P w.1 < (⨅ w : S, reducedFunctional P w.1) +
      1 / (n + 1) :=
    exists_lt_of_ciInf_lt (lt_add_of_pos_right _ (by positivity))
  choose w hwt using hlt
  set t := ⨅ w : S, reducedFunctional P w.1
  have hw (n : ℕ) : ContDiff ℝ 1 (w n).1 := (w n).2.1
  have hws (n : ℕ) : HasCompactSupport (w n).1 := (w n).2.2
  have hwt₁ (n : ℕ) : reducedFunctional P (w n).1 ≤ t + 1 := by
    have : 1 / ((n : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith [n.cast_nonneg (α := ℝ)]
    linarith [hwt n]
  -- Uniform bounds on the Dirichlet energy, the `L²` norm and the potential.
  obtain ⟨C, hC⟩ := exists_integral_le_of_reducedFunctional_le hm (t + 1)
  obtain ⟨C₁, hC₁⟩ := exists_le_two_mul_reducedFunctional_add hm
  have hB (n : ℕ) : ∫ z, pot P (w n).1 z ≤ 16 * (2 * (t + 1) + C₁) := by
    have h₁ := hC₁ _ (hw n) (hws n)
    have h₂ : 0 ≤ ∫ z, ‖fderiv ℝ (w n).1 z‖ ^ 2 := integral_nonneg fun z ↦ by positivity
    have h₃ := hwt₁ n
    simp only [pot]
    linarith
  -- Weak limits along a subsequence, and the limit is weakly differentiable.
  obtain ⟨W, D₁, D₂, u, G₁, G₂, σ, hσ, hW, hD₁, hD₂, hu, hG₁, hG₂⟩ :=
    exists_strictMono_tendsto_of_integral_le hw hws fun n ↦ hC _ (hw n) (hws n) (hwt₁ n)
  refine ⟨u, fun z ↦ G₁ z • Complex.reCLM + G₂ z • Complex.imCLM, Lp.memLp u,
    ((Lp.memLp G₁).continuousLinearMap_comp
      ((ContinuousLinearMap.id ℝ ℝ).smulRight Complex.reCLM)).add
      ((Lp.memLp G₂).continuousLinearMap_comp
        ((ContinuousLinearMap.id ℝ ℝ).smulRight Complex.imCLM)),
    hasWeakFDerivOn_of_tendsto (fun n ↦ hw _) hW hD₁ hD₂ hu hG₁ hG₂, ?_⟩
  -- The subsequence is still minimizing, so the functional at the limit is at most `t`.
  have hI : ∀ ε > 0, ∀ᶠ n in atTop, reducedFunctional P (w (σ n)).1 < t + ε := by
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    filter_upwards [eventually_ge_atTop N] with n hn
    have : 1 / ((σ n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
      one_div_le_one_div_of_le (by positivity)
        (by exact_mod_cast Nat.add_le_add_right (hn.trans (hσ.id_le n)) 1)
    linarith [hwt (σ n)]
  obtain ⟨hpot, hle⟩ := integrable_and_weakReducedFunctional_le hm (fun n ↦ hw _)
    (fun n ↦ hws _) hW hD₁ hD₂ hu hG₁ hG₂ hI (fun n ↦ hB _)
  exact ⟨hpot, fun v hv hvs ↦ hle.trans (ciInf_le hbdd ⟨v, hv, hvs⟩)⟩

end TauCeti.Vortex
