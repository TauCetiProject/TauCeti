/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import TauCeti.Probability.Concentration.Poincare.LogSobolev
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.Probability.Concentration.EfronStein

/-!
# Poincaré tensorization on finite Hilbert products

A finite product of probability measures satisfying Poincaré inequalities with a common
nonnegative constant satisfies the same inequality on the Hilbert product `PiLp 2 E`.
For different factor constants, their finite maximum is valid. The product law is transported
from `Measure.pi` to `PiLp 2 E`; its derivative energy uses the squared Hilbert norm, with no
factor one half. The statements include the empty product, whose maximum constant is zero.

The finite-product statement and Hilbert-space normalization are adapted from the
[KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean).
The fixed-constant tensorization principle is Proposition 4.3.1 in Bakry, Gentil and Ledoux,
*Analysis and Geometry of Markov Diffusion Operators* (2014). Here it is proved directly for
smooth L² tests of finite derivative energy using the Efron–Stein inequality; no identification
with a Markov-generator domain or an optimal spectral-gap constant is asserted.
-/

public section

noncomputable section

open ProbabilityTheory
open scoped ENNReal NNReal ContDiff

namespace MeasureTheory.Measure


variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, SecondCountableTopology (E i)]

/-- A finite Hilbert product of probability measures with a common nonnegative Poincaré
constant satisfies the same Poincaré inequality. -/
theorem PoincareInequality.piLp (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : ℝ≥0) (hμ : ∀ i, (μ i).PoincareInequality C) :
    ((Measure.pi μ).map (WithLp.toLp 2)).PoincareInequality C := by
  classical
  rw [PoincareInequality_def]
  intro f hf hL hD
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let F := f ∘ WithLp.toLp 2
  let G := gradient f ∘ WithLp.toLp 2
  have hm : MeasurePreserving (WithLp.toLp 2 : (∀ i, E i) → PiLp 2 E) (Measure.pi μ) ρ :=
    ⟨WithLp.measurable_toLp 2 _, rfl⟩
  have hFm : Measurable F := hf.continuous.measurable.comp hm.measurable
  have hFL : MemLp F 2 (Measure.pi μ) := hL.comp_measurePreserving hm
  have hGm : Measurable G := (TauCeti.measurable_gradient f).comp hm.measurable
  have hGL : MemLp (fun x ↦ ‖G x‖) 2 (Measure.pi μ) := by
    simpa only [G, Function.comp_def, TauCeti.norm_gradient_eq_norm_fderiv] using
      hD.comp_measurePreserving hm
  have hGim (i : ι) : Measurable (fun x ↦ ‖G x i‖) :=
    ((PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).continuous.measurable.comp hGm).norm
  have hGiL (i : ι) : MemLp (fun x ↦ ‖G x i‖) 2 (Measure.pi μ) :=
    hGL.mono' (hGim i).aestronglyMeasurable
      (ae_of_all _ fun x ↦ by
        simpa only [Real.norm_of_nonneg (norm_nonneg _)] using (PiLp.norm_apply_le (G x) i))
  have hcoord (i : ι) :
      (∫⁻ x, evariance (fun y ↦ F (Function.update x i y)) (μ i) ∂Measure.pi μ) ≤
        (C : ℝ≥0∞) * ∫⁻ x, (ENNReal.ofReal ‖G x i‖) ^ 2 ∂Measure.pi μ := by
    have hsec : ∀ᵐ x ∂Measure.pi μ,
        evariance (fun y ↦ F (Function.update x i y)) (μ i) ≤
          (C : ℝ≥0∞) * ∫⁻ y, (ENNReal.ofReal ‖G (Function.update x i y) i‖) ^ 2 ∂μ i := by
      filter_upwards [TauCeti.ae_memLp_two_pi_update μ hFm hFL i,
        TauCeti.ae_memLp_two_pi_update μ (hGim i) (hGiL i) i]
        with x hxF hxG
      have hs : ContDiff ℝ ∞ (fun y ↦ F (Function.update x i y)) :=
        hf.comp (PiLp.contDiff_toLp.comp (contDiff_update ∞ x i))
      have hnorm (y : E i) :
          ‖fderiv ℝ (fun z ↦ F (Function.update x i z)) y‖ =
            ‖G (Function.update x i y) i‖ :=
        PiLp.norm_fderiv_update f x i y (hf.differentiable (by simp) _)
      have hsecD : MemLp (fun y ↦ ‖fderiv ℝ (fun z ↦ F (Function.update x i z)) y‖)
          2 (μ i) := by simpa only [hnorm] using hxG
      have hv := (hμ i).apply _ hs hxF hsecD
      rw [← hxF.ofReal_variance_eq]
      calc
        _ ≤ ENNReal.ofReal ((C : ℝ) * ∫ y, ‖G (Function.update x i y) i‖ ^ 2 ∂μ i) :=
          ENNReal.ofReal_le_ofReal (by simpa only [hnorm] using hv)
        _ = _ := by
          rw [ENNReal.ofReal_mul C.coe_nonneg, ENNReal.ofReal_coe_nnreal,
            ofReal_integral_eq_lintegral_ofReal hxG.integrable_sq
              (ae_of_all _ fun y ↦ sq_nonneg _)]
          simp_rw [ENNReal.ofReal_pow (norm_nonneg _)]
    calc
      _ ≤ ∫⁻ x, (C : ℝ≥0∞) *
          ∫⁻ y, (ENNReal.ofReal ‖G (Function.update x i y) i‖) ^ 2 ∂μ i
            ∂Measure.pi μ := lintegral_mono_ae hsec
      _ = _ := by
        rw [lintegral_const_mul' _ _ ENNReal.coe_ne_top,
          TauCeti.lintegral_pi_update μ ((hGim i).ennreal_ofReal.pow_const 2) i]
  have hsum : (∑ i, (C : ℝ≥0∞) *
      ∫⁻ x, (ENNReal.ofReal ‖G x i‖) ^ 2 ∂Measure.pi μ) =
        (C : ℝ≥0∞) * ∫⁻ x, (ENNReal.ofReal ‖G x‖) ^ 2 ∂Measure.pi μ := by
    rw [← Finset.mul_sum]
    congr 1
    rw [← lintegral_finsetSum' _ (fun i _ ↦ ((hGim i).ennreal_ofReal.pow_const 2).aemeasurable)]
    apply lintegral_congr_ae
    filter_upwards [] with x
    rw [← ENNReal.ofReal_pow (norm_nonneg _), PiLp.norm_sq_eq_of_L2 E]
    simp only [ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg _),
      ENNReal.ofReal_pow (norm_nonneg _)]
  have henergy : ENNReal.ofReal (∫ z, ‖fderiv ℝ f z‖ ^ 2 ∂ρ) =
      ∫⁻ x, (ENNReal.ofReal ‖G x‖) ^ 2 ∂Measure.pi μ := by
    rw [ofReal_integral_eq_lintegral_ofReal hD.integrable_sq
      (ae_of_all _ fun z ↦ sq_nonneg _)]
    rw [lintegral_map'
      ((hf.continuous_fderiv (by simp)).norm.measurable.pow_const 2).ennreal_ofReal.aemeasurable
      hm.measurable.aemeasurable]
    simp only [G, Function.comp_def, ENNReal.ofReal_pow (norm_nonneg _),
      TauCeti.norm_gradient_eq_norm_fderiv]
  have hv := (TauCeti.Probability.efronStein μ hFm hFL).trans
    (Finset.sum_le_sum fun i _ ↦ hcoord i)
  have hC : ENNReal.ofReal (C : ℝ) = (C : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  rw [hsum, ← henergy, ← hC,
    ← ENNReal.ofReal_mul C.coe_nonneg, ← hFL.ofReal_variance_eq] at hv
  have hvar : variance F (Measure.pi μ) = variance f ρ :=
    hm.variance_fun_comp hf.continuous.measurable.aemeasurable
  rw [hvar] at hv
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg C.coe_nonneg
    (integral_nonneg fun _ ↦ sq_nonneg _))).mp hv

/-- A finite Hilbert product satisfies the Poincaré inequality with the maximum of its
nonnegative factor constants. For an empty family the maximum is zero. -/
theorem PoincareInequality.piLp_sup (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (C : ι → ℝ≥0)
    (hμ : ∀ i, (μ i).PoincareInequality (C i)) :
    ((Measure.pi μ).map (WithLp.toLp 2)).PoincareInequality (Finset.univ.sup C : ℝ≥0) := by
  classical
  apply PoincareInequality.piLp μ (Finset.univ.sup C)
  intro i
  exact (hμ i).mono (by exact_mod_cast Finset.le_sup (f := C) (Finset.mem_univ i))

end MeasureTheory.Measure
