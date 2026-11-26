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
import TauCeti.Analysis.Calculus.FDeriv.Pi.Lp
import TauCeti.MeasureTheory.Constructions.WithLp
import TauCeti.MeasureTheory.Integral.Entropy.Product
import TauCeti.MeasureTheory.Integral.Pi
import TauCeti.Probability.Concentration.EfronStein

/-!
# Poincaré and logarithmic Sobolev tensorization on finite Hilbert products

A finite product of probability measures satisfying Poincaré or logarithmic Sobolev inequalities
with a common nonnegative constant satisfies the same inequality on the Hilbert product
`PiLp 2 E`. For different factor constants, their finite maximum is valid; conversely, every
marginal of the Hilbert product inherits its Poincaré or logarithmic Sobolev inequality. The
product law is transported from `Measure.pi` to `PiLp 2 E`, and its derivative energy uses the
squared Hilbert norm. Both statements include the empty product, whose maximum constant is zero.

## Main results

* `MeasureTheory.Measure.PoincareInequality.of_piLp` and
  `MeasureTheory.Measure.LogSobolevInequality.of_piLp`: every marginal of a finite `PiLp 2`
  product inherits its inequality.
* `MeasureTheory.Measure.PoincareInequality.piLp` and
  `MeasureTheory.Measure.LogSobolevInequality.piLp`: tensorization with a common nonnegative
  constant `C`.
* `MeasureTheory.Measure.PoincareInequality.piLp_sup` and
  `MeasureTheory.Measure.LogSobolevInequality.piLp_sup`: tensorization with the maximum of factor
  constants.

## References

* The Poincaré finite-product statement and Hilbert-space normalization are adapted from the
  [KLS formalization](https://github.com/human-ai-mathematics/kls-lean/blob/65810c73f9dd7945fc646ab484cb19d673f5291d/formalization/FunctionalInequalities/Poincare/FiniteProduct/Tensorization.lean).
* D. Bakry, I. Gentil and M. Ledoux, *Analysis and Geometry of Markov Diffusion Operators*,
  Springer (2014), Propositions 4.3.1 and 5.2.7.
* G. W. Anderson, A. Guionnet and O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), Lemma 2.3.3.
-/

public section

noncomputable section

open ProbabilityTheory
open scoped ENNReal NNReal ContDiff

namespace MeasureTheory.Measure

section Marginals

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedSpace ℝ (E i)]
  [∀ i, MeasurableSpace (E i)]

/-- Every marginal of a finite `PiLp 2` product inherits its Poincaré inequality. -/
theorem PoincareInequality.of_piLp {μ : ∀ i, Measure (E i)}
    [∀ i, IsProbabilityMeasure (μ i)] {C : ℝ}
    (h : PoincareInequality ((Measure.pi μ).map (WithLp.toLp 2)) C) (i : ι) :
    PoincareInequality (μ i) C := by
  classical
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let q := (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i)
  have hm : MeasurePreserving q ρ (μ i) :=
    funext (PiLp.proj_apply (𝕜 := ℝ) 2 E i) ▸ PiLp.measurePreserving_eval_map_toLp 2 μ i
  rw [PoincareInequality_def]
  intro f hf hfL hdf
  have hn (x : PiLp 2 E) :
      ‖fderiv ℝ (fun y : PiLp 2 E ↦ f (q y)) x‖ = ‖fderiv ℝ f (q x)‖ :=
    PiLp.norm_fderiv_comp_proj (hf.differentiable (by simp) _)
  have hd : MemLp (fun x : PiLp 2 E ↦ ‖fderiv ℝ (fun y ↦ f (q y)) x‖) 2 ρ := by
    simp only [hn]
    exact hdf.comp_measurePreserving hm
  have hv := h.apply (fun x ↦ f (q x)) (hf.comp q.contDiff)
    (hfL.comp_measurePreserving hm) hd
  rw [hm.variance_fun_comp hfL.aemeasurable] at hv
  have he : (∫ x, ‖fderiv ℝ (fun y ↦ f (q y)) x‖ ^ 2 ∂ρ) =
      ∫ y, ‖fderiv ℝ f y‖ ^ 2 ∂μ i := by
    simp only [hn]
    have hint : AEStronglyMeasurable (fun y ↦ ‖fderiv ℝ f y‖ ^ 2) (ρ.map q) :=
      hm.map_eq.symm ▸ hdf.integrable_sq.aestronglyMeasurable
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable hint]
  rwa [he] at hv

/-- Every marginal of a finite `PiLp 2` product inherits its logarithmic Sobolev inequality. -/
theorem LogSobolevInequality.of_piLp {μ : ∀ i, Measure (E i)}
    [∀ i, IsProbabilityMeasure (μ i)] {C : ℝ}
    (h : LogSobolevInequality ((Measure.pi μ).map (WithLp.toLp 2)) C) (i : ι) :
    LogSobolevInequality (μ i) C :=
  (LogSobolevInequality_def _ _).2 fun f hf hdf hf2 hf2log ↦ by
  classical
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let q := (PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i)
  have hm : MeasurePreserving q ρ (μ i) :=
    funext (PiLp.proj_apply (𝕜 := ℝ) 2 E i) ▸ PiLp.measurePreserving_eval_map_toLp 2 μ i
  have hn (x : PiLp 2 E) : ‖fderiv ℝ (fun y : PiLp 2 E ↦ f (q y)) x‖ = ‖fderiv ℝ f (q x)‖ :=
    PiLp.norm_fderiv_comp_proj (hf.differentiable (by simp) _)
  have hv := h.apply (fun x ↦ f (q x)) (hf.comp q.contDiff)
    (by simpa only [hn, Function.comp_def] using hdf.comp_measurePreserving hm)
    (hm.integrable_comp_of_integrable hf2) (hm.integrable_comp_of_integrable hf2log)
  have hent : entropy ρ (fun x ↦ f (q x) ^ 2) = entropy (μ i) (fun y ↦ f y ^ 2) := by
    simpa only [Function.comp_def] using
      hm.entropy_comp (g := fun y ↦ f y ^ 2) hf2.aestronglyMeasurable
  have he : (∫ x, ‖fderiv ℝ (fun y ↦ f (q y)) x‖ ^ 2 ∂ρ) = ∫ y, ‖fderiv ℝ f y‖ ^ 2 ∂μ i := by
    simp only [hn]
    rw [← hm.map_eq, integral_map hm.measurable.aemeasurable
      (hm.map_eq.symm ▸ hdf.integrable_sq.aestronglyMeasurable)]
  rwa [hent, he] at hv

end Marginals

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
      filter_upwards [TauCeti.ae_memLp_pi_update μ i hFL,
        TauCeti.ae_memLp_pi_update μ i (hGiL i)]
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
    simp only [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ sq_nonneg _),
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

omit [∀ i, BorelSpace (E i)] in
/-- Integrated slice bound for `LogSobolevInequality.piLp`: applying the `i`-th factor's
logarithmic Sobolev inequality to almost every coordinate slice of `f ∘ toLp 2` and integrating
over `Measure.pi μ` bounds the `i`-th average slice entropy by the `i`-th gradient coordinate
energy. -/
private theorem integral_entropy_update_le_of_logSobolevInequality [DecidableEq ι]
    (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)] {C : ℝ} {i : ι}
    (hμi : (μ i).LogSobolevInequality C) {f : PiLp 2 E → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg_int : Integrable (fun x ↦ f (WithLp.toLp 2 x) ^ 2) (Measure.pi μ))
    (hglog_int : Integrable
      (fun x ↦ f (WithLp.toLp 2 x) ^ 2 * Real.log (f (WithLp.toLp 2 x) ^ 2)) (Measure.pi μ))
    (hGiL : MemLp (fun x ↦ ‖gradient f (WithLp.toLp 2 x) i‖) 2 (Measure.pi μ)) :
    (∫ x, entropy (μ i) (fun y ↦ f (WithLp.toLp 2 (Function.update x i y)) ^ 2) ∂Measure.pi μ) ≤
      2 * C * ∫ x, ‖gradient f (WithLp.toLp 2 x) i‖ ^ 2 ∂Measure.pi μ := by
  let g : (∀ j, E j) → ℝ := fun x ↦ f (WithLp.toLp 2 x) ^ 2
  have hg0 : 0 ≤ᵐ[Measure.pi μ] g := .of_forall fun _ ↦ sq_nonneg _
  have hsec : ∀ᵐ x ∂Measure.pi μ,
      entropy (μ i) (fun y ↦ g (Function.update x i y)) ≤
        2 * C * ∫ y, ‖gradient f (WithLp.toLp 2 (Function.update x i y)) i‖ ^ 2 ∂μ i := by
    filter_upwards [ae_integrable_mul_log_pi_update μ i hg0 hg_int hglog_int,
      TauCeti.ae_memLp_pi_update μ i hGiL] with x ⟨_, hxg, hxglog⟩ hxG
    have hnorm (y : E i) :
        ‖fderiv ℝ (fun z ↦ f (WithLp.toLp 2 (Function.update x i z))) y‖ =
          ‖gradient f (WithLp.toLp 2 (Function.update x i y)) i‖ :=
      PiLp.norm_fderiv_update f x i y (hf.differentiable (by simp) _)
    simpa only [hnorm] using hμi.apply (fun z ↦ f (WithLp.toLp 2 (Function.update x i z)))
      (hf.comp (PiLp.contDiff_toLp.comp (contDiff_update ∞ x i)))
      (by simpa only [hnorm] using hxG) hxg hxglog
  have h_rhs_int := ((TauCeti.measurePreserving_update_prod_pi μ i).integrable_comp_of_integrable
    hGiL.integrable_sq).integral_prod_left.const_mul (2 * C)
  calc _ ≤ ∫ x, (2 * C * ∫ y, ‖gradient f (WithLp.toLp 2 (Function.update x i y)) i‖ ^ 2 ∂μ i)
          ∂Measure.pi μ :=
        integral_mono_ae (integrable_entropy_update_pi μ i hg0 hg_int hglog_int) h_rhs_int hsec
    _ = 2 * C * ∫ x, ‖gradient f (WithLp.toLp 2 x) i‖ ^ 2 ∂Measure.pi μ := by
        rw [integral_const_mul, TauCeti.integral_integral_update_pi μ i hGiL.integrable_sq]

/-- A finite Hilbert product of probability measures with a common nonnegative logarithmic Sobolev
constant satisfies the same logarithmic Sobolev inequality. -/
theorem LogSobolevInequality.piLp (μ : ∀ i, Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (C : ℝ≥0) (hμ : ∀ i, (μ i).LogSobolevInequality C) :
    ((Measure.pi μ).map (WithLp.toLp 2)).LogSobolevInequality C :=
  (LogSobolevInequality_def _ _).2 fun f hf hD hf2 hf2log ↦ by
  classical
  -- Pull `f²` and `gradient f` back from `PiLp 2 E` to `∀ i, E i` along `toLp 2`.
  let ρ := (Measure.pi μ).map (WithLp.toLp 2)
  let g : (∀ i, E i) → ℝ := fun x ↦ f (WithLp.toLp 2 x) ^ 2
  let G := gradient f ∘ WithLp.toLp 2
  have hm : MeasurePreserving (WithLp.toLp 2 : (∀ i, E i) → PiLp 2 E) (Measure.pi μ) ρ :=
    ⟨WithLp.measurable_toLp 2 _, rfl⟩
  have hg0 : 0 ≤ᵐ[Measure.pi μ] g := .of_forall fun _ ↦ sq_nonneg _
  have hg_int : Integrable g (Measure.pi μ) := hm.integrable_comp_of_integrable hf2
  have hglog_int := hm.integrable_comp_of_integrable hf2log
  have hGm : Measurable G := (TauCeti.measurable_gradient f).comp hm.measurable
  have hGL : MemLp (fun x ↦ ‖G x‖) 2 (Measure.pi μ) := by
    simpa only [G, Function.comp_def, TauCeti.norm_gradient_eq_norm_fderiv] using
      hD.comp_measurePreserving hm
  have hGiL (i : ι) : MemLp (fun x ↦ ‖G x i‖) 2 (Measure.pi μ) := hGL.mono'
    ((PiLp.proj 2 E i : PiLp 2 E →L[ℝ] E i).continuous.measurable.comp
      hGm).norm.aestronglyMeasurable
    (ae_of_all _ fun x ↦ by
      simpa only [Real.norm_of_nonneg (norm_nonneg _)] using PiLp.norm_apply_le (G x) i)
  -- Apply finite-product entropy subadditivity, bound each coordinate via `hμ i`, and reassemble
  -- the squared Hilbert norm of the gradient.
  calc entropy ρ (fun z ↦ f z ^ 2)
      = entropy (Measure.pi μ) g :=
        (hm.entropy_comp (hf.continuous.pow 2).aestronglyMeasurable).symm
    _ ≤ ∑ i, ∫ x, entropy (μ i) (fun y ↦ g (Function.update x i y)) ∂Measure.pi μ :=
        entropy_pi_le_sum μ hg0 hg_int hglog_int
    _ ≤ ∑ i, 2 * (C : ℝ) * ∫ x, ‖G x i‖ ^ 2 ∂Measure.pi μ :=
        Finset.sum_le_sum fun i _ ↦
          integral_entropy_update_le_of_logSobolevInequality μ (hμ i) hf hg_int hglog_int (hGiL i)
    _ = 2 * (C : ℝ) * ∫ x, (∑ i, ‖G x i‖ ^ 2) ∂Measure.pi μ := by
        rw [← Finset.mul_sum, ← integral_finsetSum _ fun i _ ↦ (hGiL i).integrable_sq]
    _ = 2 * (C : ℝ) * ∫ x, ‖G x‖ ^ 2 ∂Measure.pi μ := by
        congr 1; exact integral_congr_ae (.of_forall fun x ↦ (PiLp.norm_sq_eq_of_L2 E (G x)).symm)
    _ = 2 * (C : ℝ) * ∫ z, ‖fderiv ℝ f z‖ ^ 2 ∂ρ := by
        rw [← hm.map_eq, integral_map hm.measurable.aemeasurable
          (hm.map_eq.symm ▸ hD.integrable_sq.aestronglyMeasurable)]
        simp only [G, Function.comp_def, TauCeti.norm_gradient_eq_norm_fderiv]

/-- A finite Hilbert product satisfies the logarithmic Sobolev inequality with the maximum of its
nonnegative factor constants. For an empty family the maximum is zero. -/
theorem LogSobolevInequality.piLp_sup (μ : ∀ i, Measure (E i))
    [∀ i, IsProbabilityMeasure (μ i)] (C : ι → ℝ≥0)
    (hμ : ∀ i, (μ i).LogSobolevInequality (C i)) :
    ((Measure.pi μ).map (WithLp.toLp 2)).LogSobolevInequality (Finset.univ.sup C : ℝ≥0) := by
  classical
  exact LogSobolevInequality.piLp μ (Finset.univ.sup C) fun i ↦
    (hμ i).mono (by exact_mod_cast Finset.le_sup (f := C) (Finset.mem_univ i))

end MeasureTheory.Measure
