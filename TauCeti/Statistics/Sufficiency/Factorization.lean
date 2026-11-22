/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Experiments.Mixture
public import TauCeti.Statistics.Sufficiency.Basic

import Mathlib.Probability.Kernel.CondDistrib
import TauCeti.MeasureTheory.Measure.Decomposition.RNDeriv
import TauCeti.Probability.Kernel.Disintegration.Map

/-!
# The Neyman–Fisher factorization theorem and minimal sufficiency of the likelihood ratio

This file proves the Halmos–Savage / Neyman–Fisher factorization theorem for dominated parametric
families and deduces the minimal sufficiency of the likelihood ratio for countable families,
building on the generic two-measure disintegration/density lemmas in
`TauCeti.Probability.Kernel.Disintegration.Map`:

* `TauCeti.IsSufficientStatistic.exists_factorization`: forward factorization (no standard Borel
  assumption needed).
* `TauCeti.isSufficientStatistic_of_exists_factorization`: converse factorization on a standard
  Borel space for any s-finite reference measure `μ`, using `ProbabilityTheory.condDistrib` under
  a Halmos–Savage dominating countable mixture.
* `TauCeti.isSufficientStatistic_iff_exists_factorization`: the Neyman–Fisher factorization theorem.
* `TauCeti.isMinimalSufficientStatistic_likelihoodRatio`: for a countable family of probability
  laws with densities `f θ` with respect to an s-finite measure `μ` on a standard Borel space `X`,
  if a reference density `f θ₀` is `μ`-almost everywhere positive, then the likelihood ratio
  `x ↦ (θ ↦ f θ x / f θ₀ x)` is minimal sufficient.

## References

* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter (1994), Theorems 1.2.10 (p. 6) and
  1.4.4 (p. 14), Corollary 1.3.11 (p. 10).
* M. J. Schervish, *Theory of Statistics*, Springer (1995), Theorems 2.21 (p. 89) and 2.29 (p. 92).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace TauCeti

variable {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]

/-! ### The Neyman–Fisher factorization theorem -/

/-- Forward direction of the factorization theorem: if `T` is sufficient for a nonempty family of
probability measures with real densities `f θ` with respect to an s-finite measure `μ`, then the
densities factor as `f θ x = g θ (T x) * h x` `μ`-almost everywhere. -/
theorem IsSufficientStatistic.exists_factorization [Nonempty Θ] {P : Θ → Measure X}
    [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure X) [SFinite μ] (f : Θ → X → ℝ)
    (hf : ∀ θ, HasDensity (P θ) μ (f θ)) {T : X → S} (hs : IsSufficientStatistic P T) :
    ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  obtain ⟨hT, K, hK, hdis⟩ := isSufficientStatistic_def.mp hs
  obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ
    fun θ ↦ (hf θ).absolutelyContinuous
  let L : Measure X := countableMixture P θs
  have hLdis : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
    map_prodMk_countableMixture_eq_compProd hT fun n ↦ hdis (θs n)
  let h : X → ℝ := fun x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)).toReal
  have hh_dens : HasDensity L μ h := HasDensity.countableMixture fun n ↦ hf (θs n)
  let g : Θ → S → ℝ := fun θ s ↦ (((P θ).map T).rnDeriv (L.map T) s).toReal
  refine ⟨g, h,
    fun θ ↦ ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg⟩,
    hh_dens.measurable, fun _ ↦ ENNReal.toReal_nonneg, fun θ ↦ ?_⟩
  have hPL_dens : HasDensity (P θ) L (fun x ↦ g θ (T x)) := by
    refine ⟨((Measure.measurable_rnDeriv _ _).ennreal_toReal).comp hT,
      ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
    rw [eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd hT (hdom θ) (hdis θ) hLdis]
    exact withDensity_congr_ae
      (ae_of_ae_map hT.aemeasurable (Measure.ofReal_toReal_rnDeriv ((P θ).map T) (L.map T)).symm)
  exact (hf θ).ae_eq_of_sigmaFinite (hPL_dens.trans hh_dens)

/-- Converse direction of the factorization theorem: on a standard Borel space `X`, if the
densities of a nonempty family of probability measures with respect to an s-finite measure `μ`
factor through a measurable statistic `T`, then `T` is sufficient. -/
theorem isSufficientStatistic_of_exists_factorization [StandardBorelSpace X]
    [Nonempty Θ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure X)
    [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S)
    (hT : Measurable T) (g : Θ → S → ℝ) (h : X → ℝ)
    (hg : ∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) (hhm : Measurable h)
    (hfac : ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x) :
    IsSufficientStatistic P T := by
  have : Nonempty X := nonempty_of_isProbabilityMeasure (P (Classical.arbitrary Θ))
  -- Step 1: pick a Halmos–Savage dominating mixture `L` and take `K = condDistrib id T L`.
  obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ
    fun θ ↦ (hf θ).absolutelyContinuous
  let L : Measure X := countableMixture P θs
  let K : Kernel S X := condDistrib id T L
  have hLdis : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
    (compProd_map_condDistrib hT.aemeasurable aemeasurable_id).symm
  -- Step 2: compute the factorized `ℝ≥0∞`-densities of each `P θ` and of `L`.
  let G : S → ℝ≥0∞ := fun s ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (g (θs n) s)
  have hGm : Measurable G :=
    Measurable.tsum fun n ↦ measurable_const.mul (hg (θs n)).1.ennreal_ofReal
  have hP_wd : ∀ θ, P θ = μ.withDensity
      (fun x ↦ ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x)) := fun θ ↦ by
    rw [(hf θ).eq_withDensity]
    refine withDensity_congr_ae ?_
    filter_upwards [hfac θ] with x hx
    rw [hx, ENNReal.ofReal_mul ((hg θ).2 (T x))]
  have hL_wd : L = μ.withDensity (fun x ↦ G (T x) * ENNReal.ofReal (h x)) :=
    countableMixture_eq_withDensity_mul (fun n ↦ (hg (θs n)).1.ennreal_ofReal.comp hT)
      hhm.ennreal_ofReal fun n ↦ hP_wd (θs n)
  -- Step 3: express each `P θ` as a `T`-measurable tilt of `L`, preserving the disintegration `K`.
  rw [isSufficientStatistic_def]
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  have hP_eq : P θ = L.withDensity ((fun s ↦ ENNReal.ofReal (g θ s) / G s) ∘ T) :=
    eq_withDensity_div_of_eq_withDensity_mul ((hg θ).1.ennreal_ofReal.comp hT).aemeasurable
      (hGm.comp hT).aemeasurable hhm.ennreal_ofReal.aemeasurable (hdom θ) (hP_wd θ) hL_wd
  rw [hP_eq]
  exact map_prodMk_withDensity_comp_eq_compProd hT hLdis ((hg θ).1.ennreal_ofReal.div hGm)

/-- **The Neyman–Fisher factorization theorem** (Pfanzagl, Theorem 1.2.10 with Corollary 1.3.11;
Schervish, Theorem 2.21): for a nonempty family of probability measures with real densities `f θ`
with respect to an s-finite measure `μ` on a standard Borel space `X`, a measurable statistic `T` is
sufficient if and only if the densities factor `μ`-almost everywhere as `f θ x = g θ (T x) * h x`
with nonnegative measurable `g θ` and `h`. -/
theorem isSufficientStatistic_iff_exists_factorization [StandardBorelSpace X]
    [Nonempty Θ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure X)
    [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S)
    (hT : Measurable T) :
    IsSufficientStatistic P T ↔ ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x :=
  ⟨fun hs ↦ hs.exists_factorization μ f hf,
    fun ⟨g, h, hg, hhm, _, hfac⟩ ↦
      isSufficientStatistic_of_exists_factorization P μ f hf T hT g h hg hhm hfac⟩

/-! ### Minimal sufficiency of the likelihood ratio -/

/-- **Minimal sufficiency of the likelihood ratio** (Schervish, Theorem 2.29; Pfanzagl,
Theorem 1.4.4): for a countable family of probability measures with real densities `f θ` with
respect to an s-finite measure `μ` on a standard Borel space `X`, if a reference density `f θ₀` is
`μ`-almost everywhere positive, then the likelihood-ratio statistic `x ↦ (θ ↦ f θ x / f θ₀ x)` is
minimal sufficient. -/
theorem isMinimalSufficientStatistic_likelihoodRatio [StandardBorelSpace X]
    [Countable Θ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure X)
    [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    (θ₀ : Θ) (hpos : ∀ᵐ x ∂μ, 0 < f θ₀ x) :
    IsMinimalSufficientStatistic P (fun x θ ↦ f θ x / f θ₀ x) := by
  have : Nonempty Θ := ⟨θ₀⟩
  let T : X → (Θ → ℝ) := fun x θ ↦ f θ x / f θ₀ x
  have hT : Measurable T :=
    measurable_pi_iff.mpr fun θ ↦ (hf θ).measurable.div (hf θ₀).measurable
  have hTsuff : IsSufficientStatistic P T := by
    refine isSufficientStatistic_of_exists_factorization P μ f hf T hT
      (fun θ r ↦ max (r θ) 0) (f θ₀)
      (fun θ ↦ ⟨(measurable_pi_apply θ).max measurable_const, fun _ ↦ le_max_right _ _⟩)
      (hf θ₀).measurable fun θ ↦ ?_
    filter_upwards [(hf θ).ae_nonneg, hpos] with x hfx hf0
    have hdiv_nn : 0 ≤ f θ x / f θ₀ x := div_nonneg hfx hf0.le
    rw [max_eq_left hdiv_nn, div_mul_cancel₀ _ hf0.ne']
  rw [isMinimalSufficientStatistic_def]
  refine ⟨hTsuff, fun S' _ U hU ↦ ?_⟩
  obtain ⟨g, h, hg, _, _, hfac⟩ := hU.exists_factorization μ f hf
  refine ⟨fun s' θ ↦ g θ s' / g θ₀ s',
    measurable_pi_iff.mpr fun θ ↦ (hg θ).1.div (hg θ₀).1, fun θ ↦ ?_⟩
  have hall_μ : ∀ᵐ x ∂μ, ∀ θ', f θ' x = g θ' (U x) * h x := ae_all_iff.mpr hfac
  filter_upwards [(hf θ).absolutelyContinuous.ae_le hall_μ,
    (hf θ).absolutelyContinuous.ae_le hpos] with x hx hf0
  ext θ'
  have hh_ne : h x ≠ 0 := right_ne_zero_of_mul (hx θ₀ ▸ hf0.ne')
  simp only [Function.comp_apply, hx θ', hx θ₀, mul_div_mul_right _ _ hh_ne]

end TauCeti
