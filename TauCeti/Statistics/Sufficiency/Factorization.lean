/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Experiments.Mixture
public import TauCeti.Statistics.Sufficiency.Basic

import Mathlib.Probability.Kernel.Composition.WithDensity
import Mathlib.Probability.Kernel.CondDistrib
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Neyman–Fisher factorization theorem and minimal sufficiency of the likelihood ratio

This file proves the Halmos–Savage / Neyman–Fisher factorization theorem for dominated parametric
families and deduces the minimal sufficiency of the likelihood ratio for countable families:

* `TauCeti.eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd`: if `P ≪ L` share a
  disintegrating kernel `K` given `T`, then `P = L.withDensity ((P.map T).rnDeriv (L.map T) ∘ T)`.
* `TauCeti.map_prodMk_withDensity_comp_eq_compProd`: tilting a measure `L` by a measurable density
  `q ∘ T` preserves any disintegrating kernel `K` given `T`.
* `TauCeti.IsSufficientStatistic.exists_factorization`: forward factorization (no standard Borel
  assumption needed).
* `TauCeti.isSufficientStatistic_of_exists_factorization`: converse factorization on a nonempty
  standard Borel space for any s-finite reference measure `μ`, using `ProbabilityTheory.condDistrib`
  under a Halmos–Savage dominating countable mixture.
* `TauCeti.isSufficientStatistic_iff_exists_factorization`: the Neyman–Fisher factorization theorem.
* `TauCeti.isMinimalSufficientStatistic_likelihoodRatio`: for a countable family of probability
  laws with densities `f θ` with respect to an s-finite measure `μ` on a nonempty standard Borel
  space `X`, if a reference density `f θ₀` is `μ`-almost everywhere positive, then the likelihood
  ratio `x ↦ (θ ↦ f θ x / f θ₀ x)` is minimal sufficient.

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

/-! ### Two-measure disintegration and density lemmas -/

/-- If `P ≪ L` share a disintegrating kernel `K` given a measurable map `T`, then `P` has
`L`-density `((P.map T).rnDeriv (L.map T)) ∘ T`. -/
theorem eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd {P L : Measure X} [SFinite L]
    {T : X → S} (hT : Measurable T) [(P.map T).HaveLebesgueDecomposition (L.map T)]
    {K : Kernel S X} [IsSFiniteKernel K] (hPL : P ≪ L)
    (hP : P.map (fun x ↦ (T x, x)) = P.map T ⊗ₘ K)
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) :
    P = L.withDensity ((P.map T).rnDeriv (L.map T) ∘ T) := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  let q : S → ℝ≥0∞ := (P.map T).rnDeriv (L.map T)
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hjoint : P.map (fun x ↦ (T x, x)) =
      (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x)) := by
    calc P.map (fun x ↦ (T x, x))
      _ = P.map T ⊗ₘ K := hP
      _ = (L.map T).withDensity q ⊗ₘ K := by
          rw [Measure.withDensity_rnDeriv_eq (P.map T) (L.map T) (hPL.map hT)]
      _ = (L.map T ⊗ₘ K).withDensity (fun p ↦ q p.1) := Measure.withDensity_compProd hq
      _ = (L.map (fun x ↦ (T x, x))).withDensity (fun p ↦ q p.1) := by rw [hL]
      _ = (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x)) :=
          (Measure.map_withDensity_comp hpair (hq.comp measurable_fst)).symm
  have hsnd := congrArg (Measure.map Prod.snd) hjoint
  rw [Measure.map_map measurable_snd hpair, Measure.map_map measurable_snd hpair] at hsnd
  simpa [Function.comp_def] using hsnd

/-- Reweighting a measure `L` by a measurable density `q ∘ T` factoring through `T` preserves any
disintegrating kernel `K` given `T`. -/
theorem map_prodMk_withDensity_comp_eq_compProd {L : Measure X} [SFinite L] {T : X → S}
    (hT : Measurable T) {K : Kernel S X} [IsSFiniteKernel K]
    (hL : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) {q : S → ℝ≥0∞} (hq : Measurable q) :
    (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x)) = (L.withDensity (q ∘ T)).map T ⊗ₘ K := by
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  calc (L.withDensity (q ∘ T)).map (fun x ↦ (T x, x))
    _ = (L.map (fun x ↦ (T x, x))).withDensity (fun p ↦ q p.1) :=
        Measure.map_withDensity_comp hpair (hq.comp measurable_fst)
    _ = (L.map T ⊗ₘ K).withDensity (fun p ↦ q p.1) := by rw [hL]
    _ = (L.map T).withDensity q ⊗ₘ K := (Measure.withDensity_compProd hq).symm
    _ = (L.withDensity (q ∘ T)).map T ⊗ₘ K := by rw [← Measure.map_withDensity_comp hT hq]

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
  have hpair : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ f hf
  let L : Measure X := countableMixture P θs
  have hLdis : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K := by
    calc L.map (fun x ↦ (T x, x))
      _ = countableMixture (fun θ ↦ (P θ).map (fun x ↦ (T x, x))) θs :=
          map_countableMixture hpair.aemeasurable
      _ = countableMixture (fun θ ↦ (P θ).map T ⊗ₘ K) θs := by
          simp_rw [hdis]
      _ = countableMixture (fun θ ↦ (P θ).map T) θs ⊗ₘ K :=
          (countableMixture_compProd (fun θ ↦ (P θ).map T) θs K).symm
      _ = L.map T ⊗ₘ K := by rw [← map_countableMixture hT.aemeasurable]
  have hh₀ : HasDensity L μ (fun x ↦ ∑' n, (mixtureWeight n).toReal * f (θs n) x) :=
    hasDensity_countableMixture hf θs
  let h : X → ℝ := fun x ↦ max (∑' n, (mixtureWeight n).toReal * f (θs n) x) 0
  have hh_dens : HasDensity L μ h := by
    refine hh₀.congr_ae (hh₀.measurable.max measurable_const) ?_
    filter_upwards [hh₀.ae_nonneg] with x hx
    exact (max_eq_left hx).symm
  let g : Θ → S → ℝ := fun θ s ↦ (((P θ).map T).rnDeriv (L.map T) s).toReal
  refine ⟨g, h,
    fun θ ↦ ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal, fun _ ↦ ENNReal.toReal_nonneg⟩,
    hh_dens.measurable, fun _ ↦ le_max_right _ _, fun θ ↦ ?_⟩
  have hPL_dens : HasDensity (P θ) L (fun x ↦ g θ (T x)) := by
    rw [hasDensity_def]
    refine ⟨((Measure.measurable_rnDeriv _ _).ennreal_toReal).comp hT,
      ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
    rw [eq_withDensity_rnDeriv_map_of_map_prodMk_eq_compProd hT (hdom θ) (hdis θ) hLdis]
    refine withDensity_congr_ae ?_
    have hlt : ∀ᵐ s ∂L.map T, ((P θ).map T).rnDeriv (L.map T) s < ∞ :=
      Measure.rnDeriv_lt_top _ _
    filter_upwards [ae_of_ae_map hT.aemeasurable hlt] with x hx
    exact (ENNReal.ofReal_toReal hx.ne).symm
  exact (hf θ).ae_eq (hPL_dens.trans hh_dens)

/-- Converse direction of the factorization theorem: on a nonempty standard Borel space `X`, if
the densities of a nonempty family of probability measures with respect to an s-finite measure `μ`
factor through a measurable statistic `T`, then `T` is sufficient. -/
theorem isSufficientStatistic_of_exists_factorization [StandardBorelSpace X] [Nonempty X]
    [Nonempty Θ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)] (μ : Measure X)
    [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ)) (T : X → S)
    (hT : Measurable T) (g : Θ → S → ℝ) (h : X → ℝ)
    (hg : ∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) (hhm : Measurable h)
    (hfac : ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x) :
    IsSufficientStatistic P T := by
  obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ f hf
  let L : Measure X := countableMixture P θs
  let K : Kernel S X := condDistrib id T L
  have hLdis : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
    (compProd_map_condDistrib hT.aemeasurable aemeasurable_id).symm
  let G : S → ℝ≥0∞ := fun s ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (g (θs n) s)
  have hGm : Measurable G :=
    Measurable.tsum fun n ↦ measurable_const.mul (hg (θs n)).1.ennreal_ofReal
  have hLhm : Measurable fun x ↦ G (T x) * ENNReal.ofReal (h x) :=
    (hGm.comp hT).mul hhm.ennreal_ofReal
  have hP_wd : ∀ θ, P θ = μ.withDensity
      (fun x ↦ ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x)) := by
    intro θ
    rw [(hf θ).eq_withDensity]
    refine withDensity_congr_ae ?_
    filter_upwards [hfac θ] with x hx
    rw [hx, ENNReal.ofReal_mul ((hg θ).2 (T x))]
  have hL_wd : L = μ.withDensity (fun x ↦ G (T x) * ENNReal.ofReal (h x)) := by
    have hPeq : P = fun θ ↦ μ.withDensity
        (fun x ↦ ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x)) := funext hP_wd
    dsimp only [L]
    rw [hPeq, countableMixture_withDensity μ
      (fun θ x ↦ ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x))
      (fun θ ↦ ((hg θ).1.comp hT).ennreal_ofReal.mul hhm.ennreal_ofReal) θs]
    congr 1 with x
    simp_rw [← mul_assoc]
    exact ENNReal.tsum_mul_right
  have hLlt : ∀ᵐ x ∂μ, G (T x) * ENNReal.ofReal (h x) < ∞ := by
    refine ae_lt_top hLhm ?_
    have huniv : ∫⁻ x, G (T x) * ENNReal.ofReal (h x) ∂μ = L univ := by
      rw [hL_wd, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [huniv]
    exact measure_ne_top _ _
  rw [isSufficientStatistic_def]
  refine ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
  let q : S → ℝ≥0∞ := fun s ↦ ENNReal.ofReal (g θ s) / G s
  have hqm : Measurable q := (hg θ).1.ennreal_ofReal.div hGm
  have hghm : Measurable fun x ↦ ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x) :=
    ((hg θ).1.comp hT).ennreal_ofReal.mul hhm.ennreal_ofReal
  have hZ : ∀ᵐ x ∂μ,
      G (T x) = 0 → ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x) = 0 := by
    let Z : Set X :=
      {x | G (T x) = 0} ∩ {x | 0 < ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x)}
    have hZm : MeasurableSet Z :=
      ((hGm.comp hT) (measurableSet_singleton 0)).inter (measurableSet_lt measurable_const hghm)
    have hLZ : L Z = 0 := by
      rw [hL_wd, withDensity_apply _ hZm]
      refine (setLIntegral_congr_fun hZm (g := fun _ ↦ 0) fun x hx ↦ ?_).trans lintegral_zero
      rw [hx.1, zero_mul]
    have hPZ : P θ Z = 0 := hdom θ hLZ
    rw [hP_wd θ, withDensity_apply _ hZm, lintegral_eq_zero_iff hghm] at hPZ
    have hμZ : μ Z = 0 := by
      have hsub : Z ⊆ {x | ¬ (ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x) = 0)} :=
        fun _ hx ↦ hx.2.ne'
      have hnull :
          μ.restrict Z {x | ¬ (ENNReal.ofReal (g θ (T x)) * ENNReal.ofReal (h x) = 0)} = 0 :=
        ae_iff.mp hPZ
      rw [Measure.restrict_apply' hZm] at hnull
      exact measure_mono_null (subset_inter hsub Subset.rfl) hnull
    rw [ae_iff]
    refine measure_mono_null (fun x hx ↦ ?_) hμZ
    obtain ⟨hG0, hne⟩ := not_imp.mp hx
    exact ⟨hG0, pos_iff_ne_zero.mpr hne⟩
  have hP_eq : P θ = L.withDensity (q ∘ T) := by
    rw [hP_wd θ, hL_wd, ← withDensity_mul _ hLhm (hqm.comp hT)]
    refine withDensity_congr_ae ?_
    filter_upwards [hLlt, hZ] with x hxlt hxZ
    simp only [Pi.mul_apply, Function.comp_apply, q]
    by_cases hh0 : ENNReal.ofReal (h x) = 0
    · simp [hh0]
    · by_cases hG0 : G (T x) = 0
      · rw [hxZ hG0, hG0, zero_mul, zero_mul]
      · have hGtop : G (T x) ≠ ∞ := by
          intro htop
          rw [htop, ENNReal.top_mul hh0] at hxlt
          exact lt_irrefl _ hxlt
        rw [mul_comm (G (T x)), mul_assoc, mul_comm (G (T x)),
          ENNReal.div_mul_cancel hG0 hGtop, mul_comm]
  rw [hP_eq]
  exact map_prodMk_withDensity_comp_eq_compProd hT hLdis hqm

/-- **The Neyman–Fisher factorization theorem** (Pfanzagl, Theorem 1.2.10 with Corollary 1.3.11;
Schervish, Theorem 2.21): for a nonempty family of probability measures with real densities `f θ`
with respect to an s-finite measure `μ` on a nonempty standard Borel space `X`, a measurable
statistic `T` is sufficient if and only if the densities factor `μ`-almost everywhere as
`f θ x = g θ (T x) * h x` with nonnegative measurable `g θ` and `h`. -/
theorem isSufficientStatistic_iff_exists_factorization [StandardBorelSpace X] [Nonempty X]
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
respect to an s-finite measure `μ` on a nonempty standard Borel space `X`, if a reference density
`f θ₀` is `μ`-almost everywhere positive, then the likelihood-ratio statistic
`x ↦ (θ ↦ f θ x / f θ₀ x)` is minimal sufficient. -/
theorem isMinimalSufficientStatistic_likelihoodRatio [StandardBorelSpace X] [Nonempty X]
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
