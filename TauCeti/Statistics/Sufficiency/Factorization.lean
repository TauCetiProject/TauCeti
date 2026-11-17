/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Statistics.Sufficiency.Basic
import Mathlib.Probability.Kernel.Composition.WithDensity
import TauCeti.MeasureTheory.Measure.WithDensity

/-!
# The Fisher–Neyman factorization theorem and minimal sufficiency of likelihood ratios

For a dominated family of probability measures with real densities `f θ` against a σ-finite
reference measure `μ`, a measurable statistic `T : X → S` is sufficient if and only if each density
factors `μ`-almost everywhere as `f θ x = g θ (T x) * h x` with measurable nonnegative factors
`g θ` and `h`.

The forward direction needs no topological or standard-Borel assumption on the sample space `X`:
two measures `P ≪ L` disintegrated along `T` by a common kernel satisfy
`P = L.withDensity (((P.map T).rnDeriv (L.map T)) ∘ T)`, and applying this to a Halmos–Savage
dominating countable mixture `L` yields `g θ` as the real Radon–Nikodym derivative of `(P θ).map T`
with respect to `L.map T` and `h` as the mixed density of `L`.

The converse uses `[StandardBorelSpace X] [Nonempty X]` to construct the common disintegrating
kernel as `condDistrib id T L` under a Halmos–Savage dominating countable mixture `L`, and requires
only `[SFinite μ]`.

For a countable family with a reference parameter `θ₀` whose density is `μ`-almost everywhere
strictly positive, combining both directions shows that the likelihood-ratio statistic
`x ↦ (θ ↦ f θ x / f θ₀ x)` is minimal sufficient.

## Main results

* `TauCeti.eq_withDensity_rnDeriv_map_of_map_prod_eq_compProd`: if `P ≪ L` share a disintegrating
  kernel along `T`, then `P = L.withDensity (((P.map T).rnDeriv (L.map T)) ∘ T)`.
* `TauCeti.map_prod_eq_compProd_of_eq_withDensity_comp`: if `P = L.withDensity (r ∘ T)` and `K`
  disintegrates `L` along `T`, then `K` also disintegrates `P` along `T`.
* `TauCeti.exists_factorization_of_isSufficientStatistic`: necessity of the Fisher–Neyman
  factorization, without `[StandardBorelSpace X]` or `[Nonempty X]`.
* `TauCeti.isSufficientStatistic_of_exists_factorization`: sufficiency of the Fisher–Neyman
  factorization on a nonempty standard Borel space for any s-finite reference measure.
* `TauCeti.isSufficientStatistic_iff_exists_factorization`: the Fisher–Neyman factorization theorem.
* `TauCeti.isMinimalSufficientStatistic_likelihoodRatio`: minimal sufficiency of the likelihood
  ratio statistic for a countable family.

## References

* P. R. Halmos and L. J. Savage, *Application of the Radon–Nikodym theorem to the theory of
  sufficient statistics*, Ann. Math. Statist. 20 (1949), 225–241, Theorem 1.
* J. Pfanzagl, *Parametric Statistical Theory*, de Gruyter, 1994, Theorems 1.2.10 and 1.4.4.
* M. J. Schervish, *Theory of Statistics*, Springer, 1995, Theorems 2.21 and 2.29.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open scoped ENNReal

namespace TauCeti

section Factorization

variable {Θ X S : Type*} [MeasurableSpace X] [MeasurableSpace S]

/-- If `P ≪ L` share a disintegrating kernel `K` along `T`, then `P` has `L`-density given by the
Radon–Nikodym derivative of `P.map T` with respect to `L.map T`, composed with `T`. -/
theorem eq_withDensity_rnDeriv_map_of_map_prod_eq_compProd
    {P L : Measure X} [SFinite L] {T : X → S} (hT : Measurable T)
    [Measure.HaveLebesgueDecomposition (P.map T) (L.map T)]
    {K : Kernel S X} [IsSFiniteKernel K]
    (hPL : P ≪ L)
    (hPK : P.map (fun x ↦ (T x, x)) = P.map T ⊗ₘ K)
    (hLK : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) :
    P = L.withDensity (((P.map T).rnDeriv (L.map T)) ∘ T) := by
  let g : S → ℝ≥0∞ := (P.map T).rnDeriv (L.map T)
  have hg : Measurable g := Measure.measurable_rnDeriv _ _
  have hPT : P.map T ≪ L.map T := hPL.map hT
  have hprod_meas : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  have hprod : P.map (fun x ↦ (T x, x)) = (L.withDensity (g ∘ T)).map (fun x ↦ (T x, x)) := by
    calc P.map (fun x ↦ (T x, x))
        = P.map T ⊗ₘ K := hPK
      _ = (L.map T).withDensity g ⊗ₘ K := by rw [Measure.withDensity_rnDeriv_eq _ _ hPT]
      _ = (L.map T ⊗ₘ K).withDensity (fun p : S × X ↦ g p.1) := Measure.withDensity_compProd hg
      _ = (L.map (fun x ↦ (T x, x))).withDensity (g ∘ Prod.fst) := by rw [← hLK]; rfl
      _ = (L.withDensity (g ∘ T)).map (fun x ↦ (T x, x)) :=
          (Measure.map_withDensity_comp hprod_meas (hg.comp measurable_fst)).symm
  have hsnd := congrArg (Measure.map Prod.snd) hprod
  rw [Measure.map_map measurable_snd hprod_meas, Measure.map_map measurable_snd hprod_meas] at hsnd
  simpa only [Function.comp_def, Measure.map_id'] using hsnd

/-- If `P = L.withDensity (r ∘ T)` with `r` measurable and `K` disintegrates `L` along `T`, then
`K` also disintegrates `P` along `T`. -/
theorem map_prod_eq_compProd_of_eq_withDensity_comp
    {P L : Measure X} [SFinite L] {T : X → S} (hT : Measurable T)
    {K : Kernel S X} [IsSFiniteKernel K]
    {r : S → ℝ≥0∞} (hr : Measurable r)
    (hPL : P = L.withDensity (r ∘ T))
    (hLK : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K) :
    P.map (fun x ↦ (T x, x)) = P.map T ⊗ₘ K := by
  have hprod_meas : Measurable fun x ↦ (T x, x) := hT.prodMk measurable_id
  calc P.map (fun x ↦ (T x, x))
      = (L.withDensity (r ∘ T)).map (fun x ↦ (T x, x)) := by rw [hPL]
    _ = (L.map (fun x ↦ (T x, x))).withDensity (r ∘ Prod.fst) :=
        Measure.map_withDensity_comp hprod_meas (hr.comp measurable_fst)
    _ = (L.map T ⊗ₘ K).withDensity (fun p : S × X ↦ r p.1) := by rw [hLK]; rfl
    _ = (L.map T).withDensity r ⊗ₘ K := (Measure.withDensity_compProd hr).symm
    _ = (L.withDensity (r ∘ T)).map T ⊗ₘ K := by rw [Measure.map_withDensity_comp hT hr]
    _ = P.map T ⊗ₘ K := by rw [hPL]

/-- **Forward Fisher–Neyman factorization**: if `T` is sufficient for a family of probability
measures having real densities `f θ` against a σ-finite measure `μ`, then `f θ` factors `μ`-almost
everywhere as `g θ (T x) * h x` with measurable nonnegative factors. No `StandardBorelSpace` or
`Nonempty` hypothesis is required. -/
theorem exists_factorization_of_isSufficientStatistic
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (μ : Measure X) [SigmaFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    {T : X → S} (hTsuff : IsSufficientStatistic P T) :
    ∃ (g : Θ → S → ℝ) (h : X → ℝ),
      (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
      ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x := by
  by_cases hΘ : Nonempty Θ
  · obtain ⟨K, hKm, hK⟩ := hTsuff.exists_kernel
    have hT : Measurable T := hTsuff.measurable
    obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ f hf
    let L : Measure X := countableMixture P θs
    have hLK : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
      countableMixture_map_prod_eq_compProd P hT hK θs
    let h : X → ℝ := fun x ↦ (∑' n, mixtureWeight n * ENNReal.ofReal (f (θs n) x)).toReal
    have hh_dens : HasDensity L μ h := hasDensity_countableMixture P μ f hf θs
    let g : Θ → S → ℝ := fun θ s ↦ (((P θ).map T).rnDeriv (L.map T) s).toReal
    refine ⟨g, h, fun θ ↦ ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal,
      fun _ ↦ ENNReal.toReal_nonneg⟩, hh_dens.measurable, fun _ ↦ ENNReal.toReal_nonneg,
      fun θ ↦ ?_⟩
    have hPL_dens : HasDensity (P θ) L (g θ ∘ T) := by
      have hPθ : P θ = L.withDensity (((P θ).map T).rnDeriv (L.map T) ∘ T) :=
        eq_withDensity_rnDeriv_map_of_map_prod_eq_compProd hT (hdom θ) (hK θ) hLK
      have hlt_map : ∀ᵐ s ∂L.map T, ((P θ).map T).rnDeriv (L.map T) s < ∞ :=
        Measure.rnDeriv_lt_top ((P θ).map T) (L.map T)
      have hlt : ∀ᵐ x ∂L, ((P θ).map T).rnDeriv (L.map T) (T x) < ∞ :=
        ae_of_ae_map hT.aemeasurable hlt_map
      refine hasDensity_iff.mpr ⟨(Measure.measurable_rnDeriv _ _).ennreal_toReal.comp hT,
        ae_of_all _ fun _ ↦ ENNReal.toReal_nonneg, ?_⟩
      rw [hPθ]
      refine withDensity_congr_ae ?_
      filter_upwards [hlt] with x hx
      exact (ENNReal.ofReal_toReal hx.ne).symm
    exact (hf θ).ae_eq_of_hasDensity (hPL_dens.trans hh_dens)
  · refine ⟨fun θ ↦ False.elim (hΘ ⟨θ⟩), fun _ ↦ 0, fun θ ↦ False.elim (hΘ ⟨θ⟩),
      measurable_const, fun _ ↦ le_rfl, fun θ ↦ False.elim (hΘ ⟨θ⟩)⟩

/-- If `P` has real `μ`-density factoring `μ`-almost everywhere as `g (T x) * h x`, `L` is a finite
measure with `μ`-density `G (T x) * ENNReal.ofReal (h x)`, and `P ≪ L`, then
`P = L.withDensity ((fun s ↦ ENNReal.ofReal (g s) / G s) ∘ T)`. -/
theorem eq_withDensity_div_comp_of_factorization
    {P L μ : Measure X} [IsFiniteMeasure L] {T : X → S} (hT : Measurable T)
    {f h : X → ℝ} {g : S → ℝ} {G : S → ℝ≥0∞}
    (hf : HasDensity P μ f) (hg_meas : Measurable g) (hg_nonneg : ∀ s, 0 ≤ g s)
    (hh_meas : Measurable h) (hh_nonneg : ∀ᵐ x ∂μ, 0 ≤ h x)
    (hG_meas : Measurable G)
    (hfac : ∀ᵐ x ∂μ, f x = g (T x) * h x)
    (hL_eq : L = μ.withDensity (fun x ↦ G (T x) * ENNReal.ofReal (h x)))
    (hPL : P ≪ L) :
    P = L.withDensity ((fun s ↦ ENNReal.ofReal (g s) / G s) ∘ T) := by
  have hGh_meas : Measurable fun x ↦ G (T x) * ENNReal.ofReal (h x) :=
    (hG_meas.comp hT).mul hh_meas.ennreal_ofReal
  have hr_meas : Measurable fun s ↦ ENNReal.ofReal (g s) / G s :=
    hg_meas.ennreal_ofReal.div hG_meas
  have hG_lt_top : ∀ᵐ x ∂μ, G (T x) * ENNReal.ofReal (h x) < ∞ := by
    refine ae_lt_top hGh_meas ?_
    have huniv : ∫⁻ x, G (T x) * ENNReal.ofReal (h x) ∂μ = L Set.univ := by
      rw [hL_eq, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
    rw [huniv]
    exact measure_ne_top L Set.univ
  have hzero_null : ∀ᵐ x ∂μ, G (T x) = 0 → ENNReal.ofReal (f x) = 0 := by
    let N : Set X := {x | G (T x) = 0}
    have hN_meas : MeasurableSet N := (hG_meas.comp hT) (measurableSet_singleton 0)
    have hLN : L N = 0 := by
      rw [hL_eq, withDensity_apply _ hN_meas, lintegral_eq_zero_iff hGh_meas,
        Filter.EventuallyEq, ae_restrict_iff' hN_meas]
      exact ae_of_all _ fun x hx ↦ by simp [N] at hx; simp [hx]
    have hPN : P N = 0 := hPL hLN
    rw [hf.eq_withDensity, withDensity_apply _ hN_meas,
      lintegral_eq_zero_iff hf.measurable.ennreal_ofReal, Filter.EventuallyEq,
      ae_restrict_iff' hN_meas] at hPN
    exact hPN
  rw [hL_eq, ← withDensity_mul μ hGh_meas (hr_meas.comp hT), hf.eq_withDensity]
  refine withDensity_congr_ae ?_
  filter_upwards [hfac, hh_nonneg, hG_lt_top, hzero_null] with x hfx hhx hlt hzero
  rw [Pi.mul_apply, Function.comp_apply]
  by_cases hh0 : h x = 0
  · simp [hfx, hh0]
  · have hh_pos : 0 < h x := lt_of_le_of_ne hhx (Ne.symm hh0)
    have hof_pos : ENNReal.ofReal (h x) ≠ 0 := (ENNReal.ofReal_pos.mpr hh_pos).ne'
    by_cases hG0 : G (T x) = 0
    · rw [hzero hG0, hG0, zero_mul, zero_mul]
    · have hG_ne_top : G (T x) ≠ ∞ := by
        intro htop
        rw [htop, ENNReal.top_mul hof_pos] at hlt
        exact lt_irrefl ∞ hlt
      calc ENNReal.ofReal (f x)
          = ENNReal.ofReal (g (T x)) * ENNReal.ofReal (h x) := by
            rw [hfx, ENNReal.ofReal_mul (hg_nonneg _)]
        _ = (G (T x) * (ENNReal.ofReal (g (T x)) / G (T x))) * ENNReal.ofReal (h x) := by
            rw [ENNReal.mul_div_cancel hG0 hG_ne_top]
        _ = G (T x) * ENNReal.ofReal (h x) * (ENNReal.ofReal (g (T x)) / G (T x)) :=
            mul_right_comm _ _ _

/-- **Converse Fisher–Neyman factorization**: on a nonempty standard Borel space, if the real
densities `f θ` of a family of probability measures against an s-finite measure `μ` factor
`μ`-almost everywhere as `g θ (T x) * h x` with measurable nonnegative factors, then `T` is
sufficient. -/
theorem isSufficientStatistic_of_exists_factorization [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (μ : Measure X) [SFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    {T : X → S} (hT : Measurable T)
    {g : Θ → S → ℝ} {h : X → ℝ}
    (hg_meas : ∀ θ, Measurable (g θ)) (hg_nonneg : ∀ θ s, 0 ≤ g θ s)
    (hh_meas : Measurable h) (hh_nonneg : ∀ᵐ x ∂μ, 0 ≤ h x)
    (hfac : ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x) :
    IsSufficientStatistic P T := by
  by_cases hΘ : Nonempty Θ
  · obtain ⟨θs, hdom⟩ := exists_absolutelyContinuous_countableMixture P μ f hf
    let L : Measure X := countableMixture P θs
    let K : Kernel S X := condDistrib (id : X → X) T L
    let G : S → ℝ≥0∞ := fun s ↦ ∑' n, mixtureWeight n * ENNReal.ofReal (g (θs n) s)
    have hG_meas : Measurable G :=
      Measurable.tsum fun n ↦ measurable_const.mul (hg_meas (θs n)).ennreal_ofReal
    have hL_eq : L = μ.withDensity (fun x ↦ G (T x) * ENNReal.ofReal (h x)) := by
      have hmix := countableMixture_eq_withDensity P μ (fun θ x ↦ ENNReal.ofReal (f θ x))
        (fun θ ↦ (hf θ).measurable.ennreal_ofReal) (fun θ ↦ (hf θ).eq_withDensity) θs
      refine hmix.trans (withDensity_congr_ae ?_)
      filter_upwards [ae_all_iff.mpr fun n ↦ hfac (θs n)] with x hx
      have hterm : ∀ n, mixtureWeight n * ENNReal.ofReal (f (θs n) x) =
          mixtureWeight n * ENNReal.ofReal (g (θs n) (T x)) * ENNReal.ofReal (h x) := fun n ↦ by
        rw [hx n, ENNReal.ofReal_mul (hg_nonneg (θs n) _), mul_assoc]
      simp_rw [hterm, ENNReal.tsum_mul_right]
      rfl
    have hLK : L.map (fun x ↦ (T x, x)) = L.map T ⊗ₘ K :=
      (compProd_map_condDistrib hT.aemeasurable aemeasurable_id).symm
    refine isSufficientStatistic_iff.mpr ⟨hT, K, inferInstance, fun θ ↦ ?_⟩
    have hPθ_eq : P θ = L.withDensity ((fun s ↦ ENNReal.ofReal (g θ s) / G s) ∘ T) :=
      eq_withDensity_div_comp_of_factorization hT (hf θ) (hg_meas θ) (hg_nonneg θ)
        hh_meas hh_nonneg hG_meas (hfac θ) hL_eq (hdom θ)
    exact map_prod_eq_compProd_of_eq_withDensity_comp hT
      ((hg_meas θ).ennreal_ofReal.div hG_meas) hPθ_eq hLK
  · refine isSufficientStatistic_iff.mpr
      ⟨hT, Kernel.const S (Measure.dirac (Classical.arbitrary X)), inferInstance,
        fun θ ↦ False.elim (hΘ ⟨θ⟩)⟩

/-- **Fisher–Neyman factorization theorem**: on a nonempty standard Borel space, a measurable
statistic `T` is sufficient for a family of probability measures with real densities `f θ` against
a σ-finite reference measure `μ` iff each density factors `μ`-almost everywhere as
`g θ (T x) * h x` with measurable nonnegative factors `g θ` and `h`. -/
theorem isSufficientStatistic_iff_exists_factorization [StandardBorelSpace X] [Nonempty X]
    (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (μ : Measure X) [SigmaFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    (T : X → S) (hT : Measurable T) :
    IsSufficientStatistic P T ↔
      ∃ (g : Θ → S → ℝ) (h : X → ℝ),
        (∀ θ, Measurable (g θ) ∧ ∀ s, 0 ≤ g θ s) ∧ Measurable h ∧ (∀ x, 0 ≤ h x) ∧
        ∀ θ, ∀ᵐ x ∂μ, f θ x = g θ (T x) * h x :=
  ⟨exists_factorization_of_isSufficientStatistic P μ f hf,
    fun ⟨_, _, hg, hh, hh₀, hfac⟩ ↦
      isSufficientStatistic_of_exists_factorization P μ f hf hT
        (fun θ ↦ (hg θ).1) (fun θ ↦ (hg θ).2) hh (ae_of_all _ hh₀) hfac⟩

/-- **Minimal sufficiency of the likelihood ratio**: for a countable family of probability measures
with real densities `f θ` against a σ-finite reference measure `μ`, if the reference density
`f θ₀` is `μ`-almost everywhere strictly positive, then the likelihood-ratio statistic
`x ↦ (θ ↦ f θ x / f θ₀ x)` is minimal sufficient. -/
theorem isMinimalSufficientStatistic_likelihoodRatio [StandardBorelSpace X] [Nonempty X]
    [Countable Θ] (P : Θ → Measure X) [∀ θ, IsProbabilityMeasure (P θ)]
    (μ : Measure X) [SigmaFinite μ] (f : Θ → X → ℝ) (hf : ∀ θ, HasDensity (P θ) μ (f θ))
    (θ₀ : Θ) (hpos : ∀ᵐ x ∂μ, 0 < f θ₀ x) :
    IsMinimalSufficientStatistic P (fun x θ ↦ f θ x / f θ₀ x) := by
  let T : X → (Θ → ℝ) := fun x θ ↦ f θ x / f θ₀ x
  have hT_meas : Measurable T :=
    measurable_pi_iff.mpr fun θ ↦ (hf θ).measurable.div (hf θ₀).measurable
  have hT_suff : IsSufficientStatistic P T := by
    refine isSufficientStatistic_of_exists_factorization P μ f hf hT_meas
      (g := fun θ q ↦ max (q θ) 0) (h := fun x ↦ max (f θ₀ x) 0)
      (fun θ ↦ (measurable_pi_apply θ).max measurable_const) (fun _ _ ↦ le_max_right _ _)
      ((hf θ₀).measurable.max measurable_const) (ae_of_all _ fun _ ↦ le_max_right _ _)
      (fun θ ↦ ?_)
    filter_upwards [(hf θ).ae_nonneg, hpos] with x hfx hf0
    have hdiv_nn : 0 ≤ f θ x / f θ₀ x := div_nonneg hfx hf0.le
    rw [max_eq_left hdiv_nn, max_eq_left hf0.le, div_mul_cancel₀ _ hf0.ne']
  refine isMinimalSufficientStatistic_iff.mpr ⟨hT_suff, fun S' _ U hU ↦ ?_⟩
  obtain ⟨g, h, hg, _, _, hfac⟩ :=
    exists_factorization_of_isSufficientStatistic P μ f hf hU
  let φ : S' → (Θ → ℝ) := fun s θ ↦ g θ s / g θ₀ s
  have hφ_meas : Measurable φ :=
    measurable_pi_iff.mpr fun θ ↦ (hg θ).1.div (hg θ₀).1
  refine ⟨φ, hφ_meas, fun θ' ↦ ?_⟩
  have hae_μ : T =ᵐ[μ] φ ∘ U := by
    filter_upwards [ae_all_iff.mpr hfac, hpos] with x hx hf0
    have hh_ne : h x ≠ 0 := by
      intro hh0
      have h0 : f θ₀ x = 0 := by rw [hx θ₀, hh0, mul_zero]
      exact hf0.ne' h0
    funext θ
    simp only [T, φ, Function.comp_apply, hx θ, hx θ₀]
    exact mul_div_mul_right (g θ (U x)) (g θ₀ (U x)) hh_ne
  exact (hf θ').absolutelyContinuous.ae_eq hae_μ

end Factorization

end TauCeti
