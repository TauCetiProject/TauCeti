/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Average
public import TauCeti.Analysis.BoundedVariation.TotalVariation
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Convex.Exhaustion
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré–Wirtinger inequality for functions of bounded variation

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, let `μ` be an additive Haar measure, and let `S ⊆ Ω` have positive measure. This
file proves the **Poincaré–Wirtinger inequality for functions of bounded variation**: every `u`
integrable on `Ω` satisfies

`∫_Ω |u - ⨍_S u| ≤ μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S) * |Du|(Ω)`,

where `|Du|(Ω)` is the variational total variation `TauCeti.totalVariationOn μ Ω u`, finite or
infinite. On a ball of radius `R`, with the mean taken over the ball, the constant is
`2 ^ (n + 1) * R`. No differentiability of `u` is assumed, and `S` need not be measurable. For a
`W^{1,1}` function the variation is the `L¹` norm of the weak gradient
(`TauCeti.HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm`), so this extends the `C¹`
inequality `TauCeti.lintegral_enorm_sub_setAverage_rpow_le_of_convex` at exponent one, with the
same constant.

The proof approximates `u` by mollification on convex open sets `U` whose closures are compact
subsets of `Ω`. A mollification by a bump of small radius is smooth on `U`, satisfies the `C¹`
inequality there, and has variation on `U` at most `|Du|(Ω)` by the convolution estimate
`ContDiffBump.totalVariationOn_normed_convolution_le`. Since the mollifications converge to `u`
in `L¹` on the closure of `U`, and their means over `S ∩ U` converge to that of `u`, the
inequality passes to `u` on `U`. An exhaustion of `Ω` by such sets
(`TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`) then gives it on `Ω`.

## Main results

* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex`: the inequality
  on a bounded convex open set.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball`: the inequality
  on a ball of radius `R`, with constant `2 ^ (n + 1) * R`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemma 7.16.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Metric Module Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal Convolution Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {S : Set E}

/-- The inequality on a convex open set `U` whose closure is a compact subset of `Ω`, with the
mean over a measurable `T ⊆ U` and the variation of `u` on `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_closure_subset {U T : Set E}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hUK : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (hu : LocallyIntegrableOn u Ω μ) (hTm : MeasurableSet T) (hT : T ⊆ U) (hT₀ : μ T ≠ 0) :
    ∫⁻ x in U, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam U ^ (finrank ℝ E + 1) / μ.real T) *
        totalVariationOn μ Ω u := by
  set K := closure U
  set C := ENNReal.ofReal (μ.real (ball 0 1) * diam U ^ (finrank ℝ E + 1) / μ.real T)
  have hUb : Bornology.IsBounded U := hUK.isBounded.subset subset_closure
  have hUfin : μ U ≠ ∞ := hUb.measure_lt_top.ne
  -- Replace `u` by the integrable function `w` equal to `u` on a closed `δ`-neighbourhood `L` of
  -- `K` inside `Ω`; it has the same variation as `u` on the open `δ`-neighbourhood `Ω'` of `K`.
  obtain ⟨δ, hδ, hLΩ⟩ := hUK.exists_cthickening_subset_open Ω.isOpen hUΩ
  set L := cthickening δ K
  have hL : IsCompact L := hUK.cthickening
  set w := L.indicator u
  have hw : Integrable w μ :=
    (hu.integrableOn_compact_subset hLΩ hL).integrable_indicator hL.measurableSet
  have hwL : ∀ x ∈ L, w x = u x := fun x hx => indicator_of_mem hx u
  have hUL : U ⊆ L := subset_closure.trans (self_subset_cthickening K)
  let Ω' : Opens E := ⟨thickening δ K, isOpen_thickening⟩
  have hΩ'L : (Ω' : Set E) ⊆ L := thickening_subset_cthickening δ K
  have hvarw : totalVariationOn μ Ω' w ≤ totalVariationOn μ Ω u := by
    have hae : w =ᵐ[μ.restrict Ω'] u := (ae_restrict_iff' isOpen_thickening.measurableSet).2
      (ae_of_all _ fun x hx => hwL x (hΩ'L hx))
    rw [totalVariationOn_congr_ae hae]
    exact totalVariationOn_mono (hΩ'L.trans hLΩ)
  -- Mollify `w` with normalized bumps of outer radius `1 / (n + 1)`.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set v : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] w
  have hsmooth (n : ℕ) : ContDiff ℝ 1 (v n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hw.locallyIntegrable
  -- The `L¹(K)` distance `e n` from `v n` to `w` tends to zero.
  set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in K, ‖v n x - w x‖ₑ ∂μ
  have he : Tendsto e atTop (𝓝 0) :=
    tendsto_setLIntegral_enorm_normed_convolution_sub hφ hw.locallyIntegrable hUK
  set M : ℝ≥0∞ := μ U / μ T
  have hM : M ≠ ∞ := ENNReal.div_ne_top hUfin hT₀
  -- Once the radius is below `δ`, the inequality holds for `u` up to an error `(1 + M) e n`.
  have hbound : ∀ᶠ n in atTop, ∫⁻ x in U, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      e n + M * e n + C * totalVariationOn μ Ω u := by
    filter_upwards [hφ.eventually (gt_mem_nhds hδ)] with n hn
    -- The smooth inequality for `v n` on `U`, whose variation there is at most `|Du|(Ω)`.
    have hvU : ∫⁻ x in U, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ ≤ C * totalVariationOn μ Ω u := by
      have h := lintegral_enorm_sub_setAverage_rpow_le_of_convex (μ := μ) hU hUc hUb
        (hsmooth n).contDiffOn hT hT₀ le_rfl
      simp only [ENNReal.rpow_one, Real.rpow_one] at h
      refine h.trans (mul_le_mul_right ?_ _)
      have hvar := ((hsmooth n).locallyLipschitz.locallyLipschitzOn (s := U)
        ).totalVariationOn_eq_setLIntegral_enorm_fderiv (μ := μ) (Ω := ⟨U, hU⟩)
      rw [Opens.coe_mk] at hvar
      rw [← hvar]
      refine ((φ n).totalVariationOn_normed_convolution_le
        (hw.locallyIntegrable.locallyIntegrableOn _) fun x hx => ?_).trans hvarw
      exact (closedBall_subset_ball hn).trans
        (ball_subset_thickening (subset_closure (s := U) hx) δ)
    -- The means over `T` differ by at most `e n / μ(T)`.
    have hab : ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ ≤ e n / μ T := by
      have hvT : IntegrableOn (v n) T μ :=
        ((hsmooth n).continuous.locallyIntegrable.integrableOn_isCompact hUK).mono_set
          (hT.trans subset_closure)
      have hwT : IntegrableOn w T μ := hw.integrableOn
      have haw : ⨍ y in T, u y ∂μ = ⨍ y in T, w y ∂μ :=
        setAverage_congr_fun hTm (ae_of_all _ fun y hy => (hwL y (hUL (hT hy))).symm)
      rw [haw, ← setAverage_fun_sub hvT hwT]
      refine (enorm_setAverage_le_setLAverage μ _ T).trans ?_
      rw [setLAverage_eq]
      gcongr
      exact lintegral_mono_set (hT.trans subset_closure)
    -- The triangle inequality through `v n` and its mean.
    have hdist : AEMeasurable (fun x => ‖v n x - w x‖ₑ) (μ.restrict U) :=
      ((hsmooth n).continuous.aestronglyMeasurable.sub hw.aestronglyMeasurable).enorm.restrict
    calc ∫⁻ x in U, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ
        ≤ ∫⁻ x in U, (‖v n x - w x‖ₑ + ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ) ∂μ := by
          refine setLIntegral_mono' hU.measurableSet fun x hx => ?_
          rw [← hwL x (hUL hx), ← enorm_neg (v n x - w x)]
          refine le_of_eq_of_le ?_
            ((enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _))
          congr 1
          ring
      _ = ∫⁻ x in U, ‖v n x - w x‖ₑ ∂μ + ∫⁻ x in U, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ * μ U := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left' hdist,
            setLIntegral_const]
      _ ≤ e n + C * totalVariationOn μ Ω u + e n / μ T * μ U := by
          gcongr
          exact lintegral_mono_set subset_closure
      _ = e n + M * e n + C * totalVariationOn μ Ω u := by
          simp only [M, div_eq_mul_inv]
          ring
  have hlim : Tendsto (fun n => e n + M * e n + C * totalVariationOn μ Ω u) atTop
      (𝓝 (0 + M * 0 + C * totalVariationOn μ Ω u)) :=
    (he.add (ENNReal.Tendsto.const_mul he (Or.inr hM))).add tendsto_const_nhds
  simpa using ge_of_tendsto hlim hbound

/-- The inequality for a measurable `S`, from the inequality on an exhaustion of `Ω` by convex
open sets with compact closures in `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_measurableSet
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hSm : MeasurableSet S) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        totalVariationOn μ Ω u := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Ω.isOpen hΩc
  have hVsub (n : ℕ) : V n ⊆ Ω := subset_closure.trans (hVclosure n)
  have hΩfin : μ Ω ≠ ∞ := hb.measure_lt_top.ne
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hΩfin (measure_mono hS)
  have hSpos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hSfin
  set K : ℝ := μ.real (ball (0 : E) 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1)
  set a := ⨍ y in S, u y ∂μ
  set T := totalVariationOn μ Ω u
  -- The measures of, and the means over, `S ∩ V n` converge to those over `S`.
  have hSVmono : Monotone fun n ↦ S ∩ V n := fun m n hmn ↦
    inter_subset_inter_right _ (hVmono hmn)
  have hSVunion : ⋃ n, S ∩ V n = S := by rw [← inter_iUnion, hVunion, inter_eq_left.2 hS]
  have hmeas : Tendsto (fun n ↦ μ.real (S ∩ V n)) atTop (𝓝 (μ.real S)) := by
    refine (ENNReal.tendsto_toReal hSfin).comp ?_
    simpa [hSVunion, Function.comp_def] using tendsto_measure_iUnion_atTop (μ := μ) hSVmono
  have havg : Tendsto (fun n ↦ ⨍ y in S ∩ V n, u y ∂μ) atTop (𝓝 a) := by
    simp only [a, setAverage_eq, smul_eq_mul]
    refine (hmeas.inv₀ hSpos.ne').mul ?_
    simpa [hSVunion] using tendsto_setIntegral_of_monotone₀
      (fun n ↦ (hSm.inter (hVopen n).measurableSet).nullMeasurableSet) hSVmono
      (by rw [hSVunion]; exact hu.mono_set hS)
  -- On `V n`, the deviation from `a` is the deviation from the mean over `S ∩ V n` up to an
  -- error `μ(Ω) |⨍_{S ∩ V n} u - a|`.
  have hpiece : ∀ᶠ n in atTop, ∫⁻ x in V n, ‖u x - a‖ₑ ∂μ ≤
      ENNReal.ofReal (K / μ.real (S ∩ V n)) * T + μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
    filter_upwards [hmeas.eventually (lt_mem_nhds hSpos)] with n hn
    have hn0 : μ (S ∩ V n) ≠ 0 := fun h => by simp [measureReal_def, h] at hn
    calc ∫⁻ x in V n, ‖u x - a‖ₑ ∂μ
        ≤ ∫⁻ x in V n, (‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ) ∂μ :=
          lintegral_mono fun x => by
            simpa only [sub_add_sub_cancel] using enorm_add_le (u x - ⨍ y in S ∩ V n, u y ∂μ)
              ((⨍ y in S ∩ V n, u y ∂μ) - a)
      _ = ∫⁻ x in V n, ‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ * μ (V n) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (K / μ.real (S ∩ V n)) * T +
            μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
          rw [mul_comm (‖_‖ₑ)]
          gcongr
          · refine (setLIntegral_enorm_sub_setAverage_le_of_closure_subset (hVopen n) (hVconv n)
              (hVcompact n) (hVclosure n) hu.locallyIntegrableOn
              (hSm.inter (hVopen n).measurableSet) inter_subset_right hn0).trans ?_
            gcongr
            simp only [K]
            gcongr
            exact diam_mono (hVsub n) hb
          · exact hVsub n
  -- The bounds converge to `C |Du|(Ω)`.
  have hlim : Tendsto (fun n => ENNReal.ofReal (K / μ.real (S ∩ V n)) * T +
      μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ) atTop
      (𝓝 (ENNReal.ofReal (K / μ.real S) * T + μ Ω * 0)) := by
    refine Tendsto.add ?_ (ENNReal.Tendsto.const_mul ?_ (Or.inr hΩfin))
    · rcases eq_or_ne K 0 with hK | hK
      · simp [hK]
      refine ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeas hSpos.ne')) (Or.inl ?_)
      exact (ENNReal.ofReal_pos.2 (div_pos (lt_of_le_of_ne (by positivity) hK.symm) hSpos)).ne'
    · have h0 : Tendsto (fun n ↦ (⨍ y in S ∩ V n, u y ∂μ) - a) atTop (𝓝 0) := by
        simpa using havg.sub_const a
      simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp h0
  rw [← hVunion, setLIntegral_iUnion_of_directed _ hVmono.directed_le]
  refine iSup_le fun k => ge_of_tendsto (by simpa using hlim) ?_
  filter_upwards [hpiece, eventually_ge_atTop k] with n hn hkn
  exact (lintegral_mono_set (hVmono hkn)).trans hn

/-- **The Poincaré–Wirtinger inequality for functions of bounded variation.** Let `Ω` be a bounded
convex open set in a finite-dimensional real inner product space of dimension `n`, and let
`S ⊆ Ω` have positive measure. Every `u` integrable on `Ω` deviates from its mean over `S` in
`L¹(Ω)` by at most `μ(B(0, 1)) * (diam Ω) ^ (n + 1) / μ(S)` times its total variation `|Du|(Ω)`,
finite or infinite. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        totalVariationOn μ Ω u := by
  -- Replace `S` by the measurable set `Ω ∩ toMeasurable μ S`, with the same restricted measure.
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono hS)
  set S' := (Ω : Set E) ∩ toMeasurable μ S
  have hres : μ.restrict S' = μ.restrict S := by
    rw [← Measure.restrict_restrict Ω.isOpen.measurableSet, Measure.restrict_toMeasurable hSfin,
      Measure.restrict_restrict Ω.isOpen.measurableSet, inter_eq_right.2 hS]
  have hμ : μ S' = μ S := by
    rw [← Measure.restrict_apply_univ, hres, Measure.restrict_apply_univ]
  have havg : ⨍ y in S', u y ∂μ = ⨍ y in S, u y ∂μ := by rw [hres]
  have hreal : μ.real S' = μ.real S := by rw [measureReal_def, measureReal_def, hμ]
  rw [← havg, ← hreal]
  exact setLIntegral_enorm_sub_setAverage_le_of_measurableSet hΩc hb hu
    (Ω.isOpen.measurableSet.inter (measurableSet_toMeasurable μ S)) inter_subset_left
    (hμ ▸ hS₀)

/-- **The Poincaré–Wirtinger inequality for functions of bounded variation on a ball.** If `Ω` is
the ball of radius `R > 0` about `c` in a finite-dimensional real inner product space of
dimension `n`, every `u` integrable on `Ω` deviates from its mean over `Ω` in `L¹(Ω)` by at most
`2 ^ (n + 1) * R` times its total variation `|Du|(Ω)`. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball {c : E} {R : ℝ}
    (hR : 0 < R) (hΩ : (Ω : Set E) = ball c R) (hu : IntegrableOn u (ball c R) μ) :
    ∫⁻ x in ball c R, ‖u x - ⨍ y in ball c R, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * R) * totalVariationOn μ Ω u := by
  have h := setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex (Ω := Ω)
    (S := ball c R) (hΩ ▸ convex_ball c R) (hΩ ▸ isBounded_ball) (hΩ ▸ hu) hΩ.symm.subset
    (measure_ball_pos μ c hR).ne'
  rw [hΩ] at h
  refine h.trans ?_
  gcongr
  exact μ.addHaar_real_ball_mul_diam_ball_pow_div_le c hR

end TauCeti
