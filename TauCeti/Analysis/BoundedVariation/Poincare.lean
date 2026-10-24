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
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré–Wirtinger inequality for functions of bounded variation

Let `Ω` be a bounded convex open subset of a finite-dimensional real inner product space `E` of
dimension `n`, let `μ` be an additive Haar measure with `ω = μ(B(0, 1))`, and let `S ⊆ Ω` have
positive measure. This file proves the **Poincaré–Wirtinger inequality for functions of bounded
variation**, localized to an arbitrary subset `A ⊆ Ω`: every `u` integrable on `Ω` satisfies

`∫_A |u - ⨍_S u| ≤ ω ^ (1 - 1/n) (diam Ω) ^ n / μ(S) μ(A) ^ (1/n) |Du|(Ω)`,

where `|Du|(Ω)` is the variational total variation `TauCeti.totalVariationOn μ Ω u`, finite or
infinite. The factor `μ(A) ^ (1/n)` makes the inequality scale-invariant: it is a weak-type
`L^{n/(n-1)}` Poincaré inequality, implied by the strong `L^{n/(n-1)}` Sobolev–Poincaré inequality
through Hölder's inequality. Its indicator case is the relative isoperimetric inequality
(`TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`).

Taking `A = Ω` and bounding `μ(Ω) ≤ ω (diam Ω) ^ n` gives the `L¹` inequality

`∫_Ω |u - ⨍_S u| ≤ ω (diam Ω) ^ (n + 1) / μ(S) |Du|(Ω)`.

On a ball of radius `R`, with the mean taken over the ball, the constant is `2 ^ (n + 1) * R`. No
differentiability of `u` is assumed, and `S` need not be measurable. For a `W^{1,1}` function the
variation is the `L¹` norm of the weak gradient
(`TauCeti.HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm`), so this extends the `C¹`
inequality `TauCeti.lintegral_enorm_sub_setAverage_rpow_le_of_convex` at exponent one, with the
same constant.

The `C¹` case (`TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex`)
integrates the Riesz potential estimate over `A` and bounds the Riesz kernel on `A` by its value
on a ball of the same measure. It passes to `u` through mollifications on convex open sets with
compact closures in `Ω`, which converge in `L¹` and do not increase the variation
(`TauCeti.exists_seq_contDiff_tendsto_setLIntegral_enorm_sub_totalVariationOn_le`), and through an
exhaustion of `Ω` by such sets
(`TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`).

## Main results

* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex`:
  the localized inequality on a bounded convex open set.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex`: the `L¹`
  inequality on a bounded convex open set.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball`: the `L¹`
  inequality on a ball of radius `R`, with constant `2 ^ (n + 1) * R`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Remark 3.50.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Lemmas 7.12 and 7.16.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Metric Module Set TopologicalSpace
open scoped ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {S A : Set E}

/-- The inequality on a convex open set `U` whose closure is a compact subset of `Ω`, with the
mean over a measurable `T ⊆ U`, a set `A ⊆ U` and the variation of `u` on `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_closure_subset {U T : Set E}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hUK : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (hu : LocallyIntegrableOn u Ω μ) (hT : T ⊆ U) (hT₀ : μ T ≠ 0) (hA : A ⊆ U) :
    ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * diam U ^ finrank ℝ E /
        μ.real T) * μ A ^ (finrank ℝ E : ℝ)⁻¹ * totalVariationOn μ Ω u := by
  set C := ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    diam U ^ finrank ℝ E / μ.real T) * μ A ^ (finrank ℝ E : ℝ)⁻¹
  have hUb : Bornology.IsBounded U := hUK.isBounded.subset subset_closure
  have hUfin : μ U ≠ ∞ := hUb.measure_lt_top.ne
  have huK : IntegrableOn u (closure U) μ := hu.integrableOn_compact_subset hUΩ hUK
  -- Smooth functions `v n` converging to `u` in `L¹(closure U)`, with variation on `U` at most
  -- `|Du|(Ω)`. The `L¹(closure U)` distance from `v n` to `u` is `e n`.
  obtain ⟨v, hv, he, hvar⟩ :=
    exists_seq_contDiff_tendsto_setLIntegral_enorm_sub_totalVariationOn_le hu hUK hUΩ
  set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in closure U, ‖v n x - u x‖ₑ ∂μ
  set M : ℝ≥0∞ := μ U / μ T
  have hM : M ≠ ∞ := ENNReal.div_ne_top hUfin hT₀
  -- The inequality holds for `u` up to an error `(1 + M) e n`.
  have hbound (n : ℕ) : ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      e n + M * e n + C * totalVariationOn μ Ω u := by
    have hv1 : ContDiff ℝ 1 (v n) := (hv n).of_le (by norm_cast)
    -- The smooth inequality for `v n` on `U`, whose variation there is at most `|Du|(Ω)`.
    have hvA : ∫⁻ x in A, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ ≤ C * totalVariationOn μ Ω u := by
      refine (setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex hU hUc hUb
        hv1.contDiffOn hT hT₀ hA).trans (mul_le_mul_right ?_ _)
      have hL := (hv1.locallyLipschitz.locallyLipschitzOn (s := U)
        ).totalVariationOn_eq_setLIntegral_enorm_fderiv (μ := μ) (Ω := ⟨U, hU⟩)
      rw [Opens.coe_mk] at hL
      exact hL ▸ hvar ⟨U, hU⟩ subset_closure n
    -- The means over `T` differ by at most `e n / μ(T)`.
    have hab : ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ ≤ e n / μ T := by
      have hTK : T ⊆ closure U := hT.trans subset_closure
      rw [← setAverage_fun_sub
        (((hv n).continuous.locallyIntegrable.integrableOn_isCompact hUK).mono_set hTK)
        (huK.mono_set hTK)]
      refine (enorm_setAverage_le_setLAverage μ _ T).trans ?_
      rw [setLAverage_eq]
      gcongr
      exact lintegral_mono_set hTK
    -- The triangle inequality through `v n` and its mean.
    have hdist : AEMeasurable (fun x => ‖v n x - u x‖ₑ) (μ.restrict A) :=
      (((hv n).continuous.aestronglyMeasurable.restrict.sub huK.aestronglyMeasurable).enorm
        ).mono_measure (Measure.restrict_mono (hA.trans subset_closure) le_rfl)
    calc ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ
        ≤ ∫⁻ x in A, (‖v n x - u x‖ₑ + ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← enorm_neg (v n x - u x)]
          refine le_of_eq_of_le ?_
            ((enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _))
          congr 1
          ring
      _ = ∫⁻ x in A, ‖v n x - u x‖ₑ ∂μ + ∫⁻ x in A, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ * μ A := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left' hdist,
            setLIntegral_const]
      _ ≤ e n + C * totalVariationOn μ Ω u + e n / μ T * μ U := by
          gcongr
          exact lintegral_mono_set (hA.trans subset_closure)
      _ = e n + M * e n + C * totalVariationOn μ Ω u := by
          simp only [M, div_eq_mul_inv]
          ring
  have hlim : Tendsto (fun n => e n + M * e n + C * totalVariationOn μ Ω u) atTop
      (𝓝 (0 + M * 0 + C * totalVariationOn μ Ω u)) :=
    (he.add (ENNReal.Tendsto.const_mul he (Or.inr hM))).add tendsto_const_nhds
  simpa using ge_of_tendsto hlim (.of_forall hbound)

/-- The inequality for a measurable `S`, from the inequality on an exhaustion of `Ω` by convex
open sets with compact closures in `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_measurableSet
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hSm : MeasurableSet S) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0)
    (hA : A ⊆ Ω) :
    ∫⁻ x in A, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Ω : Set E) ^ finrank ℝ E / μ.real S) * μ A ^ (finrank ℝ E : ℝ)⁻¹ *
        totalVariationOn μ Ω u := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Ω.isOpen hΩc
  have hVsub (n : ℕ) : V n ⊆ Ω := subset_closure.trans (hVclosure n)
  have hΩfin : μ Ω ≠ ∞ := hb.measure_lt_top.ne
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hΩfin (measure_mono hS)
  have hSpos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hSfin
  set K : ℝ := μ.real (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    diam (Ω : Set E) ^ finrank ℝ E
  set a := ⨍ y in S, u y ∂μ
  set T := μ A ^ (finrank ℝ E : ℝ)⁻¹ * totalVariationOn μ Ω u
  -- The measures of, and the means over, `S ∩ V n` converge to those over `S`.
  have hSV : S ⊆ ⋃ n, V n := hVunion ▸ hS
  have hmeas : Tendsto (fun n ↦ μ.real (S ∩ V n)) atTop (𝓝 (μ.real S)) :=
    tendsto_measureReal_inter_of_monotone hVmono hSV hSfin
  have havg : Tendsto (fun n ↦ ⨍ y in S ∩ V n, u y ∂μ) atTop (𝓝 a) :=
    tendsto_setAverage_inter_of_monotone hVmono hSV
      (fun n ↦ (hSm.inter (hVopen n).measurableSet).nullMeasurableSet) hSfin (hu.mono_set hS)
  -- On `A ∩ V n`, the deviation from `a` is the deviation from the mean over `S ∩ V n` up to an
  -- error `μ(Ω) |⨍_{S ∩ V n} u - a|`.
  have hpiece : ∀ᶠ n in atTop, ∫⁻ x in A ∩ V n, ‖u x - a‖ₑ ∂μ ≤
      ENNReal.ofReal (K / μ.real (S ∩ V n)) * T + μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
    filter_upwards [hmeas.eventually (lt_mem_nhds hSpos)] with n hn
    have hn0 : μ (S ∩ V n) ≠ 0 := fun h => by simp [measureReal_def, h] at hn
    calc ∫⁻ x in A ∩ V n, ‖u x - a‖ₑ ∂μ
        ≤ ∫⁻ x in A ∩ V n, (‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ) ∂μ :=
          lintegral_mono fun x => by
            simpa only [sub_add_sub_cancel] using enorm_add_le (u x - ⨍ y in S ∩ V n, u y ∂μ)
              ((⨍ y in S ∩ V n, u y ∂μ) - a)
      _ = ∫⁻ x in A ∩ V n, ‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ * μ (A ∩ V n) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (K / μ.real (S ∩ V n)) * T +
            μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
          rw [mul_comm (‖_‖ₑ), ← mul_assoc]
          gcongr
          · refine (setLIntegral_enorm_sub_setAverage_le_of_closure_subset (hVopen n)
              (hVconv n) (hVcompact n) (hVclosure n) hu.locallyIntegrableOn inter_subset_right
              hn0 inter_subset_right).trans ?_
            gcongr
            · simp only [K]
              gcongr
              exact diam_mono (hVsub n) hb
            · exact inter_subset_left
          · exact inter_subset_right.trans (hVsub n)
  -- The bounds converge to `C μ(A) ^ (1/n) |Du|(Ω)`.
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
  -- `A` is the increasing union of the sets `A ∩ V n`.
  have hAV : ⋃ n, A ∩ V n = A := by rw [← inter_iUnion, hVunion, inter_eq_left.2 hA]
  have hdir : Directed (· ⊆ ·) fun n => A ∩ V n :=
    Monotone.directed_le fun m n hmn => inter_subset_inter_right A (hVmono hmn)
  have hsup : ∫⁻ x in A, ‖u x - a‖ₑ ∂μ = ⨆ k, ∫⁻ x in A ∩ V k, ‖u x - a‖ₑ ∂μ := by
    rw [← setLIntegral_iUnion_of_directed _ hdir, hAV]
  rw [hsup, mul_assoc]
  refine iSup_le fun k => ge_of_tendsto (by simpa using hlim) ?_
  filter_upwards [hpiece, eventually_ge_atTop k] with n hn hkn
  exact (lintegral_mono_set (inter_subset_inter_right A (hVmono hkn))).trans hn

/-- **The Poincaré–Wirtinger inequality for functions of bounded variation, localized to a
subset.** Let `Ω` be a bounded convex open set in a finite-dimensional real inner product space of
dimension `n`, and let `S ⊆ Ω` have positive measure. For every `u` integrable on `Ω` and every
`A ⊆ Ω`, the integral over `A` of the deviation of `u` from its mean over `S` is at most
`μ(B(0, 1)) ^ (1 - 1/n) * (diam Ω) ^ n / μ(S) * μ(A) ^ (1/n)` times the total variation
`|Du|(Ω)`, finite or infinite. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) (hA : A ⊆ Ω) :
    ∫⁻ x in A, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Ω : Set E) ^ finrank ℝ E / μ.real S) * μ A ^ (finrank ℝ E : ℝ)⁻¹ *
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
    (hμ ▸ hS₀) hA

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
  set n := finrank ℝ E
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono hS)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · -- In dimension zero, `u` is constant.
    have : Subsingleton E := finrank_zero_iff.1 hn
    have h0 (x : E) : u x - ⨍ y in S, u y ∂μ = 0 := by
      rw [show (fun y => u y) = fun _ => u x from funext fun y => by rw [Subsingleton.elim y x],
        setAverage_const hS₀ hSfin, sub_self]
    simp [h0]
  -- `μ(Ω) ≤ ω d ^ n`, since `Ω` lies in the closed ball of radius `d = diam Ω` about a point of
  -- `S`.
  obtain ⟨z, hz⟩ := nonempty_of_measure_ne_zero hS₀
  set d := diam (Ω : Set E)
  set ω := μ.real (ball (0 : E) 1)
  have hd : 0 ≤ d := diam_nonneg
  have hω : 0 < ω := ENNReal.toReal_pos (measure_ball_pos μ 0 one_pos).ne' measure_ball_lt_top.ne
  have hΩ : μ.real Ω ≤ d ^ n * ω := by
    rw [← μ.addHaar_real_closedBall z hd]
    exact measureReal_mono (fun x hx => mem_closedBall.2 (dist_le_diam_of_mem hb hx (hS hz)))
      measure_closedBall_lt_top.ne
  refine (setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    hΩc hb hu hS hS₀ subset_rfl).trans ?_
  gcongr ?_ * _
  rw [← ENNReal.ofReal_toReal hb.measure_lt_top.ne,
    ENNReal.ofReal_rpow_of_nonneg ENNReal.toReal_nonneg (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc ω ^ (1 - (n : ℝ)⁻¹) * d ^ n / μ.real S * μ.real Ω ^ (n : ℝ)⁻¹
      ≤ ω ^ (1 - (n : ℝ)⁻¹) * d ^ n / μ.real S * (d ^ n * ω) ^ (n : ℝ)⁻¹ := by gcongr
    _ = ω * d ^ (n + 1) / μ.real S := by
      rw [Real.mul_rpow (by positivity) hω.le, Real.pow_rpow_inv_natCast hd hn.ne',
        Real.rpow_sub hω, Real.rpow_one]
      have : 0 < ω ^ (n : ℝ)⁻¹ := by positivity
      field_simp
      ring

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
