/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.OneDim
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.LebesgueDifferentiationThm

/-!
# Lebesgue differentiation on the line

Mathlib's `IntervalIntegrable.ae_hasDerivAt_integral` differentiates the primitive of an
interval-integrable Bochner integrand. This file records the companion statement for an extended
nonnegative density and the lower Lebesgue integral: if `f : ℝ → ℝ≥0∞` is almost everywhere
measurable on `Ι a b` with finite lower integral there, then at almost every point `t` of `[a, b]`
the averages `(∫⁻ r in Ι t s, f r) / edist s t` tend to `f t` as `s → t` with `s ≠ t`, from either
side.

Stating it for `ℝ≥0∞`-valued densities avoids choosing a real representative of `f` and the
`ENNReal.toReal` bookkeeping that comes with it, which is the convenient form when the density
bounds a distance from above, as for the metric derivative of a curve.

It also records the version of Mathlib's theorem for a Bochner integrand that is only locally
integrable on an open interval, and so need not be integrable up to the endpoints.

## Main results

* `TauCeti.ae_tendsto_setLIntegral_uIoc_div`: the one-dimensional Lebesgue differentiation theorem
  for an extended nonnegative density which is almost everywhere measurable with finite lower
  integral on an interval.
* `MeasureTheory.LocallyIntegrableOn.ae_hasDerivAt_integral`: for `f` locally integrable on
  `Ioo a b`, at almost every point of `Ioo a b` every primitive of `f` based in `Ioo a b` has
  derivative `f`.
-/

public section

open Filter IsUnifLocDoublingMeasure MeasureTheory Set Topology
open scoped ENNReal Interval

namespace TauCeti

/-- The *Lebesgue differentiation theorem* on the line for an extended nonnegative density: if
`f : ℝ → ℝ≥0∞` is almost everywhere measurable on `Ι a b` with finite lower integral there, then
for almost every `t ∈ [a, b]` the averages `(∫⁻ r in Ι t s, f r) / edist s t` over the intervals
between `t` and `s` tend to `f t` as `s` tends to `t` from either side. -/
theorem ae_tendsto_setLIntegral_uIoc_div {f : ℝ → ℝ≥0∞} {a b : ℝ}
    (hf : AEMeasurable f (volume.restrict (Ι a b))) (hfin : ∫⁻ r in Ι a b, f r ≠ ∞) :
    ∀ᵐ t, t ∈ uIcc a b →
      Tendsto (fun s ↦ (∫⁻ r in Ι t s, f r) / edist s t) (𝓝[≠] t) (𝓝 (f t)) := by
  wlog hab : a ≤ b generalizing a b
  · rw [uIoc_comm] at hf hfin
    exact uIcc_comm b a ▸ this hf hfin (le_of_not_ge hab)
  rw [uIoc_of_le hab] at hf hfin
  rw [uIcc_of_le hab]
  set g := (Ioc a b).indicator f
  have hg : AEMeasurable g := (aemeasurable_indicator_iff measurableSet_Ioc).2 hf
  have hgfin : ∫⁻ r, g r ≠ ∞ := by rwa [lintegral_indicator measurableSet_Ioc]
  filter_upwards [(vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_lintegral_div hg hgfin,
    volume.ae_ne a, volume.ae_ne b] with t ht hta htb htab
  -- `t` is an interior point of `[a, b]`, so `Ioc a b` contains every short interval around it.
  have hmem : t ∈ Ioo a b := ⟨htab.1.lt_of_ne' hta, htab.2.lt_of_ne htb⟩
  have hg_eq {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) :
      ∫⁻ r in Icc u v, g r = ∫⁻ r in Ioc u v, f r := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm, setLIntegral_indicator measurableSet_Ioc,
      inter_eq_right.2 (Ioc_subset_Ioc hu hv)]
  have hgt : g t = f t := indicator_of_mem (Ioo_subset_Ioc_self hmem) f
  rw [hgt] at ht
  rw [← nhdsLT_sup_nhdsGT]
  refine Tendsto.sup ((ht.comp (Real.tendsto_Icc_vitaliFamily_left t)).congr' ?_)
    ((ht.comp (Real.tendsto_Icc_vitaliFamily_right t)).congr' ?_)
  · filter_upwards [Ioo_mem_nhdsLT hmem.1] with s hs
    rw [Function.comp_apply, hg_eq hs.1.le hmem.2.le, Real.volume_Icc, uIoc_of_ge hs.2.le,
      edist_dist, Real.dist_eq, abs_of_neg (sub_neg.2 hs.2), neg_sub]
  · filter_upwards [Ioo_mem_nhdsGT hmem.2] with s hs
    rw [Function.comp_apply, hg_eq hmem.1.le hs.2.le, Real.volume_Icc, uIoc_of_le hs.1.le,
      edist_dist, Real.dist_eq, abs_of_pos (sub_pos.2 hs.1)]

end TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- The *Lebesgue differentiation theorem* on an open interval: if `f : ℝ → E` is locally
integrable on `Ioo a b`, then for almost every `x ∈ Ioo a b` and every `c ∈ Ioo a b`, the
derivative of `t ↦ ∫ s in c..t, f s` at `x` is `f x`. -/
theorem MeasureTheory.LocallyIntegrableOn.ae_hasDerivAt_integral {f : ℝ → E} {a b : ℝ}
    (hf : LocallyIntegrableOn f (Ioo a b)) :
    ∀ᵐ x, x ∈ Ioo a b → ∀ c ∈ Ioo a b, HasDerivAt (fun t ↦ ∫ s in c..t, f s) (f x) x := by
  -- Mathlib's theorem applies on each interval between two rational points of `Ioo a b`, and
  -- these intervals exhaust `Ioo a b`.
  have key : ∀ p q : ℚ, ∀ᵐ x, (p : ℝ) ∈ Ioo a b → (q : ℝ) ∈ Ioo a b → x ∈ uIcc (p : ℝ) q →
      ∀ c ∈ uIcc (p : ℝ) q, HasDerivAt (fun t ↦ ∫ s in c..t, f s) (f x) x := by
    intro p q
    by_cases hpq : (p : ℝ) ∈ Ioo a b ∧ (q : ℝ) ∈ Ioo a b
    · have hint : IntervalIntegrable f volume p q := (hf.integrableOn_compact_subset
        (ordConnected_Ioo.uIcc_subset hpq.1 hpq.2) isCompact_uIcc).intervalIntegrable
      filter_upwards [hint.ae_hasDerivAt_integral] with x hx _ _ using hx
    · exact Eventually.of_forall fun x hp hq ↦ absurd ⟨hp, hq⟩ hpq
  filter_upwards [ae_all_iff.2 fun p ↦ ae_all_iff.2 (key p)] with x hx hxI c hc
  obtain ⟨p, hp, hpx⟩ := exists_rat_btwn (lt_min hxI.1 hc.1)
  obtain ⟨q, hxq, hq⟩ := exists_rat_btwn (max_lt hxI.2 hc.2)
  have hpq : (p : ℝ) ≤ q := hpx.le.trans ((min_le_left _ _).trans ((le_max_left _ _).trans hxq.le))
  have hmem : ∀ z, min x c ≤ z → z ≤ max x c → z ∈ uIcc (p : ℝ) q := fun z h₁ h₂ ↦ by
    rw [uIcc_of_le hpq]
    exact ⟨hpx.le.trans h₁, h₂.trans hxq.le⟩
  exact hx p q ⟨hp, (hpx.trans_le (min_le_left _ _)).trans hxI.2⟩
    ⟨hxI.1.trans ((le_max_left _ _).trans_lt hxq), hq⟩ (hmem x (min_le_left _ _) (le_max_left _ _))
    c (hmem c (min_le_right _ _) (le_max_right _ _))
