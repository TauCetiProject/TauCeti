/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Covering.OneDim

/-!
# Lebesgue differentiation on the line for extended nonnegative densities

Mathlib's `IntervalIntegrable.ae_hasDerivAt_integral` differentiates the primitive of an
interval-integrable Bochner integrand. This file records the companion statement for an extended
nonnegative density and the lower Lebesgue integral: if `f : ℝ → ℝ≥0∞` is almost everywhere
measurable on `Ι a b` with finite lower integral there, then at almost every point `t` of `[a, b]`
the averages `(∫⁻ r in Ι t s, f r) / edist s t` tend to `f t` as `s → t` with `s ≠ t`, from either
side.

Stating it for `ℝ≥0∞`-valued densities avoids choosing a real representative of `f` and the
`ENNReal.toReal` bookkeeping that comes with it, which is the convenient form when the density
bounds a distance from above, as for the metric derivative of a curve.

## Main results

* `TauCeti.ae_tendsto_setLIntegral_uIoc_div`: the one-dimensional Lebesgue differentiation theorem
  for an extended nonnegative density which is almost everywhere measurable with finite lower
  integral on an interval.
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
    rw [uIcc_comm]
    exact this hf hfin (le_of_not_ge hab)
  rw [uIoc_of_le hab] at hf hfin
  rw [uIcc_of_le hab]
  set g := (Ioc a b).indicator f
  have hg : AEMeasurable g := (aemeasurable_indicator_iff measurableSet_Ioc).2 hf
  have hgfin : ∫⁻ r, g r ≠ ∞ := by rwa [lintegral_indicator measurableSet_Ioc]
  filter_upwards [(vitaliFamily (volume : Measure ℝ) 1).ae_tendsto_lintegral_div hg hgfin,
    volume.ae_ne a, volume.ae_ne b] with t ht hta htb htab
  -- `t` is an interior point of `[a, b]`, so `Ioc a b` contains every short interval around it.
  have hmem : t ∈ Ioo a b := ⟨lt_of_le_of_ne htab.1 hta.symm, lt_of_le_of_ne htab.2 htb⟩
  have hg_eq {u v : ℝ} (hu : a ≤ u) (hv : v ≤ b) :
      ∫⁻ r in Icc u v, g r = ∫⁻ r in Ioc u v, f r := by
    rw [setLIntegral_congr Ioc_ae_eq_Icc.symm]
    exact setLIntegral_congr_fun measurableSet_Ioc fun r hr ↦
      indicator_of_mem (Ioc_subset_Ioc hu hv hr) f
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
