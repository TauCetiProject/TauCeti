/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Uniformly small tails of a function of finite Lebesgue integral

A function `f : α → ℝ≥0∞` of finite Lebesgue integral exceeds a large constant `M` only by an
amount of small integral: `∫⁻ x, f x - M ∂μ → 0` as `M → ∞`. This is dominated convergence with
the bound `f`, since `f x - M` vanishes for `M ≥ f x` and `f` is almost everywhere finite.

The file also records a squeeze principle: if `f n ≤ g n + h n` and the integrals of `g n` and
`h n` tend to `0`, so does the integral of `f n`; and the reverse Fatou lemma for integrals over
sets: the integrals of a function of finite integral over measurable sets `s n` have limit
superior at most its integral over `limsup s n`, the set of points lying in infinitely many
`s n`, and its counterpart for `Lᵖ` seminorms.

## Main statements

* `TauCeti.tendsto_lintegral_tsub_atTop`: the integral of the excess of `f` over the constant `M`
  tends to `0` as `M → ∞`.
* `TauCeti.tendsto_lintegral_zero_of_le_add`: the integral of a function bounded by the sum of
  two functions with integrals tending to `0` tends to `0`.
* `TauCeti.limsup_setLIntegral_le`: `limsup ∫⁻_{s n} f ≤ ∫⁻_{limsup s n} f` when the `s n` lie
  in a set over which `f` has finite integral.
* `TauCeti.limsup_eLpNorm_restrict_le`: `limsup ‖g‖_{Lᵖ(s n)} ≤ ‖g‖_{Lᵖ(limsup s n)}` for
  `0 < p < ∞` when the `s n` lie in a set `t` with `g ∈ Lᵖ(t)`.
-/

public section

namespace TauCeti

open Filter MeasureTheory Topology
open scoped ENNReal NNReal

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- **Uniformly small tails.** If `f : α → ℝ≥0∞` is almost everywhere measurable with finite
Lebesgue integral, then the integral of its excess `f x - M` over a finite level `M` tends to `0`
as `M → ∞`. -/
theorem tendsto_lintegral_tsub_atTop {f : α → ℝ≥0∞} (hf : AEMeasurable f μ)
    (hfi : ∫⁻ x, f x ∂μ ≠ ∞) :
    Tendsto (fun M : ℝ≥0 ↦ ∫⁻ x, f x - M ∂μ) atTop (𝓝 0) := by
  have h := tendsto_lintegral_filter_of_dominated_convergence' (l := atTop)
    (F := fun (M : ℝ≥0) x ↦ f x - M) (f := fun _ ↦ 0) f
    (Eventually.of_forall fun M ↦ hf.sub aemeasurable_const)
    (Eventually.of_forall fun M ↦ ae_of_all _ fun x ↦ tsub_le_self) hfi ?_
  · simpa using h
  -- At a point where `f` is finite, the excess vanishes once `M ≥ f x`.
  filter_upwards [ae_lt_top' hf hfi] with x hx
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop (f x).toNNReal] with M hM
  rw [eq_comm, tsub_eq_zero_iff_le]
  exact (ENNReal.coe_toNNReal hx.ne).symm.trans_le (ENNReal.coe_le_coe.2 hM)

/-- If `f n ≤ g n + h n` pointwise, `g n` is almost everywhere measurable, and the Lebesgue
integrals of `g n` and `h n` tend to `0`, then so do those of `f n`. -/
theorem tendsto_lintegral_zero_of_le_add {ι : Type*} {l : Filter ι} {f g h : ι → α → ℝ≥0∞}
    (hfgh : ∀ i x, f i x ≤ g i x + h i x) (hg : ∀ i, AEMeasurable (g i) μ)
    (hgt : Tendsto (fun i ↦ ∫⁻ x, g i x ∂μ) l (𝓝 0))
    (hht : Tendsto (fun i ↦ ∫⁻ x, h i x ∂μ) l (𝓝 0)) :
    Tendsto (fun i ↦ ∫⁻ x, f i x ∂μ) l (𝓝 0) := by
  have hsum := hgt.add hht
  rw [add_zero] at hsum
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
    (fun _ ↦ zero_le) fun i ↦ ?_
  rw [← lintegral_add_left' (hg i)]
  exact lintegral_mono (hfgh i)

/-- **The reverse Fatou lemma for integrals over sets.** Let `f` be measurable, let the sets `s n`
be measurable and contained in a set `t` over which `f` has finite integral. Then the limit
superior of the integrals of `f` over `s n` is at most the integral of `f` over `limsup s n`, the
set of points that lie in `s n` for infinitely many `n`. -/
theorem limsup_setLIntegral_le {f : α → ℝ≥0∞} {s : ℕ → Set α} {t : Set α} (hf : Measurable f)
    (hs : ∀ n, MeasurableSet (s n)) (hst : ∀ n, s n ⊆ t) (ht : ∫⁻ x in t, f x ∂μ ≠ ∞) :
    limsup (fun n ↦ ∫⁻ x in s n, f x ∂μ) atTop ≤ ∫⁻ x in limsup s atTop, f x ∂μ := by
  simp_rw [← lintegral_indicator (hs _)]
  refine (limsup_lintegral_le (t.indicator f) (fun n ↦ hf.indicator (hs n))
    (fun n ↦ ae_of_all _ (Set.indicator_le_indicator_of_subset (hst n) fun _ ↦ zero_le))
    (ne_top_of_le_ne_top ht (lintegral_indicator_le f t))).trans
    ((lintegral_mono fun x ↦ ?_).trans (lintegral_indicator_le f _))
  -- Pointwise, the limit superior of the indicators is at most the indicator of `limsup s n`.
  by_cases hx : ∃ᶠ n in atTop, x ∈ s n
  · rw [Set.indicator_of_mem (Filter.mem_limsup_iff_frequently_mem.2 hx)]
    exact limsup_le_of_le (by isBoundedDefault) (Eventually.of_forall fun n ↦
      Set.indicator_le_self (s n) f x)
  · rw [not_frequently] at hx
    rw [limsup_congr (hx.mono fun n hn ↦ Set.indicator_of_notMem hn f)]
    simp

/-- **The reverse Fatou lemma for `Lᵖ` seminorms over sets.** Let `0 < p < ∞`, let the sets `s n`
be measurable and contained in `t`, and let `g ∈ Lᵖ(t)`. Then the limit superior of the `Lᵖ`
seminorms of `g` over `s n` is at most its `Lᵖ` seminorm over `limsup s n`. -/
theorem limsup_eLpNorm_restrict_le {E : Type*} [NormedAddCommGroup E] {g : α → E} {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) {s : ℕ → Set α} {t : Set α} (hg : MemLp g p (μ.restrict t))
    (hs : ∀ n, MeasurableSet (s n)) (hst : ∀ n, s n ⊆ t) :
    limsup (fun n ↦ eLpNorm g p (μ.restrict (s n))) atTop ≤
      eLpNorm g p (μ.restrict (limsup s atTop)) := by
  -- Replace `g` by a strongly measurable function equal to it almost everywhere on `t`.
  set h := hg.aestronglyMeasurable.mk g
  have hlim : limsup s atTop ⊆ t := fun x hx ↦
    (Filter.mem_limsup_iff_frequently_mem.1 hx).exists.elim fun n hn ↦ hst n hn
  have hgh {u : Set α} (hu : u ⊆ t) : eLpNorm g p (μ.restrict u) = eLpNorm h p (μ.restrict u) :=
    eLpNorm_congr_ae (ae_restrict_of_ae_restrict_of_subset hu hg.aestronglyMeasurable.ae_eq_mk)
  have hmeas : StronglyMeasurable h := hg.aestronglyMeasurable.stronglyMeasurable_mk
  have heq {u : Set α} (hu : u ⊆ t) : eLpNorm g p (μ.restrict u) =
      (∫⁻ x in u, ‖h x‖ₑ ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    rw [hgh hu, eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hptop hmeas.aestronglyMeasurable]
  simp_rw [heq (hst _), heq hlim]
  have hpos : 0 ≤ 1 / p.toReal := by positivity
  have hmap := (ENNReal.monotone_rpow_of_nonneg hpos).map_limsup_of_continuousAt (F := atTop)
    (fun n ↦ ∫⁻ x in s n, ‖h x‖ₑ ^ p.toReal ∂μ) ENNReal.continuous_rpow_const.continuousAt
  rw [Function.comp_def] at hmap
  rw [← hmap]
  refine ENNReal.rpow_le_rpow (limsup_setLIntegral_le
    (hmeas.enorm.pow_const _) hs hst ?_) hpos
  exact (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hptop
    ((hgh le_rfl).symm.trans_lt hg.eLpNorm_lt_top)).ne

end TauCeti
