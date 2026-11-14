/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-!
# The excised parameter set shrinks to nothing

An `ε`-excision deletes from the parameter interval every time at which the curve comes within
`ε` of one of finitely many centres. This file records that the deleted set carries no length in
the limit: the interval integral of the excision's indicator from `a` to `b` tends to `b - a` as
`ε → 0⁺`, for either orientation of the interval.

Two properties of the curve are used, for two different parts of the argument. **A.e.
measurability** makes each excised set null-measurable, so dominated convergence applies.
**Nullity of the times the curve spends exactly at a centre** gives the almost-everywhere
convergence: away from those times the curve keeps a positive distance from the finite centre
set, so the excision condition eventually fails outright (`eventually_not_exists_norm_sub_le`).
Injectivity on the interval is one convenient sufficient condition for the second — it makes those
times finite — and is the general measure-theoretic fact `Set.InjOn.measure_setOf_mem_eq_zero`; a
curve may revisit centres, so long as it does so on a null set of times.

## Main results

* `TauCeti.Contour.nullMeasurableSet_excision`: the excised parameter set is null-measurable
  against any measure for which the curve is a.e. measurable.
* `TauCeti.Contour.measurableSet_excision`: its measurable specialization.
* `TauCeti.Contour.aestronglyMeasurable_indicator_excision`: excising from an integrand supported
  where the curve is differentiable keeps it a.e. strongly measurable.
* `TauCeti.Contour.eventually_not_exists_norm_sub_le`: a point off the finite centre set
  survives every small enough excision.
* `TauCeti.Contour.tendsto_intervalIntegral_excisionIndicator`: the excision indicator's interval
  integral from `a` to `b` tends to `b - a` as `ε → 0⁺`.

## References

* [AINTLIB `LeanModularForms`](https://github.com/CBirkbeck/AINTLIB) — the valence-formula
  development. This file adapts the measure-theoretic step of
  `ForMathlib/ValenceFormula/PVChain/ArcContribution.lean`
  (`arc_non_excluded_measure_tendsto`, with its `arc_preimage_subsingleton` and
  `arc_min_dist_pos` helpers) onto the current Mathlib pin, restated for an arbitrary curve
  rather than the fundamental-domain arc.
-/

public section

open Filter MeasureTheory Set Topology

namespace TauCeti.Contour

variable {α E : Type*}

/-- The excised parameter set is the preimage under the curve of the union of the closed
`ε`-balls about the centres. -/
private theorem setOf_exists_norm_sub_le_eq_preimage [SeminormedAddCommGroup E] (γ : α → E)
    (S : Finset E) (ε : ℝ) :
    {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} = γ ⁻¹' ⋃ s ∈ S, Metric.closedBall s ε := by
  ext; simp [dist_eq_norm]

/-- **The excised parameter set is null-measurable** whenever the curve is a.e. measurable. Stated
for an arbitrary measure so that it serves both the ambient statement and the restricted-measure
one that interval integrability needs. -/
theorem nullMeasurableSet_excision [MeasurableSpace α] [SeminormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {γ : α → E} {μ : Measure α}
    (hγ : AEMeasurable γ μ) (S : Finset E) (ε : ℝ) :
    NullMeasurableSet {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} μ :=
  setOf_exists_norm_sub_le_eq_preimage γ S ε ▸ hγ.nullMeasurableSet_preimage
    (S.measurableSet_biUnion fun _ _ => measurableSet_closedBall)

/-- **The excised parameter set is measurable** whenever the curve is. -/
theorem measurableSet_excision [MeasurableSpace α] [SeminormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {γ : α → E} (hγm : Measurable γ) (S : Finset E)
    (ε : ℝ) :
    MeasurableSet {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε} :=
  setOf_exists_norm_sub_le_eq_preimage γ S ε ▸
    hγm (S.measurableSet_biUnion fun _ _ => measurableSet_closedBall)

/-- **Excising a curve's `ε`-neighbourhood of finitely many points keeps a.e.-strong
measurability, if the integrand is supported where the curve is differentiable.** Off the set of
differentiability the integrand vanishes, and on it the curve is continuous, hence measurable, so
the excised parameter set is null-measurable for the restricted measure. No measurable structure
on `E` is assumed: the proof equips `E` with its Borel one. -/
theorem aestronglyMeasurable_indicator_excision [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] {F : Type*} [TopologicalSpace F] [Zero F] {γ : ℝ → E} {μ : Measure ℝ}
    {G : ℝ → F} (hG : AEStronglyMeasurable G μ) (hG0 : ∀ t, ¬ DifferentiableAt ℝ γ t → G t = 0)
    (S : Finset E) (ε : ℝ) :
    AEStronglyMeasurable ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε}ᶜ.indicator G) μ := by
  borelize E
  have hD : MeasurableSet {t | DifferentiableAt ℝ γ t} := measurableSet_of_differentiableAt ℝ γ
  have hγD : AEMeasurable γ (μ.restrict {t | DifferentiableAt ℝ γ t}) :=
    ContinuousOn.aemeasurable (fun t ht => ht.continuousAt.continuousWithinAt) hD
  have hsupp : Function.support ({t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε}ᶜ.indicator G) ⊆
      {t | DifferentiableAt ℝ γ t} := fun t ht => by
    by_contra hdiff
    exact ht (by simp [hG0 t hdiff])
  rw [← Set.indicator_eq_self.mpr hsupp]
  exact (aestronglyMeasurable_indicator_iff hD).mpr
    ((hG.mono_measure Measure.restrict_le_self).indicator₀
      (nullMeasurableSet_excision hγD S ε).compl)

/-- **A point off the centres survives every small enough excision.** If `z` is none of the
finitely many centres `S`, then for all small enough `ε > 0` it is farther than `ε` from each
of them. -/
theorem eventually_not_exists_norm_sub_le [NormedAddGroup E] {z : E} {S : Finset E}
    (hz : z ∉ S) : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ¬ ∃ s ∈ S, ‖z - s‖ ≤ ε := by
  -- Each of the finitely many distances `‖z - s‖` is positive.
  have hlt : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ s ∈ S, ε < ‖z - s‖ :=
    (eventually_all_finset S).mpr fun s hs => (eventually_lt_nhds <| norm_sub_pos_iff.mpr
      fun h : z = s => hz (h ▸ hs)).filter_mono nhdsWithin_le_nhds
  filter_upwards [hlt] with ε hε ⟨s, hs, hle⟩
  exact (hε s hs).not_ge hle

/-- **The excised parameter set shrinks to nothing.** Deleting from `uIoc a b` the times at which
the curve comes within `ε` of one of finitely many centres costs no length as `ε → 0⁺`: the
excision indicator's interval integral tends to the full oriented length `b - a`.

The curve must be a.e. measurable on `uIoc a b`, and must spend only a null set of times there
exactly at a centre — `Set.InjOn.measure_setOf_mem_eq_zero` supplies the latter from
injectivity. -/
theorem tendsto_intervalIntegral_excisionIndicator [NormedAddCommGroup E]
    [MeasurableSpace E] [OpensMeasurableSpace E] {γ : ℝ → E} {a b : ℝ}
    (hγ : AEMeasurable γ (volume.restrict (uIoc a b))) (S : Finset E)
    (hnull : volume {t ∈ uIoc a b | γ t ∈ S} = 0) :
    Tendsto (fun ε => ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
      (𝓝[>] 0) (𝓝 (b - a)) := by
  -- Dominated convergence, with the constant bound `1`, towards the constant integrand `1`.
  suffices h : Tendsto (fun ε => ∫ t in a..b, if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1)
      (𝓝[>] 0) (𝓝 (∫ _ in a..b, (1 : ℝ))) by simpa using h
  refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence (fun _ => 1) ?_ ?_
    intervalIntegrable_const ?_
  · -- Each integrand is the indicator of the complement of the excised set.
    refine Eventually.of_forall fun ε => ?_
    have hind : (fun t => if ∃ s ∈ S, ‖γ t - s‖ ≤ ε then (0 : ℝ) else 1) =
        {t | ∃ s ∈ S, ‖γ t - s‖ ≤ ε}ᶜ.indicator 1 := by
      ext t
      by_cases ht : ∃ s ∈ S, ‖γ t - s‖ ≤ ε <;> simp [ht]
    rw [hind]
    exact aestronglyMeasurable_const.indicator₀ (nullMeasurableSet_excision hγ S ε).compl
  · exact Eventually.of_forall fun ε => Eventually.of_forall fun t _ => by split_ifs <;> simp
  · -- Off the null set of exact hits, the excision condition eventually fails outright.
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with t ht htab
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_not_exists_norm_sub_le fun h : γ t ∈ S => ht ⟨htab, h⟩]
      with ε hε
    exact (ite_eq_right hε).symm

end TauCeti.Contour
