/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.ReducedBoundary
public import Mathlib.Geometry.Euclidean.Volume.Measure
import TauCeti.Analysis.BoundedVariation.BlowUp
import TauCeti.Analysis.BoundedVariation.Isometry
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.Geometry.Euclidean.Volume.Measure
import TauCeti.MeasureTheory.Covering.DensityTheorem

/-!
# Hausdorff measure on the reduced boundary is at most the perimeter measure

Let `Ω` be an open set of a finite-dimensional real inner product space `E` of dimension `n`,
with Lebesgue measure, and let `s ⊆ E`. For `n ≥ 2`, at every point of the reduced boundary `∂*s`
of `s` in `Ω`, the perimeter measure `|Dχ_s|` has density one with respect to the normalized
Hausdorff measure `μHE[n - 1]`
(`TauCeti.tendsto_variationMeasure_closedBall_div_volume_closedBall`). For `n = 1`, where
`μHE[0]` is counting measure, every small ball around a point of `∂*s` contains Lebesgue points of
both `s` and its complement, so its perimeter measure is at least one
(`TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn`, after an isometry onto `ℝ`). The reduced
boundary is empty for `n = 0`. The density comparison for Hausdorff measure
(`MeasureTheory.Measure.mul_euclideanHausdorffMeasure_le_measure`) turns these lower density
bounds into the measure inequality

`μHE[n - 1] (A) ≤ |Dχ_s| (A)`     for every `A ⊆ ∂*s`

(`TauCeti.euclideanHausdorffMeasure_le_variationMeasure_preimage`), with the sharp constant one
and with no measurability of `A`. In measure form, `μHE[n - 1]⌊∂*s ≤ |Dχ_s|`
(`TauCeti.euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure`). This is one
of the two inequalities of the identity `|Dχ_s| = μHE[n - 1]⌊∂*s` in De Giorgi's structure theorem.
The reverse inequality uses the rectifiability of the reduced boundary and is not proved here.

Consequences:

* `TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter` and
  `TauCeti.euclideanHausdorffMeasure_reducedBoundary_le_perimeter`: the `(n - 1)`-dimensional
  measure of the reduced boundary is at most the perimeter, `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)` for
  every open `U`; in particular `μHE[n - 1] (∂*s) ≤ P(s; Ω)`.
* `TauCeti.euclideanHausdorffMeasure_reducedBoundary_inter_lt_top`: the reduced boundary has
  locally finite `μHE[n - 1]` measure in `Ω`, `μHE[n - 1] (∂*s ∩ K) < ∞` for every compact
  `K ⊆ Ω`, which is the finiteness hypothesis of the density theorem for countably rectifiable
  sets, for the pieces `∂*s ∩ K`.

The comparison in the other direction, `|Dχ_s| (A) ≤ n ω_n μH[n - 1] (A)` for `A ⊆ ∂*s` with the
raw Hausdorff measure and a nonsharp constant, is
`TauCeti.variationMeasure_preimage_le_mul_hausdorffMeasure`.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Theorem 15.9
  (De Giorgi's structure theorem) and its proof.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.8 (the structure theorem for `∂*E`), using the density comparison of §2.4.2.
-/

public section

namespace TauCeti

open MeasureTheory TopologicalSpace Set Module Filter Metric
open scoped ENNReal Topology

/-- On the real line, a measurable set that charges both itself and its complement in an open
interval has perimeter at least one there. -/
private theorem one_le_perimeter_of_ordConnected {t : Set ℝ} (ht : MeasurableSet t)
    {V : Opens ℝ} (hV : (V : Set ℝ).OrdConnected) (h1 : volume (t ∩ V) ≠ 0)
    (h0 : volume (tᶜ ∩ V) ≠ 0) : 1 ≤ perimeter volume V t := by
  have hu : LocallyIntegrable (t.indicator (1 : ℝ → ℝ)) := by
    rw [Pi.one_def]
    exact (locallyIntegrable_const 1).indicator ht
  have hae := IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume hu
  set P : ℝ → Prop := fun p => Tendsto (fun r => ⨍ y in closedBall p r,
    ‖t.indicator 1 y - t.indicator (1 : ℝ → ℝ) p‖) (𝓝[>] 0) (𝓝 0)
  -- Two ordered Lebesgue points in `V` bound the perimeter by the jump of the indicator.
  have key {p q : ℝ} (hpq : p ≤ q) (hp : p ∈ V) (hq : q ∈ V) (hp' : P p) (hq' : P q) :
      ENNReal.ofReal |t.indicator 1 q - t.indicator (1 : ℝ → ℝ) p| ≤ perimeter volume V t := by
    rw [perimeter_def]
    simpa using Real.ofReal_sum_abs_sub_le_totalVariationOn (hu.locallyIntegrableOn _)
      (x := ![p, q]) (v := fun i => t.indicator 1 (![p, q] i))
      (Fin.monotone_iff_le_succ.2 fun i => by fin_cases i; simpa using hpq) (hV.out hp hq)
      (fun i => by fin_cases i; exacts [hp', hq'])
  -- Lebesgue points of `t` and of its complement in `V`, in either order.
  obtain ⟨a, ⟨hat, haV⟩, ha⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae h1
    (ae_restrict_of_ae hae)
  obtain ⟨b, ⟨hbt, hbV⟩, hb⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae h0
    (ae_restrict_of_ae hae)
  rcases le_total a b with h | h
  · simpa [hat, notMem_of_mem_compl hbt] using key h haV hbV ha hb
  · simpa [hat, notMem_of_mem_compl hbt] using key h hbV haV hb ha

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {Ω U : Opens E} {s : Set E}

/-- In dimension one, the perimeter measure of every small closed ball around a point of the
reduced boundary is at least one. -/
private theorem eventually_one_le_variationMeasure_closedBall (hn : finrank ℝ E = 1) {x : E}
    (hx : x ∈ reducedBoundary volume Ω s) :
    ∀ᶠ r in 𝓝[>] 0,
      1 ≤ variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' closedBall x r) := by
  obtain ⟨ε, hε, hεΩ⟩ := Metric.mem_nhds_iff.1 (Ω.isOpen.mem_nhds (reducedBoundary_subset hx))
  filter_upwards [eventually_perimeter_ball_le_variationMeasure_closedBall_of_mem_reducedBoundary
    hx, Ioo_mem_nhdsGT hε] with r hr hrε
  refine le_trans ?_ hr
  -- Replace `s` by a measurable set agreeing with it on `Ω`.
  have hts : toMeasurable (volume.restrict (Ω : Set E)) s =ᵐ[volume.restrict (Ω : Set E)] s :=
    (nullMeasurableSet_restrict_of_mem_reducedBoundary hx).toMeasurable_ae_eq
  set t := toMeasurable (volume.restrict (Ω : Set E)) s
  have hxt : x ∈ reducedBoundary volume Ω t := by rwa [reducedBoundary_congr_ae hts]
  rw [← perimeter_congr_ae (ae_restrict_of_ae_restrict_of_subset
    ((ball_subset_ball hrε.2.le).trans hεΩ) hts)]
  -- Transport to the real line along a linear isometry equivalence.
  let e : ℝ ≃ₗᵢ[ℝ] E :=
    (OrthonormalBasis.singleton (Fin 1) ℝ).equiv (stdOrthonormalBasis ℝ E) (finCongr hn.symm)
  have he : MeasurePreserving e := e.measurePreserving
  rw [← e.perimeter_comap he]
  have hV : ((Opens.comap (e : C(ℝ, E)) ⟨ball x r, isOpen_ball⟩ : Opens ℝ) : Set ℝ) =
      e ⁻¹' ball x r := rfl
  have hmeas (u : Set E) : volume (e ⁻¹' u ∩ e ⁻¹' ball x r) = volume (u ∩ ball x r) := by
    rw [← preimage_inter, he.measure_preimage_emb e.toMeasurableEquiv.measurableEmbedding]
  refine one_le_perimeter_of_ordConnected ((measurableSet_toMeasurable _ _).preimage
    e.continuous.measurable) ?_ ?_ ?_
  · rw [hV]
    exact convex_iff_ordConnected.1 ((convex_ball x r).linear_preimage e.toLinearMap)
  · rw [hV, hmeas]
    exact (measure_inter_ball_pos hxt hrε.1).ne'
  · rw [hV, ← preimage_compl, hmeas]
    exact (measure_inter_ball_pos (s := tᶜ) (by rwa [reducedBoundary_compl]) hrε.1).ne'

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure.** Let `E` have
dimension `n`, with Lebesgue measure. Every set `A` of points of the reduced boundary `∂*s` of
`s` in `Ω` satisfies `μHE[n - 1] (A) ≤ |Dχ_s| (A)`. No measurability of `A` is assumed. -/
theorem euclideanHausdorffMeasure_le_variationMeasure_preimage {A : Set E}
    (hA : A ⊆ reducedBoundary volume Ω s) :
    μHE[finrank ℝ E - 1] A ≤
      variationMeasure volume Ω (s.indicator 1) (((↑) : Ω → E) ⁻¹' A) := by
  have hAΩ : A ⊆ range ((↑) : Ω → E) := fun x hx => ⟨⟨x, reducedBoundary_subset (hA hx)⟩, rfl⟩
  -- The inclusion of `Ω` carries the subspace distance, as in `isometry_subtype_coe`.
  have hΩ : Isometry ((↑) : Ω → E) := fun _ _ => rfl
  rw [← image_preimage_eq_of_subset hAΩ, hΩ.euclideanHausdorffMeasure_image,
    preimage_image_eq _ Subtype.val_injective]
  refine ENNReal.le_of_forall_lt_one_mul_le fun t ht => ?_
  refine Measure.mul_euclideanHausdorffMeasure_le_measure _ _ fun y hy => ?_
  -- The outer normal is a unit vector, so `E` is not zero-dimensional.
  have h0 : finrank ℝ E ≠ 0 := fun h0 => by
    have := finrank_zero_iff.1 h0
    simpa [Subsingleton.elim (outerNormal volume Ω s y) 0] using norm_outerNormal (hA hy)
  obtain hn | hn := (Nat.one_le_iff_ne_zero.2 h0).eq_or_lt
  · -- In dimension one, `ω₀ r ^ 0 = 1` and every small ball has perimeter measure at least one.
    refine (((eventually_one_le_variationMeasure_closedBall hn.symm (hA hy)).and
      self_mem_nhdsWithin).mono fun r ⟨hr, hr0⟩ => ?_).frequently
    rw [← Subtype.preimage_closedBall, ← hn, Nat.sub_self, volume_euclideanSpace_eq_dirac,
      Measure.dirac_apply_of_mem (mem_closedBall_self (le_of_lt hr0)), mul_one]
    exact ht.le.trans hr
  -- The density of `|Dχ_s|` at `y` is one, so it eventually exceeds `t < 1`.
  have hdens := tendsto_variationMeasure_closedBall_div_volume_closedBall hn (hA hy)
  refine ((hdens.eventually (lt_mem_nhds ht)).mono fun r hr => ?_).frequently
  rw [← Subtype.preimage_closedBall]
  exact ENNReal.mul_le_of_le_div hr.le

/-- **Hausdorff measure on the reduced boundary is at most the perimeter measure**, measure form.
Let `E` have dimension `n`, with Lebesgue measure. The restriction of `μHE[n - 1]` to the
reduced boundary of `s` in `Ω` is at most the perimeter measure `|Dχ_s|`, viewed as a measure on
the ambient space. -/
theorem euclideanHausdorffMeasure_restrict_reducedBoundary_le_map_variationMeasure :
    μHE[finrank ℝ E - 1].restrict (reducedBoundary volume Ω s) ≤
      (variationMeasure volume Ω (s.indicator 1)).map ((↑) : Ω → E) := by
  refine Measure.le_iff.2 fun N hN => ?_
  rw [Measure.restrict_apply hN, Measure.map_apply measurable_subtypeVal hN]
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_right).trans
    (measure_mono (preimage_mono inter_subset_left))

/-- **The measure of the reduced boundary is at most the perimeter**, localized. Let `E` have
dimension `n`, with Lebesgue measure. For every open `U`, the part of the reduced boundary
of `s` in `Ω` lying in `U` satisfies `μHE[n - 1] (∂*s ∩ U) ≤ P(s; U)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ U) ≤ perimeter volume U s := by
  by_cases h : LocallyIntegrableOn (s.indicator (1 : E → ℝ)) Ω volume ∧ ∀ K, IsCompact K →
      K ⊆ Ω → ∃ V : Opens E, K ⊆ (V : Set E) ∧ totalVariationOn volume V (s.indicator 1) ≠ ∞
  · refine le_trans ?_ (perimeter_mono (inf_le_left : U ⊓ Ω ≤ U))
    rw [perimeter_def, ← variationMeasure_preimage_coe h.1 h.2 inf_le_right]
    exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_left).trans
      (measure_mono (preimage_mono fun x hx => ⟨hx.2, reducedBoundary_subset hx.1⟩))
  · simp [reducedBoundary_eq_empty_of_not h]

/-- **The measure of the reduced boundary is at most the perimeter.** Let `E` have dimension
`n`, with Lebesgue measure. The reduced boundary of `s` in `Ω` satisfies
`μHE[n - 1] (∂*s) ≤ P(s; Ω)`. -/
theorem euclideanHausdorffMeasure_reducedBoundary_le_perimeter :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s) ≤ perimeter volume Ω s := by
  simpa only [inter_eq_left.2 reducedBoundary_subset] using
    euclideanHausdorffMeasure_reducedBoundary_inter_le_perimeter (Ω := Ω) (U := Ω) (s := s)

/-- **The reduced boundary has locally finite Hausdorff measure.** Let `E` have dimension `n`, with
Lebesgue measure. For every compact `K ⊆ Ω`, the part of the reduced boundary of `s` in `Ω`
lying in `K` has finite `(n - 1)`-dimensional measure. -/
theorem euclideanHausdorffMeasure_reducedBoundary_inter_lt_top {K : Set E} (hK : IsCompact K)
    (hKΩ : K ⊆ Ω) :
    μHE[finrank ℝ E - 1] (reducedBoundary volume Ω s ∩ K) < ∞ := by
  have hK' : IsCompact (((↑) : Ω → E) ⁻¹' K) :=
    Ω.isOpen.isOpenEmbedding_subtypeVal.isInducing.isCompact_preimage' hK
      (by simpa only [Subtype.range_coe] using hKΩ)
  exact (euclideanHausdorffMeasure_le_variationMeasure_preimage inter_subset_left).trans_lt
    ((measure_mono (preimage_mono inter_subset_right)).trans_lt hK'.measure_lt_top)

end TauCeti
