/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.Topology.ContinuousMap.CocompactMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Tight.LocallyBounded

/-!
# Varifold convergence

A varifold is a Radon measure on a Grassmann bundle, and a sequence of varifolds `V n` converges
to a varifold `V` when `∫ f dV n → ∫ f dV` for every compactly supported continuous function `f`
(L. Simon, §38–39; W. K. Allard, §3.1). This is vague convergence of measures, and it makes sense
for measures on any topological space, which is how `TauCeti.VarifoldTendsto` is stated. The
convention for rectifiable varifolds in which a sequence converges when its weights do is not
used: the weight does not determine a varifold.

On a locally compact Hausdorff space the measures in question are the locally finite ones, and
this file proves the basic properties of the convergence for them:

* limits are unique among regular measures (`TauCeti.VarifoldTendsto.unique`);
* a convergent sequence has locally bounded masses: `⨆ n, μ n K < ∞` for every compact `K`
  (`TauCeti.VarifoldTendsto.iSup_measure_ne_top`);
* the masses of compact sets are upper semicontinuous and those of open sets lower
  semicontinuous along the sequence (`TauCeti.VarifoldTendsto.limsup_measure_le`,
  `TauCeti.VarifoldTendsto.le_liminf_measure`); for relatively compact sets whose boundary is
  null for the limit, the masses converge by
  `MeasureTheory.Measure.tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported`;
* convergence is preserved by push-forward along continuous maps under which preimages of
  compact sets are compact (`TauCeti.VarifoldTendsto.map`); this is how the weights
  `‖V n‖ = π_* V n` of convergent varifolds converge to the weight of the limit;
* **compactness**: on a second countable space, every sequence whose masses are bounded on each
  compact set uniformly in `n` has a subsequence converging to a measure that is finite on
  compact sets (`TauCeti.exists_subseq_varifoldTendsto`; L. Simon, Theorem 4.4).

The compactness theorem weights the sequence by a strictly positive continuous function that
makes it tight with bounded total mass
(`MeasureTheory.exists_weight_bound_isTightMeasureSet_withDensity`), and applies Prokhorov's
theorem to the weighted measures (`TauCeti.exists_subseq_tendsto_integral_of_withDensity`).

The Dirac masses at a convergent sequence of points converge to the Dirac mass at the limit
(`TauCeti.varifoldTendsto_dirac`), while Dirac masses at points leaving every compact set converge
to `0` (`TauCeti.varifoldTendsto_dirac_zero`). The latter loses all of its mass in the limit, so
the total mass is only lower semicontinuous.

## References

* W. K. Allard, *On the first variation of a varifold*, Ann. of Math. 95 (1972), §3.
* L. Simon, *Lectures on Geometric Measure Theory*, Theorem 4.4 and §38–39.
-/

public section

noncomputable section

open MeasureTheory Filter Set Topology
open scoped ENNReal NNReal CompactlySupported

namespace TauCeti

variable {Y : Type*} [TopologicalSpace Y] [MeasurableSpace Y]

/-- **Varifold convergence**: `μ n` converges to `ν` when `∫ f dμ n → ∫ f dν` for every
compactly supported continuous real function `f`. This is vague convergence of measures; for
varifolds, the measures live on a Grassmann bundle. -/
def VarifoldTendsto (μ : ℕ → Measure Y) (ν : Measure Y) : Prop :=
  ∀ f : C_c(Y, ℝ), Tendsto (fun n ↦ ∫ y, f y ∂μ n) atTop (𝓝 (∫ y, f y ∂ν))

variable {μ : ℕ → Measure Y} {ν ν' : Measure Y}

/-- Unfolding lemma for `TauCeti.VarifoldTendsto`. -/
theorem varifoldTendsto_iff : VarifoldTendsto μ ν ↔
    ∀ f : C_c(Y, ℝ), Tendsto (fun n ↦ ∫ y, f y ∂μ n) atTop (𝓝 (∫ y, f y ∂ν)) :=
  Iff.rfl

/-- A constant sequence converges to its value. -/
theorem varifoldTendsto_const (ν : Measure Y) : VarifoldTendsto (fun _ ↦ ν) ν :=
  fun _ ↦ tendsto_const_nhds

/-- A compactly supported continuous function whose integral against every measure lies between
the mass of a compact set `K` and the mass of an open neighbourhood `U` of `K`; the lower bound
needs the measure to be finite on compact sets. -/
private theorem exists_cutoff [R1Space Y] [LocallyCompactSpace Y] [OpensMeasurableSpace Y]
    {K U : Set Y} (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U) :
    ∃ f : C_c(Y, ℝ), (∀ (ρ : Measure Y) [IsFiniteMeasureOnCompacts ρ],
      ρ K ≤ ENNReal.ofReal (∫ y, f y ∂ρ)) ∧
      ∀ ρ : Measure Y, ENNReal.ofReal (∫ y, f y ∂ρ) ≤ ρ U := by
  obtain ⟨f, hf1, hfc, hfU, hfr⟩ := exists_continuousMap_one_of_isCompact_subset_isOpen hK hU hKU
  refine ⟨⟨f, hfc⟩, fun ρ _ ↦ ?_, fun ρ ↦ ?_⟩
  · exact (CompactlySupportedContinuousMap.integrable ⟨f, hfc⟩).measure_le_integral
      (ae_of_all _ fun y ↦ (hfr y).1) fun _ hy ↦ (hf1 hy).ge
  · exact integral_le_measure (fun y _ ↦ (hfr y).2) fun y hy ↦
      (image_eq_zero_of_notMem_tsupport fun h ↦ hy (hfU h)).le

namespace VarifoldTendsto

/-- The integrals of a compactly supported continuous function along a convergent sequence
converge to its integral against the limit. -/
theorem tendsto_integral (h : VarifoldTendsto μ ν) (f : C_c(Y, ℝ)) :
    Tendsto (fun n ↦ ∫ y, f y ∂μ n) atTop (𝓝 (∫ y, f y ∂ν)) :=
  h f

/-- A subsequence of a convergent sequence converges to the same limit. -/
theorem comp (h : VarifoldTendsto μ ν) {φ : ℕ → ℕ} (hφ : Tendsto φ atTop atTop) :
    VarifoldTendsto (μ ∘ φ) ν :=
  fun f ↦ (h f).comp hφ

/-- **Uniqueness of limits** among regular measures. On a locally compact, second countable
Hausdorff space every measure that is finite on compact sets is regular. -/
theorem unique [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y] [ν.Regular] [ν'.Regular]
    (h : VarifoldTendsto μ ν) (h' : VarifoldTendsto μ ν') : ν = ν' :=
  Measure.ext_of_integral_eq_on_compactlySupported fun f ↦ tendsto_nhds_unique (h f) (h' f)

variable [R1Space Y] [LocallyCompactSpace Y]

/-- A convergent sequence of measures that are finite on compact sets has **locally bounded
masses**: on each compact set, the masses are bounded uniformly in `n`. -/
theorem iSup_measure_ne_top [OpensMeasurableSpace Y] [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    (h : VarifoldTendsto μ ν) {K : Set Y} (hK : IsCompact K) : ⨆ n, μ n K ≠ ∞ := by
  obtain ⟨f, hfK, -⟩ := exists_cutoff hK isOpen_univ (subset_univ K)
  obtain ⟨C, hC⟩ := (h f).bddAbove_range
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top
    (iSup_le fun n ↦ ?_)
  exact (hfK (μ n)).trans (ENNReal.ofReal_le_ofReal (hC (mem_range_self n)))

/-- **Upper semicontinuity on compact sets**: along a convergent sequence of measures that are
finite on compact sets, the limit superior of the masses of a compact set is at most its mass
for the limit. -/
theorem limsup_measure_le [OpensMeasurableSpace Y] [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    [ν.OuterRegular] (h : VarifoldTendsto μ ν) {K : Set Y} (hK : IsCompact K) :
    limsup (fun n ↦ μ n K) atTop ≤ ν K := by
  refine le_of_forall_gt_imp_ge_of_dense fun r hr ↦ ?_
  obtain ⟨U, hKU, hU, hUr⟩ := K.exists_isOpen_lt_of_lt r hr
  obtain ⟨f, hfK, hfU⟩ := exists_cutoff hK hU hKU
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (h f)
  refine limsup_le_of_le (h := ?_)
  filter_upwards [hlim.eventually (gt_mem_nhds ((hfU ν).trans_lt hUr))] with n hn
  exact ((hfK (μ n)).trans_lt hn).le

/-- **Lower semicontinuity on open sets**: along a convergent sequence of measures, the mass of
an open set for a regular limit is at most the limit inferior of its masses. -/
theorem le_liminf_measure [OpensMeasurableSpace Y] [ν.Regular] (h : VarifoldTendsto μ ν)
    {U : Set Y} (hU : IsOpen U) :
    ν U ≤ liminf (fun n ↦ μ n U) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
  obtain ⟨f, hfK, hfU⟩ := exists_cutoff hK hU hKU
  have hlim := (ENNReal.continuous_ofReal.tendsto _).comp (h f)
  refine le_liminf_of_le (h := ?_)
  filter_upwards [hlim.eventually (lt_mem_nhds (hrK.trans_le (hfK ν)))] with n hn
  exact (hn.trans_le (hfU (μ n))).le

end VarifoldTendsto

/-- **Push-forward**: convergence is preserved by the image of measures under a continuous map
under which preimages of compact sets are compact. For the projection of a Grassmann bundle onto
its base, this is the convergence of the weights of convergent varifolds. -/
theorem VarifoldTendsto.map {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
    [OpensMeasurableSpace Y] (h : VarifoldTendsto μ ν) (π : CocompactMap Y X) :
    VarifoldTendsto (fun n ↦ (μ n).map π) (ν.map π) := by
  intro f
  have hπ : Measurable π := (map_continuous π).measurable
  have hf : ∀ ρ : Measure Y, ∫ x, f x ∂ρ.map π = ∫ y, f.comp π y ∂ρ := fun ρ ↦
    integral_map hπ.aemeasurable f.continuous.aestronglyMeasurable
  simpa only [hf] using h (f.comp π)

/-- **Compactness of varifolds.** On a locally compact, second countable Hausdorff space, every
sequence of measures whose masses on each compact set are bounded uniformly in `n` has a
subsequence converging to a measure that is finite on compact sets. -/
theorem exists_subseq_varifoldTendsto [T2Space Y] [LocallyCompactSpace Y]
    [SecondCountableTopology Y] [BorelSpace Y] (μ : ℕ → Measure Y)
    (hμ : ∀ K, IsCompact K → ⨆ n, μ n K ≠ ∞) :
    ∃ (ν : Measure Y) (φ : ℕ → ℕ), IsFiniteMeasureOnCompacts ν ∧ StrictMono φ ∧
      VarifoldTendsto (μ ∘ φ) ν := by
  obtain ⟨w, hw, hpos, hmass, htight⟩ := exists_weight_bound_isTightMeasureSet_withDensity μ hμ
  obtain ⟨ν, φ, hν, hφ, hlim⟩ :=
    exists_subseq_tendsto_integral_of_withDensity μ w hw hpos 2 (by simpa using hmass) htight
  exact ⟨ν, φ, inferInstance, hφ, hlim⟩

/-- Dirac masses at a convergent sequence of points converge to the Dirac mass at the limit. -/
theorem varifoldTendsto_dirac [OpensMeasurableSpace Y] {x : ℕ → Y} {y : Y}
    (hx : Tendsto x atTop (𝓝 y)) :
    VarifoldTendsto (fun n ↦ Measure.dirac (x n)) (Measure.dirac y) := by
  intro f
  simp only [integral_dirac' (f : Y → ℝ) _ (map_continuous f).stronglyMeasurable]
  exact ((map_continuous f).tendsto y).comp hx

/-- Dirac masses at a sequence of points leaving every compact set converge to `0`, although each
has mass one. -/
theorem varifoldTendsto_dirac_zero [OpensMeasurableSpace Y] {x : ℕ → Y}
    (hx : Tendsto x atTop (cocompact Y)) :
    VarifoldTendsto (fun n ↦ Measure.dirac (x n)) 0 := by
  intro f
  simp only [integral_dirac' (f : Y → ℝ) _ (map_continuous f).stronglyMeasurable,
    integral_zero_measure]
  exact f.hasCompactSupport.is_zero_at_infty.comp hx

end TauCeti
