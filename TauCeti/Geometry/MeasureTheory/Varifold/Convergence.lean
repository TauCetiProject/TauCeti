/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.RieszMarkovKakutani.Real
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
public import Mathlib.Topology.ContinuousMap.CocompactMap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.LiminfLimsup
import Mathlib.Topology.Metrizable.Urysohn
import TauCeti.MeasureTheory.Measure.Prokhorov
import TauCeti.MeasureTheory.Measure.Vague

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
  null for the limit, the masses converge
  (`TauCeti.VarifoldTendsto.tendsto_measure_of_null_frontier`);
* convergence is preserved by push-forward along continuous maps under which preimages of
  compact sets are compact (`TauCeti.VarifoldTendsto.map`); this is how the weights
  `‖V n‖ = π_* V n` of convergent varifolds converge to the weight of the limit;
* **compactness**: on a second countable space, every sequence whose masses are bounded on each
  compact set uniformly in `n` has a subsequence converging to a measure that is finite on
  compact sets (`TauCeti.exists_subseq_varifoldTendsto`; L. Simon, Theorem 4.4).

The compactness theorem is vague compactness of measures with locally bounded masses
(`TauCeti.exists_subseq_tendsto_integral_of_iSup_measure_ne_top`), which applies because a
locally compact, second countable Hausdorff space is σ-compact and metrizable.

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

/-- Along a convergent sequence of locally finite measures, the masses of a relatively compact
measurable set whose boundary is null for the limit converge to its mass for the limit. -/
theorem tendsto_measure_of_null_frontier [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y]
    [HasOuterApproxClosed Y] [∀ n, IsLocallyFiniteMeasure (μ n)] [IsLocallyFiniteMeasure ν]
    (h : VarifoldTendsto μ ν) {s : Set Y} (hs : MeasurableSet s) (hsc : IsCompact (closure s))
    (hb : ν (frontier s) = 0) : Tendsto (fun n ↦ μ n s) atTop (𝓝 (ν s)) :=
  Measure.tendsto_measure_of_null_frontier_of_tendsto_integral_compactlySupported h hs hsc hb

/-- **Upper semicontinuity on compact sets**: along a convergent sequence of locally finite
measures, the limit superior of the masses of a compact set is at most its mass for the limit. -/
theorem limsup_measure_le [T2Space Y] [LocallyCompactSpace Y] [BorelSpace Y]
    [HasOuterApproxClosed Y] [∀ n, IsLocallyFiniteMeasure (μ n)] [IsLocallyFiniteMeasure ν]
    (h : VarifoldTendsto μ ν) {K : Set Y} (hK : IsCompact K) :
    limsup (fun n ↦ μ n K) atTop ≤ ν K :=
  Measure.limsup_measure_le_of_tendsto_integral_compactlySupported h hK

variable [R1Space Y] [LocallyCompactSpace Y]

/-- A convergent sequence of measures that are finite on compact sets has **locally bounded
masses**: on each compact set, the masses are bounded uniformly in `n`. -/
theorem iSup_measure_ne_top [OpensMeasurableSpace Y] [∀ n, IsFiniteMeasureOnCompacts (μ n)]
    (h : VarifoldTendsto μ ν) {K : Set Y} (hK : IsCompact K) : ⨆ n, μ n K ≠ ∞ := by
  obtain ⟨f, hfK, -⟩ := hK.exists_compactlySupported_measure_le_integral_le isOpen_univ
    (subset_univ K)
  obtain ⟨C, hC⟩ := (h f).bddAbove_range
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal C) ENNReal.ofReal_ne_top
    (iSup_le fun n ↦ ?_)
  exact (hfK (μ n)).trans (ENNReal.ofReal_le_ofReal (hC (mem_range_self n)))

/-- **Lower semicontinuity on open sets**: along a convergent sequence of measures, the mass of
an open set for a regular limit is at most the limit inferior of its masses. -/
theorem le_liminf_measure [OpensMeasurableSpace Y] [ν.Regular] (h : VarifoldTendsto μ ν)
    {U : Set Y} (hU : IsOpen U) :
    ν U ≤ liminf (fun n ↦ μ n U) atTop := by
  refine le_of_forall_lt_imp_le_of_dense fun r hr ↦ ?_
  obtain ⟨K, hKU, hK, hrK⟩ := hU.exists_lt_isCompact hr
  obtain ⟨f, hfK, hfU⟩ := hK.exists_compactlySupported_measure_le_integral_le hU hKU
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
  obtain ⟨ν, φ, hν, hφ, hlim⟩ := exists_subseq_tendsto_integral_of_iSup_measure_ne_top μ
    (fun K hK ↦ by rw [iSup_range]; exact hμ K hK) (.of_forall mem_range_self)
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
