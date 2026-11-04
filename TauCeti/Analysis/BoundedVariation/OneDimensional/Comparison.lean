/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.OneDimensional.Basic
public import TauCeti.Analysis.BoundedVariation.VariationMeasure
import Mathlib.Analysis.BoundedVariation
import TauCeti.Analysis.BoundedVariation.Real
import TauCeti.MeasureTheory.Covering.DensityTheorem

/-!
# Equality of classical and distributional variation on the line

For a real-valued function of globally bounded classical variation, its distributional
variation on every open set equals the variation of Mathlib's classical derivative measure.
Consequently the distributional variation measure is the restriction of that measure's
variation to the domain. Its atoms are exactly the absolute sizes of the jumps.

No continuity or whole-line integrability is assumed. The classical variation must be taken
on the right-limit representative: changing the value at a single point can change pointwise
variation, but not distributional variation. On open intervals the latter is exactly the
classical variation of the right-limit representative.

The reverse bound uses partitions through Lebesgue points and approximation from the right;
it complements the integration-by-parts upper bound in `OneDimensional.Basic`.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, §3.2 (pointwise and essential variation in one variable).
-/

public section

open MeasureTheory Set Filter TopologicalSpace
open scoped ENNReal Topology

namespace BoundedVariationOn

variable {f : ℝ → ℝ}

/-- Approximation of a partition from the right by simultaneous Lebesgue points. -/
private theorem ofReal_sum_abs_sub_rightLim_le_totalVariationOn
    (hf : BoundedVariationOn f univ) {a b : ℝ} {n : ℕ} {x : Fin (n + 1) → ℝ}
    (hx : Monotone x) (hxa : a < x 0) (hxb : x (Fin.last n) < b) :
    ENNReal.ofReal (∑ i : Fin n, |f.rightLim (x i.succ) - f.rightLim (x i.castSucc)|) ≤
      TauCeti.totalVariationOn volume ⟨Ioo a b, isOpen_Ioo⟩ f := by
  have hloc : LocallyIntegrable f := hf.memLp_top.locallyIntegrable le_top
  let P (z : ℝ) := Tendsto (fun r => ⨍ y in Metric.closedBall z r, ‖f y - f z‖)
    (𝓝[>] 0) (𝓝 0)
  have hP : ∀ᵐ z, P z :=
    IsUnifLocDoublingMeasure.ae_tendsto_average_closedBall_norm_sub volume hloc
  have hshift : ∀ᵐ t, ∀ i, P (x i + t) := by
    rw [ae_all_iff]
    intro i
    exact (measurePreserving_add_left volume (x i)).quasiMeasurePreserving.ae hP
  -- Each translate of the exceptional set is null. Avoid their finite union while making
  -- the common positive shift tend to zero and keeping the last point below `b`.
  have hex (k : ℕ) : ∃ t ∈ Ioo 0 (min (1 / ((k : ℝ) + 1)) (b - x (Fin.last n))),
      ∀ i, P (x i + t) := by
    have hpos : 0 < min (1 / ((k : ℝ) + 1)) (b - x (Fin.last n)) := by
      apply lt_min <;> positivity
    exact Measure.exists_mem_of_measure_ne_zero_of_ae
      (by simpa only [Real.volume_Ioo, sub_zero, ne_eq, ENNReal.ofReal_eq_zero, not_le] using hpos)
      (ae_restrict_of_ae hshift)
  choose t ht hgood using hex
  have htlim : Tendsto t atTop (𝓝 0) := by
    apply squeeze_zero (fun k => (ht k).1.le) (fun k => (ht k).2.le.trans (min_le_left _ _))
    simpa using (tendsto_one_div_add_atTop_nhds_zero_nat :
      Tendsto (fun k : ℕ => (1 : ℝ) / (k + 1)) atTop (𝓝 0))
  have hlim (i) : Tendsto (fun k => f (x i + t k)) atTop (𝓝 (f.rightLim (x i))) := by
    apply (hf.tendsto_rightLim (x i)).comp
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · simpa using tendsto_const_nhds.add htlim
    · exact Eventually.of_forall fun k => by simpa using (ht k).1
  -- Apply the distributional partition bound before passing to the right limits.
  refine le_of_tendsto' (ENNReal.tendsto_ofReal
    (tendsto_finsetSum _ fun i _ => ((hlim i.succ).sub (hlim i.castSucc)).abs)) fun k => ?_
  exact TauCeti.Real.ofReal_sum_abs_sub_le_totalVariationOn (m := n)
    (x := fun i => x i + t k) (v := fun i => f (x i + t k))
    (hloc.locallyIntegrableOn _) (fun i j hij => add_le_add (hx hij) le_rfl) (fun z hz => by
      have ht0 := (ht k).1
      have htb := (ht k).2.trans_le (min_le_right _ _)
      exact ⟨by simpa using lt_of_lt_of_le (by linarith : a < x 0 + t k) hz.1,
        by simpa using lt_of_le_of_lt hz.2 (by linarith : x (Fin.last n) + t k < b)⟩)
    (hgood k)

/-- On an open interval, distributional variation equals classical variation of the
right-limit representative. Isolated choices of values of the original function do not count.
The statement includes empty intervals. -/
theorem totalVariationOn_Ioo_eq_eVariationOn_rightLim
    (hf : BoundedVariationOn f univ) (a b : ℝ) :
    TauCeti.totalVariationOn volume ⟨Ioo a b, isOpen_Ioo⟩ f =
      eVariationOn f.rightLim (Ioo a b) := by
  refine le_antisymm ?_ ?_
  · rw [← hf.variation_vectorMeasure_Ioo_right]
    exact hf.totalVariationOn_le_variation_vectorMeasure _
  · rw [eVariationOn.eVariationOn_eq_strictMonoOn]
    refine iSup_le ?_
    rintro ⟨n, u, hu, hus⟩
    let x : Fin (n + 1) → ℝ := fun i => u i
    have hx : Monotone x := fun i j hij => hu.monotoneOn
      (by simp; omega) (by simp; omega) hij
    have ha : a < x 0 := (hus 0 (by simp)).1
    have hb : x (Fin.last n) < b := (hus n (by simp)).2
    have h := ofReal_sum_abs_sub_rightLim_le_totalVariationOn hf hx ha hb
    rw [ENNReal.ofReal_sum_of_nonneg (fun i _ => abs_nonneg _)] at h
    simp only [x, Fin.val_succ, Fin.val_castSucc] at h
    rw [Fin.sum_univ_eq_sum_range
      (fun i => ENNReal.ofReal |f.rightLim (u (i + 1)) - f.rightLim (u i)|) n] at h
    simpa only [edist_dist, Real.dist_eq] using h

/-- On every open set, distributional variation equals the variation of the classical
derivative measure, even for functions that are not integrable on the whole line.
The measure on the right includes jump atoms and the singular continuous part. -/
theorem totalVariationOn_eq_variation_vectorMeasure
    (hf : BoundedVariationOn f univ) (Ω : Opens ℝ) :
    TauCeti.totalVariationOn volume Ω f = hf.vectorMeasure.variation Ω := by
  have hloc : LocallyIntegrableOn f (⊤ : Opens ℝ) :=
    hf.memLp_top.locallyIntegrable le_top |>.locallyIntegrableOn _
  have hfin : ∀ K : Set ℝ, IsCompact K → K ⊆ (⊤ : Opens ℝ) →
      ∃ U : Opens ℝ, K ⊆ (U : Set ℝ) ∧ TauCeti.totalVariationOn volume U f ≠ ∞ :=
    fun K _ _ => ⟨⊤, subset_univ K, (hf.totalVariationOn_lt_top ⊤).ne⟩
  let ν := (TauCeti.variationMeasure volume ⊤ f).map ((↑) : (⊤ : Opens ℝ) → ℝ)
  have hν (U : Opens ℝ) : ν U = TauCeti.totalVariationOn volume U f := by
    rw [Measure.map_apply measurable_subtype_coe U.isOpen.measurableSet,
      TauCeti.variationMeasure_preimage_coe hloc hfin le_top]
  have : IsFiniteMeasure ν := ⟨by
    simpa using (hν ⊤).trans_lt (hf.totalVariationOn_lt_top ⊤)⟩
  have heq : ν = hf.vectorMeasure.variation := by
    apply Real.measure_ext_Ioo_rat
    intro a b
    exact (hν ⟨Ioo (a : ℝ) b, isOpen_Ioo⟩).trans
      ((hf.totalVariationOn_Ioo_eq_eVariationOn_rightLim a b).trans
        hf.variation_vectorMeasure_Ioo_right.symm)
  rw [← hν Ω, heq]

/-- The distributional variation measure on any open domain is the pullback of the variation
of the classical derivative measure. This identifies the measures on all sets, not just
intervals. -/
theorem variationMeasure_eq_comap_variation_vectorMeasure
    (hf : BoundedVariationOn f univ) (Ω : Opens ℝ) :
    TauCeti.variationMeasure volume Ω f =
      hf.vectorMeasure.variation.comap ((↑) : Ω → ℝ) := by
  -- Fix the domain as `Ω`, rather than the subtype of its underlying set, for rewriting.
  have hemb : Topology.IsOpenEmbedding ((↑) : Ω → ℝ) := Ω.isOpen.isOpenEmbedding_subtypeVal
  have := Measure.OuterRegular.comap' hf.vectorMeasure.variation hemb.continuous
    hemb.measurableEmbedding
  apply (TauCeti.eq_variationMeasure
    (hf.memLp_top.locallyIntegrable le_top |>.locallyIntegrableOn _)
    (fun K _ _ => ⟨⊤, subset_univ K, (hf.totalVariationOn_lt_top ⊤).ne⟩) ?_).symm
  intro U hU
  rw [hemb.measurableEmbedding.comap_apply]
  rw [image_preimage_eq_of_subset (f := ((↑) : Ω → ℝ)) (by simpa using hU)]
  exact (hf.totalVariationOn_eq_variation_vectorMeasure U).symm

/-- On any subset of an open domain, distributional variation is the variation of the
classical derivative measure evaluated on its image in the real line. -/
@[simp]
theorem variationMeasure_apply (hf : BoundedVariationOn f univ)
    (Ω : Opens ℝ) (s : Set Ω) :
    TauCeti.variationMeasure volume Ω f s = hf.vectorMeasure.variation (Subtype.val '' s) := by
  -- The embedding theorem is stated for the underlying set's subtype; specify `Ω` explicitly.
  have hemb : Topology.IsOpenEmbedding ((↑) : Ω → ℝ) := Ω.isOpen.isOpenEmbedding_subtypeVal
  rw [hf.variationMeasure_eq_comap_variation_vectorMeasure, hemb.measurableEmbedding.comap_apply]

/-- The atom of distributional variation at a point is the absolute size of its jump.
In particular changing only the value at the point creates no distributional atom. -/
theorem variationMeasure_singleton (hf : BoundedVariationOn f univ)
    (Ω : Opens ℝ) (x : Ω) :
    TauCeti.variationMeasure volume Ω f {x} = ‖f.rightLim x - f.leftLim x‖ₑ := by
  rw [hf.variationMeasure_apply, image_singleton, hf.variation_vectorMeasure_singleton]

end BoundedVariationOn
