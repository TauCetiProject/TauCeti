/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.Probability.Cdf

/-!
# The quantile function of a real law

The *quantile function*, or generalized inverse cumulative distribution function, of a measure
`μ` on `ℝ` sends a level `t` to the least point at which `ProbabilityTheory.cdf μ` reaches `t`:

`μ.quantile t = sInf {x | t ≤ cdf μ x}`.

Because `cdf μ` is monotone and right continuous with limits `0` at `-∞` and `1` at `+∞`, that
infimum is attained for every level `t` strictly between `0` and `1`, and the defining set is
exactly the closed ray to the right of the quantile. The quantile is therefore characterized by
the Galois property `μ.quantile t ≤ x ↔ t ≤ cdf μ x`. Outside `Ioo 0 1` the infimum ranges over
all of `ℝ` or over the empty set, so the value there is the junk value `0`; every statement below
restricts the level to `Ioo 0 1`, and that is also the interval the uniform law is taken on.

The main result is **inverse transform sampling**: for a probability measure `μ` the quantile
function pushes the uniform law on the open unit interval forward to `μ`. It presents every real
law as the law of one explicit measurable function of a single uniform variable, and it is what
makes the monotone rearrangement of two real laws a transport plan between them.

## Main definitions

* `MeasureTheory.Measure.quantile` — the generalized inverse of the cumulative distribution
  function.

## Main statements

* `MeasureTheory.Measure.quantile_le_iff` — the Galois characterization of the quantile, with
  `MeasureTheory.Measure.setOf_le_cdf_eq_Ici` its set-level form and
  `MeasureTheory.Measure.lt_quantile_iff` its negation;
* `MeasureTheory.Measure.map_quantile_volume_Ioo` — inverse transform sampling: the quantile
  function pushes the uniform law on `Ioo 0 1` forward to the original law, packaged as
  `MeasureTheory.Measure.measurePreserving_quantile`;
* `MeasureTheory.Measure.quantile_dirac` — the quantile function of a Dirac law.

## References

* R. B. Nelsen, *An Introduction to Copulas*, Springer 2006, §2.3, for the generalized inverse
  and its Galois property.
* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

/-- The **quantile function** of a measure on `ℝ`: the least point at which its cumulative
distribution function reaches the level `t`.

This is the honest generalized inverse of `ProbabilityTheory.cdf μ` for `t` in `Set.Ioo 0 1`; at
other levels the defining infimum ranges over all of `ℝ` or over the empty set, and the value is
the junk value `0`. -/
def quantile (μ : Measure ℝ) (t : ℝ) : ℝ := sInf {x : ℝ | t ≤ cdf μ x}

/-- The quantile function is the infimum of the points at which the cumulative distribution
function reaches the level. The definition's body is not exposed, so this is the lemma downstream
modules should rewrite with. -/
theorem quantile_def (μ : Measure ℝ) (t : ℝ) :
    μ.quantile t = sInf {x : ℝ | t ≤ cdf μ x} := (rfl)

variable {t x : ℝ}

/-- Below the level `1` some point has cumulative mass at least the level, because the cumulative
distribution function tends to `1` at `+∞`. -/
theorem nonempty_setOf_le_cdf (μ : Measure ℝ) (ht : t < 1) : {x : ℝ | t ≤ cdf μ x}.Nonempty :=
  ((tendsto_cdf_atTop μ).eventually (eventually_gt_nhds ht)).exists.imp fun _ h ↦ h.le

/-- Above the level `0` the points whose cumulative mass reaches the level are bounded below,
because the cumulative distribution function tends to `0` at `-∞`. -/
theorem bddBelow_setOf_le_cdf (μ : Measure ℝ) (ht : 0 < t) : BddBelow {x : ℝ | t ≤ cdf μ x} := by
  obtain ⟨a, ha⟩ :=
    eventually_atBot.mp ((tendsto_cdf_atBot μ).eventually (eventually_lt_nhds ht))
  refine ⟨a, fun x hx ↦ ?_⟩
  by_contra hxa
  exact absurd (ha x (not_le.mp hxa).le) (not_lt.mpr hx)

/-- At a nonpositive level the quantile function takes the junk value `0`: every point has
cumulative mass at least the level. -/
theorem quantile_of_nonpos (μ : Measure ℝ) (ht : t ≤ 0) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = univ := eq_univ_of_forall fun x ↦ ht.trans (cdf_nonneg μ x)
  rw [quantile_def, hset, Real.sInf_univ]

/-- Above the level `1` the quantile function takes the junk value `0`: no point has cumulative
mass that large. -/
theorem quantile_of_one_lt (μ : Measure ℝ) (ht : 1 < t) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ absurd (hx.trans (cdf_le_one μ x)) (not_le.2 ht)
  rw [quantile_def, hset, Real.sInf_empty]

/-- The infimum defining the quantile is attained: right continuity of the cumulative
distribution function makes the level still dominated at the quantile itself. -/
theorem le_cdf_quantile (μ : Measure ℝ) (h1 : t < 1) : t ≤ cdf μ (μ.quantile t) := by
  have key : ∀ r : Ioi (μ.quantile t), t ≤ cdf μ r := by
    rintro ⟨r, hr⟩
    obtain ⟨y, hy, hyr⟩ := exists_lt_of_csInf_lt (nonempty_setOf_le_cdf μ h1) hr
    exact hy.trans (monotone_cdf μ hyr.le)
  have h := le_ciInf key
  rwa [StieltjesFunction.iInf_Ioi_eq] at h

/-- **The Galois characterization of the quantile.** For a level strictly between `0` and `1`,
the quantile lies below a point exactly when the cumulative distribution function at that point
reaches the level. -/
theorem quantile_le_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    μ.quantile t ≤ x ↔ t ≤ cdf μ x :=
  ⟨fun h ↦ (le_cdf_quantile μ h1).trans (monotone_cdf μ h),
    fun h ↦ csInf_le (bddBelow_setOf_le_cdf μ h0) h⟩

/-- The set of points whose cumulative mass reaches a level strictly between `0` and `1` is the
closed ray to the right of the quantile at that level. -/
theorem setOf_le_cdf_eq_Ici (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    {x : ℝ | t ≤ cdf μ x} = Ici (μ.quantile t) := by
  ext x
  exact (quantile_le_iff μ h0 h1).symm

/-- A point lies strictly below the quantile at a level exactly when its cumulative mass has not
yet reached that level. -/
theorem lt_quantile_iff (μ : Measure ℝ) (h0 : 0 < t) (h1 : t < 1) :
    x < μ.quantile t ↔ cdf μ x < t := by
  simpa only [not_le] using (quantile_le_iff (x := x) μ h0 h1).not

/-- The quantile function is monotone on the levels where it is the honest generalized
inverse. -/
theorem monotoneOn_quantile (μ : Measure ℝ) : MonotoneOn μ.quantile (Ioo 0 1) := by
  rintro s ⟨hs0, hs1⟩ t ⟨ht0, ht1⟩ hst
  exact (quantile_le_iff μ hs0 hs1).mpr (hst.trans (le_cdf_quantile μ ht1))

/-- Off `Ioo 0 1` the quantile function is constant equal to its junk value `0`, except possibly
at the single level `1`; that is enough for the part of a sublevel set living there to be
measurable. -/
private theorem measurableSet_quantile_preimage_Iic_inter_compl (μ : Measure ℝ) (x : ℝ) :
    MeasurableSet (μ.quantile ⁻¹' Iic x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
  have hzero : ∀ ⦃s : ℝ⦄, s ∈ Iic (0 : ℝ) ∪ Ioi 1 → μ.quantile s = 0 := by
    rintro s (hs | hs)
    · exact quantile_of_nonpos μ hs
    · exact quantile_of_one_lt μ hs
  have hcover : (Ioo (0 : ℝ) 1)ᶜ = (Iic (0 : ℝ) ∪ Ioi 1) ∪ {(1 : ℝ)} := by
    ext s
    simp only [mem_compl_iff, mem_Ioo, not_and_or, not_lt, mem_union, mem_Iic, mem_Ioi,
      mem_singleton_iff]
    grind
  rw [hcover, inter_union_distrib_left]
  refine MeasurableSet.union ?_ ((subsingleton_singleton.anti inter_subset_right).measurableSet)
  by_cases hx : (0 : ℝ) ≤ x
  · have hall : μ.quantile ⁻¹' Iic x ∩ (Iic (0 : ℝ) ∪ Ioi 1) = Iic (0 : ℝ) ∪ Ioi 1 :=
      inter_eq_right.mpr fun s hs ↦ by simp [mem_preimage, hzero hs, hx]
    rw [hall]
    exact measurableSet_Iic.union measurableSet_Ioi
  · have hnone : μ.quantile ⁻¹' Iic x ∩ (Iic (0 : ℝ) ∪ Ioi 1) = ∅ := by
      refine eq_empty_of_forall_notMem fun s hs ↦ hx ?_
      have hqs := hs.1
      rwa [mem_preimage, hzero hs.2, mem_Iic] at hqs
    rw [hnone]
    exact MeasurableSet.empty

/-- The quantile function is measurable. -/
@[fun_prop]
theorem measurable_quantile (μ : Measure ℝ) : Measurable μ.quantile := by
  refine measurable_of_Iic fun x ↦ ?_
  have hsplit : μ.quantile ⁻¹' Iic x =
      (Ioo (0 : ℝ) 1 ∩ Iic (cdf μ x)) ∪ (μ.quantile ⁻¹' Iic x ∩ (Ioo (0 : ℝ) 1)ᶜ) := by
    ext s
    by_cases hs : s ∈ Ioo (0 : ℝ) 1
    · simp [hs, quantile_le_iff μ hs.1 hs.2]
    · simp [hs]
  rw [hsplit]
  exact (measurableSet_Ioo.inter measurableSet_Iic).union
    (measurableSet_quantile_preimage_Iic_inter_compl μ x)

/-- **Inverse transform sampling.** The quantile function of a probability law on `ℝ` pushes the
uniform law on the open unit interval forward to that law. -/
theorem map_quantile_volume_Ioo (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    (volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile = μ := by
  have huniform : IsProbabilityMeasure (volume.restrict (Ioo (0 : ℝ) 1)) := ⟨by simp⟩
  have hmap : IsProbabilityMeasure ((volume.restrict (Ioo (0 : ℝ) 1)).map μ.quantile) :=
    (Measure.isProbabilityMeasure_map_iff (measurable_quantile μ).aemeasurable).mpr huniform
  refine Measure.ext_of_Iic _ _ fun x ↦ ?_
  rw [Measure.map_apply (measurable_quantile μ) measurableSet_Iic,
    Measure.restrict_apply (measurable_quantile μ measurableSet_Iic), ← ofReal_cdf μ x]
  have hsub : μ.quantile ⁻¹' Iic x ∩ Ioo (0 : ℝ) 1 = Ioc (0 : ℝ) (cdf μ x) \ {(1 : ℝ)} := by
    ext s
    simp only [mem_inter_iff, mem_preimage, mem_Iic, mem_Ioo, Set.mem_sdiff, mem_Ioc,
      mem_singleton_iff]
    constructor
    · rintro ⟨hq, hs0, hs1⟩
      exact ⟨⟨hs0, (quantile_le_iff μ hs0 hs1).mp hq⟩, hs1.ne⟩
    · rintro ⟨⟨hs0, hsc⟩, hs1⟩
      have hlt : s < 1 := lt_of_le_of_ne (hsc.trans (cdf_le_one μ x)) hs1
      exact ⟨(quantile_le_iff μ hs0 hlt).mpr hsc, hs0, hlt⟩
  rw [hsub, measure_sdiff_null (measure_singleton _), Real.volume_Ioc, sub_zero]

/-- Inverse transform sampling, as a measure-preserving map from the uniform law on the open unit
interval. -/
theorem measurePreserving_quantile (μ : Measure ℝ) [IsProbabilityMeasure μ] :
    MeasurePreserving μ.quantile (volume.restrict (Ioo (0 : ℝ) 1)) μ :=
  ⟨measurable_quantile μ, map_quantile_volume_Ioo μ⟩

/-- At every level where it is the honest generalized inverse, the quantile function of a Dirac
law is its atom. -/
@[simp]
theorem quantile_dirac (a : ℝ) (h0 : 0 < t) (h1 : t < 1) : (dirac a).quantile t = a := by
  refine le_antisymm ((quantile_le_iff _ h0 h1).mpr ?_) (le_of_forall_lt fun x hx ↦ ?_)
  · simpa using h1.le
  · exact (lt_quantile_iff _ h0 h1).mpr (by simpa [not_le.mpr hx] using h0)

end MeasureTheory.Measure
