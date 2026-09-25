/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import TauCeti.MeasureTheory.Measure.MeasurePreserving
public import TauCeti.Probability.Cdf

/-!
# The quantile function of a real law

The *quantile function*, or generalized inverse cumulative distribution function, of a measure
`μ` on `ℝ` sends a level `t` to the least point at which `ProbabilityTheory.cdf μ` reaches `t`:

`μ.quantile t = sInf {x | t ≤ cdf μ x}`.

Because `cdf μ` is monotone and right continuous with limits `0` at `-∞` and `1` at `+∞`, that
infimum is attained for every level `t` strictly between `0` and `1`, and the defining set is
exactly the closed ray to the right of the quantile. The quantile is therefore characterized by
the Galois property `μ.quantile t ≤ x ↔ t ≤ cdf μ x`. At levels `t ≤ 0` and `1 < t` the infimum
ranges over all of `ℝ` or over the empty set, so the value there is the junk value `0`. The
endpoint level `t = 1` is not junk: the quantile there is the least point of full cumulative mass
when such a point exists (for instance `(dirac a).quantile 1 = a`), and `0` when the law has
unbounded support to the right. The inverse characterizations below use levels in `Ioo 0 1`,
which is also the interval the uniform law is taken on.

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
* `MeasureTheory.Measure.cdf_map_eq_volume_restrict` — the probability integral transform for an
  atomless real law;
* `MeasureTheory.Measure.cdf_quantile_ae` and
  `MeasureTheory.Measure.quantile_cdf_ae` — the two almost-everywhere inverse laws.

## References

* R. B. Nelsen, *An Introduction to Copulas*, Springer 2006, §2.3, for the generalized inverse
  and its Galois property.
* P. Embrechts and M. Hofert, *A note on generalized inverses*, Mathematical Methods of
  Operations Research 77 (2013), 423--432.
-/

public section

noncomputable section

open Filter MeasureTheory ProbabilityTheory Set Function Topology

namespace MeasureTheory.Measure

/-- The **quantile function** of a measure on `ℝ`: the least point at which its cumulative
distribution function reaches the level `t`.

This is the honest generalized inverse of `ProbabilityTheory.cdf μ` for `t` in `Set.Ioo 0 1`. At
levels `t ≤ 0` and `1 < t` the defining infimum ranges over all of `ℝ` or over the empty set, and
the value is the junk value `0` (`quantile_of_nonpos`, `quantile_of_one_lt`). At the endpoint
level `t = 1` the value is the least point where the cumulative distribution function reaches `1`
if there is one, and `0` otherwise. -/
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
@[simp]
theorem quantile_of_nonpos (μ : Measure ℝ) (ht : t ≤ 0) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = univ := eq_univ_of_forall fun x ↦ ht.trans (cdf_nonneg μ x)
  rw [quantile_def, hset, Real.sInf_univ]

/-- Above the level `1` the quantile function takes the junk value `0`: no point has cumulative
mass that large. -/
@[simp]
theorem quantile_of_one_lt (μ : Measure ℝ) (ht : 1 < t) : μ.quantile t = 0 := by
  have hset : {x : ℝ | t ≤ cdf μ x} = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ absurd (hx.trans (cdf_le_one μ x)) (not_le.2 ht)
  rw [quantile_def, hset, Real.sInf_empty]

/-- The cumulative distribution function at the quantile reaches every level strictly below
`1`. -/
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
@[simp]
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
@[simp]
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

/-- The measure of the sublevel set `{x | cdf ν x ≤ y}` is `ENNReal.ofReal y` when
`y < 1`. -/
private lemma cdf_sublevel_measure (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν]
    (y : ℝ) (hy1 : y < 1) :
    ν {x | cdf ν x ≤ y} = ENNReal.ofReal y := by
  set S : Set ℝ := {x | cdf ν x ≤ y}
  have hScl : IsClosed S := isClosed_Iic.preimage (continuous_cdf_of_noAtoms ν)
  have hevt : ∀ᶠ x in atTop, y < cdf ν x :=
    (tendsto_cdf_atTop ν).eventually (eventually_gt_nhds hy1)
  obtain ⟨M, hM⟩ := eventually_atTop.mp hevt
  have hSbdd : BddAbove S := by
    refine ⟨M, fun x hx => ?_⟩
    by_contra hxM
    exact absurd (hM x (le_of_lt (not_le.mp hxM))) (not_lt.2 hx)
  by_cases hSne : S.Nonempty
  · set q := sSup S
    have hq_mem : q ∈ S := hScl.csSup_mem hSne hSbdd
    have hSeq : S = Iic q := by
      ext x
      constructor
      · intro hx; exact le_csSup hSbdd hx
      · intro hx
        exact le_trans ((cdf ν).mono hx) hq_mem
    have hcdfq : cdf ν q = y := by
      refine le_antisymm hq_mem ?_
      have htend : Tendsto (cdf ν) (𝓝[>] q) (𝓝 (cdf ν q)) :=
        ((continuous_cdf_of_noAtoms ν).tendsto q).mono_left nhdsWithin_le_nhds
      have hevt2 : ∀ᶠ x in 𝓝[>] q, y ≤ cdf ν x := by
        refine Filter.eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
        have : x ∉ S := fun hxS => absurd (le_csSup hSbdd hxS) (not_le.2 hx)
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto htend hevt2
    rw [hSeq, ← ofReal_cdf ν q, hcdfq]
  · rw [not_nonempty_iff_eq_empty] at hSne
    have hyle : y ≤ 0 := by
      have hfor : ∀ᶠ x in atBot, y ≤ cdf ν x := by
        refine Filter.Eventually.of_forall (fun x => ?_)
        have : x ∉ S := by rw [hSne]; simp
        exact le_of_lt (not_le.mp this)
      exact ge_of_tendsto (tendsto_cdf_atBot ν) hfor
    have hνS : ν S = 0 := by rw [hSne]; exact measure_empty
    rw [ENNReal.ofReal_eq_zero.mpr hyle]
    exact hνS

/-- **The probability integral transform.** The CDF of an atomless probability measure on
`ℝ` pushes the measure forward to Lebesgue measure restricted to `[0, 1]`. -/
@[simp]
theorem cdf_map_eq_volume_restrict (ν : Measure ℝ) [IsProbabilityMeasure ν]
    [NullSingletonClass ν] :
    Measure.map (cdf ν) ν = volume.restrict (Set.Icc (0 : ℝ) 1) := by
  have hmeas : Measurable (cdf ν) := (cdf ν).mono.measurable
  refine Measure.ext_of_Iic _ _ (fun y => ?_)
  rw [Measure.map_apply hmeas measurableSet_Iic, Measure.restrict_apply measurableSet_Iic]
  rcases lt_or_ge y 1 with hy1 | hy1
  · have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 y := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨hxy, hx0, _⟩; exact ⟨hx0, hxy⟩
      · rintro ⟨hx0, hxy⟩; exact ⟨hxy, hx0, le_of_lt (lt_of_le_of_lt hxy hy1)⟩
    rw [hrset, Real.volume_Icc, sub_zero]
    exact cdf_sublevel_measure ν y hy1
  · have hset : cdf ν ⁻¹' Iic y = univ := by
      ext x
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      exact le_trans (cdf_le_one ν x) hy1
    have hrset : Iic y ∩ Icc (0 : ℝ) 1 = Icc 0 1 := by
      ext x
      simp only [mem_inter_iff, mem_Iic, mem_Icc, and_iff_right_iff_imp]
      rintro ⟨_, hx1⟩; exact le_trans hx1 hy1
    rw [hset, hrset, measure_univ, Real.volume_Icc, sub_zero, ENNReal.ofReal_one]

/-- On the closed unit interval, the CDF and quantile are inverse almost everywhere. -/
theorem cdf_quantile_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun u => cdf ν (ν.quantile u)) =ᵐ[volume.restrict (Set.Icc 0 1)] id := by
  refine (ae_restrict_iff' measurableSet_Icc).mpr ?_
  filter_upwards [Set.Countable.ae_notMem
      ((Set.countable_singleton (1 : ℝ)).insert 0) volume] with u hu huIcc
  have hu0 : u ≠ 0 := fun h => hu (by simp [h])
  have hu1 : u ≠ 1 := fun h => hu (by simp [h])
  have h0 : 0 < u := lt_of_le_of_ne huIcc.1 (Ne.symm hu0)
  have h1 : u < 1 := lt_of_le_of_ne huIcc.2 hu1
  have hlower : u ≤ cdf ν (ν.quantile u) := le_cdf_quantile ν h1
  have hupper : cdf ν (ν.quantile u) ≤ u := by
    have htend : Tendsto (cdf ν) (𝓝[<] (ν.quantile u))
        (𝓝 (cdf ν (ν.quantile u))) :=
      ((continuous_cdf_of_noAtoms ν).tendsto _).mono_left nhdsWithin_le_nhds
    have hevt : ∀ᶠ x in 𝓝[<] (ν.quantile u), cdf ν x ≤ u := by
      refine eventually_of_mem self_mem_nhdsWithin (fun x hx => ?_)
      have hxlt : x < ν.quantile u := hx
      have hqnot : ¬ ν.quantile u ≤ x := not_le_of_gt hxlt
      have hnot : ¬ u ≤ cdf ν x := by
        intro hcdf
        exact hqnot ((quantile_le_iff ν h0 h1).mpr hcdf)
      exact le_of_lt (not_le.mp hnot)
    exact le_of_tendsto htend hevt
  exact le_antisymm hupper hlower

/-- The quantile of the CDF is the identity almost everywhere. -/
theorem quantile_cdf_ae (ν : Measure ℝ) [IsProbabilityMeasure ν] [NullSingletonClass ν] :
    (fun x => ν.quantile (cdf ν x)) =ᵐ[ν] id := by
  have hq : Measurable ν.quantile := measurable_quantile ν
  have hcdf : Measurable (cdf ν) := (cdf ν).mono.measurable
  have hpos : ∀ᵐ x ∂ν, 0 < cdf ν x := by
    have h0 : ν {x | cdf ν x ≤ 0} = 0 := by
      have h := cdf_sublevel_measure ν 0 (by norm_num)
      simpa using h
    rw [ae_iff]
    simp only [not_lt]
    exact h0
  have hle : ∀ᵐ x ∂ν, ν.quantile (cdf ν x) ≤ x := by
    filter_upwards [hpos] with x hx
    rw [quantile_def]
    exact csInf_le (bddBelow_setOf_le_cdf ν hx) (le_refl (cdf ν x))
  have hmap : Measure.map (fun x => ν.quantile (cdf ν x)) ν = ν := by
    have hcomp : (fun x => ν.quantile (cdf ν x)) = ν.quantile ∘ cdf ν := rfl
    rw [hcomp, ← Measure.map_map hq hcdf, cdf_map_eq_volume_restrict ν]
    simpa only [MeasureTheory.restrict_Ioo_eq_restrict_Icc] using
      (map_quantile_volume_Ioo ν)
  exact ae_eq_id_of_measurePreserving_of_le (hq.comp hcdf) hmap hle

end MeasureTheory.Measure
