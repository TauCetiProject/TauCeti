/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.Quantile
import TauCeti.MeasureTheory.OuterMeasure.SymmDiff

/-!
# The Wasserstein distance of two real laws at exponent one

On the real line the transport problem for the ground distance is solved explicitly: for two
probability laws `μ` and `ν` on `ℝ`,

`W₁ (μ, ν) = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ = ‖μ.quantile - ν.quantile‖_{L¹ (0, 1)}`,

the area between the two cumulative distribution functions, equivalently the `L¹` distance of the
two quantile functions on the unit interval. The monotone coupling
`MeasureTheory.Measure.quantileCoupling` attains it, so the monotone rearrangement of two real
laws is an optimal transport plan for the ground distance.

Both identities are identities in `[0, ∞]` and need no moment hypothesis: their two sides are
infinite together, so laws with divergent first moments are covered as they stand.

One measure-theoretic identity drives both,
`TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff`: the `L¹` distance of two real
measurable functions is the integral, over the levels `s`, of the measure of the set where exactly
one of them is at most `s`. On the two coordinates of a transport plan it rewrites the transport
objective as an integral of plan masses, each at least the gap between the two cumulative
distribution functions at that level, since a set on which exactly one coordinate is small carries
at least the difference of the two marginal masses. On the two quantile functions it rewrites the
objective of the monotone plan as the integral of exactly those gaps, by the Galois property of
the quantile. Lower bound and attained value therefore meet.

Exponents `p > 1` are not covered: the argument uses that the ground cost is the distance itself,
and the one-dimensional formula for the costs `|x - y| ^ p` is a rearrangement statement with an
unrelated proof.

## Main statements

* `TauCeti.lintegral_enorm_sub_eq_lintegral_measure_symmDiff` — the `L¹` distance of two
  measurable real functions as an integral over levels of the measure of a symmetric difference;
* `TauCeti.wassersteinEDist_one_eq_lintegral_enorm_cdf_sub` — the Wasserstein distance at
  exponent one is the area between the two cumulative distribution functions;
* `TauCeti.wassersteinEDist_one_eq_eLpNorm_quantile_sub` — it is also the `L¹ (0, 1)` distance of
  the two quantile functions;
* `TauCeti.isOptimalCoupling_quantileCoupling` — the monotone coupling is an optimal plan for the
  ground distance.

## References

* S. S. Vallender, *Calculation of the Wasserstein distance between probability distributions on
  the line*, Theory of Probability and its Applications 18 (1974), 784--786.
* C. Villani, *Topics in Optimal Transportation*, GSM 58, AMS 2003, §2.2.
* F. Santambrogio, *Optimal Transport for Applied Mathematicians*, Birkhäuser 2015, §2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal symmDiff

namespace TauCeti

section LayerCake

variable {α : Type*} [MeasurableSpace α]

/-- A level lies between two reals exactly when exactly one of them is at most that level. -/
private theorem mem_Ico_min_max_iff {x y s : ℝ} :
    s ∈ Ico (min x y) (max x y) ↔ ((x ≤ s ∧ ¬ y ≤ s) ∨ (y ≤ s ∧ ¬ x ≤ s)) := by
  rw [mem_Ico]
  rcases le_total x y with h | h
  · rw [min_eq_left h, max_eq_right h]
    refine ⟨fun hs ↦ Or.inl ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact ⟨h1, not_le.1 h2⟩
    · exact absurd (h.trans h1) h2
  · rw [min_eq_right h, max_eq_left h]
    refine ⟨fun hs ↦ Or.inr ⟨hs.1, not_le.2 hs.2⟩, ?_⟩
    rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact absurd (h.trans h1) h2
    · exact ⟨h1, not_le.1 h2⟩

/-- **The area between two graphs.** The `L¹` distance of two measurable real functions is the
integral, over the levels `s`, of the measure of the set where exactly one of the two functions is
at most `s`. -/
theorem lintegral_enorm_sub_eq_lintegral_measure_symmDiff (m : Measure α) [SFinite m]
    {f g : α → ℝ} (hf : Measurable f) (hg : Measurable g) :
    ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
  set F : Set (α × ℝ) := {q | min (f q.1) (g q.1) ≤ q.2 ∧ q.2 < max (f q.1) (g q.1)} with hFdef
  have hF : MeasurableSet F :=
    (measurableSet_le ((hf.comp measurable_fst).min (hg.comp measurable_fst)) measurable_snd).inter
      (measurableSet_lt measurable_snd ((hf.comp measurable_fst).max (hg.comp measurable_fst)))
  have hmem_Ico : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ s ∈ Ico (min (f a) (g a)) (max (f a) (g a)) := by
    intro a s
    simp [hFdef, mem_Ico]
  have hmem_symmDiff : ∀ (a : α) (s : ℝ),
      (a, s) ∈ F ↔ a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro a s
    rw [hmem_Ico, Set.mem_symmDiff]
    exact mem_Ico_min_max_iff
  have hlevel : ∀ a : α, (∫⁻ s, F.indicator 1 (a, s)) = ‖f a - g a‖ₑ := by
    intro a
    have hfun : (fun s ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = (Ico (min (f a) (g a)) (max (f a) (g a))).indicator 1 := by
      funext s
      by_cases hs : s ∈ Ico (min (f a) (g a)) (max (f a) (g a))
      · rw [Set.indicator_of_mem hs, Set.indicator_of_mem ((hmem_Ico a s).mpr hs), Pi.one_apply,
          Pi.one_apply]
      · rw [Set.indicator_of_notMem hs,
          Set.indicator_of_notMem (fun hq ↦ hs ((hmem_Ico a s).mp hq))]
    rw [hfun, lintegral_indicator_one measurableSet_Ico, Real.volume_Ico, max_sub_min_eq_abs,
      abs_sub_comm, Real.enorm_eq_ofReal_abs]
  have hsection : ∀ s : ℝ,
      (∫⁻ a, F.indicator 1 (a, s) ∂m) = m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by
    intro s
    have hmeas : MeasurableSet ({a | f a ≤ s} ∆ {a | g a ≤ s}) :=
      (measurableSet_le hf measurable_const).symmDiff (measurableSet_le hg measurable_const)
    have hfun : (fun a ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
        = ({a | f a ≤ s} ∆ {a | g a ≤ s}).indicator 1 := by
      funext a
      by_cases ha : a ∈ ({a | f a ≤ s} ∆ {a | g a ≤ s})
      · rw [Set.indicator_of_mem ha, Set.indicator_of_mem ((hmem_symmDiff a s).mpr ha),
          Pi.one_apply, Pi.one_apply]
      · rw [Set.indicator_of_notMem ha,
          Set.indicator_of_notMem (fun hq ↦ ha ((hmem_symmDiff a s).mp hq))]
    rw [hfun, lintegral_indicator_one hmeas]
  calc ∫⁻ a, ‖f a - g a‖ₑ ∂m = ∫⁻ a, (∫⁻ s, F.indicator 1 (a, s)) ∂m := by
        simp_rw [hlevel]
    _ = ∫⁻ s, (∫⁻ a, F.indicator 1 (a, s) ∂m) :=
        lintegral_lintegral_swap
          (f := fun (a : α) (s : ℝ) ↦ F.indicator (1 : α × ℝ → ℝ≥0∞) (a, s))
          (measurable_const.indicator hF).aemeasurable
    _ = ∫⁻ s, m ({a | f a ≤ s} ∆ {a | g a ≤ s}) := by simp_rw [hsection]

end LayerCake

section RealLaws

/-- On a transport plan of two real laws, the set of pairs whose two coordinates are separated by
the level `s` has mass at least the gap between the two cumulative distribution functions at
`s`. -/
theorem enorm_cdf_sub_le_measure_symmDiff {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] {π : Measure (ℝ × ℝ)} (hπ : IsCoupling π μ ν) (s : ℝ) :
    ‖cdf μ s - cdf ν s‖ₑ ≤ π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s}) := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hfst : {z : ℝ × ℝ | z.1 ≤ s} = Iic s ×ˢ univ := by ext z; simp
  have hsnd : {z : ℝ × ℝ | z.2 ≤ s} = univ ×ˢ Iic s := by ext z; simp
  have hμ : cdf μ s = (π {z : ℝ × ℝ | z.1 ≤ s}).toReal := by
    rw [cdf_eq_real, measureReal_def, hfst, hπ.measure_prod_univ measurableSet_Iic]
  have hν : cdf ν s = (π {z : ℝ × ℝ | z.2 ≤ s}).toReal := by
    rw [cdf_eq_real, measureReal_def, hsnd, hπ.measure_univ_prod measurableSet_Iic]
  have hbound : |cdf μ s - cdf ν s|
      ≤ (π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s})).toReal := by
    rw [hμ, hν]
    exact MeasureTheory.abs_toReal_sub_le_toReal_symmDiff (measure_ne_top π _)
      (measure_ne_top π _)
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_toReal (measure_ne_top π _)]
  exact ENNReal.ofReal_le_ofReal hbound

/-- A level is at most exactly one of two reals precisely on the half-open interval between
them. -/
private theorem mem_Ioc_min_max_iff {a b t : ℝ} :
    ((t ≤ a ∧ ¬ t ≤ b) ∨ (t ≤ b ∧ ¬ t ≤ a)) ↔ t ∈ Ioc (min a b) (max a b) := by
  rw [mem_Ioc]
  rcases le_total a b with h | h
  · rw [min_eq_left h, max_eq_right h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact absurd (h1.trans h) h2
      · exact ⟨not_le.1 h2, h1⟩
    · exact fun ht ↦ Or.inr ⟨ht.2, not_le.2 ht.1⟩
  · rw [min_eq_right h, max_eq_left h]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
      · exact ⟨not_le.1 h2, h1⟩
      · exact absurd (h1.trans h) h2
    · exact fun ht ↦ Or.inl ⟨ht.2, not_le.2 ht.1⟩

/-- The `L¹ (0, 1)` distance of the two quantile functions is the area between the two cumulative
distribution functions. -/
theorem lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    ∫⁻ t, ‖μ.quantile t - ν.quantile t‖ₑ ∂volume.restrict (Ioo (0 : ℝ) 1)
      = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ := by
  rw [lintegral_enorm_sub_eq_lintegral_measure_symmDiff _ (Measure.measurable_quantile μ)
    (Measure.measurable_quantile ν)]
  refine lintegral_congr fun s ↦ ?_
  have hset : ({t | μ.quantile t ≤ s} ∆ {t | ν.quantile t ≤ s}) ∩ Ioo (0 : ℝ) 1
      = Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1 := by
    ext t
    simp only [mem_inter_iff, Set.mem_symmDiff, Set.mem_ofPred_eq, mem_Ioc, mem_Ioo,
      and_congr_left_iff]
    rintro ⟨ht0, ht1⟩
    rw [Measure.quantile_le_iff μ ht0 ht1, Measure.quantile_le_iff ν ht0 ht1]
    exact mem_Ioc_min_max_iff
  have hmeas : MeasurableSet ({t | μ.quantile t ≤ s} ∆ {t | ν.quantile t ≤ s}) :=
    (measurableSet_le (Measure.measurable_quantile μ) measurable_const).symmDiff
      (measurableSet_le (Measure.measurable_quantile ν) measurable_const)
  rw [Measure.restrict_apply hmeas, hset]
  refine le_antisymm ?_ ?_
  · calc volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1)
        ≤ volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s))) :=
          measure_mono inter_subset_left
      _ = ‖cdf μ s - cdf ν s‖ₑ := by
          rw [Real.volume_Ioc, max_sub_min_eq_abs, abs_sub_comm, Real.enorm_eq_ofReal_abs]
  · calc ‖cdf μ s - cdf ν s‖ₑ
        = volume (Ioo (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s))) := by
          rw [Real.volume_Ioo, max_sub_min_eq_abs, abs_sub_comm, Real.enorm_eq_ofReal_abs]
      _ ≤ volume (Ioc (min (cdf μ s) (cdf ν s)) (max (cdf μ s) (cdf ν s)) ∩ Ioo (0 : ℝ) 1) := by
          refine measure_mono fun t ht ↦ ⟨Ioo_subset_Ioc_self ht, ?_⟩
          exact ⟨lt_of_le_of_lt (le_min (cdf_nonneg μ s) (cdf_nonneg ν s)) ht.1,
            lt_of_lt_of_le ht.2 (max_le (cdf_le_one μ s) (cdf_le_one ν s))⟩

/-- **The one-dimensional Kantorovich formula.** The Wasserstein distance at exponent one of two
probability laws on `ℝ` is the area between their cumulative distribution functions. -/
theorem wassersteinEDist_one_eq_lintegral_enorm_cdf_sub (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    wassersteinEDist 1 μ ν = ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ := by
  refine le_antisymm ?_ ?_
  · refine (wassersteinEDist_le_eLpNorm_quantile_sub 1 μ ν).trans_eq ?_
    rw [eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub μ ν
  · rw [wassersteinEDist_one_eq_transportCost]
    refine le_transportCost fun π hπ ↦ ?_
    have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
    calc ∫⁻ s, ‖cdf μ s - cdf ν s‖ₑ
        ≤ ∫⁻ s, π ({z : ℝ × ℝ | z.1 ≤ s} ∆ {z : ℝ × ℝ | z.2 ≤ s}) :=
          lintegral_mono fun s ↦ enorm_cdf_sub_le_measure_symmDiff hπ s
      _ = ∫⁻ z, ‖z.1 - z.2‖ₑ ∂π :=
          (lintegral_enorm_sub_eq_lintegral_measure_symmDiff π measurable_fst measurable_snd).symm
      _ = ∫⁻ z, edist z.1 z.2 ∂π := by simp_rw [edist_eq_enorm_sub]

/-- **The one-dimensional quantile formula.** The Wasserstein distance at exponent one of two
probability laws on `ℝ` is the `L¹ (0, 1)` distance of their quantile functions. -/
theorem wassersteinEDist_one_eq_eLpNorm_quantile_sub (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    wassersteinEDist 1 μ ν
      = eLpNorm (fun t ↦ μ.quantile t - ν.quantile t) 1 (volume.restrict (Ioo (0 : ℝ) 1)) := by
  rw [wassersteinEDist_one_eq_lintegral_enorm_cdf_sub, eLpNorm_one_eq_lintegral_enorm,
    lintegral_enorm_quantile_sub_eq_lintegral_enorm_cdf_sub]

/-- **The monotone rearrangement is optimal.** The monotone coupling of two real laws minimizes
the transport objective of the ground distance. -/
theorem isOptimalCoupling_quantileCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] :
    IsOptimalCoupling (fun z : ℝ × ℝ ↦ edist z.1 z.2) (μ.quantileCoupling ν) μ ν where
  toIsCoupling := μ.isCoupling_quantileCoupling ν
  lintegral_eq := by
    rw [← wassersteinEDist_one_eq_transportCost, wassersteinEDist_one_eq_eLpNorm_quantile_sub,
      ← eLpNorm_edist_quantileCoupling 1 μ ν, eLpNorm_one_eq_lintegral_enorm]
    exact lintegral_congr fun z ↦ by simp

end RealLaws

end TauCeti
