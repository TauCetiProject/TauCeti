/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Action.Pointwise.Finset
public import Mathlib.Data.Finset.SymmDiff
public import Mathlib.MeasureTheory.Group.FoelnerFilter
public import Mathlib.MeasureTheory.Measure.Count
import TauCeti.Data.ENNReal.NatCastDiv

/-!
# Følner sets of a group for counting measure

Mathlib's `IsFoelner G μ l F` and `maxFoelner G μ` describe Følner families and the maximal Følner
filter for a group `G` acting on a measure space. For the left regular action of a group on itself
with counting measure on all subsets, this file identifies nontriviality of the maximal Følner
filter with the classical finite-set condition: for every finite `K ⊆ G` and `ε > 0` there is a
finite nonempty `F ⊆ G` with

```text
|gF △ F| < ε · |F|        for all g ∈ K.
```

`TauCeti.HasFoelnerSets G` names nontriviality of the counting-measure Følner filter. It installs
the discrete measurable space `⊤` locally, so every subset is measurable and the notion depends
only on the group, with no topology or countability hypothesis.

The two directions go through explicit Følner families, which we treat for counting measure on
any type `X` with measurable singletons acted on by `G`. A Følner family along a nontrivial filter
passes all finite tests, because finitely many eventual conditions hold simultaneously.
Conversely, if every finite test has a witness, there is a Følner family of finite nonempty sets
indexed by pairs `(K, n)` of a finite test set and a natural number, along `atTop`, which is a
nontrivial filter. The proof picks for `(K, n)` a witness for `K` with tolerance `1 / (n + 1)`.

## Main definitions

* `TauCeti.HasFoelnerSets G`, `TauCeti.HasAddFoelnerSets A`: the counting-measure Følner filter of
  a multiplicative or additive group is nontrivial.

## Main results

* `IsFoelner.tendsto_card_smul_symmDiff_div_card`,
  `IsAddFoelner.tendsto_card_vadd_symmDiff_div_card`: the real cardinality ratios of a
  counting-measure Følner family of finite sets tend to zero.
* `IsFoelner.exists_finset_card_smul_symmDiff_lt`,
  `IsAddFoelner.exists_finset_card_vadd_symmDiff_lt`: a nontrivial counting-measure Følner family
  passes every finite test.
* `TauCeti.exists_isFoelner_atTop`, `TauCeti.exists_isAddFoelner_atTop`: if every finite test has a
  witness, there is a Følner family of finite nonempty sets indexed by `Finset G × ℕ` along `atTop`.
* `TauCeti.hasFoelnerSets_iff`, `TauCeti.hasAddFoelnerSets_iff`: `HasFoelnerSets G` and
  `HasAddFoelnerSets A` are equivalent to the finite-set condition.
* `TauCeti.HasFoelnerSets.of_isFoelner`, `TauCeti.HasAddFoelnerSets.of_isAddFoelner`: any
  counting-measure Følner family along a nontrivial filter witnesses Følner sets.
* `TauCeti.HasFoelnerSets.of_tendsto_card_smul_symmDiff_div_card`,
  `TauCeti.HasAddFoelnerSets.of_tendsto_card_vadd_symmDiff_div_card`: finite sets with vanishing
  relative translation boundaries along a nontrivial filter give Følner sets.
* `MulEquiv.hasFoelnerSets_iff`, `AddEquiv.hasAddFoelnerSets_iff`: having Følner sets is invariant
  under group isomorphisms.
* `TauCeti.isAddFoelner_iff_isFoelner_multiplicative`,
  `TauCeti.hasAddFoelnerSets_iff_hasFoelnerSets_multiplicative`: explicit compatibility across
  `Multiplicative` and `Additive`.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Appendix G.5.
-/

public section

open MeasureTheory Filter Finset
open scoped ENNReal Pointwise symmDiff Topology

variable {G : Type*} [Group G]

section Count

variable {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X] [DecidableEq X]

/-- For a finite nonempty `F`, the counting-measure Følner ratio of `F` at `m` is below
`ENNReal.ofReal ε` exactly when `|mF △ F| < ε · |F|`. -/
@[to_additive /-- For a finite nonempty `F`, the counting-measure additive Følner ratio of `F` at
`m` is below `ENNReal.ofReal ε` exactly when `|(m +ᵥ F) △ F| < ε · |F|`. -/]
theorem MeasureTheory.Measure.count_smul_symmDiff_div_count_lt_ofReal_iff {M : Type*}
    [SMul M X] {F : Finset X} (hF : F.Nonempty) (m : M) {ε : ℝ} :
    Measure.count ((m • (F : Set X)) ∆ F) / Measure.count (F : Set X) < ENNReal.ofReal ε ↔
      (#((m • F) ∆ F) : ℝ) < ε * #F := by
  -- Turn the counting measures into cardinalities.
  simp only [← coe_smul_finset, ← coe_symmDiff, Measure.count_apply_finset]
  exact ENNReal.natCast_div_natCast_lt_ofReal_iff (Finset.card_pos.2 hF)

omit [MeasurableSingletonClass X] in
/-- The counting-measure Følner ratio of a measurable finite set bounds the cardinality ratio
from above. -/
@[to_additive /-- The counting-measure additive Følner ratio of a measurable finite set bounds the
cardinality ratio from above. -/]
theorem MeasureTheory.Measure.card_smul_symmDiff_div_card_le_count_div_count {M : Type*}
    [SMul M X] {F : Finset X} (hFm : MeasurableSet (F : Set X)) (m : M) :
    (#((m • F) ∆ F) : ℝ≥0∞) / #F ≤
      Measure.count ((m • (F : Set X)) ∆ F) / Measure.count (F : Set X) := by
  rw [Measure.count_apply_finset' hFm]
  refine ENNReal.div_le_div_right ?_ _
  rw [← coe_smul_finset, ← coe_symmDiff]
  calc (#((m • F) ∆ F) : ℝ≥0∞) = ∑' _ : (((m • F) ∆ F : Finset X) : Set X), (1 : ℝ≥0∞) := by simp
    _ ≤ _ := Measure.le_count_apply

omit [MeasurableSingletonClass X] in
/-- The real cardinality ratios of a counting-measure Følner family of finite sets tend to
zero for every group element. -/
@[to_additive /-- The real cardinality ratios of a counting-measure additive Følner family of
finite sets tend to zero for every group element. -/]
theorem IsFoelner.tendsto_card_smul_symmDiff_div_card [MulAction G X] {ι : Type*}
    {l : Filter ι} {F : ι → Finset X}
    (hF : IsFoelner G Measure.count l (fun i => (F i : Set X))) (g : G) :
    Tendsto (fun i => (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0) := by
  have hlimit := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp
    (hF.tendsto_meas_smul_symmDiff g)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall fun i => by positivity) ?_
  filter_upwards [hF.eventually_measurableSet,
    (hF.tendsto_meas_smul_symmDiff g).eventually (gt_mem_nhds zero_lt_one)] with i hFm hlt
  have hle := Measure.card_smul_symmDiff_div_card_le_count_div_count hFm g
  have := ENNReal.toReal_mono hlt.ne_top hle
  simpa [ENNReal.toReal_div, Function.comp_def] using this

omit [MeasurableSingletonClass X] in
/-- A Følner family for counting measure along a nontrivial filter passes every finite test: for
each finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ X` with `|gF △ F| < ε · |F|` for
all `g ∈ K`. -/
@[to_additive /-- An additive Følner family for counting measure along a nontrivial filter passes
every finite test: for each finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ X` with
`|(g +ᵥ F) △ F| < ε · |F|` for all `g ∈ K`. -/]
theorem IsFoelner.exists_finset_card_smul_symmDiff_lt [MulAction G X] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set X} (hF : IsFoelner G Measure.count l F)
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F' : Finset X, F'.Nonempty ∧ ∀ g ∈ K, (#((g • F') ∆ F') : ℝ) < ε * #F' := by
  have hK : ∀ᶠ i in l, ∀ g ∈ K,
      Measure.count ((g • F i) ∆ F i) / Measure.count (F i) < ENNReal.ofReal ε :=
    (eventually_all_finset K).2 fun g _ =>
      (hF.tendsto_meas_smul_symmDiff g).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨i, hi0, hitop, hmeas, hiK⟩ :=
    (hF.eventually_meas_ne_zero.and (hF.eventually_meas_ne_top.and
      (hF.eventually_measurableSet.and hK))).exists
  have hfin : (F i).Finite := (Measure.count_apply_lt_top' hmeas).1 (lt_top_iff_ne_top.2 hitop)
  have hne : hfin.toFinset.Nonempty := by
    simpa [Set.nonempty_iff_ne_empty] using mt Measure.count_eq_zero_iff.2 hi0
  have hmeas' : MeasurableSet (hfin.toFinset : Set X) := by simpa using hmeas
  refine ⟨hfin.toFinset, hne, fun g hg => ?_⟩
  have hlt := (Measure.card_smul_symmDiff_div_card_le_count_div_count hmeas' g).trans_lt
    (by simpa only [Set.Finite.coe_toFinset] using hiK g hg)
  exact (ENNReal.natCast_div_natCast_lt_ofReal_iff (Finset.card_pos.2 hne)).1 hlt

namespace TauCeti

/-- If every finite test has a witness, then there is a Følner family of finite nonempty sets for
counting measure, indexed by `Finset G × ℕ` along `atTop`. -/
@[to_additive exists_isAddFoelner_atTop /-- If every finite test has a witness, then there is an
additive Følner family of finite nonempty sets for counting measure, indexed by `Finset G × ℕ` along
`atTop`. -/]
theorem exists_isFoelner_atTop [MulAction G X]
    (h : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F) :
    ∃ F : Finset G × ℕ → Finset X, (∀ i, (F i).Nonempty) ∧
      IsFoelner G Measure.count atTop (fun i => (F i : Set X)) := by
  -- At `(K, n)`, take a witness for the test set `K` with tolerance `1 / (n + 1)`.
  choose F hne hlt using fun i : Finset G × ℕ => h i.1 (1 / (i.2 + 1)) (by positivity)
  refine ⟨F, hne, Eventually.of_forall fun i => (F i).measurableSet,
    Eventually.of_forall fun i => by simp [Measure.count_apply_finset, (hne i).ne_empty],
    Eventually.of_forall fun i => by simp [Measure.count_apply_finset], fun g => ?_⟩
  -- The ratio is eventually below `ofReal (1 / (n + 1))`, which tends to `0` with `n`.
  have hsnd : Tendsto (fun i : Finset G × ℕ => i.2) atTop atTop :=
    tendsto_atTop_atTop_of_monotone (fun _ _ h => h.2) fun n => ⟨(∅, n), le_rfl⟩
  have hbound : Tendsto (fun i : Finset G × ℕ => ENNReal.ofReal (1 / (i.2 + 1))) atTop (𝓝 0) := by
    simpa [Function.comp_def] using
      (ENNReal.tendsto_ofReal tendsto_one_div_add_atTop_nhds_zero_nat).comp hsnd
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    (Eventually.of_forall fun _ => zero_le) ?_
  filter_upwards [eventually_ge_atTop ({g}, 0)] with i hi
  refine ((Measure.count_smul_symmDiff_div_count_lt_ofReal_iff (hne i) g).2 (hlt i g ?_)).le
  exact hi.1 (mem_singleton_self g)

end TauCeti

end Count

namespace TauCeti

variable (G) in
/-- A group `G` has Følner sets when Mathlib's maximal Følner filter for the left regular action
of `G` on itself with counting measure is nontrivial. The measurable space `⊤` is installed
locally, so every subset of `G` is measurable and the notion depends only on the group. -/
@[to_additive HasAddFoelnerSets /-- An additive group `G` has additive Følner sets when Mathlib's
maximal additive Følner filter for the left regular action of `G` on itself with counting measure is
nontrivial. The measurable space `⊤` is installed locally, so every subset of `G` is measurable and
the notion depends only on the group. -/]
abbrev HasFoelnerSets : Prop :=
  letI : MeasurableSpace G := ⊤
  NeBot (maxFoelner G (Measure.count : Measure G))

/-- A group has Følner sets exactly when for every finite `K ⊆ G` and every `ε > 0` there is a
finite nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`. -/
@[to_additive hasAddFoelnerSets_iff /-- An additive group has additive Følner sets exactly when for
every finite `K ⊆ G` and every `ε > 0` there is a finite nonempty `F ⊆ G` with
`|(g +ᵥ F) △ F| < ε · |F|` for all `g ∈ K`. -/]
theorem hasFoelnerSets_iff [DecidableEq G] : HasFoelnerSets G ↔
    ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  let : MeasurableSpace G := ⊤
  refine ⟨fun h K ε hε => (isFoelner_maxFoelner G Measure.count).exists_finset_card_smul_symmDiff_lt
    K hε, fun h => ?_⟩
  obtain ⟨F, -, hF⟩ := exists_isFoelner_atTop h
  exact ((isFoelner_iff_tendsto _ _).1 hF).neBot

/-- A group with a counting-measure Følner family along a nontrivial filter, for any
measurable-space structure on `G`, has Følner sets. -/
@[to_additive HasAddFoelnerSets.of_isAddFoelner /-- An additive group with a counting-measure
additive Følner family along a nontrivial filter, for any measurable-space structure on `G`, has
additive Følner sets. -/]
theorem HasFoelnerSets.of_isFoelner [MeasurableSpace G] {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → Set G} (hF : IsFoelner G Measure.count l F) : HasFoelnerSets G := by
  classical
  exact hasFoelnerSets_iff.2 fun K _ hε => hF.exists_finset_card_smul_symmDiff_lt K hε

/-- A group has Følner sets if a family of eventually nonempty finite sets has vanishing
relative translation boundaries along a nontrivial filter. -/
@[to_additive HasAddFoelnerSets.of_tendsto_card_vadd_symmDiff_div_card /-- An additive group has
additive Følner sets if a family of eventually nonempty finite sets has vanishing relative
translation boundaries along a nontrivial filter. -/]
theorem HasFoelnerSets.of_tendsto_card_smul_symmDiff_div_card [DecidableEq G] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (hF : ∀ g : G, Tendsto (fun i => (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    HasFoelnerSets G := by
  rw [hasFoelnerSets_iff]
  intro K ε hε
  have hevent : ∀ᶠ i in l, ∀ g ∈ K, (#((g • F i) ∆ F i) : ℝ) / #(F i) < ε :=
    (eventually_all_finset K).2 fun g _ => (hF g).eventually (gt_mem_nhds hε)
  obtain ⟨i, hni, hi⟩ := (hne.and hevent).exists
  exact ⟨F i, hni, fun g hg =>
    (div_lt_iff₀ (by exact_mod_cast hni.card_pos)).1 (hi g hg)⟩

end TauCeti

namespace MulEquiv

open TauCeti

variable {H : Type*} [Group H]

/-- An isomorphism carries Følner sets of `G` to Følner sets of `H`. -/
@[to_additive /-- An additive isomorphism carries additive Følner sets of `G` to additive Følner
sets of `H`. -/]
private theorem hasFoelnerSets_of_mulEquiv (e : G ≃* H) (h : HasFoelnerSets G) :
    HasFoelnerSets H := by
  classical
  rw [TauCeti.hasFoelnerSets_iff] at h ⊢
  intro K ε hε
  obtain ⟨F, hF, hFK⟩ := h (K.image e.symm) ε hε
  refine ⟨F.image e, hF.image e, fun g hg => ?_⟩
  -- The isomorphism carries the test for `e.symm g` on `F` to the test for `g` on `e '' F`.
  have h_eq : (g • F.image e) ∆ F.image e = ((e.symm g • F) ∆ F).image e := by
    rw [image_symmDiff _ _ e.injective, image_smul_distrib, apply_symm_apply]
  rw [h_eq, card_image_of_injective _ e.injective, card_image_of_injective _ e.injective]
  exact hFK _ (mem_image_of_mem _ hg)

/-- Having Følner sets is invariant under group isomorphisms. -/
@[to_additive hasAddFoelnerSets_iff /-- Having additive Følner sets is invariant under additive
group isomorphisms. -/]
theorem hasFoelnerSets_iff (e : G ≃* H) : HasFoelnerSets G ↔ HasFoelnerSets H :=
  ⟨hasFoelnerSets_of_mulEquiv e, hasFoelnerSets_of_mulEquiv e.symm⟩

end MulEquiv

namespace TauCeti

section TypeTags

variable {A : Type*} [AddGroup A] {X : Type*} [MeasurableSpace X]

/-- An additive Følner family for `A` acting on `X` is a multiplicative Følner family for
`Multiplicative A` acting on `X`. -/
theorem isAddFoelner_iff_isFoelner_multiplicative [AddAction A X] (μ : Measure X)
    {ι : Type*} (l : Filter ι) (F : ι → Set X) :
    IsAddFoelner A μ l F ↔ IsFoelner (Multiplicative A) μ l F := by
  simp only [isAddFoelner_iff, isFoelner_iff, Multiplicative.forall]
  rfl

/-- A multiplicative Følner family for `G` acting on `X` is an additive Følner family for
`Additive G` acting on `X`. -/
theorem isFoelner_iff_isAddFoelner_additive [MulAction G X] (μ : Measure X)
    {ι : Type*} (l : Filter ι) (F : ι → Set X) :
    IsFoelner G μ l F ↔ IsAddFoelner (Additive G) μ l F := by
  simp only [isFoelner_iff, isAddFoelner_iff, Additive.forall]
  rfl

/-- An additive group `A` has additive Følner sets if and only if `Multiplicative A` has Følner
sets. -/
theorem hasAddFoelnerSets_iff_hasFoelnerSets_multiplicative :
    HasAddFoelnerSets A ↔ HasFoelnerSets (Multiplicative A) := by
  classical
  simp only [hasAddFoelnerSets_iff, hasFoelnerSets_iff]
  refine ⟨fun h K ε hε => ?_, fun h K ε hε => ?_⟩
  · obtain ⟨F, hF, hFK⟩ := h (K.image Multiplicative.toAdd) ε hε
    refine ⟨F.image Multiplicative.ofAdd, hF.image _, fun g hg => ?_⟩
    have htr : g • F.image Multiplicative.ofAdd =
        (g.toAdd +ᵥ F).image Multiplicative.ofAdd := by
      simp only [smul_finset_def, vadd_finset_def, image_image]
      rfl
    rw [htr, ← image_symmDiff _ _ Multiplicative.ofAdd.injective,
      card_image_of_injective _ Multiplicative.ofAdd.injective,
      card_image_of_injective _ Multiplicative.ofAdd.injective]
    exact hFK g.toAdd (mem_image_of_mem _ hg)
  · obtain ⟨F, hF, hFK⟩ := h (K.image Multiplicative.ofAdd) ε hε
    refine ⟨F.image Multiplicative.toAdd, hF.image _, fun a ha => ?_⟩
    have htr : a +ᵥ F.image Multiplicative.toAdd =
        (Multiplicative.ofAdd a • F).image Multiplicative.toAdd := by
      ext x
      simp [mem_smul_finset, mem_vadd_finset, ← ofAdd_add]
    rw [htr, ← image_symmDiff _ _ Multiplicative.toAdd.injective,
      card_image_of_injective _ Multiplicative.toAdd.injective,
      card_image_of_injective _ Multiplicative.toAdd.injective]
    exact hFK (.ofAdd a) (mem_image_of_mem _ ha)

/-- A group `G` has Følner sets if and only if `Additive G` has additive Følner sets. -/
theorem hasFoelnerSets_iff_hasAddFoelnerSets_additive :
    HasFoelnerSets G ↔ HasAddFoelnerSets (Additive G) := by
  rw [hasAddFoelnerSets_iff_hasFoelnerSets_multiplicative,
    (MulEquiv.multiplicativeAdditive G).hasFoelnerSets_iff]

end TypeTags

end TauCeti
