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
Conversely, the witnesses of the finite tests, indexed by pairs `(K, n)` of a finite test set and
a natural number and chosen with tolerance `1 / (n + 1)`, form a Følner family along `atTop`,
which is a nontrivial filter.

## Main definitions

* `TauCeti.HasFoelnerSets G`: the counting-measure Følner filter of `G` is nontrivial.

## Main results

* `IsFoelner.exists_finset_card_smul_symmDiff_lt`: a nontrivial counting-measure Følner family
  passes every finite test.
* `TauCeti.exists_isFoelner_atTop`: witnesses of all finite tests form a Følner family indexed by
  `Finset G × ℕ`.
* `TauCeti.hasFoelnerSets_iff`: `HasFoelnerSets G` is equivalent to the finite-set condition.
* `MulEquiv.hasFoelnerSets_iff`: having Følner sets is invariant under group isomorphisms.

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
theorem MeasureTheory.Measure.count_smul_symmDiff_div_count_lt_ofReal_iff {M : Type*}
    [SMul M X] {F : Finset X} (hF : F.Nonempty) (m : M) {ε : ℝ} (hε : 0 < ε) :
    Measure.count ((m • (F : Set X)) ∆ F) / Measure.count (F : Set X) < ENNReal.ofReal ε ↔
      (#((m • F) ∆ F) : ℝ) < ε * #F := by
  rw [← coe_smul_finset, ← coe_symmDiff, Measure.count_apply_finset,
    Measure.count_apply_finset, ENNReal.div_lt_iff (by simp [hF.ne_empty]) (by simp),
    ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul hε.le,
    ENNReal.ofReal_lt_ofReal_iff (mul_pos hε (by exact_mod_cast hF.card_pos))]

/-- A Følner family for counting measure along a nontrivial filter passes every finite test: for
each finite `K ⊆ G` and `ε > 0` there is a finite nonempty `F ⊆ X` with `|gF △ F| < ε · |F|` for
all `g ∈ K`. -/
theorem IsFoelner.exists_finset_card_smul_symmDiff_lt [MulAction G X] {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Set X} (hF : IsFoelner G Measure.count l F)
    (K : Finset G) {ε : ℝ} (hε : 0 < ε) :
    ∃ F' : Finset X, F'.Nonempty ∧ ∀ g ∈ K, (#((g • F') ∆ F') : ℝ) < ε * #F' := by
  have hK : ∀ᶠ i in l, ∀ g ∈ K,
      Measure.count ((g • F i) ∆ F i) / Measure.count (F i) < ENNReal.ofReal ε :=
    (eventually_all_finset K).2 fun g _ =>
      (hF.tendsto_meas_smul_symmDiff g).eventually (gt_mem_nhds (ENNReal.ofReal_pos.2 hε))
  obtain ⟨i, hi0, hitop, hiK⟩ :=
    (hF.eventually_meas_ne_zero.and (hF.eventually_meas_ne_top.and hK)).exists
  have hfin : (F i).Finite := Measure.count_apply_lt_top.1 (lt_top_iff_ne_top.2 hitop)
  have hne : hfin.toFinset.Nonempty := by
    simpa [Set.nonempty_iff_ne_empty] using mt Measure.count_eq_zero_iff.2 hi0
  refine ⟨hfin.toFinset, hne, fun g hg => ?_⟩
  rw [← Measure.count_smul_symmDiff_div_count_lt_ofReal_iff hne g hε, Set.Finite.coe_toFinset]
  exact hiK g hg

namespace TauCeti

/-- If every finite test has a witness, then choosing a witness `F (K, n)` for the test set `K`
with tolerance `1 / (n + 1)` gives a Følner family of finite nonempty sets for counting measure,
indexed by `Finset G × ℕ` along `atTop`. -/
theorem exists_isFoelner_atTop [MulAction G X]
    (h : ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset X, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F) :
    ∃ F : Finset G × ℕ → Finset X, (∀ i, (F i).Nonempty) ∧
      IsFoelner G Measure.count atTop (fun i => (F i : Set X)) := by
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
  refine ((Measure.count_smul_symmDiff_div_count_lt_ofReal_iff (hne i) g
    (by positivity)).2 (hlt i g ?_)).le
  exact hi.1 (mem_singleton_self g)

end TauCeti

end Count

namespace TauCeti

variable (G) in
/-- A group `G` has Følner sets when Mathlib's maximal Følner filter for the left regular action
of `G` on itself with counting measure is nontrivial. The measurable space `⊤` is installed
locally, so every subset of `G` is measurable and the notion depends only on the group. -/
abbrev HasFoelnerSets : Prop :=
  letI : MeasurableSpace G := ⊤
  NeBot (maxFoelner G (Measure.count : Measure G))

/-- A group has Følner sets exactly when for every finite `K ⊆ G` and every `ε > 0` there is a
finite nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`. -/
theorem hasFoelnerSets_iff [DecidableEq G] : HasFoelnerSets G ↔
    ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
      ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  let : MeasurableSpace G := ⊤
  refine ⟨fun h K ε hε => (isFoelner_maxFoelner G Measure.count).exists_finset_card_smul_symmDiff_lt
    K hε, fun h => ?_⟩
  obtain ⟨F, -, hF⟩ := exists_isFoelner_atTop h
  exact ((isFoelner_iff_tendsto _ _).1 hF).neBot

end TauCeti

namespace MulEquiv

open TauCeti

variable {H : Type*} [Group H]

/-- An isomorphism carries Følner sets of `G` to Følner sets of `H`. -/
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
theorem hasFoelnerSets_iff (e : G ≃* H) : HasFoelnerSets G ↔ HasFoelnerSets H :=
  ⟨hasFoelnerSets_of_mulEquiv e, hasFoelnerSets_of_mulEquiv e.symm⟩

end MulEquiv
