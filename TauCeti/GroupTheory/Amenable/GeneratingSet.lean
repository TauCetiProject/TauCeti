/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
import TauCeti.Algebra.Group.Action.Pointwise.Finset

/-!
# Generating-set Følner characterizations of amenability

By subadditivity of symmetric differences under left translation
(`Finset.card_mul_smul_finset_symmDiff_le` and `MeasureTheory.measure_mul_smul_symmDiff_le`),
controlling the translation boundaries `|gF △ F|` of a finite set `F ⊆ G` on a generating set `S`
of `G` controls `|gF △ F|` on all words in `S ∪ S⁻¹`, with a uniform multiplicative constant
`M : ℕ` independent of `F` (`Finset.exists_finset_card_smul_symmDiff_le_of_subset_closure`).

Building on the basic finite-test generator reductions
`TauCeti.hasFoelnerSets_iff_of_closure_eq_top` and
`TauCeti.hasFoelnerSets_iff_of_closure_finset_eq_top` (and their discrete-amenability forms
`TauCeti.amenable_iff_exists_finset_of_closure_eq_top` and
`TauCeti.amenable_iff_exists_finset_of_closure_finset_eq_top`), this file develops the remaining
generating-set Følner and amenability characterizations:

* `DecidableEq`-free finite-`Set` (`Set.ncard`) criteria on an arbitrary generating set `S : Set G`.
* For a **finite** generating set `S : Finset G` (`Subgroup.closure (S : Set G) = ⊤`), equivalences
  with small summed generator boundary `∑ g ∈ S, |gF △ F| < ε · |F|` and non-expansion of the unit
  Cayley ball `|({1} ∪ S) • F| < (1 + c) · |F|`. Negating gives a positive Cheeger /
  vertex-expansion constant on `{1} ∪ S` itself for every nonamenable finitely generated group.
* Along any nontrivial filter `l`, vanishing of `#((g • F i) ∆ F i) / #(F i)` on a generating
  set `S` for an eventually nonempty family `F` is sufficient for `HasFoelnerSets G` (and hence
  for `Amenable G` in every group topology). When `G` is countable, the existence of a sequence
  along `ℕ` of nonempty finite sets with vanishing ratios on `S` characterizes `HasFoelnerSets G`
  and discrete `Amenable G`.

## Main results

* `TauCeti.hasFoelnerSets_iff_exists_finite_set_of_closure_eq_top`: `DecidableEq`-free `Set.ncard`
  characterization testing finite subsets of an arbitrary generating set `S : Set G`.
* `TauCeti.hasFoelnerSets_iff_sum_lt_of_closure_eq_top`,
  `TauCeti.hasFoelnerSets_iff_card_insert_one_smul_lt_of_closure_eq_top`: boundary-sum and
  Cayley-ball expansion criteria for a finite generating set `S : Finset G`.
* `TauCeti.Amenable.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top`: Følner-net generator
  criterion for topological `Amenable`.
* `TauCeti.hasFoelnerSets_iff_exists_seq_of_closure_eq_top`,
  `TauCeti.amenable_iff_exists_seq_of_closure_eq_top`: countable Følner-sequence generator
  characterizations.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Lemma 3.4,
  Theorem 3.6.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and Remark G.5.3.
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped ENNReal Pointwise symmDiff

namespace TauCeti

variable {G : Type*} [Group G]

/-! ### Generating-set criteria -/

/-- **Garrido Lemma 3.4 (arbitrary generating set, `Set.ncard` form).** When `S` generates `G`,
`HasFoelnerSets G` holds iff every finite `K ⊆ S` and `ε > 0` admit a finite nonempty `F : Set G`
passing the `K`-test. -/
@[to_additive hasAddFoelnerSets_iff_exists_finite_set_of_closure_eq_top
/-- **Garrido Lemma 3.4 (arbitrary additive generating set, `Set.ncard` form).** When `S` generates
`G`, `HasAddFoelnerSets G` holds iff every finite `K ⊆ S` and `ε > 0` admit a finite nonempty
`F : Set G` passing the `K`-test. -/]
theorem hasFoelnerSets_iff_exists_finite_set_of_closure_eq_top {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    HasFoelnerSets G ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ, 0 < ε →
        ∃ F : Set G, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  let : MeasurableSpace G := ⊤
  exact maxFoelner_count_neBot_iff_of_closure_eq_top hS

/-- Summed-boundary (isoperimetric / Cheeger) Følner criterion for a finite generating set `S`. -/
@[to_additive hasAddFoelnerSets_iff_sum_lt_of_closure_eq_top
/-- Summed-boundary (isoperimetric / Cheeger) additive Følner criterion for a finite generating set
`S`. -/]
theorem hasFoelnerSets_iff_sum_lt_of_closure_eq_top [DecidableEq G] {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    HasFoelnerSets G ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ F : Finset G, F.Nonempty ∧ (∑ g ∈ S, (#((g • F) ∆ F) : ℝ)) < ε * #F := by
  rw [hasFoelnerSets_iff_of_closure_finset_eq_top hS]
  constructor
  · intro h ε hε
    obtain ⟨F, hne, hFS⟩ := h (ε / (#S + 1)) (by positivity)
    refine ⟨F, hne, ?_⟩
    have hFpos : (0 : ℝ) < #F := by exact_mod_cast hne.card_pos
    calc
      (∑ g ∈ S, (#((g • F) ∆ F) : ℝ))
        ≤ ∑ _g ∈ S, ε / (#S + 1) * #F := sum_le_sum fun g hg ↦ (hFS g hg).le
      _ = #S * (ε / (#S + 1)) * #F := by simp [mul_assoc]
      _ < ε * #F := by
        refine mul_lt_mul_of_pos_right ?_ hFpos
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        linarith
  · intro h ε hε
    obtain ⟨F, hne, hFS⟩ := h ε hε
    exact ⟨F, hne, fun g hg ↦
      (single_le_sum (fun x _ ↦ Nat.cast_nonneg #((x • F) ∆ F)) hg).trans_lt hFS⟩

/-- Cayley-ball non-expansion characterization: for a finite generating set `S`, `G` has Følner
sets iff `{1} ∪ S` fails to expand all finite nonempty subsets by a uniform factor `1 + c > 1`. -/
@[to_additive hasAddFoelnerSets_iff_card_insert_zero_vadd_lt_of_closure_eq_top
/-- Additive Cayley-ball non-expansion characterization: for a finite generating set `S`, `G` has
additive Følner sets iff `{0} ∪ S` fails to expand all finite nonempty subsets by a uniform factor
`1 + c > 1`. -/]
theorem hasFoelnerSets_iff_card_insert_one_smul_lt_of_closure_eq_top [DecidableEq G] {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    HasFoelnerSets G ↔
      ∀ c : ℝ, 0 < c →
        ∃ F : Finset G, F.Nonempty ∧ (#(insert 1 S • F) : ℝ) < (1 + c) * #F := by
  constructor
  · intro h c hc
    obtain ⟨F, hne, hFS⟩ :=
      (hasFoelnerSets_iff_sum_lt_of_closure_eq_top hS).1 h (2 * c) (by positivity)
    refine ⟨F, hne, ?_⟩
    have hsd : (∑ g ∈ S, (#((g • F) ∆ F) : ℝ)) = 2 * ∑ g ∈ S, (#(g • F \ F) : ℝ) := by
      simp_rw [card_smul_finset_symmDiff, Nat.cast_mul, Nat.cast_ofNat, ← mul_sum]
    have hcast : (#(insert 1 S • F) : ℝ) ≤ (∑ g ∈ S, (#(g • F \ F) : ℝ)) + #F := by
      exact_mod_cast card_insert_one_smul_finset_le S F
    linarith
  · intro h
    rw [hasFoelnerSets_iff_of_closure_finset_eq_top hS]
    intro ε hε
    obtain ⟨F, hne, hFc⟩ := h (ε / 2) (by positivity)
    refine ⟨F, hne, fun g hg ↦ ?_⟩
    have hsub : g • F ∪ F ⊆ insert 1 S • F :=
      union_subset (smul_finset_subset_smul (mem_insert_of_mem hg))
        (by simpa using smul_finset_subset_smul (t := F) (mem_insert_self 1 S))
    have hle : (#(g • F \ F) : ℝ) + #F ≤ #(insert 1 S • F) := by
      exact_mod_cast (card_sdiff_add_card _ _).trans_le (card_le_card hsub)
    have hsd : (#((g • F) ∆ F) : ℝ) = 2 * #(g • F \ F) := by
      exact_mod_cast card_smul_finset_symmDiff g F
    linarith

/-! ### Net and sequence generator criteria -/

/-- Along a nontrivial filter, vanishing of `#((g • F i) ∆ F i) / #(F i)` on a generating set `S`
for an eventually nonempty family `F` makes `G` amenable for every group topology. -/
theorem Amenable.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top [TopologicalSpace G]
    [IsTopologicalGroup G] [DecidableEq G] {S : Set G} (hS : Subgroup.closure S = ⊤) {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (hF : ∀ g ∈ S, Tendsto (fun i ↦ (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    Amenable G :=
  .of_hasFoelnerSets (.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top hS hne hF)

/-- When `G` is countable and `S` generates `G`, `HasFoelnerSets G` holds iff there is a sequence
of finite nonempty sets whose relative translation boundaries tend to zero on `S`. -/
@[to_additive hasAddFoelnerSets_iff_exists_seq_of_closure_eq_top
/-- When `G` is countable and `S` generates `G`, `HasAddFoelnerSets G` holds iff there is a sequence
of finite nonempty sets whose relative translation boundaries tend to zero on `S`. -/]
theorem hasFoelnerSets_iff_exists_seq_of_closure_eq_top [Countable G] [DecidableEq G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    HasFoelnerSets G ↔
      ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
        ∀ g ∈ S, Tendsto (fun n ↦ (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  ⟨fun h ↦ let ⟨F, hne, hF⟩ := hasFoelnerSets_iff_exists_seq.1 h; ⟨F, hne, fun g _ ↦ hF g⟩,
    fun ⟨_, hne, hF⟩ ↦
      .of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top hS (.of_forall hne) hF⟩

/-- Countable Følner-sequence characterization of discrete amenability tested on a generating set
`S`. -/
theorem amenable_iff_exists_seq_of_closure_eq_top [Countable G] [TopologicalSpace G]
    [DiscreteTopology G] [DecidableEq G] {S : Set G} (hS : Subgroup.closure S = ⊤) :
    Amenable G ↔
      ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
        ∀ g ∈ S, Tendsto (fun n ↦ (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  amenable_iff_hasFoelnerSets.trans (hasFoelnerSets_iff_exists_seq_of_closure_eq_top hS)

end TauCeti
