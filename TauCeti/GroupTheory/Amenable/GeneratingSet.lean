/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Action.Pointwise.Finset
public import TauCeti.GroupTheory.Amenable.DiscreteFoelner
public import TauCeti.GroupTheory.Amenable.Sequence
public import TauCeti.MeasureTheory.Group.Foelner.Count

/-!
# Generating-set and finite-set Følner characterizations of amenability

By subadditivity of symmetric differences under left translation (`Finset.card_symmDiff_le` and
`MeasureTheory.measure_mul_smul_symmDiff_le`), controlling the translation boundaries `|gF △ F|` of
a finite set `F ⊆ G` on a generating set `S` of `G` controls `|gF △ F|` on all words in `S ∪ S⁻¹`,
with an explicit word-length factor
(`Finset.exists_finset_card_smul_symmDiff_le_of_subset_closure`).

This file develops the resulting Følner and amenability characterizations for discrete and
topological groups, together with test-set/tolerance monotonicity, countable Følner-sequence
bridges, and `DecidableEq`-free finite `Set` (`Set.ncard`) bridges:

* For any generating set `S : Set G` (`Subgroup.closure S = ⊤`), `HasFoelnerSets G` (and, when `G`
  is discrete, `Amenable G`) holds iff every finite subset `K ⊆ S` and `ε > 0` admit a finite
  nonempty `F ⊆ G` with `|gF △ F| < ε · |F|` for all `g ∈ K`.
* For a **finite** generating set `S : Finset G` (`Subgroup.closure (S : Set G) = ⊤`), only the
  single test set `S` is needed: `HasFoelnerSets G` is equivalent to small individual generator
  boundaries, small summed generator boundary `∑ g ∈ S, |gF △ F| < ε · |F|`, and non-expansion of
  the unit Cayley ball `|({1} ∪ S) • F| < (1 + c) · |F|`. Negating gives a positive Cheeger /
  vertex-expansion constant on `{1} ∪ S` itself for every nonamenable finitely generated group.
* Along any nontrivial filter `l` (and, when `G` is countable, along `ℕ`), vanishing of
  `#((g • F i) ∆ F i) / #(F i)` on a generating set `S` characterizes `HasFoelnerSets G` and
  discrete `Amenable G`, and implies `Amenable G` in every group topology.

## Main results

* `Finset.exists_finset_card_smul_symmDiff_le_of_subset_closure`: quantitative generator-to-test-set
  boundary bound for any group action on finite sets.
* `TauCeti.hasFoelnerSets_iff_exists_finite_set`, `TauCeti.amenable_iff_exists_finite_set`:
  `DecidableEq`-free characterizations via `Set.Finite` and `Set.ncard`.
* `TauCeti.hasFoelnerSets_iff_of_closure_eq_top`, `TauCeti.amenable_iff_of_closure_eq_top`:
  characterizations testing finite subsets of an arbitrary generating set `S : Set G`.
* `TauCeti.hasFoelnerSets_iff_forall_pos_of_closure_eq_top`,
  `TauCeti.hasFoelnerSets_iff_sum_lt_of_closure_eq_top`,
  `TauCeti.hasFoelnerSets_iff_card_insert_one_smul_lt_of_closure_eq_top`: single-test, boundary-sum,
  and Cayley-ball expansion criteria for a finite generating set `S : Finset G`.
* `TauCeti.HasFoelnerSets.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top`,
  `TauCeti.Amenable.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top`: Følner-net generator
  criteria for `HasFoelnerSets` and topological `Amenable`.
* `TauCeti.amenable_iff_exists_seq`, `TauCeti.hasFoelnerSets_iff_exists_seq_of_closure_eq_top`,
  `TauCeti.amenable_iff_exists_seq_of_closure_eq_top`: countable Følner-sequence characterizations.

## References

* A. Garrido, *An introduction to amenable groups*, Definitions 3.1 and 3.3, Lemma 3.4,
  Theorem 3.6.
* B. Bekka, P. de la Harpe, A. Valette, *Kazhdan's Property (T)*, Theorem G.5.1 and Remark G.5.3.
-/

public section

open Filter Finset MeasureTheory Set Topology
open scoped ENNReal Pointwise symmDiff

section WordBound

variable {G X : Type*} [Group G] [MulAction G X] [DecidableEq X]

/-- Every element `g ∈ Subgroup.closure S` has a finite subset `K₀ ⊆ S` and a multiplicity `M`
bounding `#((g • F) ∆ F) ≤ M * ∑ s ∈ K₀, #((s • F) ∆ F)` uniformly for all `F : Finset X`. -/
@[to_additive
/-- Every element `g ∈ AddSubgroup.closure S` has a finite subset `K₀ ⊆ S` and a multiplicity `M`
bounding `#((g +ᵥ F) ∆ F) ≤ M * ∑ s ∈ K₀, #((s +ᵥ F) ∆ F)` uniformly for all `F : Finset X`. -/]
theorem Subgroup.exists_finset_card_smul_symmDiff_le_of_mem_closure {S : Set G} {g : G}
    (hg : g ∈ Subgroup.closure S) :
    ∃ K₀ : Finset G, (K₀ : Set G) ⊆ S ∧ ∃ M : ℕ,
      ∀ F : Finset X, #((g • F) ∆ F) ≤ M * ∑ s ∈ K₀, #((s • F) ∆ F) := by
  classical
  induction hg using Subgroup.closure_induction with
  | mem s hs =>
    exact ⟨{s}, singleton_subset_set_iff.2 hs, 1, fun F ↦ by simp⟩
  | one =>
    exact ⟨∅, by simp, 0, fun F ↦ by simp⟩
  | mul x y _ _ ihx ihy =>
    obtain ⟨Kx, hKx, Mx, hMx⟩ := ihx
    obtain ⟨Ky, hKy, My, hMy⟩ := ihy
    refine ⟨Kx ∪ Ky, coe_union Kx Ky ▸ Set.union_subset hKx hKy, Mx + My, fun F ↦ ?_⟩
    have hx : ∑ s ∈ Kx, #((s • F) ∆ F) ≤ ∑ s ∈ Kx ∪ Ky, #((s • F) ∆ F) :=
      sum_le_sum_of_subset subset_union_left
    have hy : ∑ s ∈ Ky, #((s • F) ∆ F) ≤ ∑ s ∈ Kx ∪ Ky, #((s • F) ∆ F) :=
      sum_le_sum_of_subset subset_union_right
    calc
      #(((x * y) • F) ∆ F) ≤ #((y • F) ∆ F) + #((x • F) ∆ F) :=
        card_mul_smul_finset_symmDiff_le x y F
      _ ≤ My * ∑ s ∈ Ky, #((s • F) ∆ F) + Mx * ∑ s ∈ Kx, #((s • F) ∆ F) :=
        Nat.add_le_add (hMy F) (hMx F)
      _ ≤ My * ∑ s ∈ Kx ∪ Ky, #((s • F) ∆ F) + Mx * ∑ s ∈ Kx ∪ Ky, #((s • F) ∆ F) :=
        Nat.add_le_add (Nat.mul_le_mul_left _ hy) (Nat.mul_le_mul_left _ hx)
      _ = (Mx + My) * ∑ s ∈ Kx ∪ Ky, #((s • F) ∆ F) := by rw [Nat.add_comm, Nat.add_mul]
  | inv x _ ihx =>
    obtain ⟨Kx, hKx, Mx, hMx⟩ := ihx
    refine ⟨Kx, hKx, Mx, fun F ↦ ?_⟩
    rw [card_inv_smul_finset_symmDiff_self]
    exact hMx F

/-- Quantitative generator-to-test-set bound: for any finite set `K` contained in
`Subgroup.closure S`, there exist a finite `K₀ ⊆ S` and `M : ℕ` bounding `#((g • F) ∆ F)` for all
`g ∈ K` and `F : Finset X` simultaneously. -/
@[to_additive
/-- Quantitative generator-to-test-set bound: for any finite set `K` contained in
`AddSubgroup.closure S`, there exist a finite `K₀ ⊆ S` and `M : ℕ` bounding `#((g +ᵥ F) ∆ F)` for
all `g ∈ K` and `F : Finset X` simultaneously. -/]
theorem Finset.exists_finset_card_smul_symmDiff_le_of_subset_closure {S : Set G} {K : Finset G}
    (hK : (K : Set G) ⊆ Subgroup.closure S) :
    ∃ K₀ : Finset G, (K₀ : Set G) ⊆ S ∧ ∃ M : ℕ,
      ∀ F : Finset X, ∀ g ∈ K, #((g • F) ∆ F) ≤ M * ∑ s ∈ K₀, #((s • F) ∆ F) := by
  classical
  induction K using Finset.induction with
  | empty => exact ⟨∅, by simp, 0, fun _ _ hg ↦ (notMem_empty _ hg).elim⟩
  | insert g K hgK ih =>
    rw [coe_insert, Set.insert_subset_iff] at hK
    obtain ⟨K₁, hK₁, M₁, hM₁⟩ :=
      Subgroup.exists_finset_card_smul_symmDiff_le_of_mem_closure (X := X) hK.1
    obtain ⟨K₂, hK₂, M₂, hM₂⟩ := ih hK.2
    refine ⟨K₁ ∪ K₂, coe_union K₁ K₂ ▸ Set.union_subset hK₁ hK₂, max M₁ M₂, fun F x hx ↦ ?_⟩
    rcases mem_insert.1 hx with rfl | hxK
    · exact (hM₁ F).trans (Nat.mul_le_mul (le_max_left _ _)
        (sum_le_sum_of_subset subset_union_left))
    · exact (hM₂ F x hxK).trans (Nat.mul_le_mul (le_max_right _ _)
        (sum_le_sum_of_subset subset_union_right))

end WordBound

namespace TauCeti

variable {G : Type*} [Group G]

/-! ### Finite-test monotonicity and `Set.Finite` bridges -/

/-- Monotonicity of a finite Følner test in both the test set `K₁ ⊆ K₂` and tolerance `ε₁ ≤ ε₂`. -/
theorem foelnerTest_mono [DecidableEq G] {K₁ K₂ : Finset G} (hK : K₁ ⊆ K₂) {ε₁ ε₂ : ℝ}
    (hε : ε₁ ≤ ε₂) {F : Finset G}
    (hF : ∀ g ∈ K₂, (#((g • F) ∆ F) : ℝ) < ε₁ * #F) :
    ∀ g ∈ K₁, (#((g • F) ∆ F) : ℝ) < ε₂ * #F :=
  fun g hg ↦ (hF g (hK hg)).trans_le (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _))

/-- `DecidableEq`-free finite-`Set` characterization of `HasFoelnerSets G` via `Set.ncard`. -/
theorem hasFoelnerSets_iff_exists_finite_set :
    HasFoelnerSets G ↔
      ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
        ∃ F : Set G, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  let : MeasurableSpace G := ⊤
  exact maxFoelner_count_neBot_iff

/-- `DecidableEq`-free finite-`Set` characterization of discrete group amenability. -/
theorem amenable_iff_exists_finite_set [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] :
    Amenable G ↔
      ∀ K : Finset G, ∀ ε : ℝ, 0 < ε →
        ∃ F : Set G, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard :=
  amenable_iff_hasFoelnerSets.trans hasFoelnerSets_iff_exists_finite_set

/-! ### Generating-set criteria for `HasFoelnerSets` and `Amenable` -/

/-- **Garrido Lemma 3.4 (arbitrary generating set, `Set.ncard` form).** When `S` generates `G`,
`HasFoelnerSets G` holds iff every finite `K ⊆ S` and `ε > 0` admit a finite nonempty `F : Set G`
passing the `K`-test. -/
theorem hasFoelnerSets_iff_exists_finite_set_of_closure_eq_top {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    HasFoelnerSets G ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ, 0 < ε →
        ∃ F : Set G, F.Finite ∧ F.Nonempty ∧
          ∀ g ∈ K, (((g • F) ∆ F).ncard : ℝ) < ε * F.ncard := by
  let : MeasurableSpace G := ⊤
  exact maxFoelner_count_neBot_iff_of_closure_eq_top hS

/-- **Garrido Lemma 3.4 (`Finset` form).** When `S` generates `G`, `HasFoelnerSets G` holds iff
every finite subset `K ⊆ S` and `ε > 0` admit a nonempty `F : Finset G` with
`#((g • F) ∆ F) < ε * #F` for all `g ∈ K`. -/
theorem hasFoelnerSets_iff_of_closure_eq_top [DecidableEq G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    HasFoelnerSets G ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ, 0 < ε →
        ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [hasFoelnerSets_iff_exists_finite_set_of_closure_eq_top hS]
  constructor
  · intro h K hKS ε hε
    obtain ⟨F, hfin, hne, hFK⟩ := h K hKS ε hε
    refine ⟨hfin.toFinset, hfin.toFinset_nonempty.2 hne, fun g hg ↦ ?_⟩
    rw [← Set.ncard_coe_finset, coe_symmDiff, coe_smul_finset, Finite.coe_toFinset,
      ← Set.ncard_eq_toFinset_card _ hfin]
    exact hFK g hg
  · intro h K hKS ε hε
    obtain ⟨F, hne, hFK⟩ := h K hKS ε hε
    refine ⟨F, F.finite_toSet, coe_nonempty.2 hne, fun g hg ↦ ?_⟩
    simpa only [← coe_smul_finset, ← coe_symmDiff, Set.ncard_coe_finset] using hFK g hg

/-- Discrete amenability tested on finite subsets of a generating set `S : Set G`. -/
theorem amenable_iff_of_closure_eq_top [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [DecidableEq G] {S : Set G} (hS : Subgroup.closure S = ⊤) :
    Amenable G ↔
      ∀ K : Finset G, (K : Set G) ⊆ S → ∀ ε : ℝ, 0 < ε →
        ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ K, (#((g • F) ∆ F) : ℝ) < ε * #F :=
  amenable_iff_hasFoelnerSets.trans (hasFoelnerSets_iff_of_closure_eq_top hS)

/-- **Single-test Følner criterion for finitely generated groups (Garrido Lemma 3.4,
BDHV Remark G.5.3).** If `S : Finset G` generates `G`, then `HasFoelnerSets G` holds iff for every
`ε > 0` there is a finite nonempty `F ⊆ G` with `#((g • F) ∆ F) < ε * #F` for all `g ∈ S`. -/
theorem hasFoelnerSets_iff_forall_pos_of_closure_eq_top [DecidableEq G] {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    HasFoelnerSets G ↔
      ∀ ε : ℝ, 0 < ε → ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ S, (#((g • F) ∆ F) : ℝ) < ε * #F := by
  rw [hasFoelnerSets_iff_of_closure_eq_top hS]
  exact ⟨fun h ε hε ↦ h S Set.Subset.rfl ε hε, fun h K hKS ε hε ↦
    let ⟨F, hne, hFS⟩ := h ε hε
    ⟨F, hne, foelnerTest_mono (coe_subset.1 hKS) le_rfl hFS⟩⟩

/-- Single-test amenability criterion for a discrete group generated by a finite set `S`. -/
theorem amenable_iff_forall_pos_of_closure_eq_top [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [DecidableEq G] {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    Amenable G ↔
      ∀ ε : ℝ, 0 < ε → ∃ F : Finset G, F.Nonempty ∧ ∀ g ∈ S, (#((g • F) ∆ F) : ℝ) < ε * #F :=
  amenable_iff_hasFoelnerSets.trans (hasFoelnerSets_iff_forall_pos_of_closure_eq_top hS)

/-- Summed-boundary (isoperimetric / Cheeger) Følner criterion for a finite generating set `S`. -/
theorem hasFoelnerSets_iff_sum_lt_of_closure_eq_top [DecidableEq G] {S : Finset G}
    (hS : Subgroup.closure (S : Set G) = ⊤) :
    HasFoelnerSets G ↔
      ∀ ε : ℝ, 0 < ε →
        ∃ F : Finset G, F.Nonempty ∧ (∑ g ∈ S, (#((g • F) ∆ F) : ℝ)) < ε * #F := by
  rw [hasFoelnerSets_iff_forall_pos_of_closure_eq_top hS]
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
    rw [hasFoelnerSets_iff_forall_pos_of_closure_eq_top hS]
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
gives `HasFoelnerSets G`. -/
theorem HasFoelnerSets.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top [DecidableEq G]
    {S : Set G} (hS : Subgroup.closure S = ⊤) {ι : Type*} {l : Filter ι} [l.NeBot]
    {F : ι → Finset G} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (hF : ∀ g ∈ S, Tendsto (fun i ↦ (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    HasFoelnerSets G := by
  rw [hasFoelnerSets_iff_of_closure_eq_top hS]
  intro K hKS ε hε
  have hev : ∀ᶠ i in l, ∀ g ∈ K, (#((g • F i) ∆ F i) : ℝ) / #(F i) < ε :=
    (eventually_all_finset K).2 fun g hg ↦ (hF g (hKS hg)).eventually (gt_mem_nhds hε)
  obtain ⟨i, hni, hi⟩ := (hne.and hev).exists
  exact ⟨F i, hni, fun g hg ↦ (div_lt_iff₀ (by exact_mod_cast hni.card_pos)).1 (hi g hg)⟩

/-- Along a nontrivial filter, vanishing of `#((g • F i) ∆ F i) / #(F i)` on a generating set `S`
makes `G` amenable for every group topology. -/
theorem Amenable.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top [TopologicalSpace G]
    [IsTopologicalGroup G] [DecidableEq G] {S : Set G} (hS : Subgroup.closure S = ⊤) {ι : Type*}
    {l : Filter ι} [l.NeBot] {F : ι → Finset G} (hne : ∀ᶠ i in l, (F i).Nonempty)
    (hF : ∀ g ∈ S, Tendsto (fun i ↦ (#((g • F i) ∆ F i) : ℝ) / #(F i)) l (𝓝 0)) :
    Amenable G :=
  .of_hasFoelnerSets (.of_tendsto_card_smul_symmDiff_div_card_of_closure_eq_top hS hne hF)

/-- A countable discrete group is amenable iff it admits a sequence of finite nonempty sets whose
relative translation boundaries tend to zero for every group element. -/
theorem amenable_iff_exists_seq [Countable G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DiscreteTopology G] [DecidableEq G] :
    Amenable G ↔
      ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
        ∀ g : G, Tendsto (fun n ↦ (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  amenable_iff_hasFoelnerSets.trans hasFoelnerSets_iff_exists_seq

/-- When `G` is countable and `S` generates `G`, `HasFoelnerSets G` holds iff there is a sequence
of finite nonempty sets whose relative translation boundaries tend to zero on `S`. -/
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
    [IsTopologicalGroup G] [DiscreteTopology G] [DecidableEq G] {S : Set G}
    (hS : Subgroup.closure S = ⊤) :
    Amenable G ↔
      ∃ F : ℕ → Finset G, (∀ n, (F n).Nonempty) ∧
        ∀ g ∈ S, Tendsto (fun n ↦ (#((g • F n) ∆ F n) : ℝ) / #(F n)) atTop (𝓝 0) :=
  amenable_iff_hasFoelnerSets.trans (hasFoelnerSets_iff_exists_seq_of_closure_eq_top hS)

end TauCeti
