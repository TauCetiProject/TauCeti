/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Density
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import TauCeti.Algebra.Order.BigOperators.Sum.UnitWeights
import TauCeti.Combinatorics.SimpleGraph.Density
import TauCeti.Order.Partition.Finpartition

/-!
# Regularity of pair colors and of the lower skeleton

For a pair-color system `S` and two vertex sets `s` and `t`, `S.IsRegularPair ε s t` says that
the density of every palette color on `(s, t)` is within `ε` of its density on every pair of
subsets `s' ⊆ s`, `t' ⊆ t` with `ε * #s ≤ #s'` and `ε * #t ≤ #t'`. The condition is
coordinatewise: each color is controlled separately. Densities are taken among ordered
*distinct* pairs, so the condition is meaningful also when `s = t`.

For disjoint `s` and `t`, an `ε`-regular pair has small *rectangle discrepancy*: for every color
`c`, the number of pairs of color `c` in `s' ×ˢ t'` is within `ε |s| |t|` of the count
`d_c(s, t) |s'| |t'|` predicted by the density on `(s, t)`. The same bound holds when the
indicator of `c` is tested against functions with values in `[0, 1]`; this is the input of
counting lemmas. Both follow the corresponding bounds for uniform pairs of a graph,
`SimpleGraph.IsUniform.abs_card_interedges_sub_le` and
`SimpleGraph.IsUniform.abs_sum_sum_mul_sub_le`.

A `PairSkeleton3` bundles a partition of the host into vertex cells with a pair-color system.
It is the lower skeleton over which triple densities and their regularity are measured.
`PairSkeleton3.IsPairColorRegular S ε` asks for `ε`-regularity of every ordered pair of vertex
cells, diagonal pairs included; `PairSkeleton3.LowerSkeletonRegular S F` evaluates an error
schedule `F : ℕ → ℝ` at the lower complexity, the number of vertex cells plus the palette size.

## Main declarations

* `TauCeti.PairColorSystem.IsRegularPair`: coordinatewise `ε`-regularity of a pair of sets.
* `TauCeti.PairColorSystem.isRegularPair_comm`: regularity is symmetric in the two sets.
* `TauCeti.PairColorSystem.IsRegularPair.of_subset`: the slicing lemma; subsets of at least an
  `α`-fraction of the sizes form a `max (2ε) (ε / α)`-regular pair.
* `TauCeti.PairColorSystem.IsRegularPair.abs_card_filter_colorOfPair_sub_le`: rectangle
  discrepancy of a regular pair of disjoint sets.
* `TauCeti.PairColorSystem.abs_card_filter_colorOfPair_sub_le_of_refines`: aggregating fine-block
  rectangle discrepancy across a refinement `Q ≤ P` to coarse blocks.
* `TauCeti.PairColorSystem.isRegularPair_of_abs_card_filter_colorOfPair_sub_le`: converse
  criterion deducing `IsRegularPair` and density proximity from small rectangle count discrepancy.
* `TauCeti.PairColorSystem.IsRegularPair.abs_sum_sum_mul_sub_le`: the same bound for tests with
  values in `[0, 1]`.
* `TauCeti.PairSkeleton3`: vertex cells together with a pair-color system.
* `TauCeti.PairSkeleton3.IsPairColorRegular`: every pair of vertex cells is regular.
* `TauCeti.PairSkeleton3.isPairColorRegular_bot`: the partition into singletons is regular.
* `TauCeti.PairSkeleton3.LowerSkeletonRegular`: regularity at the lower complexity.
* `TauCeti.PairSkeleton3.relabel`: renaming the pair palette along an equivalence, preserving
  `IsRegularPair`, `IsPairColorRegular`, and `LowerSkeletonRegular`.

## References

* J. Komlós and M. Simonovits, *Szemerédi's regularity lemma and its applications in graph
  theory*, in Combinatorics, Paul Erdős is Eighty, Vol. 2 (1996), Fact 1.5 (the slicing lemma).
* V. Rödl, M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007).
* C. Terry, *Growth of regular partitions 4: strong regularity and the pairs partition*,
  arXiv:2404.02030.
-/

public section

open Finset

namespace TauCeti

variable {κ V : Type*}

namespace PairColorSystem

/-- A pair `(s, t)` of vertex sets is `ε`-regular for the pair-color system `S` when, for every
color, its density on any `s' ⊆ s` and `t' ⊆ t` with `ε * #s ≤ #s'` and `ε * #t ≤ #t'` is within
`ε` of its density on `(s, t)`. Each color is controlled separately. -/
def IsRegularPair (S : PairColorSystem κ V) (ε : ℝ) (s t : Finset V) : Prop :=
  ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
    |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε

variable {S : PairColorSystem κ V} {ε ε' : ℝ} {s t : Finset V}

/-- Unfolded form of `PairColorSystem.IsRegularPair`. -/
theorem isRegularPair_iff : S.IsRegularPair ε s t ↔
    ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t, ε * #s ≤ #s' → ε * #t ≤ #t' →
      |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t| ≤ ε :=
  Iff.rfl

/-- Regularity is monotone in its parameter. -/
theorem IsRegularPair.mono (h : S.IsRegularPair ε s t) (hε : ε ≤ ε') :
    S.IsRegularPair ε' s t := by
  intro c s' hs' t' ht' hs ht
  refine (h c s' hs' t' ht' ?_ ?_).trans hε
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans hs
  · exact (mul_le_mul_of_nonneg_right hε (Nat.cast_nonneg _)).trans ht

/-- Every pair is `ε`-regular once `1 ≤ ε`, since densities lie in `[0, 1]`. -/
theorem isRegularPair_of_one_le (hε : 1 ≤ ε) : S.IsRegularPair ε s t := by
  intro c s' _ t' _ _ _
  have h₀ : (0 : ℝ) ≤ pairColorDensity S c s' t' := mod_cast pairColorDensity_nonneg S c s' t'
  have h₁ : (pairColorDensity S c s' t' : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s' t'
  have h₀' : (0 : ℝ) ≤ pairColorDensity S c s t := mod_cast pairColorDensity_nonneg S c s t
  have h₁' : (pairColorDensity S c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s t
  exact (abs_sub_le_iff.mpr ⟨by linarith, by linarith⟩).trans hε

/-- Exchanging the two sets preserves regularity. -/
theorem IsRegularPair.symm (h : S.IsRegularPair ε s t) : S.IsRegularPair ε t s := by
  intro c t' ht' s' hs' ht hs
  have hc := h (S.rev c) s' hs' t' ht' hs ht
  rwa [← pairColorDensity_swap S (S.rev c) s' t', ← pairColorDensity_swap S (S.rev c) s t,
    rev_rev] at hc

/-- Regularity is symmetric in the two sets. -/
theorem isRegularPair_comm : S.IsRegularPair ε s t ↔ S.IsRegularPair ε t s :=
  ⟨IsRegularPair.symm, IsRegularPair.symm⟩

/-- A regular pair for a nonempty palette has a nonnegative parameter: for a negative parameter,
the empty subsets pass the size thresholds. -/
theorem IsRegularPair.nonneg [Nonempty κ] (h : S.IsRegularPair ε s t) : 0 ≤ ε := by
  by_contra! hε
  have h₀ (u : Finset V) : ε * #u ≤ (#(∅ : Finset V) : ℝ) := by
    rw [card_empty, Nat.cast_zero]
    exact mul_nonpos_of_nonpos_of_nonneg hε.le (Nat.cast_nonneg _)
  exact (abs_nonneg _).not_gt
    ((h (Classical.arbitrary κ) ∅ (empty_subset _) ∅ (empty_subset _) (h₀ s) (h₀ t)).trans_lt hε)

/-- **Slicing lemma.** If `(s, t)` is `ε`-regular, then every pair of subsets `s₁ ⊆ s` and
`t₁ ⊆ t` of at least an `α`-fraction of the sizes of `s` and `t` is
`max (2ε) (ε / α)`-regular. -/
theorem IsRegularPair.of_subset (h : S.IsRegularPair ε s t) {s₁ t₁ : Finset V} (hs : s₁ ⊆ s)
    (ht : t₁ ⊆ t) {α : ℝ} (hα : 0 < α) (hs₁ : α * #s ≤ #s₁) (ht₁ : α * #t ≤ #t₁) :
    S.IsRegularPair (max (2 * ε) (ε / α)) s₁ t₁ := by
  intro c s' hs' t' ht' hs'₁ ht'₁
  have hε : 0 ≤ ε := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  obtain hαε | hεα := lt_or_ge α ε
  · exact isRegularPair_of_one_le (le_max_of_le_right ((one_lt_div hα).2 hαε).le) c s' hs' t' ht'
      hs'₁ ht'₁
  -- A subset of `u₁` passing the sliced threshold passes the original threshold in `u`.
  have key {u u₁ u' : Finset V} (hu₁ : α * #u ≤ #u₁)
      (hu' : max (2 * ε) (ε / α) * #u₁ ≤ #u') : ε * #u ≤ #u' :=
    calc ε * #u = ε / α * (α * #u) := by rw [← mul_assoc, div_mul_cancel₀ ε hα.ne']
      _ ≤ ε / α * #u₁ := by gcongr
      _ ≤ max (2 * ε) (ε / α) * #u₁ := by gcongr; exact le_max_right _ _
      _ ≤ #u' := hu'
  have h₁ := h c s' (hs'.trans hs) t' (ht'.trans ht) (key hs₁ hs'₁) (key ht₁ ht'₁)
  have h₂ := h c s₁ hs t₁ ht (by grw [hεα, hs₁]) (by grw [hεα, ht₁])
  rw [abs_sub_comm] at h₂
  calc _ ≤ _ := abs_sub_le _ (pairColorDensity S c s t : ℝ) _
    _ ≤ 2 * ε := by linarith
    _ ≤ _ := le_max_left _ _

/-- Two singletons form an `ε`-regular pair for every `ε > 0`. -/
theorem isRegularPair_singleton (hε : 0 < ε) (u v : V) : S.IsRegularPair ε {u} {v} := by
  intro c s' hs' t' ht' hs ht
  rw [card_singleton, Nat.cast_one, mul_one] at hs ht
  obtain rfl | rfl := subset_singleton_iff.mp hs'
  · exact absurd hs (by simpa using hε)
  obtain rfl | rfl := subset_singleton_iff.mp ht'
  · exact absurd ht (by simpa using hε)
  simpa using hε.le

/-- Renaming the palette along an equivalence preserves `IsRegularPair`. -/
@[simp]
theorem isRegularPair_relabel_iff {κ' : Type*} (e : κ ≃ κ') :
    (S.relabel e).IsRegularPair ε s t ↔ S.IsRegularPair ε s t := by
  refine ⟨fun h c s' hs' t' ht' hs ht ↦ ?_, fun h c s' hs' t' ht' hs ht ↦ ?_⟩
  · simpa only [pairColorDensity_relabel, e.symm_apply_apply] using h (e c) s' hs' t' ht' hs ht
  · simpa only [pairColorDensity_relabel] using h (e.symm c) s' hs' t' ht' hs ht

/-- Renaming the palette along an equivalence preserves `IsRegularPair`. -/
theorem IsRegularPair.relabel {κ' : Type*} (h : S.IsRegularPair ε s t) (e : κ ≃ κ') :
    (S.relabel e).IsRegularPair ε s t :=
  (isRegularPair_relabel_iff e).2 h

section Discrepancy

variable [DecidableEq κ] {s' t' : Finset V} {c : κ}

/-- **Rectangle discrepancy of a regular pair.** If `(s, t)` is an `ε`-regular pair of disjoint
sets, then for all `s' ⊆ s` and `t' ⊆ t` the number of pairs of color `c` in `s' ×ˢ t'` is within
`ε |s| |t|` of the count `d_c(s, t) |s'| |t'|` predicted by the density of `c` on `(s, t)`. -/
theorem IsRegularPair.abs_card_filter_colorOfPair_sub_le (h : S.IsRegularPair ε s t)
    (hst : Disjoint s t) (hs' : s' ⊆ s) (ht' : t' ⊆ t) :
    |(#{p ∈ s' ×ˢ t' | S.colorOfPair p.1 p.2 = some c} : ℝ) -
        pairColorDensity S c s t * #s' * #t'| ≤ ε * #s * #t := by
  classical
  have hε : 0 ≤ ε := haveI : Nonempty κ := ⟨c⟩; h.nonneg
  have hs : (#s' : ℝ) ≤ #s := by exact_mod_cast card_le_card hs'
  have ht : (#t' : ℝ) ≤ #t := by exact_mod_cast card_le_card ht'
  have hcount : (#{p ∈ s' ×ˢ t' | S.colorOfPair p.1 p.2 = some c} : ℝ) =
      pairColorDensity S c s' t' * (#s' * #t') :=
    mod_cast (pairColorDensity_mul_card_of_disjoint S c (hst.mono hs' ht')).symm
  have hd₀ : (0 : ℝ) ≤ pairColorDensity S c s t := mod_cast pairColorDensity_nonneg S c s t
  have hd₁ : (pairColorDensity S c s t : ℝ) ≤ 1 := mod_cast pairColorDensity_le_one S c s t
  by_cases hbig : ε * #s ≤ #s' ∧ ε * #t ≤ #t'
  · rw [hcount, mul_assoc (pairColorDensity S c s t : ℝ), ← sub_mul, abs_mul,
      abs_of_nonneg (a := (#s' : ℝ) * #t') (by positivity), mul_assoc]
    exact mul_le_mul (h c s' hs' t' ht' hbig.1 hbig.2) (mul_le_mul hs ht (by positivity)
      (by positivity)) (by positivity) hε
  · -- A thin rectangle has at most `ε |s| |t|` pairs, which bounds both counts.
    have hsmall : (#s' : ℝ) * #t' ≤ ε * #s * #t := by
      rcases not_and_or.1 hbig with hb | hb
      · calc (#s' : ℝ) * #t' ≤ (ε * #s) * #t :=
              mul_le_mul (not_le.1 hb).le ht (by positivity) (by positivity)
          _ = ε * #s * #t := by ring
      · calc (#s' : ℝ) * #t' ≤ #s * (ε * #t) :=
              mul_le_mul hs (not_le.1 hb).le (by positivity) (by positivity)
          _ = ε * #s * #t := by ring
    refine (abs_sub_le_of_nonneg_of_le (by positivity) ?_ (by positivity) ?_).trans hsmall
    · rw [hcount]
      exact mul_le_of_le_one_left (by positivity) (mod_cast pairColorDensity_le_one S c s' t')
    · rw [mul_assoc]
      exact mul_le_of_le_one_left (by positivity) hd₁

/-- **Test-function discrepancy of a regular pair.** If `(s, t)` is an `ε`-regular pair of
disjoint sets, then testing the deviation of the indicator of a color `c` from its density on
`(s, t)` against functions `f` on `s` and `g` on `t` with values in `[0, 1]` gives at most
`ε |s| |t|`. -/
theorem IsRegularPair.abs_sum_sum_mul_sub_le (h : S.IsRegularPair ε s t) (hst : Disjoint s t)
    (c : κ) {f g : V → ℝ} (hf₀ : ∀ x ∈ s, 0 ≤ f x) (hf₁ : ∀ x ∈ s, f x ≤ 1)
    (hg₀ : ∀ y ∈ t, 0 ≤ g y) (hg₁ : ∀ y ∈ t, g y ≤ 1) :
    |∑ x ∈ s, ∑ y ∈ t, f x * g y *
        ((if S.colorOfPair x y = some c then 1 else 0) - pairColorDensity S c s t)| ≤
      ε * #s * #t := by
  refine abs_sum_sum_mul_mul_le_of_forall_subset hf₀ hf₁ hg₀ hg₁ fun s' hs' t' ht' ↦ ?_
  convert h.abs_card_filter_colorOfPair_sub_le (c := c) hst hs' ht' using 2
  rw [natCast_card_filter, sum_product]
  simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  ring

variable (S) in
/-- **Coarse rectangle discrepancy from fine blocks.** Let `Q ≤ P` be finite partitions of `u`, and
let `A, B ∈ P.parts` be coarse parts. If for `X ⊆ A`, `Y ⊆ B`, and a color `c`, every pair
`(A', B')` of fine parts in `A` and `B` has count discrepancy at most `η * (#A' * #B')` around `d`
on `(X ∩ A') ×ˢ (Y ∩ B')`, then `X ×ˢ Y` has count discrepancy at most `η * (#A * #B)` around
`d`. -/
theorem abs_card_filter_colorOfPair_sub_le_of_refines [DecidableEq V]
    {u : Finset V} {P Q : Finpartition u} (hQP : Q ≤ P)
    {A B : Finset V} (hA : A ∈ P.parts) (hB : B ∈ P.parts) {d η : ℝ}
    (c : κ) {X Y : Finset V} (hX : X ⊆ A) (hY : Y ⊆ B)
    (hfine : ∀ A' ∈ Q.parts, A' ⊆ A → ∀ B' ∈ Q.parts, B' ⊆ B →
      |(#{q ∈ (X ∩ A') ×ˢ (Y ∩ B') | S.colorOfPair q.1 q.2 = some c} : ℝ) -
        d * (#(X ∩ A') * #(Y ∩ B'))| ≤ η * (#A' * #B')) :
    |(#{q ∈ X ×ˢ Y | S.colorOfPair q.1 q.2 = some c} : ℝ) - d * (#X * #Y)| ≤
      η * (#A * #B) := by
  let pA : P.parts := ⟨A, hA⟩
  let pB : P.parts := ⟨B, hB⟩
  set QA : Finset Q.parts := {A' | Finpartition.refinementParent hQP A' = pA}
  set QB : Finset Q.parts := {B' | Finpartition.refinementParent hQP B' = pB}
  let r (x y : V) : Prop := S.colorOfPair x y = some c
  have hinter (s t : Finset V) :
      {q ∈ s ×ˢ t | S.colorOfPair q.1 q.2 = some c} = Rel.interedges r s t := rfl
  have hXA : QA.biUnion (fun A' ↦ X ∩ A'.val) = X := by
    rw [← inter_biUnion, Finpartition.biUnion_filter_refinementParent_eq hQP pA,
      inter_eq_left.2 hX]
  have hYB : QB.biUnion (fun B' ↦ Y ∩ B'.val) = Y := by
    rw [← inter_biUnion, Finpartition.biUnion_filter_refinementParent_eq hQP pB,
      inter_eq_left.2 hY]
  have hXcard : (#X : ℝ) = ∑ A' ∈ QA, (#(X ∩ A'.val) : ℝ) := by
    exact_mod_cast (congrArg card (inter_eq_left.2 hX).symm).trans
      (Finpartition.sum_card_inter_filter_refinementParent_eq hQP pA X).symm
  have hYcard : (#Y : ℝ) = ∑ B' ∈ QB, (#(Y ∩ B'.val) : ℝ) := by
    exact_mod_cast (congrArg card (inter_eq_left.2 hY).symm).trans
      (Finpartition.sum_card_inter_filter_refinementParent_eq hQP pB Y).symm
  have hAcard : (#A : ℝ) = ∑ A' ∈ QA, (#A'.val : ℝ) := by
    exact_mod_cast (Finpartition.sum_card_filter_refinementParent_eq hQP pA).symm
  have hBcard : (#B : ℝ) = ∑ B' ∈ QB, (#B'.val : ℝ) := by
    exact_mod_cast (Finpartition.sum_card_filter_refinementParent_eq hQP pB).symm
  have hcount : (#{q ∈ X ×ˢ Y | S.colorOfPair q.1 q.2 = some c} : ℝ) =
      ∑ A' ∈ QA, ∑ B' ∈ QB,
        (#{q ∈ (X ∩ A'.val) ×ˢ (Y ∩ B'.val) | S.colorOfPair q.1 q.2 = some c} : ℝ) := by
    simp_rw [hinter]
    have hnat : #(Rel.interedges r X Y) =
        ∑ A' ∈ QA, ∑ B' ∈ QB, #(Rel.interedges r (X ∩ A'.val) (Y ∩ B'.val)) := by
      conv_lhs => rw [← hXA, ← hYB]
      rw [Rel.card_interedges_biUnion_left r QA _ _
        ((Q.pairwiseDisjoint_subtype_val _).mono fun _ ↦ inter_subset_right)]
      exact sum_congr rfl fun A' _ ↦ Rel.card_interedges_biUnion_right r _ QB _
        ((Q.pairwiseDisjoint_subtype_val _).mono fun _ ↦ inter_subset_right)
    exact_mod_cast hnat
  have hmean : d * (#X * #Y) = ∑ A' ∈ QA, ∑ B' ∈ QB, d * (#(X ∩ A'.val) * #(Y ∩ B'.val)) := by
    rw [hXcard, hYcard, sum_mul_sum, mul_sum]
    exact sum_congr rfl fun _ _ ↦ mul_sum _ _ _
  rw [hcount, hmean, ← sum_sub_distrib, hAcard, hBcard, sum_mul_sum, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun A' hA' ↦ ?_)
  rw [← sum_sub_distrib, mul_sum]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun B' hB' ↦ ?_)
  exact hfine A'.val A'.property
    ((Finpartition.refinementParent_eq_iff hQP).1 (mem_filter.1 hA').2)
    B'.val B'.property ((Finpartition.refinementParent_eq_iff hQP).1 (mem_filter.1 hB').2)

variable (S) in
/-- Small rectangle count discrepancy on disjoint nonempty `(s, t)` around `p` implies both
`|(pairColorDensity S c s t : ℝ) - p c| ≤ η` and `S.IsRegularPair θ s t` whenever `0 < θ` and
`θ < 1 → 2 * η ≤ θ ^ 3`. -/
theorem isRegularPair_of_abs_card_filter_colorOfPair_sub_le (hst : Disjoint s t) (hs : s.Nonempty)
    (ht : t.Nonempty) {p : κ → ℝ} {η θ : ℝ} (hθ : 0 < θ) (hη : θ < 1 → 2 * η ≤ θ ^ 3)
    (hrect : ∀ c, ∀ s' ⊆ s, ∀ t' ⊆ t,
      |(#{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c} : ℝ) - p c * (#s' * #t')| ≤
        η * (#s * #t)) :
    S.IsRegularPair θ s t ∧ ∀ c, |(pairColorDensity S c s t : ℝ) - p c| ≤ η := by
  classical
  have hs0 : (0 : ℝ) < #s := Nat.cast_pos.2 hs.card_pos
  have ht0 : (0 : ℝ) < #t := Nat.cast_pos.2 ht.card_pos
  have hd_le {s' t' : Finset V} (hs' : s' ⊆ s) (ht' : t' ⊆ t) (c : κ) :
      |(pairColorDensity S c s' t' : ℝ) - p c| * (#s' * #t') ≤ η * (#s * #t) := by
    have hc : (#{q ∈ s' ×ˢ t' | S.colorOfPair q.1 q.2 = some c} : ℝ) =
        pairColorDensity S c s' t' * (#s' * #t') :=
      mod_cast (pairColorDensity_mul_card_of_disjoint S c (hst.mono hs' ht')).symm
    have hr := hrect c s' hs' t' ht'
    rwa [hc, ← sub_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ #s' * #t')] at hr
  have hfull (c : κ) : |(pairColorDensity S c s t : ℝ) - p c| ≤ η :=
    le_of_mul_le_mul_right (hd_le subset_rfl subset_rfl c) (mul_pos hs0 ht0)
  refine ⟨?_, hfull⟩
  obtain h1θ | hθ1 := le_or_gt 1 θ
  · exact isRegularPair_of_one_le h1θ
  specialize hη hθ1
  rw [isRegularPair_iff]
  intro c s' hs' t' ht' hs's ht't
  have hpos : (0 : ℝ) < #s' * #t' := mul_pos ((mul_pos hθ hs0).trans_le hs's)
    ((mul_pos hθ ht0).trans_le ht't)
  have hsub : |(pairColorDensity S c s' t' : ℝ) - p c| ≤ θ / 2 := by
    refine le_of_mul_le_mul_right ?_ hpos
    calc |(pairColorDensity S c s' t' : ℝ) - p c| * (#s' * #t')
        ≤ η * (#s * #t) := hd_le hs' ht' c
      _ ≤ (θ ^ 3 / 2) * (#s * #t) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = (θ / 2) * ((θ * #s) * (θ * #t)) := by ring
      _ ≤ (θ / 2) * (#s' * #t') := by gcongr
  have hη_le : η ≤ θ / 2 := by
    have : θ ^ 3 ≤ θ := by nlinarith [sq_nonneg θ]
    linarith
  calc |(pairColorDensity S c s' t' : ℝ) - pairColorDensity S c s t|
      ≤ |(pairColorDensity S c s' t' : ℝ) - p c| + |p c - pairColorDensity S c s t| :=
        abs_sub_le _ _ _
    _ ≤ θ := by rw [abs_sub_comm (p c)]; linarith [hfull c]

end Discrepancy

end PairColorSystem

/-- The lower skeleton of an arity-three complex: a partition of the host into vertex cells,
together with a coherent coloring of the ordered distinct vertex pairs. -/
@[ext]
structure PairSkeleton3 (κ : Type*) (V : Type*) [Fintype V] [DecidableEq V] where
  /-- The partition of the host into vertex cells. -/
  vertexPart : Finpartition (univ : Finset V)
  /-- The coloring of ordered distinct vertex pairs. -/
  pairColors : PairColorSystem κ V

namespace PairSkeleton3

variable [Fintype V] [DecidableEq V] (S : PairSkeleton3 κ V) {ε ε' : ℝ}

/-- The lower skeleton is `ε`-regular when every ordered pair of its vertex cells, including a
cell paired with itself, is `ε`-regular for its pair colors. The test subsets range over the
subsets of the actual cells, tying pair regularity to the skeleton. -/
def IsPairColorRegular (ε : ℝ) : Prop :=
  ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts, S.pairColors.IsRegularPair ε A B

variable {S}

/-- Unfolded form of `PairSkeleton3.IsPairColorRegular`: for every color and every ordered pair
of vertex cells, the color density is stable on all large enough subcells. -/
theorem isPairColorRegular_iff : S.IsPairColorRegular ε ↔
    ∀ c, ∀ A ∈ S.vertexPart.parts, ∀ B ∈ S.vertexPart.parts, ∀ A' ⊆ A, ∀ B' ⊆ B,
      ε * #A ≤ #A' → ε * #B ≤ #B' →
        |(pairColorDensity S.pairColors c A' B' : ℝ) - pairColorDensity S.pairColors c A B| ≤
          ε :=
  ⟨fun h c A hA B hB => h A hA B hB c, fun h A hA B hB c => h c A hA B hB⟩

/-- In a regular lower skeleton, every ordered pair of vertex cells is a regular pair. -/
theorem IsPairColorRegular.isRegularPair (h : S.IsPairColorRegular ε) {A B : Finset V}
    (hA : A ∈ S.vertexPart.parts) (hB : B ∈ S.vertexPart.parts) :
    S.pairColors.IsRegularPair ε A B :=
  h A hA B hB

/-- Pair-color regularity is monotone in its parameter. -/
theorem IsPairColorRegular.mono (h : S.IsPairColorRegular ε) (hε : ε ≤ ε') :
    S.IsPairColorRegular ε' :=
  fun A hA B hB => (h A hA B hB).mono hε

/-- Every lower skeleton is `ε`-regular once `1 ≤ ε`. -/
theorem isPairColorRegular_of_one_le (hε : 1 ≤ ε) : S.IsPairColorRegular ε :=
  fun _ _ _ _ => PairColorSystem.isRegularPair_of_one_le hε

/-- A regular lower skeleton on a nonempty host with a nonempty palette has a nonnegative
parameter. -/
theorem IsPairColorRegular.nonneg [Nonempty κ] [Nonempty V] (h : S.IsPairColorRegular ε) :
    0 ≤ ε := by
  obtain ⟨A, hA⟩ := S.vertexPart.parts_nonempty univ_nonempty.ne_empty
  exact (h A hA A hA).nonneg

/-- A lower skeleton whose vertex cells are the singletons is `ε`-regular for every `ε > 0`. -/
theorem isPairColorRegular_bot (hε : 0 < ε) (C : PairColorSystem κ V) :
    (⟨⊥, C⟩ : PairSkeleton3 κ V).IsPairColorRegular ε := by
  intro A hA B hB
  obtain ⟨u, -, rfl⟩ := Finpartition.mem_bot_iff.mp hA
  obtain ⟨v, -, rfl⟩ := Finpartition.mem_bot_iff.mp hB
  exact PairColorSystem.isRegularPair_singleton hε u v

variable (S) in
/-- Lower-skeleton regularity for an error schedule `F : ℕ → ℝ`: pair-color regularity at the
parameter `F` takes at the lower complexity, the number of vertex cells plus the palette size. -/
def LowerSkeletonRegular [Fintype κ] (F : ℕ → ℝ) : Prop :=
  S.IsPairColorRegular (F (#S.vertexPart.parts + Fintype.card κ))

/-- Unfolded form of `PairSkeleton3.LowerSkeletonRegular`. -/
theorem lowerSkeletonRegular_iff [Fintype κ] {F : ℕ → ℝ} :
    S.LowerSkeletonRegular F ↔ S.IsPairColorRegular (F (#S.vertexPart.parts + Fintype.card κ)) :=
  Iff.rfl

/-- A lower skeleton regular for a schedule is regular at every parameter dominating the
scheduled one. -/
theorem LowerSkeletonRegular.isPairColorRegular [Fintype κ] {F : ℕ → ℝ}
    (h : S.LowerSkeletonRegular F) (hε : F (#S.vertexPart.parts + Fintype.card κ) ≤ ε) :
    S.IsPairColorRegular ε :=
  IsPairColorRegular.mono h hε

variable (S) in
/-- Rename the pair palette of a lower skeleton along an equivalence, keeping its vertex cells. -/
def relabel {κ' : Type*} (e : κ ≃ κ') : PairSkeleton3 κ' V :=
  ⟨S.vertexPart, S.pairColors.relabel e⟩

@[simp]
theorem relabel_vertexPart {κ' : Type*} (e : κ ≃ κ') : (S.relabel e).vertexPart = S.vertexPart :=
  (rfl)

@[simp]
theorem relabel_pairColors {κ' : Type*} (e : κ ≃ κ') :
    (S.relabel e).pairColors = S.pairColors.relabel e :=
  (rfl)

/-- Renaming the pair palette preserves pair-color regularity of a lower skeleton. -/
@[simp]
theorem isPairColorRegular_relabel_iff {κ' : Type*} (e : κ ≃ κ') :
    (S.relabel e).IsPairColorRegular ε ↔ S.IsPairColorRegular ε := by
  simp [IsPairColorRegular]

/-- Renaming the palette along an equivalence preserves `IsPairColorRegular`. -/
theorem IsPairColorRegular.relabel {κ' : Type*} (h : S.IsPairColorRegular ε) (e : κ ≃ κ') :
    (S.relabel e).IsPairColorRegular ε :=
  (isPairColorRegular_relabel_iff e).2 h

/-- Renaming the pair palette preserves scheduled lower-skeleton regularity. -/
@[simp]
theorem lowerSkeletonRegular_relabel_iff {κ' : Type*} [Fintype κ] [Fintype κ'] (e : κ ≃ κ')
    {F : ℕ → ℝ} :
    (S.relabel e).LowerSkeletonRegular F ↔ S.LowerSkeletonRegular F := by
  simp [LowerSkeletonRegular, Fintype.card_congr e]

/-- Renaming the palette along an equivalence preserves `LowerSkeletonRegular`. -/
theorem LowerSkeletonRegular.relabel {κ' : Type*} [Fintype κ] [Fintype κ'] {F : ℕ → ℝ}
    (h : S.LowerSkeletonRegular F) (e : κ ≃ κ') :
    (S.relabel e).LowerSkeletonRegular F :=
  (lowerSkeletonRegular_relabel_iff e).2 h

end PairSkeleton3

end TauCeti
