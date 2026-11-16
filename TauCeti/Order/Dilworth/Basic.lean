/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Order.Antichain

import Mathlib.Order.Antisymmetrization
import Mathlib.Order.Preorder.Finite
import TauCeti.Order.Chain

/-!
# Dilworth's theorem and antichain width for finite orders

For any binary relation on a type, an antichain meets each chain in at most one element, so its
cardinality is bounded above by the size of any chain cover
(`IsAntichain.card_le_card_of_chainCover`). When a finite set carries a transitive relation (in
particular, any preorder or partial order), **Dilworth's theorem**
(`Finset.exists_isAntichain_chainPartition` and `TauCeti.finite_dilworth`) asserts that this bound
is attained: there exist an antichain `A` and a partition `C` into nonempty chains with
`A.card = C.card`.

We also define the finite antichain width `Finset.antichainWidth` and prove its basic API together
with `Finset.exists_chainPartition_card_eq_antichainWidth`.

## Main definitions

* `Finset.antichainWidth`: the maximum cardinality of an antichain contained in a finite set `s`.

## Main results

* `IsAntichain.card_le_card_of_chainCover` and
  `IsAntichain.existsUnique_mem_of_chainCover_of_card_le`: weak duality between antichains and
  chain covers, and unique intersection at equality.
* `Finset.exists_isAntichain_chainPartition` and `TauCeti.finite_dilworth`: Dilworth's theorem
  for finite subsets of a transitive relation and for finite types, proved by Galvin's induction.
* `Finset.exists_chainPartition_card_eq_antichainWidth`: every finite set in a transitive order
  admits a partition into `s.antichainWidth` nonempty chains.

## References

* R. P. Dilworth, *A decomposition theorem for partially ordered sets*, Ann. of Math. **51**
  (1950), 161–166.
* F. Galvin, *A proof of Dilworth's chain decomposition theorem*, Amer. Math. Monthly **101**
  (1994), 352–353.
-/

public section

section WeakDuality

namespace IsAntichain

/-- **Weak duality between antichains and chain covers.** An antichain covered by a finite family
of chains has cardinality at most the number of chains, for any binary relation. -/
theorem card_le_card_of_chainCover {α : Type*} {r : α → α → Prop}
    {A : Finset α} {C : Finset (Finset α)}
    (hA : IsAntichain r (A : Set α))
    (hC : ∀ c ∈ C, IsChain r (c : Set α))
    (hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) :
    A.card ≤ C.card := by
  classical
  let f : α → Finset α := fun a ↦ if ha : a ∈ A then (hcov a ha).choose else ∅
  have hf_mem : ∀ a ∈ A, f a ∈ C ∧ a ∈ f a := fun a ha ↦ by
    simpa only [f, ha, ↓reduceDIte] using (hcov a ha).choose_spec
  refine Finset.card_le_card_of_injOn f (fun a ha ↦ (hf_mem a ha).1) fun a ha b hb hfab ↦ ?_
  have hsub := inter_subsingleton_of_isAntichain_of_isChain hA (hC (f a) (hf_mem a ha).1)
  exact hsub ⟨ha, (hf_mem a ha).2⟩ ⟨hb, hfab ▸ (hf_mem b hb).2⟩

/-- **Tightness of weak duality.** When an antichain covered by a finite family of chains has
cardinality at least the number of chains, every chain in the cover meets the antichain in a
unique element. -/
theorem existsUnique_mem_of_chainCover_of_card_le {α : Type*} {r : α → α → Prop}
    {A : Finset α} {C : Finset (Finset α)}
    (hA : IsAntichain r (A : Set α))
    (hC : ∀ c ∈ C, IsChain r (c : Set α))
    (hcov : ∀ a ∈ A, ∃ c ∈ C, a ∈ c)
    (hcard : C.card ≤ A.card) {c : Finset α} (hc : c ∈ C) :
    ∃! a, a ∈ A ∧ a ∈ c := by
  classical
  let f : α → Finset α := fun a ↦ if ha : a ∈ A then (hcov a ha).choose else ∅
  have hf_mem : ∀ a ∈ A, f a ∈ C ∧ a ∈ f a := fun a ha ↦ by
    simpa only [f, ha, ↓reduceDIte] using (hcov a ha).choose_spec
  have hmaps : Set.MapsTo f (A : Set α) (C : Set (Finset α)) := fun a ha ↦ (hf_mem a ha).1
  have hinj : Set.InjOn f (A : Set α) := fun a ha b hb hfab ↦
    inter_subsingleton_of_isAntichain_of_isChain hA (hC (f a) (hf_mem a ha).1)
      ⟨ha, (hf_mem a ha).2⟩ ⟨hb, hfab ▸ (hf_mem b hb).2⟩
  obtain ⟨a, ha, rfl⟩ := Finset.surjOn_of_injOn_of_card_le f hmaps hinj hcard hc
  refine ⟨a, ⟨ha, (hf_mem a ha).2⟩, fun b hb ↦ ?_⟩
  exact inter_subsingleton_of_isAntichain_of_isChain hA (hC (f a) hc) hb ⟨ha, (hf_mem a ha).2⟩

end IsAntichain

end WeakDuality

section Dilworth

namespace Finset

section PartialOrderHelpers

variable {α : Type*} [PartialOrder α] [DecidableEq α]

/-- Given a tight antichain and chain partition of `s'`, choosing in each chain its greatest element
belonging to some maximum-size antichain yields an antichain `X` of the same cardinality whose
elements dominate all maximum-antichain elements in their respective chains. -/
private theorem exists_top_antichain_of_chainPartition {s' A' : Finset α} {C' : Finset (Finset α)}
    (hA's : A' ⊆ s') (hA' : IsAntichain (· ≤ ·) (A' : Set α))
    (hC' : ∀ c ∈ C', c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α))
    (hC'disj : (C' : Set (Finset α)).Pairwise Disjoint)
    (hC'cov : C'.biUnion id = s') (hcard : A'.card = C'.card) :
    ∃ X : Finset α,
      X ⊆ s' ∧ IsAntichain (· ≤ ·) (X : Set α) ∧ X.card = C'.card ∧
      ∀ x ∈ X, ∃ c ∈ C', x ∈ c ∧
        ∀ y ∈ c, (∃ B : Finset α, B ⊆ s' ∧ IsAntichain (· ≤ ·) (B : Set α) ∧
          B.card = C'.card ∧ y ∈ B) → y ≤ x := by
  classical
  let P (y : α) : Prop :=
    ∃ B : Finset α, B ⊆ s' ∧ IsAntichain (· ≤ ·) (B : Set α) ∧ B.card = C'.card ∧ y ∈ B
  have hcovOf : ∀ B : Finset α, B ⊆ s' → ∀ b ∈ B, ∃ c ∈ C', b ∈ c := fun B hB b hb ↦ by
    simpa [← hC'cov] using hB hb
  have hex : ∀ c ∈ C', ∃ x, IsGreatest ((c.filter P : Finset α) : Set α) x := by
    intro c hc
    obtain ⟨a, ⟨haA', hac⟩, -⟩ :=
      hA'.existsUnique_mem_of_chainCover_of_card_le (fun d hd ↦ (hC' d hd).2)
        (hcovOf A' hA's) hcard.ge hc
    have hne : ((c.filter P : Finset α) : Set α).Nonempty :=
      ⟨a, mem_coe.mpr (mem_filter.mpr ⟨hac, A', hA's, hA', hcard, haA'⟩)⟩
    have hch : IsChain (· ≤ ·) ((c.filter P : Finset α) : Set α) :=
      (hC' c hc).2.mono (coe_subset.mpr (filter_subset P c))
    exact hch.exists_isGreatest (c.filter P).finite_toSet hne
  let f : {c // c ∈ C'} → α := fun c ↦ (hex c.1 c.2).choose
  have hf_great : ∀ c : {c // c ∈ C'}, IsGreatest ((c.1.filter P : Finset α) : Set α) (f c) :=
    fun c ↦ (hex c.1 c.2).choose_spec
  have hf_mem : ∀ c, f c ∈ c.1 := fun c ↦ (mem_filter.mp (hf_great c).1).1
  have hf_P : ∀ c, P (f c) := fun c ↦ (mem_filter.mp (hf_great c).1).2
  have hf_max : ∀ c, ∀ y ∈ c.1, P y → y ≤ f c := fun c y hy hPy ↦
    (hf_great c).2 (mem_coe.mpr (mem_filter.mpr ⟨hy, hPy⟩))
  have hf_inj : Function.Injective f := fun c₁ c₂ heq ↦ Subtype.ext <| by
    by_contra hne
    exact Finset.disjoint_left.mp (hC'disj c₁.2 c₂.2 hne) (hf_mem c₁) (heq ▸ hf_mem c₂)
  refine ⟨C'.attach.image f, ?_, ?_, by rw [card_image_of_injective _ hf_inj, card_attach], ?_⟩
  · intro x hx
    obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    rw [← hC'cov]
    exact mem_biUnion.mpr ⟨c.1, c.2, hf_mem c⟩
  · intro x₁ hx₁ x₂ hx₂ hne hle
    obtain ⟨c₁, -, rfl⟩ := mem_image.mp (mem_coe.mp hx₁)
    obtain ⟨c₂, -, rfl⟩ := mem_image.mp (mem_coe.mp hx₂)
    obtain ⟨B, hBs', hB, hBcard, hf₂B⟩ := hf_P c₂
    obtain ⟨y, ⟨hyB, hyc₁⟩, -⟩ :=
      hB.existsUnique_mem_of_chainCover_of_card_le (fun d hd ↦ (hC' d hd).2)
        (hcovOf B hBs') hBcard.ge c₁.2
    have hy_le : y ≤ f c₁ := hf_max c₁ y hyc₁ ⟨B, hBs', hB, hBcard, hyB⟩
    have hy_eq : y = f c₂ := hB.eq hyB hf₂B (hy_le.trans hle)
    exact hne (le_antisymm hle (hy_eq ▸ hy_le))
  · intro x hx
    obtain ⟨c, -, rfl⟩ := mem_image.mp hx
    exact ⟨c.1, c.2, hf_mem c, hf_max c⟩

/-- In Galvin's induction step, when a maximal element `m` lies above the chosen top element `x₀`,
removing the chain `insert m (c₀.filter (· ≤ x₀))` strictly drops the maximum antichain size. -/
private theorem card_lt_of_subset_sdiff_topChain [DecidableRel ((· ≤ ·) : α → α → Prop)]
    {s : Finset α} {m x₀ : α}
    {C' : Finset (Finset α)} {c₀ : Finset α}
    (hC' : ∀ c ∈ C', c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α))
    (hC'cov : C'.biUnion id = s.erase m)
    (hc₀ : c₀ ∈ C')
    (hx₀_max : ∀ y ∈ c₀,
      (∃ B : Finset α, B ⊆ s.erase m ∧ IsAntichain (· ≤ ·) (B : Set α) ∧
        B.card = C'.card ∧ y ∈ B) → y ≤ x₀)
    {B : Finset α} (hBsub : B ⊆ s \ insert m (c₀.filter (· ≤ x₀)))
    (hB : IsAntichain (· ≤ ·) (B : Set α)) :
    B.card < C'.card := by
  have hBs' : B ⊆ s.erase m := fun x hx ↦ by
    have hmem := hBsub hx
    rw [mem_sdiff, mem_insert, not_or] at hmem
    exact mem_erase.mpr ⟨hmem.2.1, hmem.1⟩
  have hcov : ∀ b ∈ B, ∃ c ∈ C', b ∈ c := fun b hb ↦ by
    simpa [← hC'cov] using hBs' hb
  have hle : B.card ≤ C'.card := hB.card_le_card_of_chainCover (fun c hc ↦ (hC' c hc).2) hcov
  refine lt_of_le_of_ne hle fun hcard ↦ ?_
  obtain ⟨y, ⟨hyB, hyc₀⟩, -⟩ :=
    hB.existsUnique_mem_of_chainCover_of_card_le (fun c hc ↦ (hC' c hc).2) hcov hcard.ge hc₀
  have hyle : y ≤ x₀ := hx₀_max y hyc₀ ⟨B, hBs', hB, hcard, hyB⟩
  exact (mem_sdiff.mp (hBsub hyB)).2 (mem_insert_of_mem (mem_filter.mpr ⟨hyc₀, hyle⟩))

/-- Case 1 of Galvin's induction: when no element of the top antichain `X` lies below `m`,
adjoining `m` to `X` and `{m}` to `C'` increases both cardinalities by one. -/
private theorem galvin_case_incomparable {s X : Finset α} {m : α}
    {C' : Finset (Finset α)}
    (hm : Maximal (· ∈ s) m)
    (hC' : ∀ c ∈ C', c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α))
    (hC'disj : (C' : Set (Finset α)).Pairwise Disjoint)
    (hC'cov : C'.biUnion id = s.erase m)
    (hXs' : X ⊆ s.erase m) (hX : IsAntichain (· ≤ ·) (X : Set α)) (hXcard : X.card = C'.card)
    (hno : ∀ x ∈ X, ¬ x ≤ m) :
    ∃ (A : Finset α) (C : Finset (Finset α)),
      A ⊆ s ∧ IsAntichain (· ≤ ·) (A : Set α) ∧
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ A.card = C.card := by
  have hmX : m ∉ X := fun h ↦ (mem_erase.mp (hXs' h)).1 rfl
  have hmC' : {m} ∉ C' := fun h ↦ by
    have : m ∈ C'.biUnion id := mem_biUnion.mpr ⟨{m}, h, mem_singleton_self m⟩
    rw [hC'cov] at this
    exact (mem_erase.mp this).1 rfl
  refine ⟨insert m X, insert {m} C', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact insert_subset hm.prop (hXs'.trans (erase_subset m s))
  · rw [coe_insert]
    refine hX.insert (fun x hx _ hxm ↦ hno x (mem_coe.mp hx) hxm) (fun x hx hmx hle ↦ ?_)
    exact hmx (le_antisymm hle (hm.le_of_ge (erase_subset m s (hXs' (mem_coe.mp hx))) hle))
  · intro c hc
    rcases mem_insert.mp hc with rfl | hc'
    · exact ⟨singleton_nonempty m, by simp⟩
    · exact hC' c hc'
  · rw [coe_insert, Set.pairwise_insert_of_symm]
    refine ⟨hC'disj, fun c hc _ ↦ Finset.disjoint_singleton_left.mpr fun hmc ↦ ?_⟩
    have : m ∈ C'.biUnion id := mem_biUnion.mpr ⟨c, hc, hmc⟩
    rw [hC'cov] at this
    exact (mem_erase.mp this).1 rfl
  · rw [biUnion_insert, id_eq, hC'cov, singleton_union, insert_erase hm.prop]
  · rw [card_insert_of_notMem hmX, card_insert_of_notMem hmC', hXcard]

/-- Case 2 of Galvin's induction: when some `x₀ ∈ X` satisfies `x₀ ≤ m`, merging
`insert m (c₀.filter (· ≤ x₀))` with a tight chain partition of its complement matches the
cardinality of the top antichain. -/
private theorem galvin_case_comparable [DecidableRel ((· ≤ ·) : α → α → Prop)]
    {s : Finset α} {m : α}
    {C' Cₜ : Finset (Finset α)} {X Aₜ : Finset α} {c₀ : Finset α} {x₀ : α}
    (hms : m ∈ s)
    (hC' : ∀ c ∈ C', c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α))
    (hC'cov : C'.biUnion id = s.erase m)
    (hXs' : X ⊆ s.erase m) (hX : IsAntichain (· ≤ ·) (X : Set α)) (hXcard : X.card = C'.card)
    (hc₀ : c₀ ∈ C') (hle : x₀ ≤ m)
    (hCₜ : ∀ c ∈ Cₜ, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α))
    (hCₜdisj : (Cₜ : Set (Finset α)).Pairwise Disjoint)
    (hCₜcov : Cₜ.biUnion id = s \ insert m (c₀.filter (· ≤ x₀)))
    (hAₜcard : Aₜ.card = Cₜ.card) (hAₜlt : Aₜ.card < C'.card) :
    ∃ (A : Finset α) (C : Finset (Finset α)),
      A ⊆ s ∧ IsAntichain (· ≤ ·) (A : Set α) ∧
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ A.card = C.card := by
  let K : Finset α := insert m (c₀.filter (· ≤ x₀))
  have hKs : K ⊆ s := insert_subset hms fun y hy ↦
    erase_subset m s (hC'cov ▸ mem_biUnion.mpr ⟨c₀, hc₀, (mem_filter.mp hy).1⟩)
  have hKchain : IsChain (· ≤ ·) (K : Set α) := by
    rw [coe_insert]
    exact ((hC' c₀ hc₀).2.mono (coe_subset.mpr (filter_subset _ c₀))).insert fun y hy _ ↦
      Or.inr ((mem_filter.mp (mem_coe.mp hy)).2.trans hle)
  have hKdisj : ∀ c ∈ Cₜ, Disjoint K c := fun c hc ↦
    Finset.disjoint_right.mpr fun y hyc hyK ↦ by
      have : y ∈ Cₜ.biUnion id := mem_biUnion.mpr ⟨c, hc, hyc⟩
      rw [hCₜcov] at this
      exact (mem_sdiff.mp this).2 hyK
  have hKmem : K ∉ Cₜ := fun h ↦
    Finset.disjoint_left.mp (hKdisj K h) (mem_insert_self m _) (mem_insert_self m _)
  have hcov : (insert K Cₜ).biUnion id = s := by
    rw [biUnion_insert, id_eq, hCₜcov, union_sdiff_of_subset hKs]
  have hchains : ∀ c ∈ insert K Cₜ, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α) := by
    intro c hc
    rcases mem_insert.mp hc with rfl | hc'
    · exact ⟨insert_nonempty _ _, hKchain⟩
    · exact hCₜ c hc'
  have hXle : X.card ≤ (insert K Cₜ).card :=
    hX.card_le_card_of_chainCover (fun c hc ↦ (hchains c hc).2) fun x hx ↦ by
      simpa [← hcov] using erase_subset m s (hXs' hx)
  refine ⟨X, insert K Cₜ, hXs'.trans (erase_subset m s), hX, hchains, ?_, hcov, ?_⟩
  · rw [coe_insert, Set.pairwise_insert_of_symm]
    exact ⟨hCₜdisj, fun c hc _ ↦ hKdisj c hc⟩
  · have hle' : (insert K Cₜ).card ≤ X.card := by
      rw [card_insert_of_notMem hKmem, hXcard]
      omega
    exact le_antisymm hXle hle'

/-- Dilworth's theorem for a finite subset of a partial order, proved by Galvin's induction on
cardinality. -/
private theorem exists_isAntichain_chainPartition_partialOrder (s : Finset α) :
    ∃ (A : Finset α) (C : Finset (Finset α)),
      A ⊆ s ∧ IsAntichain (· ≤ ·) (A : Set α) ∧
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ A.card = C.card := by
  classical
  induction hn : s.card using Nat.strong_induction_on generalizing s with
  | _ n ih =>
    rcases s.eq_empty_or_nonempty with rfl | hs
    · exact ⟨∅, ∅, by simp⟩
    · obtain ⟨m, hm⟩ := s.exists_maximal hs
      have hcard_erase : (s.erase m).card < n := hn ▸ card_erase_lt_of_mem hm.prop
      obtain ⟨A', C', hA's, hA', hC', hC'disj, hC'cov, hcard⟩ := ih _ hcard_erase (s.erase m) rfl
      obtain ⟨X, hXs', hX, hXcard, hXmax⟩ :=
        exists_top_antichain_of_chainPartition hA's hA' hC' hC'disj hC'cov hcard
      by_cases hex : ∃ x₀ ∈ X, x₀ ≤ m
      · obtain ⟨x₀, hx₀X, hle⟩ := hex
        obtain ⟨c₀, hc₀, -, hx₀_max⟩ := hXmax x₀ hx₀X
        let K : Finset α := insert m (c₀.filter (· ≤ x₀))
        have ht_lt : (s \ K).card < n := by
          have hsub : s \ K ⊆ s.erase m := fun x hx ↦ by
            rw [mem_sdiff] at hx
            exact mem_erase.mpr ⟨fun hxm ↦ hx.2 (hxm ▸ mem_insert_self m _), hx.1⟩
          exact (card_le_card hsub).trans_lt hcard_erase
        obtain ⟨Aₜ, Cₜ, hAₜt, hAₜ, hCₜ, hCₜdisj, hCₜcov, hAₜcard⟩ := ih _ ht_lt (s \ K) rfl
        have hAₜlt : Aₜ.card < C'.card :=
          card_lt_of_subset_sdiff_topChain hC' hC'cov hc₀ hx₀_max hAₜt hAₜ
        exact galvin_case_comparable hm.prop hC' hC'cov hXs' hX hXcard hc₀ hle hCₜ hCₜdisj
          hCₜcov hAₜcard hAₜlt
      · exact galvin_case_incomparable hm hC' hC'disj hC'cov hXs' hX hXcard fun x hx hle ↦
          hex ⟨x, hx, hle⟩

end PartialOrderHelpers

/-- Private wrapper equipping a transitive relation with its reflexive closure as a `Preorder`. -/
private structure ReflClosure (α : Type*) where
  val : α

private instance {α : Type*} [LE α] [IsTrans α (· ≤ ·)] : Preorder (ReflClosure α) where
  le x y := x.val = y.val ∨ x.val ≤ y.val
  le_refl _ := Or.inl rfl
  le_trans _ _ _ h₁ h₂ := by
    rcases h₁ with h₁ | h₁
    · rwa [h₁]
    · rcases h₂ with h₂ | h₂
      · exact Or.inr (h₂ ▸ h₁)
      · exact Or.inr (_root_.trans h₁ h₂)

/-- Pulling back a chain partition of the antisymmetrization of `ReflClosure α` along the quotient
map yields a chain partition of `s` of the same cardinality. -/
private theorem fiber_chainPartition_reflClosure {α : Type*} [LE α] [IsTrans α (· ≤ ·)]
    [DecidableEq α] [DecidableEq (Antisymmetrization (ReflClosure α) (· ≤ ·))] {s : Finset α}
    {C' : Finset (Finset (Antisymmetrization (ReflClosure α) (· ≤ ·)))}
    (hC' : ∀ c' ∈ C',
      c'.Nonempty ∧ IsChain (· ≤ ·) (c' : Set (Antisymmetrization (ReflClosure α) (· ≤ ·))))
    (hC'disj :
      (C' : Set (Finset (Antisymmetrization (ReflClosure α) (· ≤ ·)))).Pairwise Disjoint)
    (hC'cov : C'.biUnion id = s.image fun a ↦ toAntisymmetrization (· ≤ ·) (ReflClosure.mk a)) :
    ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ C.card = C'.card := by
  classical
  let q : α → Antisymmetrization (ReflClosure α) (· ≤ ·) :=
    fun a ↦ toAntisymmetrization (· ≤ ·) ⟨a⟩
  have hq_le : ∀ a b : α, q a ≤ q b ↔ a = b ∨ a ≤ b := fun _ _ ↦ Iff.rfl
  let fiber : Finset (Antisymmetrization (ReflClosure α) (· ≤ ·)) → Finset α :=
    fun c' ↦ s.filter fun a ↦ q a ∈ c'
  have hfiber_ne : ∀ c' ∈ C', (fiber c').Nonempty := fun c' hc' ↦ by
    obtain ⟨y, hyc'⟩ := (hC' c' hc').1
    obtain ⟨a, has, hqa⟩ := mem_image.mp (hC'cov ▸ mem_biUnion.mpr ⟨c', hc', hyc'⟩)
    refine ⟨a, mem_filter.mpr ⟨has, ?_⟩⟩
    dsimp only [q]
    rwa [hqa]
  have hfiber_inj : Set.InjOn fiber (C' : Set _) := by
    intro c₁ hc₁ c₂ hc₂ heq
    by_contra hne
    obtain ⟨a, ha⟩ := hfiber_ne c₁ hc₁
    have ha₂ : a ∈ fiber c₂ := heq ▸ ha
    exact Finset.disjoint_left.mp (hC'disj hc₁ hc₂ hne)
      (mem_filter.mp ha).2 (mem_filter.mp ha₂).2
  refine ⟨C'.image fiber, ?_, ?_, ?_, Finset.card_image_of_injOn hfiber_inj⟩
  · intro c hc
    obtain ⟨c', hc', rfl⟩ := mem_image.mp hc
    refine ⟨hfiber_ne c' hc', fun a₁ ha₁ a₂ ha₂ hne ↦ ?_⟩
    have h₁ := (mem_filter.mp (mem_coe.mp ha₁)).2
    have h₂ := (mem_filter.mp (mem_coe.mp ha₂)).2
    have htot : q a₁ ≤ q a₂ ∨ q a₂ ≤ q a₁ := by
      rcases eq_or_ne (q a₁) (q a₂) with heq | hqne
      · exact Or.inl heq.le
      · exact (hC' c' hc').2 h₁ h₂ hqne
    rcases htot with h | h
    · exact Or.inl (((hq_le a₁ a₂).mp h).resolve_left hne)
    · exact Or.inr (((hq_le a₂ a₁).mp h).resolve_left hne.symm)
  · intro c₁ hc₁ c₂ hc₂ hne
    obtain ⟨c₁', hc₁', rfl⟩ := mem_image.mp (mem_coe.mp hc₁)
    obtain ⟨c₂', hc₂', rfl⟩ := mem_image.mp (mem_coe.mp hc₂)
    refine Finset.disjoint_left.mpr fun a ha₁ ha₂ ↦ ?_
    exact Finset.disjoint_left.mp (hC'disj hc₁' hc₂' (fun h ↦ hne (congrArg fiber h)))
      (mem_filter.mp ha₁).2 (mem_filter.mp ha₂).2
  · ext a
    simp only [mem_biUnion, id_eq, mem_image, fiber]
    refine ⟨fun ⟨_, ⟨_, _, rfl⟩, ha⟩ ↦ (mem_filter.mp ha).1, fun has ↦ ?_⟩
    have hqa : q a ∈ C'.biUnion id := hC'cov.symm ▸ mem_image_of_mem q has
    obtain ⟨c', hc', hqc'⟩ := mem_biUnion.mp hqa
    exact ⟨fiber c', ⟨c', hc', rfl⟩, mem_filter.mpr ⟨has, hqc'⟩⟩

/-- **Dilworth's theorem for finite subsets of a transitive relation.** Every finite subset `s` of
a type equipped with a transitive relation `≤` (in particular, any preorder or partial order)
admits an antichain `A ⊆ s` and a partition `C` of `s` into nonempty chains with
`A.card = C.card`. -/
theorem exists_isAntichain_chainPartition {α : Type*} [LE α] [IsTrans α (· ≤ ·)] [DecidableEq α]
    (s : Finset α) :
    ∃ (A : Finset α) (C : Finset (Finset α)),
      A ⊆ s ∧ IsAntichain (· ≤ ·) (A : Set α) ∧
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ A.card = C.card := by
  classical
  let q : α → Antisymmetrization (ReflClosure α) (· ≤ ·) :=
    fun a ↦ toAntisymmetrization (· ≤ ·) ⟨a⟩
  have hq_le : ∀ a b : α, q a ≤ q b ↔ a = b ∨ a ≤ b := fun _ _ ↦ Iff.rfl
  obtain ⟨A', C', hA's, hA', hC', hC'disj, hC'cov, hcard⟩ :=
    exists_isAntichain_chainPartition_partialOrder (s.image q)
  obtain ⟨C, hC, hCdisj, hCcov, hCcard⟩ := fiber_chainPartition_reflClosure hC' hC'disj hC'cov
  have hlift : ∀ y ∈ A', ∃ a ∈ s, q a = y := fun y hy ↦ mem_image.mp (hA's hy)
  let pick : {y // y ∈ A'} → α := fun y ↦ (hlift y.1 y.2).choose
  have hpick : ∀ y : {y // y ∈ A'}, pick y ∈ s ∧ q (pick y) = y.1 := fun y ↦
    (hlift y.1 y.2).choose_spec
  have hpick_inj : Function.Injective pick := fun y₁ y₂ heq ↦ Subtype.ext <| by
    rw [← (hpick y₁).2, ← (hpick y₂).2, heq]
  refine ⟨A'.attach.image pick, C, ?_, ?_, hC, hCdisj, hCcov, ?_⟩
  · intro a ha
    obtain ⟨y, -, rfl⟩ := mem_image.mp ha
    exact (hpick y).1
  · intro a₁ ha₁ a₂ ha₂ hne hle
    obtain ⟨y₁, -, rfl⟩ := mem_image.mp (mem_coe.mp ha₁)
    obtain ⟨y₂, -, rfl⟩ := mem_image.mp (mem_coe.mp ha₂)
    have hy_ne : y₁.1 ≠ y₂.1 := fun h ↦ hne (congrArg pick (Subtype.ext h))
    refine hA' y₁.2 y₂.2 hy_ne ?_
    rw [← (hpick y₁).2, ← (hpick y₂).2]
    exact (hq_le (pick y₁) (pick y₂)).mpr (Or.inr hle)
  · rw [card_image_of_injective _ hpick_inj, card_attach, hcard, hCcard]

end Finset

namespace TauCeti

/-- **Dilworth's theorem for finite orders.** Every finite type equipped with a transitive relation
`≤` (in particular, any finite partial order) has an antichain `A` and a partition `C` into
nonempty chains with `A.card = C.card`. -/
theorem finite_dilworth {α : Type*} [LE α] [IsTrans α (· ≤ ·)] [Fintype α] [DecidableEq α] :
    ∃ (A : Finset α) (C : Finset (Finset α)),
      IsAntichain (· ≤ ·) (A : Set α) ∧
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = Finset.univ ∧ A.card = C.card := by
  obtain ⟨A, C, -, hA, hC, hdisj, hcov, hcard⟩ :=
    (Finset.univ : Finset α).exists_isAntichain_chainPartition
  exact ⟨A, C, hA, hC, hdisj, hcov, hcard⟩

end TauCeti

end Dilworth

section AntichainWidth

namespace Finset

variable {α : Type*} [LE α]

open scoped Classical in
/-- The maximum cardinality of an antichain contained in `s`. -/
noncomputable def antichainWidth (s : Finset α) : ℕ :=
  (s.powerset.filter fun A : Finset α ↦ IsAntichain (· ≤ ·) (A : Set α)).sup Finset.card

/-- Every antichain contained in `s` has cardinality at most `s.antichainWidth`. -/
theorem card_le_antichainWidth {s A : Finset α} (hAs : A ⊆ s)
    (hA : IsAntichain (· ≤ ·) (A : Set α)) : A.card ≤ s.antichainWidth := by
  classical
  exact Finset.le_sup (f := Finset.card) (mem_filter.mpr ⟨mem_powerset.mpr hAs, hA⟩)

/-- `s.antichainWidth ≤ n` if and only if every antichain in `s` has cardinality at most `n`. -/
theorem antichainWidth_le_iff {s : Finset α} {n : ℕ} :
    s.antichainWidth ≤ n ↔ ∀ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) → A.card ≤ n := by
  classical
  simp only [antichainWidth, Finset.sup_le_iff, mem_filter, mem_powerset, and_imp]

/-- Some antichain contained in `s` attains `s.antichainWidth`. -/
theorem exists_isAntichain_card_eq_antichainWidth (s : Finset α) :
    ∃ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) ∧ A.card = s.antichainWidth := by
  classical
  have hne : (s.powerset.filter fun A : Finset α ↦ IsAntichain (· ≤ ·) (A : Set α)).Nonempty :=
    ⟨∅, mem_filter.mpr ⟨mem_powerset.mpr (empty_subset s), by simp⟩⟩
  obtain ⟨A, hA, hEq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  exact ⟨A, mem_powerset.mp (mem_filter.mp hA).1, (mem_filter.mp hA).2, hEq.symm⟩

/-- `n ≤ s.antichainWidth` if and only if some antichain in `s` has cardinality at least `n`. -/
theorem le_antichainWidth_iff {s : Finset α} {n : ℕ} :
    n ≤ s.antichainWidth ↔ ∃ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) ∧ n ≤ A.card := by
  refine ⟨fun h ↦ ?_, fun ⟨_, hAs, hA, hn⟩ ↦ hn.trans (card_le_antichainWidth hAs hA)⟩
  obtain ⟨A, hAs, hA, hcard⟩ := s.exists_isAntichain_card_eq_antichainWidth
  exact ⟨A, hAs, hA, hcard.symm ▸ h⟩

@[simp]
theorem antichainWidth_empty : (∅ : Finset α).antichainWidth = 0 := by
  apply Nat.eq_zero_of_le_zero
  rw [antichainWidth_le_iff]
  intro A hA _
  simp [subset_empty.mp hA]

@[simp]
theorem antichainWidth_singleton (a : α) : ({a} : Finset α).antichainWidth = 1 := by
  apply le_antisymm
  · rw [antichainWidth_le_iff]
    intro A hA _
    exact (card_le_card hA).trans (by simp)
  · exact (card_singleton a) ▸ card_le_antichainWidth Subset.rfl (by simp)

/-- The antichain width of `s` is zero if and only if `s` is empty. -/
@[simp]
theorem antichainWidth_eq_zero_iff {s : Finset α} : s.antichainWidth = 0 ↔ s = ∅ := by
  refine ⟨fun h ↦ eq_empty_iff_forall_notMem.mpr fun a ha ↦ ?_, fun h ↦ h ▸ antichainWidth_empty⟩
  have h1 : 1 ≤ s.antichainWidth :=
    (card_singleton a) ▸ card_le_antichainWidth (singleton_subset_iff.mpr ha) (by simp)
  omega

/-- The antichain width of `s` is positive if and only if `s` is nonempty. -/
@[simp]
theorem antichainWidth_pos_iff {s : Finset α} : 0 < s.antichainWidth ↔ s.Nonempty := by
  rw [Nat.pos_iff_ne_zero, ne_eq, antichainWidth_eq_zero_iff, nonempty_iff_ne_empty]

/-- The antichain width of `s` is at most the cardinality of `s`. -/
theorem antichainWidth_le_card (s : Finset α) : s.antichainWidth ≤ s.card :=
  antichainWidth_le_iff.mpr fun _ hAs _ ↦ card_le_card hAs

/-- Antichain width is monotone under set inclusion. -/
theorem antichainWidth_mono {s t : Finset α} (h : s ⊆ t) : s.antichainWidth ≤ t.antichainWidth :=
  antichainWidth_le_iff.mpr fun _ hAs hA ↦ card_le_antichainWidth (hAs.trans h) hA

/-- The antichain width of `s` equals `s.card` if and only if `s` is an antichain. -/
theorem antichainWidth_eq_card_iff {s : Finset α} :
    s.antichainWidth = s.card ↔ IsAntichain (· ≤ ·) (s : Set α) := by
  constructor
  · intro h
    obtain ⟨A, hAs, hA, hAcard⟩ := s.exists_isAntichain_card_eq_antichainWidth
    have heq : A = s := eq_of_subset_of_card_le hAs (by omega)
    exact heq ▸ hA
  · exact fun hs ↦ le_antisymm (antichainWidth_le_card s) (card_le_antichainWidth Subset.rfl hs)

/-- The antichain width of `s` equals one if and only if `s` is a nonempty chain. -/
theorem antichainWidth_eq_one_iff {s : Finset α} :
    s.antichainWidth = 1 ↔ s.Nonempty ∧ IsChain (· ≤ ·) (s : Set α) := by
  constructor
  · intro h
    refine ⟨antichainWidth_pos_iff.mp (by omega), fun a ha b hb hne ↦ ?_⟩
    classical
    by_contra hnot
    push Not at hnot
    have hA : IsAntichain (· ≤ ·) (({a, b} : Finset α) : Set α) := by
      intro x hx y hy hxy
      rcases mem_insert.mp (mem_coe.mp hx) with rfl | hx' <;>
        rcases mem_insert.mp (mem_coe.mp hy) with rfl | hy'
      · exact absurd rfl hxy
      · rw [mem_singleton.mp hy']; exact hnot.1
      · rw [mem_singleton.mp hx']; exact hnot.2
      · rw [mem_singleton.mp hx', mem_singleton.mp hy'] at hxy; exact absurd rfl hxy
    have h2 : 2 ≤ s.antichainWidth := by
      rw [← card_pair hne]
      exact card_le_antichainWidth (insert_subset_iff.mpr ⟨ha, singleton_subset_iff.mpr hb⟩) hA
    omega
  · rintro ⟨hs, hchain⟩
    apply le_antisymm
    · rw [antichainWidth_le_iff]
      intro A hAs hA
      exact card_le_one.mpr fun a ha b hb ↦
        subsingleton_of_isChain_of_isAntichain (hchain.mono (coe_subset.mpr hAs)) hA ha hb
    · exact antichainWidth_pos_iff.mpr hs

/-- Order embeddings preserve antichain width. -/
@[simp]
theorem antichainWidth_map {β : Type*} [LE β] (s : Finset α) (f : α ↪o β) :
    (s.map f.toEmbedding).antichainWidth = s.antichainWidth := by
  classical
  apply le_antisymm
  · rw [antichainWidth_le_iff]
    intro B hBs hB
    let A : Finset α := s.filter fun a ↦ f a ∈ B
    have hAB : A.map f.toEmbedding = B := by
      ext b
      simp only [A, mem_map, mem_filter, RelEmbedding.coe_toEmbedding]
      refine ⟨fun ⟨_, ⟨_, hfa⟩, heq⟩ ↦ heq ▸ hfa, fun hb ↦ ?_⟩
      obtain ⟨a, has, rfl⟩ := mem_map.mp (hBs hb)
      exact ⟨a, ⟨has, hb⟩, rfl⟩
    have hA : IsAntichain (· ≤ ·) (A : Set α) := by
      rw [← IsAntichain.image_embedding_iff (φ := f), ← RelEmbedding.coe_toEmbedding, ← coe_map,
        hAB]
      exact hB
    rw [← hAB, card_map]
    exact card_le_antichainWidth (filter_subset _ s) hA
  · rw [antichainWidth_le_iff]
    intro A hAs hA
    have hAf : IsAntichain (· ≤ ·) ((A.map f.toEmbedding : Finset β) : Set β) := by
      rw [coe_map]
      exact hA.image_embedding f
    simpa using card_le_antichainWidth (map_subset_map.mpr hAs) hAf

/-- Any chain cover of `s` has at least `s.antichainWidth` chains. -/
theorem antichainWidth_le_card_of_chainCover {s : Finset α} {C : Finset (Finset α)}
    (hC : ∀ c ∈ C, IsChain (· ≤ ·) (c : Set α)) (hcov : ∀ x ∈ s, ∃ c ∈ C, x ∈ c) :
    s.antichainWidth ≤ C.card :=
  antichainWidth_le_iff.mpr fun _ hAs hA ↦
    hA.card_le_card_of_chainCover hC fun a ha ↦ hcov a (hAs ha)

/-- Every finite subset of a transitive order admits a partition into `s.antichainWidth` nonempty
chains. -/
theorem exists_chainPartition_card_eq_antichainWidth [IsTrans α (· ≤ ·)] [DecidableEq α]
    (s : Finset α) :
    ∃ C : Finset (Finset α),
      (∀ c ∈ C, c.Nonempty ∧ IsChain (· ≤ ·) (c : Set α)) ∧
      (C : Set (Finset α)).Pairwise Disjoint ∧
      C.biUnion id = s ∧ C.card = s.antichainWidth := by
  obtain ⟨A, C, hAs, hA, hC, hdisj, hcov, hcard⟩ := s.exists_isAntichain_chainPartition
  have hle : s.antichainWidth ≤ C.card :=
    antichainWidth_le_card_of_chainCover (fun c hc ↦ (hC c hc).2) fun x hx ↦ by
      simpa [← hcov] using hx
  have hge : C.card ≤ s.antichainWidth := hcard ▸ card_le_antichainWidth hAs hA
  exact ⟨C, hC, hdisj, hcov, le_antisymm hge hle⟩

end Finset

end AntichainWidth
