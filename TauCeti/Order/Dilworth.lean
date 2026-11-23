/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Partition.Finpartition
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Order.Preorder.Finite
import TauCeti.Order.Chain

/-!
# Dilworth's theorem for finite partial orders

Every finite set `s` in a partial order can be partitioned into as many chains as the largest
size of an antichain contained in `s`. This file proves both halves of this min-max statement.

* Weak duality holds for an arbitrary relation: a chain meets an antichain in at most one point,
  so an antichain covered by finitely many chains has at most as many points as there are chains.
* Dilworth's theorem: some antichain `A ⊆ s` and some finite partition of `s` into chains have the
  same cardinality. By weak duality, `A` is then an antichain of maximum cardinality in `s`, and
  the partition has the fewest parts among all partitions of `s` into chains.

The chain partition is produced as the fibres of a colouring `f : α → ℕ` of `s` by the colours
`0, …, #A - 1` whose fibres in `s` are chains. Such a colouring is built by Galvin's induction on
`#s`, removing a maximal point.

These statements feed comparisons of chain partitions with matchings in the split bipartite graph
of a finite poset, and with weighted chains of integral intervals in multisegments.

## Main results

* `IsAntichain.card_le_card_of_forall_isChain`: weak duality for arbitrary chain covers.
* `IsAntichain.card_le_card_parts`: weak duality for finite partitions into chains.
* `Finset.exists_isAntichain_card_eq_card_parts`: Dilworth's theorem for a finite set in a partial
  order; taking `s = Finset.univ` gives it for a finite partial order.

## References

* R. P. Dilworth, *A decomposition theorem for partially ordered sets*, Ann. of Math. (2) 51
  (1950), 161–166.
* F. Galvin, *A proof of Dilworth's chain decomposition theorem*, Amer. Math. Monthly 101 (1994),
  no. 4, 352–353.
-/

public section

open Finset

variable {α : Type*}

/-! ### Weak duality -/

namespace IsAntichain

/-- **Weak duality.** An antichain covered by a finite family of chains has at most as many points
as there are chains, since each chain meets the antichain in at most one point. -/
theorem card_le_card_of_forall_isChain {r : α → α → Prop} {A : Finset α}
    {C : Finset (Finset α)} (hA : IsAntichain r (A : Set α))
    (hC : ∀ c ∈ C, IsChain r (c : Set α)) (hAC : ∀ a ∈ A, ∃ c ∈ C, a ∈ c) : #A ≤ #C := by
  refine card_le_card_of_forall_subsingleton (· ∈ ·) hAC fun c hc x hx y hy => ?_
  exact inter_subsingleton_of_isChain_of_isAntichain (hC c hc) hA ⟨hx.2, hx.1⟩ ⟨hy.2, hy.1⟩

/-- **Weak duality** for partitions: an antichain contained in `s` has at most as many points as
any finite partition of `s` into chains has parts. -/
theorem card_le_card_parts [DecidableEq α] {r : α → α → Prop} {s A : Finset α}
    (hA : IsAntichain r (A : Set α)) (hAs : A ⊆ s) (P : Finpartition s)
    (hP : ∀ c ∈ P.parts, IsChain r (c : Set α)) : #A ≤ #P.parts :=
  hA.card_le_card_of_forall_isChain hP fun _ ha => P.exists_mem (hAs ha)

end IsAntichain

/-! ### Chain colourings -/

namespace Finset

section ChainColouring

variable [PartialOrder α]

/-- A colouring `f` of `s` by the colours `0, …, k - 1` whose fibres in `s` are chains. -/
private structure IsChainColouring (s : Finset α) (k : ℕ) (f : α → ℕ) : Prop where
  /-- Every point of `s` receives one of the colours `0, …, k - 1`. -/
  lt : ∀ x ∈ s, f x < k
  /-- Two points of `s` of the same colour are comparable. -/
  le_or_le : ∀ x ∈ s, ∀ y ∈ s, f x = f y → x ≤ y ∨ y ≤ x

/-- A chain colouring by `k` colours maps its domain into `range k`. -/
private theorem IsChainColouring.mapsTo {s B : Finset α} {k : ℕ} {f : α → ℕ}
    (hf : IsChainColouring s k f) (hBs : B ⊆ s) : Set.MapsTo f B (range k) :=
  fun x hx => mem_range.2 (hf.lt x (hBs hx))

/-- A chain colouring by `k` colours is also one by any larger number of colours. -/
private theorem IsChainColouring.mono {s : Finset α} {k l : ℕ} {f : α → ℕ}
    (hf : IsChainColouring s k f) (hkl : k ≤ l) : IsChainColouring s l f :=
  ⟨fun x hx => (hf.lt x hx).trans_le hkl, hf.le_or_le⟩

/-- A chain colouring of `t` by `k` colours extends to a chain colouring of `s` by `k + 1` colours,
giving the new colour `k` to the points of `s` outside `t`, provided these are pairwise
comparable. -/
private theorem IsChainColouring.extend [DecidableEq α] {s t : Finset α} {k : ℕ} {g : α → ℕ}
    (hg : IsChainColouring t k g) (hst : ∀ x ∈ s, x ∉ t → ∀ y ∈ s, y ∉ t → x ≤ y ∨ y ≤ x) :
    IsChainColouring s (k + 1) fun x => if x ∈ t then g x else k := by
  refine ⟨fun x _ => ?_, fun x hx y hy hxy => ?_⟩
  · split_ifs with hxt
    · exact (hg.lt x hxt).trans k.lt_succ_self
    · exact k.lt_succ_self
  by_cases hxt : x ∈ t <;> by_cases hyt : y ∈ t <;> simp only [hxt, hyt, ↓reduceIte] at hxy
  · exact hg.le_or_le x hxt y hyt hxy
  · exact absurd hxy (hg.lt x hxt).ne
  · exact absurd hxy.symm (hg.lt y hyt).ne
  · exact hst x hx hxt y hy hyt

/-- A chain colouring is injective on every antichain contained in its domain. -/
private theorem IsChainColouring.injOn {s B : Finset α} {k : ℕ} {f : α → ℕ}
    (hf : IsChainColouring s k f) (hBs : B ⊆ s) (hB : IsAntichain (· ≤ ·) (B : Set α)) :
    Set.InjOn f B := fun x hx y hy hxy =>
  (hf.le_or_le x (hBs hx) y (hBs hy) hxy).elim (hB.eq hx hy) fun h => (hB.eq hy hx h).symm

/-- An antichain inside the domain of a chain colouring by `k` colours has at most `k` points. -/
private theorem IsChainColouring.card_le {s B : Finset α} {k : ℕ} {f : α → ℕ}
    (hf : IsChainColouring s k f) (hBs : B ⊆ s) (hB : IsAntichain (· ≤ ·) (B : Set α)) :
    #B ≤ k := by
  simpa using card_le_card_of_injOn f (hf.mapsTo hBs) (hf.injOn hBs hB)

/-- An antichain of at least `k` points inside the domain of a chain colouring by `k` colours meets
every colour. -/
private theorem IsChainColouring.exists_mem_eq {s B : Finset α} {k : ℕ} {f : α → ℕ}
    (hf : IsChainColouring s k f) (hBs : B ⊆ s) (hB : IsAntichain (· ≤ ·) (B : Set α))
    (hkB : k ≤ #B) {i : ℕ} (hi : i < k) : ∃ b ∈ B, f b = i := by
  obtain ⟨b, hb, hbi⟩ := surjOn_of_injOn_of_card_le f (hf.mapsTo hBs) (hf.injOn hBs hB)
    (by simpa using hkB) (mem_range.2 hi)
  exact ⟨b, hb, hbi⟩

/-- **Galvin's antichain.** Given a chain colouring of `s` by `k` colours and an antichain of `k`
points in `s`, choose in each colour the largest point lying on some antichain of `k` points in `s`.
These points form an antichain of at least `k` points, each lying above every point of its colour
that lies on an antichain of `k` points in `s`. -/
private theorem IsChainColouring.exists_isAntichain_top {s A : Finset α} {f : α → ℕ}
    (hf : IsChainColouring s #A f) (hAs : A ⊆ s) (hA : IsAntichain (· ≤ ·) (A : Set α)) :
    ∃ X ⊆ s, IsAntichain (· ≤ ·) (X : Set α) ∧ #A ≤ #X ∧
      ∀ x ∈ X, ∀ B ⊆ s, IsAntichain (· ≤ ·) (B : Set α) → #B = #A →
        ∀ y ∈ B, f y = f x → y ≤ x := by
  classical
  -- The points of `s` lying on some antichain of `#A` points in `s`.
  let G : Finset α := {y ∈ s | ∃ B ⊆ s, IsAntichain (· ≤ ·) (B : Set α) ∧ #B = #A ∧ y ∈ B}
  -- Each point of `G` lies below a point of `G` of its colour which is largest in its colour.
  have htop : ∀ y ∈ G, ∃ x ∈ G, f x = f y ∧ y ≤ x ∧ ∀ z ∈ G, f z = f x → z ≤ x := by
    intro y hy
    have hchain : IsChain (· ≤ ·) (({z ∈ G | f z = f y} : Finset α) : Set α) := by
      intro z hz w hw _
      simp only [coe_filter, Set.mem_ofPred_eq] at hz hw
      exact hf.le_or_le z (mem_filter.1 hz.1).1 w (mem_filter.1 hw.1).1 (hz.2.trans hw.2.symm)
    obtain ⟨x, hx, hxg⟩ := hchain.exists_isGreatest (finite_toSet _) ⟨y, by simpa using hy⟩
    simp only [coe_filter, Set.mem_ofPred_eq] at hx
    exact ⟨x, hx.1, hx.2, hxg (by simpa using hy), fun z hz hzx =>
      hxg (by simpa using ⟨hz, hzx.trans hx.2⟩)⟩
  refine ⟨{x ∈ G | ∀ z ∈ G, f z = f x → z ≤ x}, fun x hx => (mem_filter.1 (mem_filter.1 hx).1).1,
    ?_, ?_, ?_⟩
  · intro x hx z hz hxz hle
    simp only [coe_filter, Set.mem_ofPred_eq] at hx hz
    by_cases hc : f x = f z
    · exact hxz (le_antisymm hle (hx.2 z hz.1 hc.symm))
    -- Otherwise an antichain of `#A` points through `z` has a point `y ≤ x` of the colour of `x`.
    obtain ⟨-, B, hBs, hB, hBA, hzB⟩ := mem_filter.1 hz.1
    obtain ⟨y, hyB, hy⟩ := hf.exists_mem_eq hBs hB hBA.ge
      (hf.lt x (mem_filter.1 hx.1).1)
    have hyx : y ≤ x := hx.2 y (mem_filter.2 ⟨hBs hyB, B, hBs, hB, hBA, hyB⟩) hy
    have hyz : y ≠ z := fun h => hc (h ▸ hy.symm)
    exact hB hyB hzB hyz (hyx.trans hle)
  · have hsub : range #A ⊆ image f {x ∈ G | ∀ z ∈ G, f z = f x → z ≤ x} := fun i hi => by
      obtain ⟨b, hbA, rfl⟩ := hf.exists_mem_eq hAs hA le_rfl (mem_range.1 hi)
      obtain ⟨x, hx, hfx, -, hxtop⟩ := htop b (mem_filter.2 ⟨hAs hbA, A, hAs, hA, rfl, hbA⟩)
      exact mem_image.2 ⟨x, mem_filter.2 ⟨hx, hxtop⟩, hfx⟩
    simpa using (card_le_card hsub).trans card_image_le
  · intro x hx B hBs hB hBA y hyB hy
    exact (mem_filter.1 hx).2 y (mem_filter.2 ⟨hBs hyB, B, hBs, hB, hBA, hyB⟩) hy

/-- A finite set together with an antichain inside it and a chain colouring by as many colours as
the antichain has points. -/
private abbrev HasDilworthColouring (s : Finset α) : Prop :=
  ∃ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) ∧ ∃ f, IsChainColouring s #A f

/-- Galvin's first case: if no point of the top antichain `X` of `s.erase a` lies below the
maximal point `a`, then `a` extends `X` to a larger antichain, and `a` receives a new colour. -/
private theorem hasDilworthColouring_of_forall_not_le [DecidableEq α] {s X : Finset α} {a : α}
    {k : ℕ} {f : α → ℕ} (ha : Maximal (· ∈ s) a) (hf : IsChainColouring (s.erase a) k f)
    (hXs : X ⊆ s.erase a) (hX : IsAntichain (· ≤ ·) (X : Set α)) (hkX : k ≤ #X)
    (hXa : ∀ x ∈ X, ¬x ≤ a) : HasDilworthColouring s := by
  have haX : a ∉ X := fun h => (mem_erase.1 (hXs h)).1 rfl
  -- The only point of `s` outside `s.erase a` is `a`.
  have hout : ∀ x ∈ s, x ∉ s.erase a → x = a := fun x hx hxa =>
    not_not.1 fun h => hxa (mem_erase.2 ⟨h, hx⟩)
  refine ⟨insert a X, insert_subset ha.1 fun x hx => mem_of_mem_erase (hXs hx), ?_, _,
    (hf.extend fun x hx hxa y hy hya => Or.inl (hout x hx hxa ▸ hout y hy hya ▸ le_rfl)).mono ?_⟩
  · rw [coe_insert]
    exact hX.insert (fun b hb _ => hXa b hb) fun b hb _ h =>
      hXa b hb (ha.le_of_ge (mem_of_mem_erase (hXs hb)) h)
  · rw [card_insert_of_notMem haX]
    exact Nat.succ_le_succ hkX

/-- Galvin's second case: if a point `x₀` of the top antichain of `s.erase a` lies below the
maximal point `a`, then removing `a` and the points of the colour of `x₀` below `x₀` leaves a set
`t` whose antichains have fewer than `#A` points. A colouring of `t` with fewer colours, together
with one new colour for the removed chain, colours `s`. -/
private theorem hasDilworthColouring_of_le [DecidableEq α] {s A : Finset α} {a x₀ : α}
    {f : α → ℕ} (ha : a ∈ s) (hAs : A ⊆ s.erase a) (hA : IsAntichain (· ≤ ·) (A : Set α))
    (hf : IsChainColouring (s.erase a) #A f) (hx₀ : x₀ ∈ s.erase a) (hx₀a : x₀ ≤ a)
    (hx₀top : ∀ B ⊆ s.erase a, IsAntichain (· ≤ ·) (B : Set α) → #B = #A →
      ∀ y ∈ B, f y = f x₀ → y ≤ x₀)
    (ih : ∀ t ⊂ s, HasDilworthColouring t) : HasDilworthColouring s := by
  classical
  set t := {y ∈ s.erase a | ¬(f y = f x₀ ∧ y ≤ x₀)}
  obtain ⟨C, hCt, hC, g, hg⟩ :=
    ih t ((filter_subset _ _).trans_ssubset (erase_ssubset ha))
  have hCs : C ⊆ s.erase a := hCt.trans (filter_subset _ _)
  -- An antichain of `#A` points in `t` would contain a point of the colour of `x₀` below `x₀`.
  have hCA : #C < #A := by
    refine (hf.card_le hCs hC).lt_of_ne fun hCA => ?_
    obtain ⟨y, hyC, hy⟩ := hf.exists_mem_eq hCs hC hCA.ge (hf.lt x₀ hx₀)
    exact (mem_filter.1 (hCt hyC)).2 ⟨hy, hx₀top C hCs hC hCA y hyC hy⟩
  -- Outside `t`, a point of `s` is `a` or a point of the colour of `x₀` below `x₀ ≤ a`.
  have hout : ∀ y ∈ s, y ∉ t → y = a ∨ (y ∈ s.erase a ∧ f y = f x₀ ∧ y ≤ x₀) := by
    intro y hy hyt
    by_cases hya : y = a
    · exact Or.inl hya
    · have hy' : y ∈ s.erase a := mem_erase.2 ⟨hya, hy⟩
      exact Or.inr ⟨hy', not_not.1 fun h => hyt (mem_filter.2 ⟨hy', h⟩)⟩
  refine ⟨A, hAs.trans (erase_subset _ _), hA, _, (hg.extend fun y hy hyt z hz hzt => ?_).mono hCA⟩
  rcases hout y hy hyt with rfl | ⟨hy', hfy, hyx₀⟩ <;>
    rcases hout z hz hzt with rfl | ⟨hz', hfz, hzx₀⟩
  · exact Or.inl le_rfl
  · exact Or.inr (hzx₀.trans hx₀a)
  · exact Or.inl (hyx₀.trans hx₀a)
  · exact hf.le_or_le y hy' z hz' (hfy.trans hfz.symm)

/-- Every finite set in a partial order carries an antichain and a chain colouring by as many
colours as the antichain has points. -/
private theorem hasDilworthColouring (s : Finset α) : HasDilworthColouring s := by
  classical
  induction s using Finset.strongInduction with
  | H s ih =>
  rcases s.eq_empty_or_nonempty with rfl | hs
  · exact ⟨∅, empty_subset _, by simp, fun _ => 0, ⟨by simp, by simp⟩⟩
  obtain ⟨a, ha⟩ := s.exists_maximal hs
  obtain ⟨A, hAs, hA, f, hf⟩ := ih _ (erase_ssubset ha.1)
  obtain ⟨X, hXs, hX, hAX, hXtop⟩ := hf.exists_isAntichain_top hAs hA
  by_cases hXa : ∃ x₀ ∈ X, x₀ ≤ a
  · obtain ⟨x₀, hx₀X, hx₀a⟩ := hXa
    exact hasDilworthColouring_of_le ha.1 hAs hA hf (hXs hx₀X) hx₀a (hXtop x₀ hx₀X) ih
  · push Not at hXa
    exact hasDilworthColouring_of_forall_not_le ha hf hXs hX hAX hXa

end ChainColouring

/-! ### Dilworth's theorem -/

/-- **Dilworth's theorem.** A finite set `s` in a partial order contains an antichain `A` and has
a finite partition into chains with exactly `#A` parts. -/
theorem exists_isAntichain_card_eq_card_parts [PartialOrder α] [DecidableEq α] (s : Finset α) :
    ∃ A ⊆ s, IsAntichain (· ≤ ·) (A : Set α) ∧ ∃ P : Finpartition s,
      (∀ c ∈ P.parts, IsChain (· ≤ ·) (c : Set α)) ∧ #A = #P.parts := by
  classical
  obtain ⟨A, hAs, hA, f, hf⟩ := hasDilworthColouring s
  let P := Finpartition.ofSetSetoid (Setoid.ker f) s
  have hparts : P.parts = (s.image f).image fun i => {y ∈ s | i = f y} := by
    simp only [P, Finpartition.ofSetSetoid_parts, image_image, Setoid.ker_def, Function.comp_def]
  have hP : ∀ c ∈ P.parts, IsChain (· ≤ ·) (c : Set α) := by
    intro c hc x hx y hy _
    rw [hparts] at hc
    obtain ⟨i, -, rfl⟩ := mem_image.1 hc
    simp only [coe_filter, Set.mem_ofPred_eq] at hx hy
    exact hf.le_or_le x hx.1 y hy.1 (hx.2.symm.trans hy.2)
  refine ⟨A, hAs, hA, P, hP, (hA.card_le_card_parts hAs P hP).antisymm ?_⟩
  rw [hparts]
  exact card_image_le.trans ((card_le_card (hf.mapsTo subset_rfl).finsetImage_subset).trans
    (card_range #A).le)

end Finset
