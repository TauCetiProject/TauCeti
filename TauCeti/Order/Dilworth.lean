/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Order.Antichain
public import Mathlib.Order.Partition.Finpartition
public import Mathlib.Data.Finset.Prod
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Logic.Relation
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

Fulkerson's form of Dilworth's theorem replaces chain partitions by matchings in the split
bipartite graph of a strict order `r` on `s`: a set `E` of pairs `(x, y)` with `r x y`, using each
point of `s` at most once as a first coordinate and at most once as a second coordinate. Following
the edges of `E` from a point gives a path, and the paths are chains; conversely, consecutive points
of the chains of a partition form a matching. Hence the largest antichain and the largest matching
have sizes adding up to `#s`.

## Main definitions

* `TauCeti.IsSplitMatching r s E`: `E` is a matching in the split bipartite graph of the relation
  `r` on `s`.

## Main results

* `IsAntichain.card_le_card_of_forall_isChain`: weak duality for arbitrary chain covers.
* `IsAntichain.card_le_card_parts`: weak duality for finite partitions into chains.
* `Finset.exists_isAntichain_card_eq_card_parts`: Dilworth's theorem for a finite set in a partial
  order; taking `s = Finset.univ` gives it for a finite partial order.
* `TauCeti.IsSplitMatching.card_add_card_le_card`: an antichain and a split-graph matching of a
  strict order on `s` have at most `#s` elements and edges together.
* `TauCeti.exists_isAntichain_isSplitMatching_card_add_card_eq`: some antichain and some
  split-graph matching have exactly `#s` elements and edges together.

## References

* R. P. Dilworth, *A decomposition theorem for partially ordered sets*, Ann. of Math. (2) 51
  (1950), 161–166.
* F. Galvin, *A proof of Dilworth's chain decomposition theorem*, Amer. Math. Monthly 101 (1994),
  no. 4, 352–353.
* D. R. Fulkerson, *Note on Dilworth's decomposition theorem for partially ordered sets*, Proc.
  Amer. Math. Soc. 7 (1956), 701–702.
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

/-! ### Matchings in the split graph -/

namespace TauCeti

open Finset

/-- `E` is a matching in the split bipartite graph of the relation `r` on `s`: its edges are pairs
`(x, y)` of points of `s` with `r x y`, and no two edges share a first coordinate or share a second
coordinate. A point may occur once as a first coordinate and once as a second coordinate. Thus `E`
is the edge set of a matching of the bipartite graph between two copies of `s` joining `x` in the
first copy to `y` in the second when `r x y`, recorded directly by its oriented edges. -/
structure IsSplitMatching (r : α → α → Prop) (s : Finset α) (E : Finset (α × α)) : Prop where
  /-- Both coordinates of every edge lie in `s`. -/
  subset : E ⊆ s ×ˢ s
  /-- Every edge `(x, y)` satisfies `r x y`. -/
  rel : ∀ e ∈ E, r e.1 e.2
  /-- No two edges share a first coordinate. -/
  injOn_fst : Set.InjOn Prod.fst (E : Set (α × α))
  /-- No two edges share a second coordinate. -/
  injOn_snd : Set.InjOn Prod.snd (E : Set (α × α))

namespace IsSplitMatching

variable {r : α → α → Prop} {s A : Finset α} {E : Finset (α × α)}

/-- The empty set is a split-graph matching. -/
@[simp]
theorem empty (r : α → α → Prop) (s : Finset α) : IsSplitMatching r s ∅ :=
  ⟨empty_subset _, by simp, by simp, by simp⟩

/-- The first coordinates of the edges of a split-graph matching on `s` lie in `s`. -/
theorem image_fst_subset [DecidableEq α] (hE : IsSplitMatching r s E) : E.image Prod.fst ⊆ s :=
  fun x hx => by
    obtain ⟨e, he, rfl⟩ := mem_image.1 hx
    exact (mem_product.1 (hE.subset he)).1

/-- A split-graph matching on `s` has at most `#s` edges. -/
theorem card_le_card (hE : IsSplitMatching r s E) : #E ≤ #s := by
  classical
  exact card_image_of_injOn hE.injOn_fst ▸ Finset.card_le_card hE.image_fst_subset

/-- Mapping a split-graph matching along an embedding `f` which sends related points to related
points gives a split-graph matching on any finite set containing the image of `s`. -/
theorem map {β : Type*} {r' : β → β → Prop} {t : Finset β} (hE : IsSplitMatching r s E)
    (f : α ↪ β) (hf : ∀ ⦃x y⦄, r x y → r' (f x) (f y)) (hst : s.map f ⊆ t) :
    IsSplitMatching r' t (E.map (f.prodMap f)) := by
  refine ⟨fun e he => ?_, fun e he => ?_, ?_, ?_⟩
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_map.1 he
    obtain ⟨hx, hy⟩ := mem_product.1 (hE.subset hxy)
    exact mem_product.2 ⟨hst (mem_map_of_mem f hx), hst (mem_map_of_mem f hy)⟩
  · obtain ⟨⟨x, y⟩, hxy, rfl⟩ := mem_map.1 he
    exact hf (hE.rel _ hxy)
  · rintro _ he _ he' h
    obtain ⟨e, hmem, rfl⟩ := mem_map.1 he
    obtain ⟨e', hmem', rfl⟩ := mem_map.1 he'
    exact congrArg _ (hE.injOn_fst hmem hmem' (f.injective h))
  · rintro _ he _ he' h
    obtain ⟨e, hmem, rfl⟩ := mem_map.1 he
    obtain ⟨e', hmem', rfl⟩ := mem_map.1 he'
    exact congrArg _ (hE.injOn_snd hmem hmem' (f.injective h))

/-- Following the edges of a split-graph matching of a transitive relation only moves up along
the relation. -/
private theorem eq_or_rel_of_reflTransGen [IsTrans α r] (hE : IsSplitMatching r s E) {x y : α}
    (h : Relation.ReflTransGen (fun x y => (x, y) ∈ E) x y) : x = y ∨ r x y := by
  induction h with
  | refl => exact Or.inl rfl
  | tail _ hyz ih =>
    exact Or.inr (ih.elim (fun h => h ▸ hE.rel _ hyz) fun h => _root_.trans h (hE.rel _ hyz))

/-- From every point of `s`, following the edges of a split-graph matching of a strict order ends
at a point of `s` which is not the first coordinate of any edge. -/
private theorem exists_reflTransGen_forall_notMem [IsStrictOrder α r] (hE : IsSplitMatching r s E)
    {x : α} (hx : x ∈ s) : ∃ z ∈ s, (∀ y, (z, y) ∉ E) ∧
      Relation.ReflTransGen (fun x y => (x, y) ∈ E) x z := by
  classical
  let := partialOrderOfSO r
  obtain ⟨z, hz⟩ := (s.filter (Relation.ReflTransGen (fun x y => (x, y) ∈ E) x)).exists_maximal
    ⟨x, mem_filter.2 ⟨hx, .refl⟩⟩
  obtain ⟨hzs, hxz⟩ := mem_filter.1 hz.prop
  refine ⟨z, hzs, fun y hzy => ?_, hxz⟩
  exact hz.not_gt (y := y) (mem_filter.2 ⟨(mem_product.1 (hE.subset hzy)).2, hxz.tail hzy⟩)
    (hE.rel _ hzy)

/-- **Weak duality for matchings.** An antichain in `s` and a matching in the split bipartite
graph of a strict order on `s` have at most `#s` points and edges together. -/
theorem card_add_card_le_card [IsStrictOrder α r] (hE : IsSplitMatching r s E)
    (hA : IsAntichain r (A : Set α)) (hAs : A ⊆ s) : #A + #E ≤ #s := by
  classical
  let R : α → α → Prop := fun x y => (x, y) ∈ E
  have hcard : #A ≤ #(s \ E.image Prod.fst) := by
    refine card_le_card_of_forall_subsingleton (Relation.ReflTransGen R) (fun x hx => ?_)
      fun z _ x hx y hy => ?_
    · obtain ⟨z, hz, hzE, hxz⟩ := hE.exists_reflTransGen_forall_notMem (hAs hx)
      exact ⟨z, mem_sdiff.2 ⟨hz, by simpa using hzE⟩, hxz⟩
    · -- Two points of `A` reaching `z` lie on the same path ending at `z`, so they are comparable.
      have hU : Relator.RightUnique (Function.swap R) := fun _ _ _ h₁ h₂ =>
        congrArg Prod.fst (hE.injOn_snd h₁ h₂ rfl)
      obtain ⟨hx, hxz⟩ := hx
      obtain ⟨hy, hyz⟩ := hy
      rcases hxz.swap.total_of_right_unique hU hyz.swap with h | h
      · exact (hE.eq_or_rel_of_reflTransGen h.swap).elim Eq.symm fun h => (hA.eq hy hx h).symm
      · exact (hE.eq_or_rel_of_reflTransGen h.swap).elim id fun h => hA.eq hx hy h
  rw [card_sdiff_of_subset hE.image_fst_subset, card_image_of_injOn hE.injOn_fst] at hcard
  have := hE.card_le_card
  omega

end IsSplitMatching

end TauCeti

/-! ### Matchings from chain partitions -/

namespace Finpartition

open Finset TauCeti

variable {r : α → α → Prop} [DecidableEq α] {s : Finset α}

/-- Two distinct points of a part of a partition into chains are related one way or the other. -/
private theorem rel_or_rel_of_mem_part {P : Finpartition s}
    (hP : ∀ c ∈ P.parts, IsChain r (c : Set α)) {x y z : α} (hx : x ∈ s) (hy : y ∈ P.part x)
    (hz : z ∈ P.part x) : y = z ∨ r y z ∨ r z y := by
  by_cases hyz : y = z
  · exact Or.inl hyz
  · exact Or.inr (hP _ (P.part_mem.2 hx) hy hz hyz)

section DecidableRel

variable [DecidableRel r]

/-- The edges joining each point of a part of `P` to its successor in that part for `r`. -/
private def succEdges (r : α → α → Prop) [DecidableRel r] (P : Finpartition s) :
    Finset (α × α) :=
  (s ×ˢ s).filter fun e => r e.1 e.2 ∧ e.2 ∈ P.part e.1 ∧ ∀ z ∈ P.part e.1, ¬(r e.1 z ∧ r z e.2)

private theorem mem_succEdges {P : Finpartition s} {x y : α} :
    (x, y) ∈ succEdges r P ↔ x ∈ s ∧ y ∈ s ∧ r x y ∧ y ∈ P.part x ∧
      ∀ z ∈ P.part x, ¬(r x z ∧ r z y) := by
  simp [succEdges, and_assoc]

/-- Successor edges in a partition into chains form a split-graph matching. -/
private theorem isSplitMatching_succEdges {P : Finpartition s}
    (hP : ∀ c ∈ P.parts, IsChain r (c : Set α)) : IsSplitMatching r s (succEdges r P) := by
  refine ⟨filter_subset _ _, fun e he => (mem_filter.1 he).2.1, ?_, ?_⟩
  · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' (rfl : x = x')
    obtain ⟨hx, -, hr, hy, hmin⟩ := mem_succEdges.1 hxy
    obtain ⟨-, -, hr', hy', hmin'⟩ := mem_succEdges.1 hxy'
    rcases rel_or_rel_of_mem_part hP hx hy hy' with h | h | h
    · rw [h]
    · exact (hmin' y hy ⟨hr, h⟩).elim
    · exact (hmin y' hy' ⟨hr', h⟩).elim
  · rintro ⟨x, y⟩ hxy ⟨x', y'⟩ hxy' (rfl : y = y')
    obtain ⟨hx, -, hr, hy, hmin⟩ := mem_succEdges.1 hxy
    obtain ⟨hx', -, hr', hy', hmin'⟩ := mem_succEdges.1 hxy'
    have hpart : P.part x' = P.part x :=
      (P.part_eq_of_mem (P.part_mem.2 hx') hy').symm.trans (P.part_eq_of_mem (P.part_mem.2 hx) hy)
    have hx'x : x' ∈ P.part x := hpart ▸ P.mem_part hx'
    rcases rel_or_rel_of_mem_part hP hx (P.mem_part hx) hx'x with h | h | h
    · rw [h]
    · exact (hmin x' hx'x ⟨h, hr'⟩).elim
    · exact (hmin' x (hpart ▸ P.mem_part hx) ⟨h, hr⟩).elim

/-- A point is the first coordinate of a successor edge exactly when it is not the greatest point
of its part. -/
private theorem image_fst_succEdges [IsStrictOrder α r] (P : Finpartition s) :
    (succEdges r P).image Prod.fst = s.filter fun x => ∃ y ∈ P.part x, r x y := by
  let := partialOrderOfSO r
  ext x
  simp only [mem_image, mem_filter]
  constructor
  · rintro ⟨⟨x, y⟩, hxy, rfl⟩
    obtain ⟨hx, -, hr, hy, -⟩ := mem_succEdges.1 hxy
    exact ⟨hx, y, hy, hr⟩
  · rintro ⟨hx, y₀, hy₀, hr₀⟩
    obtain ⟨y, hy⟩ := ((P.part x).filter (r x)).exists_minimal ⟨y₀, mem_filter.2 ⟨hy₀, hr₀⟩⟩
    obtain ⟨hyx, hry⟩ := mem_filter.1 hy.prop
    refine ⟨(x, y), mem_succEdges.2 ⟨hx, P.part_subset x hyx, hry, hyx, fun z hz hxzy => ?_⟩, rfl⟩
    exact hy.not_lt (y := z) (mem_filter.2 ⟨hz, hxzy.1⟩) hxzy.2

/-- In a partition into chains, the greatest points of the parts are as many as the parts. -/
private theorem card_filter_forall_not_rel [IsStrictOrder α r] {P : Finpartition s}
    (hP : ∀ c ∈ P.parts, IsChain r (c : Set α)) :
    #(s.filter fun x => ∀ y ∈ P.part x, ¬r x y) = #P.parts := by
  let := partialOrderOfSO r
  refine card_nbij P.part (fun x hx => P.part_mem.2 (mem_filter.1 hx).1) ?_ ?_
  · intro x hx y hy hxy
    obtain ⟨hx, hxmax⟩ := mem_filter.1 hx
    obtain ⟨hy, hymax⟩ := mem_filter.1 hy
    have hyx : y ∈ P.part x := hxy ▸ P.mem_part hy
    rcases rel_or_rel_of_mem_part hP hx (P.mem_part hx) hyx with h | h | h
    · exact h
    · exact (hxmax y hyx h).elim
    · exact (hymax x (hxy.symm ▸ P.mem_part hx) h).elim
  · intro c hc
    obtain ⟨g, hg⟩ := c.exists_maximal (P.nonempty_of_mem_parts hc)
    have hgc : P.part g = c := P.part_eq_of_mem hc hg.prop
    exact ⟨g, mem_filter.2 ⟨P.le hc hg.prop, fun y hy hgy => hg.not_gt (y := y) (hgc ▸ hy) hgy⟩,
      hgc⟩

end DecidableRel

/-- Joining each point of a part of a partition `P` of `s` into chains of a strict order `r` to its
successor in that part gives a matching of the split bipartite graph of `r` on `s` with
`#s - #P.parts` edges. -/
theorem exists_isSplitMatching_card_add_card_parts_eq [IsStrictOrder α r] (P : Finpartition s)
    (hP : ∀ c ∈ P.parts, IsChain r (c : Set α)) :
    ∃ E, IsSplitMatching r s E ∧ #E + #P.parts = #s := by
  classical
  refine ⟨succEdges r P, isSplitMatching_succEdges hP, ?_⟩
  rw [← card_image_of_injOn (isSplitMatching_succEdges hP).injOn_fst, image_fst_succEdges,
    ← card_filter_forall_not_rel hP, ← card_filter_add_card_filter_not (s := s)
      fun x => ∃ y ∈ P.part x, r x y]
  simp only [not_exists, not_and]

end Finpartition

namespace TauCeti

open Finset

/-- **Fulkerson's form of Dilworth's theorem.** For a strict order `r`, a finite set `s` contains an
antichain `A` and carries a matching `E` of the split bipartite graph of `r` on `s` with
`#A + #E = #s`. By `TauCeti.IsSplitMatching.card_add_card_le_card`, `A` is then a largest
antichain and `E` a largest matching. -/
theorem exists_isAntichain_isSplitMatching_card_add_card_eq (r : α → α → Prop)
    [IsStrictOrder α r] (s : Finset α) :
    ∃ A ⊆ s, IsAntichain r (A : Set α) ∧ ∃ E, IsSplitMatching r s E ∧ #A + #E = #s := by
  classical
  let := partialOrderOfSO r
  obtain ⟨A, hAs, hA, P, hP, hAP⟩ := s.exists_isAntichain_card_eq_card_parts
  obtain ⟨E, hE, hEP⟩ := P.exists_isSplitMatching_card_add_card_parts_eq (r := r)
    fun c hc x hx y hy hxy =>
      (hP c hc hx hy hxy).imp (·.resolve_left hxy) (·.resolve_left (Ne.symm hxy))
  exact ⟨A, hAs, fun x hx y hy hxy h => hA hx hy hxy (Or.inr h), E, hE, by omega⟩

end TauCeti
