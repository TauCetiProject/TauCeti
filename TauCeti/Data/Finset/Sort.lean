/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.List.Rotate
public import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.List.Chain

/-!
# Sorting finsets

Sorting the finset `{a, b}` of two distinct elements with `r a b` gives the list `[a, b]`, and
sorting `s.erase a` gives the sorted list of `s` with `a` erased.

For a map `f` that is monotone on a finset `s` of a linear order, the points of `s` sorted in
increasing order are the concatenation, over the values `y` of `f` on `s` in increasing order, of
the sorted fibres `{x ∈ s | f x = y}`. Consequently the ordered product of a word along `s` is the
ordered product, over the values of `f` on `s`, of the ordered products along the fibres.

Consecutive entries of the sorted list of `s` are the pairs of positions of `s` with no position of
`s` strictly between them, so a chain condition on the sorted list is a condition on such adjacent
pairs.

Moving the points of a finset `B` of `Fin n` along the rotation `finRotate n` (`i ↦ i + 1`, the
last position going to `0`) commutes with sorting up to a cyclic rotation of the list.
-/

public section

namespace Finset

variable {α : Type*} (r : α → α → Prop) [DecidableRel r] [IsTrans α r] [Std.Antisymm r]
  [Std.Total r] [DecidableEq α]

/-- Sorting a two-element finset `{a, b}` with `r a b` lists `a` before `b`. -/
theorem sort_pair {a b : α} (hab : r a b) (hne : a ≠ b) : sort {a, b} r = [a, b] := by
  rw [sort_insert r (fun c hc => mem_singleton.1 hc ▸ hab) (notMem_singleton.2 hne),
    sort_singleton]

/-- Sorting `s.erase a` erases `a` from the sorted list of `s`. -/
theorem sort_erase (s : Finset α) (a : α) : sort (s.erase a) r = (sort s r).erase a :=
  List.Perm.eq_of_pairwise' (pairwise_sort _ r) ((pairwise_sort s r).erase a) <|
    Multiset.coe_eq_coe.1 <| by rw [sort_eq, erase_val, ← Multiset.coe_erase, sort_eq]

section LinearOrder

variable {α β : Type*} [LinearOrder α] [LinearOrder β] {s : Finset α} {f : α → β}

/-- Collapsing `j` onto its predecessor `i` in `s` is monotone on `s`, identifies only
`i` and `j`, and strictly decreases the cardinality of the image of `s`. -/
theorem collapse_adjacent_spec {i j : α} (hi : i ∈ s) (hj : j ∈ s) (hij : i < j)
    (hadj : ∀ z ∈ s, z ≤ i ∨ j ≤ z) :
    MonotoneOn (fun z => if z = j then i else z) s ∧
      (∀ {u v}, (if u = j then i else u) = (if v = j then i else v) → u ≠ v →
        (u = i ∨ u = j) ∧ (v = i ∨ v = j)) ∧
      #(s.image fun z => if z = j then i else z) < #s :=
  ⟨fun z hz w _ hzw => by grind [hadj z hz], fun huv hne => by grind,
    card_image_le.lt_of_ne fun h => hij.ne (card_image_iff.1 h hi hj (by simp))⟩

/-- For a map `f` that is monotone on `s`, listing the values of `f` on `s` in increasing order and
replacing each value `y` by the increasing list of the points of `s` over `y` lists `s` in
increasing order. -/
theorem flatten_map_sort_filter_eq_sort (hf : MonotoneOn f s) :
    ((s.image f).sort.map fun y => {x ∈ s | f x = y}.sort).flatten = s.sort := by
  refine List.SortedLT.eq_of_mem_iff ?_ (sortedLT_sort s) fun x => ?_
  · rw [List.sortedLT_iff_pairwise, List.pairwise_flatten, List.pairwise_map]
    refine ⟨fun l hl => ?_, (sortedLT_sort _).pairwise.imp fun {y z} hyz x hx w hw => ?_⟩
    · obtain ⟨y, -, rfl⟩ := List.mem_map.1 hl
      exact (sortedLT_sort _).pairwise
    · rw [mem_sort, mem_filter] at hx hw
      exact hf.reflect_lt hx.1 hw.1 (hx.2 ▸ hw.2 ▸ hyz)
  · rw [mem_sort, List.mem_flatten]
    simp only [List.mem_map]
    constructor
    · rintro ⟨_, ⟨y, -, rfl⟩, hx⟩
      exact (mem_filter.1 ((mem_sort _).1 hx)).1
    · intro hx
      exact ⟨_, ⟨f x, (mem_sort _).2 (mem_image_of_mem f hx), rfl⟩,
        (mem_sort _).2 (mem_filter.2 ⟨hx, rfl⟩)⟩

/-- For a map `f` that is monotone on `s`, the product of a word `a` along `s` in increasing order
is the product, over the values `y` of `f` on `s` in increasing order, of the products of `a` along
the fibres `{x ∈ s | f x = y}` in increasing order. -/
theorem prod_map_sort_eq_prod_map_sort_image {M : Type*} [Monoid M] (hf : MonotoneOn f s)
    (a : α → M) :
    (s.sort.map a).prod =
      ((s.image f).sort.map fun y => ({x ∈ s | f x = y}.sort.map a).prod).prod := by
  rw [← flatten_map_sort_filter_eq_sort hf, List.map_flatten, List.prod_flatten, List.map_map,
    List.map_map, Function.comp_def, Function.comp_def]

/-- A relation holds between the images of consecutive entries of `s` sorted in increasing order
exactly when it holds between the images of any two positions `x < y` of `s` with no position of
`s` strictly between them. -/
theorem isChain_map_sort_iff {γ : Type*} {r : γ → γ → Prop} {g : α → γ} :
    (s.sort.map g).IsChain r ↔
      ∀ x ∈ s, ∀ y ∈ s, x < y → (∀ z ∈ s, z ≤ x ∨ y ≤ z) → r (g x) (g y) := by
  have hl := sortedLT_sort s
  have hmem : ∀ {x}, x ∈ s.sort ↔ x ∈ s := mem_sort _
  rw [List.isChain_map, List.isChain_iff_getElem]
  refine ⟨fun h x hx y hy hxy hadj => ?_, fun h i hi => ?_⟩
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hmem.2 hx)
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hmem.2 hy)
    have hik : i < k := hl.getElem_lt_getElem_iff.1 hxy
    obtain rfl : k = i + 1 := by
      by_contra hne
      have hi1 : i + 1 < s.sort.length := by omega
      rcases hadj _ (hmem.1 (List.getElem_mem hi1)) with h' | h'
      · exact absurd (hl.getElem_le_getElem_iff.1 h') (by omega)
      · exact absurd (hl.getElem_le_getElem_iff.1 h') (by omega)
    exact h i hk
  · refine h _ (hmem.1 (List.getElem_mem _)) _ (hmem.1 (List.getElem_mem _))
      (hl.getElem_lt_getElem_iff.2 (by omega)) fun z hz => ?_
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem (hmem.2 hz)
    rw [hl.getElem_le_getElem_iff, hl.getElem_le_getElem_iff]
    omega

/-- Sorting a finset `B` of `Fin n` and then moving its points along `finRotate n` gives a cyclic
rotation of the sorted list of the moved points: the order is unchanged except that the last
position, which moves to `0`, goes from the end of the list to its front. -/
theorem isRotated_sort_map_finRotate {n : ℕ} (B : Finset (Fin n)) :
    B.sort.map (finRotate n) ~r (B.map (finRotate n).toEmbedding).sort := by
  cases n with
  | zero => simp [eq_empty_of_isEmpty B]
  | succ n =>
    -- Away from the last position, `finRotate` is strictly monotone, so it commutes with sorting.
    have hsort {C : Finset (Fin (n + 1))} (hC : Fin.last n ∉ C) :
        (C.map (finRotate (n + 1)).toEmbedding).sort = C.sort.map (finRotate (n + 1)) := by
      have hmono : StrictMonoOn (finRotate (n + 1)).toEmbedding C := fun i hi j hj hij => by
        rw [Fin.lt_def] at hij ⊢
        simp only [Equiv.coe_toEmbedding, coe_finRotate_of_ne_last (ne_of_mem_of_not_mem hi hC),
          coe_finRotate_of_ne_last (ne_of_mem_of_not_mem hj hC)]
        omega
      rw [← hmono.map_finsetSort, Equiv.coe_toEmbedding]
    by_cases hB : Fin.last n ∈ B
    · set C := B.erase (Fin.last n)
      have hC : Fin.last n ∉ C := notMem_erase _ _
      have hBC : B.sort = C.sort ++ [Fin.last n] := by
        refine List.SortedLT.eq_of_mem_iff (sortedLT_sort B)
          (List.sortedLT_append.2 ⟨sortedLT_sort C,
            List.sortedLT_cons.2 ⟨by simp, List.sortedLT_nil⟩, fun x hx y hy => ?_⟩) fun x => ?_
        · rw [List.mem_singleton.1 hy, Fin.lt_last_iff_ne_last]
          exact ne_of_mem_of_not_mem ((mem_sort _).1 hx) hC
        · simp only [mem_sort, List.mem_append, List.mem_singleton, C, mem_erase]
          by_cases hx : x = Fin.last n <;> simp [hx, hB]
      have h0 : (finRotate (n + 1)).symm 0 = Fin.last n :=
        (finRotate (n + 1)).symm_apply_eq.2 finRotate_last.symm
      -- The last position moves to `0`, which comes first among the moved points.
      have hBC' : (B.map (finRotate (n + 1)).toEmbedding).sort =
          0 :: C.sort.map (finRotate (n + 1)) := by
        rw [← insert_erase hB, map_insert, Equiv.coe_toEmbedding, finRotate_last,
          sort_insert _ (fun _ _ => Fin.zero_le _) (by rw [mem_map_equiv, h0]; exact hC), hsort hC]
      rw [hBC, hBC']
      simpa using List.isRotated_append (l := C.sort.map (finRotate (n + 1))) (l' := [0])
    · rw [hsort hB]

end LinearOrder

end Finset
