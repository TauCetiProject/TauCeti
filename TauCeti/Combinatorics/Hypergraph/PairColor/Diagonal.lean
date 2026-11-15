/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Regular
public import TauCeti.Order.Partition.Finpartition
public import Mathlib.Data.Fintype.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Cleaning up diagonal pair blocks

`PairColorSystem.fillDiagonal` gives all distinct pairs inside each vertex cell a fresh,
reversal-fixed color `none`, retaining the original colors as `some c` between different cells.
Thus regularity between different cells is preserved. A diagonal block is regular provided
its test subsets must contain at least two vertices; this size condition matters because pair
densities exclude equal vertices and vanish on a coincident singleton.

The number of edited ordered pairs is exactly the sum of the within-cell ordered distinct-pair
counts, and is at most `m * |V|` if every cell has at most `m` vertices. This permits diagonal
blocks to be cleaned up at small edit cost when constructing a regular lower skeleton.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the edited-approximation approach.
-/

public section

open Finset

namespace TauCeti.PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]

/-- Replace colors inside vertex cells by a fresh fixed color, leaving all other colors intact.
The new palette has one more color than the old palette. -/
def fillDiagonal (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V)) :
    PairColorSystem (Option κ) V where
  color p := if P.part p.1.1 = P.part p.1.2 then none else some (S.color p)
  rev := Option.map S.rev
  rev_involutive c := by cases c <;> simp only [Option.map_none, Option.map_some, rev_rev]
  color_rev p := by
    by_cases h : P.part p.1.1 = P.part p.1.2
    · simp only [Prod.fst_swap, Prod.snd_swap, ite_eq_left h, ite_eq_left h.symm, Option.map_none]
    · simp only [Prod.fst_swap, Prod.snd_swap, ite_eq_right h, ite_eq_right (Ne.symm h),
        Option.map_some]
      exact congrArg some (S.color_rev p)

/-- Inside a cell the new color is `none`; between cells the original color is retained. -/
@[simp]
theorem fillDiagonal_color (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V))
    (p : {p : V × V // p.1 ≠ p.2}) :
    (S.fillDiagonal P).color p =
      if P.part p.1.1 = P.part p.1.2 then none else some (S.color p) := (rfl)

/-- Reversal fixes the fresh color and acts on old colors as before. -/
@[simp]
theorem fillDiagonal_rev (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V))
    (c : Option κ) : (S.fillDiagonal P).rev c = c.map S.rev := (rfl)

variable (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V))

/-- The total coloring is unchanged, up to the inclusion of palettes, between different cells. -/
theorem fillDiagonal_colorOfPair_of_ne {x y : V} (h : P.part x ≠ P.part y) :
    (S.fillDiagonal P).colorOfPair x y = (S.colorOfPair x y).map some := by
  have hxy : x ≠ y := fun hxy ↦ h (hxy ▸ rfl)
  simp [colorOfPair_of_ne _ hxy, h]

/-- Distinct vertices in the same cell receive the fresh color. -/
theorem fillDiagonal_colorOfPair_of_eq {x y : V} (hxy : x ≠ y)
    (h : P.part x = P.part y) : (S.fillDiagonal P).colorOfPair x y = some none := by
  simp [colorOfPair_of_ne _ hxy, h]

/-- A pair is edited exactly when its vertices are distinct and in the same cell. -/
@[simp]
theorem fillDiagonal_colorOfPair_ne_iff (x y : V) :
    (S.fillDiagonal P).colorOfPair x y ≠ (S.colorOfPair x y).map some ↔
      x ≠ y ∧ P.part x = P.part y := by
  by_cases hxy : x = y
  · subst y
    simp
  · by_cases h : P.part x = P.part y
    · rw [S.fillDiagonal_colorOfPair_of_eq P hxy h, S.colorOfPair_of_ne hxy]
      simp [hxy, h]
    · simp [S.fillDiagonal_colorOfPair_of_ne P h, h]

/-- Density on subrectangles between different cells is preserved for old colors, and is zero
for the fresh color. -/
theorem pairColorDensity_fillDiagonal_of_ne {A B s t : Finset V}
    (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) (hs : s ⊆ A) (ht : t ⊆ B)
    (c : Option κ) :
    pairColorDensity (S.fillDiagonal P) c s t = c.elim 0 (fun c ↦ pairColorDensity S c s t) := by
  classical
  have hc (x y : V) (hx : x ∈ s) (hy : y ∈ t) :
      (S.fillDiagonal P).colorOfPair x y = (S.colorOfPair x y).map some :=
    S.fillDiagonal_colorOfPair_of_ne P (by
      rwa [P.part_eq_of_mem hA (hs hx), P.part_eq_of_mem hB (ht hy)])
  cases c with
  | none =>
    have hempty : {p ∈ s ×ˢ t | (S.fillDiagonal P).colorOfPair p.1 p.2 = some none} = ∅ := by
      ext p
      simp only [mem_filter, notMem_empty, iff_false, not_and]
      intro hp heq
      obtain ⟨hx, hy⟩ := mem_product.1 hp
      rw [hc _ _ hx hy] at heq
      cases S.colorOfPair p.1 p.2 <;> simp at heq
    simp [pairColorDensity_def, hempty]
  | some c =>
    have hfilter : {p ∈ s ×ˢ t | (S.fillDiagonal P).colorOfPair p.1 p.2 = some (some c)} =
        {p ∈ s ×ˢ t | S.colorOfPair p.1 p.2 = some c} := by
      ext p
      simp only [mem_filter, mem_product]
      apply and_congr_right
      rintro ⟨hx, hy⟩
      rw [hc _ _ hx hy]
      cases S.colorOfPair p.1 p.2 <;> simp
    simp only [Option.elim_some, pairColorDensity_def, hfilter]

variable {S P} in
/-- Filling diagonal blocks preserves regularity between different cells. -/
theorem IsRegularPair.fillDiagonal {ε : ℝ} {A B : Finset V}
    (h : S.IsRegularPair ε A B) (hA : A ∈ P.parts) (hB : B ∈ P.parts) (hAB : A ≠ B) :
    (S.fillDiagonal P).IsRegularPair ε A B := by
  obtain ⟨x, hx⟩ := P.nonempty_of_mem_parts hA
  obtain ⟨y, hy⟩ := P.nonempty_of_mem_parts hB
  have hxy : x ≠ y := fun hxy ↦ hAB (P.eq_of_mem_parts hA hB hx (hxy.symm ▸ hy))
  let : Nonempty κ := ⟨S.color ⟨(x, y), hxy⟩⟩
  have hε : 0 ≤ ε := h.nonneg
  apply isRegularPair_iff.2
  intro c s hs t ht hs' ht'
  rw [S.pairColorDensity_fillDiagonal_of_ne P hA hB hAB hs ht c,
    S.pairColorDensity_fillDiagonal_of_ne P hA hB hAB (Subset.refl A) (Subset.refl B) c]
  cases c with
  | none => simpa using hε
  | some c => exact isRegularPair_iff.1 h c s hs t ht hs' ht'

/-- On a nonempty distinct-pair subrectangle inside a cell the fresh color has density one
and every old color has density zero. -/
theorem pairColorDensity_fillDiagonal_self {A s t : Finset V} (hA : A ∈ P.parts)
    (hs : s ⊆ A) (ht : t ⊆ A) (h : ((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2).Nonempty)
    (c : Option κ) :
    pairColorDensity (S.fillDiagonal P) c s t = if c = none then 1 else 0 := by
  classical
  have hc (x y : V) (hx : x ∈ s) (hy : y ∈ t) (hxy : x ≠ y) :
      (S.fillDiagonal P).colorOfPair x y = some none := by
    exact S.fillDiagonal_colorOfPair_of_eq P hxy (by
      rw [P.part_eq_of_mem hA (hs hx), P.part_eq_of_mem hA (ht hy)])
  have hfilter : {p ∈ s ×ˢ t | (S.fillDiagonal P).colorOfPair p.1 p.2 = some c} =
      if c = none then (s ×ˢ t).filter (fun p ↦ p.1 ≠ p.2) else ∅ := by
    ext p
    by_cases hp : p.1 ≠ p.2
    · by_cases hm : p ∈ s ×ˢ t
      · obtain ⟨hx, hy⟩ := mem_product.1 hm
        rw [mem_filter, hc _ _ hx hy hp]
        by_cases hc' : c = none <;> simp [hc', hm, hp, eq_comm]
      · by_cases hc' : c = none <;> simp [hc', hm]
    · have heq : p.1 = p.2 := not_ne_iff.1 hp
      by_cases hc' : c = none <;> simp [hc', heq]
  rw [pairColorDensity_def, hfilter]
  split_ifs <;> simp [h.card_pos.ne']

/-- A filled diagonal block is regular when every tested subset must have at least two
vertices. The condition `1 < ε * #A` rules out the zero-density singleton tests. -/
theorem isRegularPair_fillDiagonal_self {ε : ℝ} {A : Finset V} (hA : A ∈ P.parts)
    (hsize : 1 < ε * #A) : (S.fillDiagonal P).IsRegularPair ε A A := by
  have hε : 0 < ε := pos_of_mul_pos_left (one_pos.trans hsize) (Nat.cast_nonneg _)
  by_cases hlarge : 1 ≤ ε
  · exact isRegularPair_of_one_le hlarge
  have hAcard : 1 < #A := by
    have : ε * (#A : ℝ) ≤ #A := mul_le_of_le_one_left (by positivity) (le_of_not_ge hlarge)
    exact_mod_cast hsize.trans_le this
  have hsupp {s t : Finset V} (hs : 1 < #s) (ht : t.Nonempty) :
      ((s ×ˢ t).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
    obtain ⟨y, hy⟩ := ht
    obtain ⟨x, hx, hxy⟩ := exists_mem_ne hs y
    exact ⟨(x, y), mem_filter.2 ⟨mem_product.2 ⟨hx, hy⟩, hxy⟩⟩
  apply isRegularPair_iff.2
  intro c s hs t ht hs' ht'
  have hs₂ : 1 < #s := by exact_mod_cast hsize.trans_le hs'
  have ht₂ : 1 < #t := by exact_mod_cast hsize.trans_le ht'
  rw [S.pairColorDensity_fillDiagonal_self P hA hs ht (hsupp hs₂ (card_pos.1 (by omega))) c,
    S.pairColorDensity_fillDiagonal_self P hA (Subset.refl A) (Subset.refl A)
      (hsupp hAcard (card_pos.1 (by omega))) c]
  simp [hε.le]

/-- Cleanup converts regularity of all off-diagonal cell pairs into regularity of the entire
lower skeleton, provided the cells are large enough to exclude singleton tests. -/
theorem isPairColorRegular_fillDiagonal {ε : ℝ}
    (hsize : ∀ A ∈ P.parts, 1 < ε * #A)
    (hreg : ∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → S.IsRegularPair ε A B) :
    (⟨P, S.fillDiagonal P⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular ε := by
  apply PairSkeleton3.isPairColorRegular_iff.2
  intro c A hA B hB s hs t ht hs' ht'
  have hpair : (S.fillDiagonal P).IsRegularPair ε A B := by
    by_cases hAB : A = B
    · subst B
      exact S.isRegularPair_fillDiagonal_self P hA (hsize A hA)
    · exact (hreg A hA B hB hAB).fillDiagonal hA hB hAB
  exact isRegularPair_iff.1 hpair c s hs t ht hs' ht'

open Classical in
/-- The exact number of edited ordered pairs is the sum of the within-cell distinct-pair
counts. There is no factor of two or contribution from equal vertices. -/
theorem card_fillDiagonal_colorOfPair_ne :
    #{p : V × V | (S.fillDiagonal P).colorOfPair p.1 p.2 ≠
      (S.colorOfPair p.1 p.2).map some} = ∑ A ∈ P.parts, #A * (#A - 1) := by
  classical
  have heq : (univ.filter fun p : V × V ↦ (S.fillDiagonal P).colorOfPair p.1 p.2 ≠
      (S.colorOfPair p.1 p.2).map some) = P.parts.biUnion offDiag := by
    ext p
    simp only [mem_filter, mem_univ, true_and, fillDiagonal_colorOfPair_ne_iff, mem_biUnion,
      mem_offDiag]
    constructor
    · rintro ⟨hxy, hpart⟩
      exact ⟨P.part p.1, P.part_mem.2 (mem_univ _), P.mem_part_self.2 (mem_univ _),
        hpart ▸ P.mem_part_self.2 (mem_univ _), hxy⟩
    · rintro ⟨A, hA, hx, hy, hxy⟩
      exact ⟨hxy, by rw [P.part_eq_of_mem hA hx, P.part_eq_of_mem hA hy]⟩
  rw [heq, card_biUnion]
  · simp [Nat.mul_sub_left_distrib]
  · intro A hA B hB hAB
    refine disjoint_left.2 fun p hpA hpB ↦ hAB ?_
    exact P.eq_of_mem_parts hA hB (mem_offDiag.1 hpA).1 (mem_offDiag.1 hpB).1

open Classical in
/-- The edit count is bounded by the sum of the squares of cell sizes. -/
theorem card_fillDiagonal_colorOfPair_ne_le :
    #{p : V × V | (S.fillDiagonal P).colorOfPair p.1 p.2 ≠
      (S.colorOfPair p.1 p.2).map some} ≤ ∑ A ∈ P.parts, #A ^ 2 := by
  classical
  rw [S.card_fillDiagonal_colorOfPair_ne P]
  exact sum_le_sum fun A _ ↦ by
    rw [sq]
    exact Nat.mul_le_mul_left _ (Nat.sub_le _ _)

open Classical in
/-- If all cells have size at most `m`, diagonal cleanup edits at most `m * |V|` ordered pairs. -/
theorem card_fillDiagonal_colorOfPair_ne_le_of_card_le {m : ℕ} (hm : ∀ A ∈ P.parts, #A ≤ m) :
    #{p : V × V | (S.fillDiagonal P).colorOfPair p.1 p.2 ≠
      (S.colorOfPair p.1 p.2).map some} ≤ m * Fintype.card V := by
  classical
  exact (S.card_fillDiagonal_colorOfPair_ne_le P).trans (by simpa using P.sum_sq_card_parts_le hm)

end TauCeti.PairColorSystem
