/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Hypergraph.PairColor.Recoloring
public import TauCeti.Combinatorics.Hypergraph.PairColor.Regularization
public import TauCeti.Combinatorics.Hypergraph.PairColor.Diagonal
import TauCeti.Data.Finset.Basic
import Mathlib.Data.Rat.BigOperators

/-!
# Cleaning up irregular pairs of vertex cells

Local regular recolorings can be chosen simultaneously on all irregular pairs of cells of a
vertex partition. Choose one orientation of each pair of distinct cells and use its coherent
recoloring in both directions. Regular pairs and within-cell pairs retain their colors. The
number of edited ordered pairs is bounded by the original irregular-pair mass, and every
color density between distinct cells changes by at most the requested tolerance.

Combining this construction with diagonal cleanup gives a regular lower skeleton on the same
vertex partition, with one fresh reversal-fixed color. The edit bound charges irregular
rectangles and within-cell distinct pairs separately. These constructions are used to replace
a lower skeleton that is regular outside a small exceptional set by an everywhere regular one.

The two existence theorems are `PairColorSystem.exists_recoloring_regular_offDiag` and
`PairColorSystem.exists_recoloring_isPairColorRegular`. Neither requires equitable cells;
the size assumption depends only on the tolerance and the size of the original palette.

## References

* V. Rödl and M. Schacht, *Regular partitions of hypergraphs: regularity lemmas*,
  Combin. Probab. Comput. 16 (2007), the edited-approximation construction.
-/

public section

open Finset

namespace TauCeti

namespace PairColorSystem

variable {κ V : Type*} [Fintype V] [DecidableEq V]
  (S : PairColorSystem κ V) (P : Finpartition (univ : Finset V)) {ε : ℝ}

private theorem exists_local_recoloring [Fintype κ] (hε : 0 < ε)
    (hsize : ∀ A ∈ P.parts, Fintype.card κ + 1 ≤ ε ^ 6 * #A) (A B : P.parts) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (A = B ∨ S.IsRegularPair ε A B → T = S) ∧
      (A ≠ B → T.IsRegularPair (2 * ε) A B ∧
        ∀ c, |(pairColorDensity T c A B : ℝ) - pairColorDensity S c A B| ≤ ε) := by
  classical
  by_cases h : A = B ∨ S.IsRegularPair ε A B
  · refine ⟨S, rfl, fun _ ↦ rfl, fun hAB ↦ ?_⟩
    exact ⟨(h.resolve_left hAB).mono (by linarith), fun c ↦ by simp [hε.le]⟩
  · have hAB : (A : Finset V) ≠ B := fun heq ↦ h (Or.inl (Subtype.ext heq))
    have hdisj : Disjoint A.1 B.1 := P.disjoint A.2 B.2 hAB
    have hnonempty : ((A.1 ×ˢ B.1).filter fun p ↦ p.1 ≠ p.2).Nonempty := by
      rw [filter_ne_product_of_disjoint hdisj]
      exact (P.nonempty_of_mem_parts A.2).product (P.nonempty_of_mem_parts B.2)
    obtain ⟨T, hrev, -, hreg, hdens⟩ := S.exists_recoloring_isRegularPair hdisj
      (p := fun c ↦ (pairColorDensity S c A B : ℝ))
      (fun c ↦ by exact_mod_cast pairColorDensity_nonneg S c A B)
      (by exact_mod_cast sum_pairColorDensity S A B hnonempty) hε
      (hsize A A.2) (hsize B B.2)
    exact ⟨T, hrev, fun hh ↦ (h hh).elim, fun _ ↦ ⟨hreg, hdens⟩⟩

variable (order : LinearOrder P.parts) (T : P.parts → P.parts → PairColorSystem κ V)

private theorem exists_cellwise_recoloring
    (hrev : ∀ A B, (T A B).rev = S.rev) :
    ∃ R : PairColorSystem κ V, R.rev = S.rev ∧
      ∀ A B : P.parts, order.le A B → ∀ x ∈ A.1, ∀ y ∈ B.1,
        R.colorOfPair x y = (T A B).colorOfPair x y := by
  classical
  let : LinearOrder P.parts := order
  let : LE P.parts := order.toLE
  let cell (x : V) : P.parts := ⟨P.part x, P.part_mem.2 (mem_univ x)⟩
  have hcell (A : P.parts) {x : V} (hx : x ∈ A.1) : cell x = A :=
    Subtype.ext (P.part_eq_of_mem A.2 hx)
  -- The minimum and maximum select the same local system in both orientations.
  let R : PairColorSystem κ V :=
    { color := fun p ↦ (T (min (cell p.1.1) (cell p.1.2))
        (max (cell p.1.1) (cell p.1.2))).color p
      rev := S.rev
      rev_involutive := S.rev_involutive
      color_rev := fun p ↦ by
        dsimp only [Prod.fst_swap, Prod.snd_swap]
        rw [min_comm (cell p.1.2), max_comm (cell p.1.2)]
        rw [(T _ _).color_rev, hrev] }
  refine ⟨R, rfl, fun A B hAB x hx y hy ↦ ?_⟩
  have hlocal (A B : P.parts) (hAB : A ≤ B) {x y : V} (hx : x ∈ A.1) (hy : y ∈ B.1) :
      R.colorOfPair x y = (T A B).colorOfPair x y := by
    by_cases hxy : x = y
    · simp [hxy]
    · simp [colorOfPair_of_ne _ hxy, R, hcell A hx, hcell B hy, min_eq_left hAB,
        max_eq_right hAB]
  exact hlocal A B hAB hx hy

variable (R : PairColorSystem κ V)
  (hlocal : ∀ A B : P.parts, order.le A B → ∀ x ∈ A.1, ∀ y ∈ B.1,
    R.colorOfPair x y = (T A B).colorOfPair x y)

include hlocal in
private theorem recoloring_agrees (hRrev : R.rev = S.rev)
    (hkeep : ∀ A B : P.parts, A = B ∨ S.IsRegularPair ε A B → T A B = S)
    (x y : V) (h : P.part x = P.part y ∨ S.IsRegularPair ε (P.part x) (P.part y)) :
    R.colorOfPair x y = S.colorOfPair x y := by
  let : LinearOrder P.parts := order
  let : LE P.parts := order.toLE
  let cell (x : V) : P.parts := ⟨P.part x, P.part_mem.2 (mem_univ x)⟩
  have hk (A B : P.parts) (hx : x ∈ A.1) (hy : y ∈ B.1) (hAB : A ≤ B)
      (hgood : A = B ∨ S.IsRegularPair ε A B) : R.colorOfPair x y = S.colorOfPair x y := by
    rw [hlocal A B hAB x hx y hy, hkeep A B hgood]
  have hgood : cell x = cell y ∨ S.IsRegularPair ε (cell x) (cell y) :=
    h.imp (fun heq ↦ Subtype.ext heq) id
  rcases le_total (cell x) (cell y) with hle | hle
  · exact hk _ _ (P.mem_part_self.2 (mem_univ _))
      (P.mem_part_self.2 (mem_univ _)) hle hgood
  · rw [R.colorOfPair_swap y x, S.colorOfPair_swap y x, hRrev]
    congr 1
    rw [hlocal (cell y) (cell x) hle y (P.mem_part_self.2 (mem_univ _))
      x (P.mem_part_self.2 (mem_univ _)), hkeep _ _ (hgood.imp Eq.symm IsRegularPair.symm)]

include hlocal in
private theorem regular_density_of_cellwise (hRrev : R.rev = S.rev)
    (hreg : ∀ A B : P.parts, A ≠ B → (T A B).IsRegularPair (2 * ε) A B ∧
      ∀ c, |(pairColorDensity (T A B) c A B : ℝ) - pairColorDensity S c A B| ≤ ε)
    (A B : P.parts) (hne : A ≠ B) : R.IsRegularPair (2 * ε) A B ∧
      ∀ c, |(pairColorDensity R c A B : ℝ) - pairColorDensity S c A B| ≤ ε := by
  let : LinearOrder P.parts := order
  let : LE P.parts := order.toLE
  have hdensity (A B : P.parts) (hAB : A ≤ B) {s t : Finset V} (hs : s ⊆ A.1)
      (ht : t ⊆ B.1) (c : κ) : pairColorDensity R c s t = pairColorDensity (T A B) c s t :=
    pairColorDensity_congr (fun x hx y hy ↦ hlocal A B hAB x (hs hx) y (ht hy)) c
  have hregular (A B : P.parts) (hAB : A ≤ B) (hne : A ≠ B) :
      R.IsRegularPair (2 * ε) A B := by
    apply isRegularPair_iff.2
    intro c s hs t ht hsc htc
    rw [hdensity A B hAB hs ht, hdensity A B hAB (Subset.refl _) (Subset.refl _)]
    exact isRegularPair_iff.1 (hreg A B hne).1 c s hs t ht hsc htc
  rcases le_total A B with hle | hle
  · refine ⟨hregular A B hle hne, fun c ↦ ?_⟩
    rw [hdensity A B hle (Subset.refl _) (Subset.refl _)]
    exact (hreg A B hne).2 c
  · refine ⟨(hregular B A hle hne.symm).symm, fun c ↦ ?_⟩
    have he := (hreg B A hne.symm).2 (S.rev c)
    rw [← hdensity B A hle (Subset.refl _) (Subset.refl _)] at he
    have he' : |(pairColorDensity R (R.rev c) B A : ℝ) -
        pairColorDensity S (S.rev c) B A| ≤ ε := by simpa only [hRrev] using he
    simpa only [pairColorDensity_swap] using he'

open Classical in
private theorem card_edits_le_irregularPairs (R : PairColorSystem κ V)
    (hagree : ∀ x y, P.part x = P.part y ∨ S.IsRegularPair ε (P.part x) (P.part y) →
      R.colorOfPair x y = S.colorOfPair x y) :
    #{p : V × V | R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} ≤
      ∑ AB ∈ S.irregularPairs ε P, #AB.1 * #AB.2 := by
  have hsub : (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ⊆
      (S.irregularPairs ε P).biUnion (fun AB ↦ AB.1 ×ˢ AB.2) := by
    intro p hp
    have hne := (mem_filter.1 hp).2
    have hbad : ¬(P.part p.1 = P.part p.2 ∨
        S.IsRegularPair ε (P.part p.1) (P.part p.2)) := fun h ↦ hne (hagree _ _ h)
    exact mem_biUnion.2 ⟨(P.part p.1, P.part p.2), (S.mem_irregularPairs).2
      ⟨P.part_mem.2 (mem_univ _), P.part_mem.2 (mem_univ _),
        fun h ↦ hbad (Or.inl h), fun h ↦ hbad (Or.inr h)⟩,
      mem_product.2 ⟨P.mem_part_self.2 (mem_univ _), P.mem_part_self.2 (mem_univ _)⟩⟩
  exact (card_le_card hsub).trans (card_biUnion_le.trans_eq (by simp only [card_product]))

open Classical in
/-- Recolor all irregular off-diagonal cell pairs simultaneously. The palette reversal,
within-cell colors, and all originally `ε`-regular cell pairs are preserved. Every distinct
cell pair becomes `2ε`-regular, its color densities change by at most `ε`, and the ordered-pair
edit count is at most the original irregular-pair mass. -/
theorem exists_recoloring_regular_offDiag [Fintype κ] (hε : 0 < ε)
    (hsize : ∀ A ∈ P.parts, Fintype.card κ + 1 ≤ ε ^ 6 * #A) :
    ∃ T : PairColorSystem κ V, T.rev = S.rev ∧
      (∀ x y, P.part x = P.part y ∨ S.IsRegularPair ε (P.part x) (P.part y) →
        T.colorOfPair x y = S.colorOfPair x y) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → T.IsRegularPair (2 * ε) A B) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) - pairColorDensity S c A B| ≤ ε) ∧
      #{p : V × V | T.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2} ≤
        ∑ AB ∈ S.irregularPairs ε P, #AB.1 * #AB.2 := by
  classical
  let order : LinearOrder P.parts := LinearOrder.lift' (Fintype.equivFin P.parts)
    (Fintype.equivFin P.parts).injective
  choose T hrev hkeep hreg using S.exists_local_recoloring P hε hsize
  obtain ⟨R, hRrev, hlocal⟩ := S.exists_cellwise_recoloring P order T hrev
  have hagree := S.recoloring_agrees P order T R hlocal hRrev hkeep
  have hpairs := S.regular_density_of_cellwise P order T R hlocal hRrev hreg
  refine ⟨R, hRrev, hagree, ?_, ?_, S.card_edits_le_irregularPairs P R hagree⟩
  · intro A hA B hB hne
    exact (hpairs ⟨A, hA⟩ ⟨B, hB⟩ (fun h ↦ hne (congrArg Subtype.val h))).1
  · intro A hA B hB hne
    exact (hpairs ⟨A, hA⟩ ⟨B, hB⟩ (fun h ↦ hne (congrArg Subtype.val h))).2

open Classical in
/-- Replace a lower skeleton by an everywhere regular one on the same cells. The palette
adds a fresh reversal-fixed color for diagonal blocks. Original colors' off-diagonal densities
change by at most `ε`; the fresh color has density at most `ε` there, compared to zero. The
ordered-pair edit bound is the original irregular-pair mass plus the within-cell distinct-pair
mass. -/
theorem exists_recoloring_isPairColorRegular [Fintype κ] (hε : 0 < ε)
    (hsize : ∀ A ∈ P.parts, Fintype.card κ + 1 ≤ ε ^ 6 * #A) :
    ∃ T : PairColorSystem (Option κ) V, T.rev = Option.map S.rev ∧
      (⟨P, T⟩ : PairSkeleton3 (Option κ) V).IsPairColorRegular (2 * ε) ∧
      (∀ A ∈ P.parts, ∀ B ∈ P.parts, A ≠ B → ∀ c,
        |(pairColorDensity T c A B : ℝ) -
          c.elim 0 (fun c ↦ (pairColorDensity S c A B : ℝ))| ≤ ε) ∧
      #{p : V × V | T.colorOfPair p.1 p.2 ≠ (S.colorOfPair p.1 p.2).map some} ≤
        (∑ AB ∈ S.irregularPairs ε P, #AB.1 * #AB.2) +
          ∑ A ∈ P.parts, #A * (#A - 1) := by
  classical
  obtain ⟨R, hrev, -, hreg, hdens, hedit⟩ := S.exists_recoloring_regular_offDiag P hε hsize
  have hlarge (A) (hA : A ∈ P.parts) : 1 < 2 * ε * #A := by
    have hA₀ : (1 : ℝ) ≤ #A := by exact_mod_cast (P.nonempty_of_mem_parts hA).card_pos
    have h := hsize A hA
    obtain hε₁ | hε₁ := le_or_gt ε 1
    · have hp : ε ^ 6 ≤ ε := pow_le_of_le_one hε.le hε₁ (by norm_num)
      nlinarith [mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg (α := ℝ) #A),
        Nat.cast_nonneg (α := ℝ) (Fintype.card κ)]
    · nlinarith
  refine ⟨R.fillDiagonal P, ?_, R.isPairColorRegular_fillDiagonal P hlarge hreg, ?_, ?_⟩
  · exact funext fun c ↦ by simp only [fillDiagonal_rev, hrev]
  · intro A hA B hB hAB c
    rw [R.pairColorDensity_fillDiagonal_of_ne P hA hB hAB (Subset.refl _) (Subset.refl _)]
    cases c with
    | none => simp [hε.le]
    | some c => simpa only [Option.elim_some] using hdens A hA B hB hAB c
  · have hsub : (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
          (S.colorOfPair p.1 p.2).map some) ⊆
        (univ.filter fun p : V × V ↦ R.colorOfPair p.1 p.2 ≠ S.colorOfPair p.1 p.2) ∪
          (univ.filter fun p : V × V ↦ (R.fillDiagonal P).colorOfPair p.1 p.2 ≠
            (R.colorOfPair p.1 p.2).map some) := by
      intro p hp
      simp only [mem_union, mem_filter, mem_univ, true_and] at hp ⊢
      by_cases h : R.colorOfPair p.1 p.2 = S.colorOfPair p.1 p.2
      · exact Or.inr (by simpa only [h] using hp)
      · exact Or.inl h
    exact (card_le_card hsub).trans (card_union_le _ _ |>.trans
      (add_le_add hedit (R.card_fillDiagonal_colorOfPair_ne P).le))

end PairColorSystem

end TauCeti
