/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LowDimTopology.Bordered.StrandsAlgebra.StrandDiagram

/-!
# Adding horizontal strands to strand diagrams

A strand of a strand diagram is *horizontal* when it ends where it starts. The algebra `A(Z)` of a
pointed matched circle is spanned by sums of strand diagrams which differ only in their horizontal
strands, so its multiplication law reduces to understanding how horizontal strands behave under
concatenation. This file sets up that bookkeeping for strand diagrams on an arbitrary linear order;
moving a horizontal strand between matched points is treated in
`TauCeti.LowDimTopology.Bordered.StrandsAlgebra.Horizontal`.

`TauCeti.StrandDiagram.addHorizontal φ U` is the diagram `φ` with a horizontal strand added at each
point of the finite set `U`; strands of `φ` starting or ending in `U` are dropped, so that the
operation is defined for every `U`. When `U` avoids the source and target of `φ` nothing is dropped,
and the source and target of the result are those of `φ` together with `U`.

A horizontal strand at `w` crosses exactly the strands `i ↦ j` of `φ` with `i < w < j`. Such a
strand of a composite `φ.trans ψ` passing through a point other than `w` crosses `w` in exactly one
of the two halves. So adding the same horizontal strands to both factors adds the same number of
crossings to both sides of the equation `inv (φ.trans ψ) = inv φ + inv ψ`, and does not change
whether two diagrams have a nonzero product in the strands algebra
(`TauCeti.StrandDiagram.composable_addHorizontal_iff`).

## Main definitions

* `TauCeti.StrandDiagram.addHorizontal`: add horizontal strands along a finite set.

## Main results

* `TauCeti.StrandDiagram.source_addHorizontal`, `TauCeti.StrandDiagram.target_addHorizontal`: the
  source and target grow by the added points.
* `TauCeti.StrandDiagram.addHorizontal_trans_addHorizontal`: horizontal strands added to both
  factors pass through the composite.
* `TauCeti.StrandDiagram.composable_addHorizontal_iff`: adding common horizontal strands does not
  change composability.

## References

* R. Lipshitz, P. Ozsváth and D. Thurston, *Bordered Heegaard Floer homology*, Mem. Amer. Math.
  Soc. **254** (2018), no. 1216, [arXiv:0810.0687](https://arxiv.org/abs/0810.0687), §3.1 (strand
  diagrams and horizontal strands) and §3.2 (the algebra of a pointed matched circle).
-/

public section

open Finset

namespace TauCeti

namespace StrandDiagram

variable {α : Type*} [LinearOrder α]

/-- The diagram `φ` with a horizontal strand added at every point of `U`. Strands of `φ` starting
or ending in `U` are removed; when `U` avoids the source and the target of `φ` none are. -/
def addHorizontal (φ : StrandDiagram α) (U : Finset α) : StrandDiagram α where
  toPEquiv :=
    { toFun i := if i ∈ U then some i else (φ i).bind fun j ↦ if j ∈ U then none else some j
      invFun j := if j ∈ U then some j else
        (φ.toPEquiv.symm j).bind fun i ↦ if i ∈ U then none else some i
      inv i j := by
        have key : φ.toPEquiv.symm j = some i ↔ φ i = some j := PEquiv.eq_some_iff _
        split_ifs <;> grind [Option.bind_eq_some_iff] }
  le_of_mem' i j h := by
    -- `addHorizontal_apply` is not available yet: unfold the coercion of the `PEquiv` built above
    -- to its `toFun` field, and `j ∈ o` to `o = some j`.
    change (if i ∈ U then some i else _) = some j at h
    split_ifs at h with hi
    · exact (Option.some.inj h).le
    · obtain ⟨k, hk, hkj⟩ := Option.bind_eq_some_iff.1 h
      split_ifs at hkj with hkU
      exact Option.some.inj hkj ▸ φ.le_of_mem hk

theorem addHorizontal_apply (φ : StrandDiagram α) (U : Finset α) (i : α) :
    φ.addHorizontal U i =
      if i ∈ U then some i else (φ i).bind fun j ↦ if j ∈ U then none else some j :=
  (rfl)

theorem mem_addHorizontal {φ : StrandDiagram α} {U : Finset α} {i j : α} :
    j ∈ φ.addHorizontal U i ↔ i ∈ U ∧ j = i ∨ i ∉ U ∧ j ∉ U ∧ j ∈ φ i := by
  rw [Option.mem_def, addHorizontal_apply]
  by_cases hi : i ∈ U
  · simp [hi, eq_comm]
  · simp only [hi, ↓reduceIte, Option.bind_eq_some_iff, Option.ite_none_left_eq_some,
      false_and, not_false_eq_true, true_and, false_or, Option.mem_def]
    grind

@[simp]
theorem addHorizontal_apply_of_mem (φ : StrandDiagram α) {U : Finset α} {i : α} (hi : i ∈ U) :
    φ.addHorizontal U i = some i := by
  simp [addHorizontal_apply, hi]

@[simp]
theorem addHorizontal_empty (φ : StrandDiagram α) : φ.addHorizontal ∅ = φ := by
  ext i j
  simp [← Option.mem_def, mem_addHorizontal]

/-- Adding horizontal strands in two steps adds them along the union. -/
@[simp]
theorem addHorizontal_addHorizontal (φ : StrandDiagram α) (U V : Finset α) :
    (φ.addHorizontal U).addHorizontal V = φ.addHorizontal (U ∪ V) := by
  ext i j
  simp only [← Option.mem_def, mem_addHorizontal, mem_union]
  grind

/-- Adding horizontal strands to an identity diagram gives an identity diagram. -/
@[simp]
theorem idOn_addHorizontal (s U : Finset α) : (idOn s).addHorizontal U = idOn (s ∪ U) := by
  ext i j
  simp only [← Option.mem_def, mem_addHorizontal, mem_idOn, mem_union]
  grind

/-- Horizontal strands added to both factors, along a set avoiding the target of the first, pass
through the composite. -/
theorem addHorizontal_trans_addHorizontal {φ ψ : StrandDiagram α} {W : Finset α}
    (h : ∀ i j, j ∈ φ i → j ∉ W) :
    (φ.addHorizontal W).trans (ψ.addHorizontal W) = (φ.trans ψ).addHorizontal W := by
  ext i k
  simp only [← Option.mem_def, mem_trans, mem_addHorizontal]
  have := h i
  grind

/-- If `φ` has no horizontal strands, the horizontal strands of `φ.addHorizontal U` are exactly
those at the points of `U`. -/
theorem mem_addHorizontal_self {φ : StrandDiagram α} {U : Finset α} {i : α}
    (hφ : ∀ j, j ∉ φ j) : i ∈ φ.addHorizontal U i ↔ i ∈ U := by
  rw [mem_addHorizontal]
  simp [hφ i]

section Finite

variable [Fintype α]

/-- When `U` avoids the target of `φ`, the source of `φ.addHorizontal U` is that of `φ` together
with `U`. -/
theorem source_addHorizontal {φ : StrandDiagram α} {U : Finset α} (ht : Disjoint φ.target U) :
    (φ.addHorizontal U).source = φ.source ∪ U := by
  ext i
  simp only [mem_source, mem_addHorizontal, mem_union]
  constructor
  · rintro ⟨j, (⟨hi, -⟩ | ⟨-, -, hij⟩)⟩
    · exact Or.inr hi
    · exact Or.inl ⟨j, hij⟩
  · intro hi'
    by_cases hi : i ∈ U
    · exact ⟨i, Or.inl ⟨hi, rfl⟩⟩
    obtain ⟨j, hij⟩ := hi'.resolve_right hi
    exact ⟨j, Or.inr ⟨hi, notMem_of_mem_of_disjoint_target ht hij, hij⟩⟩

/-- When `U` avoids the source of `φ`, the target of `φ.addHorizontal U` is that of `φ` together
with `U`. -/
theorem target_addHorizontal {φ : StrandDiagram α} {U : Finset α} (hs : Disjoint φ.source U) :
    (φ.addHorizontal U).target = φ.target ∪ U := by
  ext j
  simp only [mem_target, mem_addHorizontal, mem_union]
  constructor
  · rintro ⟨i, (⟨hi, rfl⟩ | ⟨-, -, hij⟩)⟩
    · exact Or.inr hi
    · exact Or.inl ⟨i, hij⟩
  · intro hj'
    by_cases hj : j ∈ U
    · exact ⟨j, Or.inl ⟨hj, rfl⟩⟩
    obtain ⟨i, hij⟩ := hj'.resolve_right hj
    exact ⟨i, Or.inr ⟨notMem_of_mem_of_disjoint_source hs hij, hj, hij⟩⟩

/-- On a point outside `U`, `φ.addHorizontal U` agrees with `φ` when `U` avoids the target. -/
@[simp]
theorem addHorizontal_apply_of_notMem {φ : StrandDiagram α} {U : Finset α}
    (ht : Disjoint φ.target U) {i : α} (hi : i ∉ U) : φ.addHorizontal U i = φ i := by
  ext j
  simp only [← Option.mem_def, mem_addHorizontal, hi, false_and, not_false_eq_true, true_and,
    false_or, and_iff_right_iff_imp]
  exact notMem_of_mem_of_disjoint_target ht

/-- The crossings of the strands of `φ` with horizontal strands at the points of `W`: pairs
`(i, w)` with `w ∈ W` and a strand `i ↦ j` of `φ` with `i < w < j`. -/
private def horizontalCrossings (φ : StrandDiagram α) (W : Finset α) : Finset (α × α) :=
  (φ.source ×ˢ W).filter fun p ↦ p.1 < p.2 ∧ p.2 < (φ p.1).getD p.1

private theorem mem_horizontalCrossings {φ : StrandDiagram α} {W : Finset α} {p : α × α} :
    p ∈ horizontalCrossings φ W ↔ p.2 ∈ W ∧ p.1 < p.2 ∧ ∃ j ∈ φ p.1, p.2 < j := by
  rw [horizontalCrossings, mem_filter, mem_product, mem_source]
  constructor
  · rintro ⟨⟨⟨j, hj⟩, hw⟩, hlt, hwj⟩
    rw [Option.mem_def] at hj
    exact ⟨hw, hlt, j, hj, by simpa [hj] using hwj⟩
  · rintro ⟨hw, hlt, j, hj, hwj⟩
    rw [Option.mem_def] at hj
    exact ⟨⟨⟨j, hj⟩, hw⟩, hlt, by simpa [hj] using hwj⟩

/-- **Crossings with horizontal strands.** If `W` avoids the source and target of `φ`, the
crossings of `φ.addHorizontal W` are those of `φ` together with one crossing for each strand
`i ↦ j` of `φ` and each `w ∈ W` with `i < w < j`. -/
private theorem inversionCount_addHorizontal {φ : StrandDiagram α} {W : Finset α}
    (hs : Disjoint φ.source W) (ht : Disjoint φ.target W) :
    (φ.addHorizontal W).inversionCount = φ.inversionCount + #(horizontalCrossings φ W) := by
  have hnotW {i j : α} (hij : j ∈ φ i) : i ∉ W ∧ j ∉ W :=
    ⟨notMem_of_mem_of_disjoint_source hs hij, notMem_of_mem_of_disjoint_target ht hij⟩
  have heq : (φ.addHorizontal W).inversions = φ.inversions ∪ horizontalCrossings φ W := by
    ext ⟨i, k⟩
    simp only [mem_union, mem_inversions, mem_horizontalCrossings, mem_addHorizontal]
    constructor
    · rintro ⟨hik, a, (⟨hiW, rfl⟩ | ⟨hiW, haW, hia⟩), b, (⟨hkW, rfl⟩ | ⟨hkW, hbW, hkb⟩), hba⟩
      · exact absurd (hik.trans hba) (lt_irrefl _)
      · exact absurd (hik.trans_le (φ.le_of_mem hkb)) (not_lt.2 hba.le)
      · exact Or.inr ⟨hkW, hik, a, hia, hba⟩
      · exact Or.inl ⟨hik, a, hia, b, hkb, hba⟩
    · rintro (⟨hik, a, hia, b, hkb, hba⟩ | ⟨hkW, hik, a, hia, hka⟩)
      · exact ⟨hik, a, Or.inr ⟨(hnotW hia).1, (hnotW hia).2, hia⟩, b,
          Or.inr ⟨(hnotW hkb).1, (hnotW hkb).2, hkb⟩, hba⟩
      · exact ⟨hik, a, Or.inr ⟨(hnotW hia).1, (hnotW hia).2, hia⟩, k, Or.inl ⟨hkW, rfl⟩, hka⟩
  rw [inversionCount_def, inversionCount_def, heq, card_union_of_disjoint]
  rw [disjoint_left]
  rintro ⟨i, k⟩ hφ hW
  obtain ⟨-, -, -, b, hkb, -⟩ := mem_inversions.1 hφ
  exact (hnotW hkb).1 (mem_horizontalCrossings.1 hW).1

/-- Crossings with horizontal strands are additive under composition: a strand `i ↦ j ↦ k` of
`φ.trans ψ` crosses a horizontal strand at `w ≠ j` in exactly one of the two halves. -/
private theorem card_horizontalCrossings_trans {φ ψ : StrandDiagram α} {W : Finset α}
    (hφψ : φ.target = ψ.source) (ht : Disjoint φ.target W) :
    #(horizontalCrossings (φ.trans ψ) W) =
      #(horizontalCrossings φ W) + #(horizontalCrossings ψ W) := by
  set C := horizontalCrossings (φ.trans ψ) W
  rw [← card_filter_add_card_filter_not (s := C) fun p ↦ ∃ j ∈ φ p.1, p.2 < j]
  congr 1
  · -- The crossings in the first half are the crossings of `φ`.
    congr 1
    ext ⟨i, w⟩
    simp only [C, mem_filter, mem_horizontalCrossings, mem_trans]
    constructor
    · rintro ⟨⟨hw, hiw, -⟩, j, hij, hwj⟩
      exact ⟨hw, hiw, j, hij, hwj⟩
    · rintro ⟨hw, hiw, j, hij, hwj⟩
      obtain ⟨k, hjk⟩ := mem_source.1 (hφψ ▸ mem_target.2 ⟨i, hij⟩)
      exact ⟨⟨hw, hiw, k, ⟨j, hij, hjk⟩, hwj.trans_le (ψ.le_of_mem hjk)⟩, j, hij, hwj⟩
  · -- The crossings in the second half are carried by `φ` onto the crossings of `ψ`.
    refine card_bij (fun p _ ↦ ((φ p.1).getD p.1, p.2)) ?_ ?_ ?_
    · rintro ⟨i, w⟩ hp
      simp only [C, mem_filter, mem_horizontalCrossings, mem_trans, not_exists, not_and,
        not_lt] at hp
      obtain ⟨⟨hw, -, k, ⟨j, hij, hjk⟩, hwk⟩, hjw⟩ := hp
      rw [Option.mem_def] at hij
      have hjw' : j < w := lt_of_le_of_ne (hjw j hij) fun h ↦
        notMem_of_mem_of_disjoint_target ht hij (h ▸ hw)
      simp only [hij, Option.getD_some]
      exact mem_horizontalCrossings.2 ⟨hw, hjw', k, hjk, hwk⟩
    · rintro ⟨i, w⟩ hp ⟨i', w'⟩ hp' he
      simp only [C, mem_filter, mem_horizontalCrossings, mem_trans] at hp hp'
      obtain ⟨⟨-, -, -, ⟨j, hij, -⟩, -⟩, -⟩ := hp
      obtain ⟨⟨-, -, -, ⟨j', hij', -⟩, -⟩, -⟩ := hp'
      rw [Option.mem_def] at hij hij'
      simp only [hij, hij', Option.getD_some, Prod.mk.injEq] at he
      obtain ⟨rfl, rfl⟩ := he
      exact Prod.ext (φ.toPEquiv.inj hij hij') rfl
    · rintro ⟨j, w⟩ hp
      obtain ⟨hw, hjw, k, hjk, hwk⟩ := mem_horizontalCrossings.1 hp
      obtain ⟨i, hij⟩ := mem_target.1 (hφψ ▸ mem_source.2 ⟨k, hjk⟩)
      refine ⟨(i, w), ?_, ?_⟩
      · simp only [C, mem_filter, mem_horizontalCrossings, mem_trans, not_exists, not_and,
          not_lt]
        refine ⟨⟨hw, (φ.le_of_mem hij).trans_lt hjw, k, ⟨j, hij, hjk⟩, hwk⟩, fun j' hij' ↦ ?_⟩
        exact (Option.mem_unique hij' hij ▸ hjw).le
      · rw [Option.mem_def] at hij
        simp [hij]

/-- **Common horizontal strands do not affect composability.** If `W` avoids the sources and
targets of `φ` and `ψ`, then `φ.addHorizontal W` and `ψ.addHorizontal W` have a nonzero product in
the strands algebra exactly when `φ` and `ψ` do. -/
theorem composable_addHorizontal_iff {φ ψ : StrandDiagram α} {W : Finset α}
    (hφs : Disjoint φ.source W) (hφt : Disjoint φ.target W) (hψs : Disjoint ψ.source W)
    (hψt : Disjoint ψ.target W) :
    (φ.addHorizontal W).Composable (ψ.addHorizontal W) ↔ φ.Composable ψ := by
  have htarget : (φ.addHorizontal W).target = (ψ.addHorizontal W).source ↔ φ.target = ψ.source := by
    rw [target_addHorizontal hφs, source_addHorizontal hψt]
    refine ⟨fun h ↦ ?_, fun h ↦ h ▸ rfl⟩
    ext i
    constructor <;> intro hi
    · have := h ▸ mem_union_left W hi
      exact (mem_union.1 this).resolve_right (disjoint_left.1 hφt hi)
    · have := h.symm ▸ mem_union_left W hi
      exact (mem_union.1 this).resolve_right (disjoint_left.1 hψs hi)
  rw [composable_iff, composable_iff, htarget]
  refine and_congr_right fun hφψ ↦ ?_
  rw [addHorizontal_trans_addHorizontal fun _ _ ↦ notMem_of_mem_of_disjoint_target hφt,
    inversionCount_addHorizontal hφs hφt, inversionCount_addHorizontal hψs hψt,
    inversionCount_addHorizontal (by rwa [source_trans_of_target_eq hφψ])
      (by rwa [target_trans_of_target_eq hφψ]), card_horizontalCrossings_trans hφψ hφt]
  omega

end Finite

end StrandDiagram

end TauCeti
