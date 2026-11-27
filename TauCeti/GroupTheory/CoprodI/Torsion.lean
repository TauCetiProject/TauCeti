/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.GroupTheory.CoprodI.Word
import TauCeti.GroupTheory.GraphOfGroups.BassSerre.Torsion
import TauCeti.GroupTheory.GraphOfGroups.FreeProduct

/-!
# Torsion elements in indexed free products

Every element of finite order in an indexed free product of groups `Monoid.CoprodI G` is conjugate
to an element of finite order in one of the free factors `G i`; in particular, an indexed free
product of torsion-free groups is torsion-free, and any mixed two-letter product `of x * of y` of
nontrivial elements from distinct factors has infinite order.

## Main results

* `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`: a nonempty reduced word with distinct
  endpoint indices has infinite order.
* `Monoid.CoprodI.isOfFinOrder_of_iff`, `Monoid.CoprodI.orderOf_of`: the canonical embedding
  `of : M i →* CoprodI M` preserves and reflects finite order and element orders.
* `Monoid.CoprodI.not_isOfFinOrder_of_mul_of`: in `CoprodI M`, `of x * of y` for nontrivial
  elements of distinct factors has infinite order.
* `Monoid.CoprodI.exists_isConj_of_isOfFinOrder_of_ne_one`,
  `Monoid.CoprodI.eq_one_or_exists_isConj_of_isOfFinOrder`,
  `Monoid.CoprodI.exists_isConj_of_isOfFinOrder`,
  `Monoid.CoprodI.isOfFinOrder_iff`: classification of torsion elements in `CoprodI G`.
* `Monoid.CoprodI.instIsMulTorsionFree`: an indexed free product of torsion-free groups is
  torsion-free.

## Implementation notes

The infinite-order criterion `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne` holds for
arbitrary monoids via Mathlib's reduced-word normal form `Monoid.CoprodI.Word.equiv`. For groups,
`Monoid.CoprodI.exists_isConj_of_isOfFinOrder_of_ne_one` transports the Bass–Serre finite-order
classification (`TauCeti.GraphOfGroups.π₁.exists_vertexHom_eq_of_isOfFinOrder`) across the
isomorphism `TauCeti.GraphOfGroups.coprodIEquivπ₁` with the fundamental group of the free-product
graph of groups.

## References

* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §5.1 and §6.5.
* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, Theorem 1.4.
-/

public section

namespace Monoid.CoprodI

section Monoid

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- A nonempty reduced word whose first and last letters lie in distinct factors represents an
element of infinite order in `CoprodI M`. -/
theorem NeWord.not_isOfFinOrder_prod_of_ne {i j : ι} (u : NeWord M i j) (hij : i ≠ j) :
    ¬IsOfFinOrder u.prod := by
  rw [isOfFinOrder_iff_pow_eq_one]
  rintro ⟨n, hn, hpow⟩
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hprod : (u.powSucc hij.symm k).toWord.prod = (Word.empty : Word M).prod := by
    rw [← NeWord.prod, NeWord.powSucc_prod, hpow, Word.prod_empty]
  have hempty : (u.powSucc hij.symm k).toWord = Word.empty :=
    Word.prod_injective hprod
  exact (u.powSucc hij.symm k).toList_ne_nil (congrArg Word.toList hempty)

/-- An element of `M i` has finite order in `CoprodI M` if and only if it has finite order in
`M i`. -/
@[simp]
theorem isOfFinOrder_of_iff {i : ι} {x : M i} :
    IsOfFinOrder (of x : CoprodI M) ↔ IsOfFinOrder x :=
  (of_injective i).isOfFinOrder_iff

/-- The canonical embedding `of : M i →* CoprodI M` preserves element orders. -/
@[simp]
theorem orderOf_of {i : ι} (x : M i) : orderOf (of x : CoprodI M) = orderOf x :=
  orderOf_injective of (of_injective i) x

/-- In `CoprodI M`, the product `of x * of y` of two nontrivial elements from distinct factors
`M i` and `M j` (`i ≠ j`) has infinite order. -/
theorem not_isOfFinOrder_of_mul_of {i j : ι} (hij : i ≠ j) {x : M i} {y : M j}
    (hx : x ≠ 1) (hy : y ≠ 1) : ¬IsOfFinOrder (of x * of y : CoprodI M) := by
  have hprod : ((NeWord.singleton x hx).append hij (NeWord.singleton y hy)).prod =
      of x * of y := by
    rw [NeWord.append_prod, NeWord.prod_singleton, NeWord.prod_singleton]
  rw [← hprod]
  exact ((NeWord.singleton x hx).append hij (NeWord.singleton y hy)).not_isOfFinOrder_prod_of_ne hij

end Monoid

section Group

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- Every nontrivial element of finite order in an indexed free product of groups `CoprodI G` is
conjugate to a nontrivial element of finite order in one of the factor groups `G i`. -/
theorem exists_isConj_of_isOfFinOrder_of_ne_one {g : CoprodI G}
    (hg : IsOfFinOrder g) (hg1 : g ≠ 1) :
    ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsConj g (of x) ∧ IsOfFinOrder x := by
  let e := TauCeti.GraphOfGroups.coprodIEquivπ₁ G
  obtain ⟨b, p, y, hy, hp⟩ :=
    TauCeti.GraphOfGroups.π₁.exists_vertexHom_eq_of_isOfFinOrder (e.toMonoidHom.isOfFinOrder hg)
  rcases TauCeti.SerreGraph.starRose.eq_center_or_eq_tip b with rfl | ⟨i, rfl⟩
  · have hy1 : y = 1 := Subsingleton.elim _ _
    rw [hy1, map_one] at hp
    exact absurd (e.injective (by simpa using hp.symm)) hg1
  · let y' : G i := y
    let q := (TauCeti.GraphOfGroups.dartPrefunctor
      (TauCeti.GraphOfGroups.freeProduct G PEmpty.{1})).mapPath
      ((TauCeti.SerreGraph.starRoseTree ι PEmpty).path
        (TauCeti.SerreGraph.starRose.center ι PEmpty)
        (TauCeti.SerreGraph.starRose.tip _ i))
    have hconj_π₁ : IsConj (e g) (e (of y')) := by
      change TauCeti.GraphOfGroups.π₁.vertexHom p y = e g at hp
      rw [← hp]
      dsimp only [e]
      rw [TauCeti.GraphOfGroups.coprodIEquivπ₁_of G y',
        TauCeti.GraphOfGroups.π₁.vertexHom_eq_conj_comp_apply q p y]
      exact (isConj_iff.mpr
        ⟨TauCeti.GraphOfGroups.π₁.mk (p.comp q.reverse), by simp [q, y', mul_assoc]⟩).symm
    have hconj : IsConj g (of y') := by
      simpa using e.symm.toMonoidHom.map_isConj hconj_π₁
    refine ⟨i, y', fun hy1 => hg1 ?_, hconj, hy⟩
    simpa [hy1] using hconj

/-- Every element of finite order in `CoprodI G` is either `1` or conjugate to an element of finite
order in one of the factor groups `G i`. -/
theorem eq_one_or_exists_isConj_of_isOfFinOrder {g : CoprodI G} (hg : IsOfFinOrder g) :
    g = 1 ∨ ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsConj g (of x) ∧ IsOfFinOrder x := by
  by_cases hg1 : g = 1
  · exact Or.inl hg1
  · exact Or.inr (exists_isConj_of_isOfFinOrder_of_ne_one hg hg1)

/-- In a nonempty indexed free product `CoprodI G`, every element of finite order is conjugate to an
element of finite order in one of the factor groups `G i`. -/
theorem exists_isConj_of_isOfFinOrder [Nonempty ι] {g : CoprodI G} (hg : IsOfFinOrder g) :
    ∃ (i : ι) (x : G i), IsConj g (of x) ∧ IsOfFinOrder x := by
  rcases eq_one_or_exists_isConj_of_isOfFinOrder hg with rfl | ⟨i, x, -, hconj, hx⟩
  · obtain ⟨i⟩ := ‹Nonempty ι›
    exact ⟨i, 1, by simp, .one⟩
  · exact ⟨i, x, hconj, hx⟩

/-- An element of `CoprodI G` has finite order if and only if it is `1` or conjugate to an element
of finite order in some factor `G i`. -/
theorem isOfFinOrder_iff {g : CoprodI G} :
    IsOfFinOrder g ↔ g = 1 ∨ ∃ (i : ι) (x : G i), IsConj g (of x) ∧ IsOfFinOrder x := by
  refine ⟨fun hg => ?_, ?_⟩
  · rcases eq_one_or_exists_isConj_of_isOfFinOrder hg with rfl | ⟨i, x, -, hconj, hx⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨i, x, hconj, hx⟩
  · rintro (rfl | ⟨i, x, hconj, hx⟩)
    · exact .one
    · exact hconj.symm.isOfFinOrder (of.isOfFinOrder hx)

/-- An indexed free product of torsion-free groups is torsion-free. -/
instance instIsMulTorsionFree [∀ i, IsMulTorsionFree (G i)] : IsMulTorsionFree (CoprodI G) := by
  refine .of_not_isOfFinOrder fun g hg1 hg => ?_
  obtain ⟨i, x, hx1, -, hx_fin⟩ := exists_isConj_of_isOfFinOrder_of_ne_one hg hg1
  exact isMulTorsionFree_iff_not_isOfFinOrder.mp inferInstance hx1 hx_fin

end Group

end Monoid.CoprodI
