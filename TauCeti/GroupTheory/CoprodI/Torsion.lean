/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.OrderOfElement
public import TauCeti.GroupTheory.CoprodI.Word

/-!
# Torsion in indexed free products

Any nonempty reduced word in `Monoid.CoprodI M` whose first and last letters lie in distinct
factors is cyclically reduced of length at least `2`, so its powers concatenate without boundary
cancellation (`Monoid.CoprodI.NeWord.injective_pow_prod_of_ne`) and hence it has infinite order.

When the factors are groups, combining boundary conjugation (`NeWord.exists_isConj_length_lt`) with
this infinite-order obstruction classifies all elements of finite order in `Monoid.CoprodI G`:
every torsion element is either `1` or conjugate to a nonidentity torsion element of a single
factor, of the same order.

## Main results

* `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`,
  `Monoid.CoprodI.NeWord.orderOf_prod_eq_zero_of_ne`: a nonempty reduced word whose endpoints lie
  in distinct factors has infinite order.
* `Monoid.CoprodI.NeWord.exists_isConj_length_lt`: a nonempty reduced word of length at least `2`
  whose endpoints lie in the same factor is conjugate to a strictly shorter reduced word.
* `Monoid.CoprodI.eq_one_or_exists_isConj_of_of_isOfFinOrder`, `Monoid.CoprodI.isOfFinOrder_iff`,
  `Monoid.CoprodI.orderOf_eq_iff`: classification of finite-order elements and elements of given
  finite order `n > 1` in an indexed free product of groups.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1,
  Theorem 1.4.
* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §4.2, Corollary 1.
-/

public section

namespace Monoid.CoprodI

section Monoid

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

namespace NeWord

/-- A nonempty reduced word whose first and last letters lie in distinct factors has infinite
order in `CoprodI M`. -/
theorem not_isOfFinOrder_prod_of_ne {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    ¬ IsOfFinOrder w.prod :=
  not_isOfFinOrder_of_injective_pow (injective_pow_prod_of_ne hij w)

/-- The `orderOf` a nonempty reduced word with distinct endpoint factors is `0`. -/
@[simp]
theorem orderOf_prod_eq_zero_of_ne {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    orderOf w.prod = 0 :=
  orderOf_eq_zero (not_isOfFinOrder_prod_of_ne hij w)

end NeWord

end Monoid

section Group

variable {ι : Type*} {G : ι → Type*} [∀ i, Group (G i)]

/-- **Cyclic reduction step.** If a nonempty reduced word `u : NeWord G i i` has length at least
`2` and starts and ends in the same factor `G i`, then conjugating by its last letter merges the
endpoints into a strictly shorter reduced word `w`. -/
theorem NeWord.exists_isConj_length_lt {i : ι} (u : NeWord G i i) (hu : 1 < u.toList.length) :
    ∃ w : Word G, IsConj u.prod w.prod ∧ w.toList.length < u.toList.length := by
  classical
  rcases hu_cons : u.toList with _ | ⟨a, rest⟩
  · exact absurd hu_cons u.toList_ne_nil
  · have hrest : rest ≠ [] := by
      rintro rfl
      simp [hu_cons] at hu
    set b := rest.getLast hrest
    set mid := rest.dropLast
    have hlist : u.toList = a :: (mid ++ [b]) := by
      rw [hu_cons, List.dropLast_append_getLast hrest]
    have ha : a = ⟨i, u.head⟩ := by
      simpa [hlist] using u.toList_head?
    have hb : b = ⟨i, u.last⟩ := by
      have hlast : (a :: (mid ++ [b])).getLast? = some b := by
        rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp : [b] ≠ []),
          List.getLast?_singleton]
      simpa [hlist, hlast] using u.toList_getLast?
    rw [ha, hb] at hlist
    have hchain :
        List.IsChain (fun p q ↦ p.1 ≠ q.1) (⟨i, u.head⟩ :: (mid ++ [⟨i, u.last⟩])) := by
      simpa [NeWord.toWord, hlist] using u.toWord.chain_ne
    have hmid_ne : mid ≠ [] := by
      intro hmid0
      simp [hmid0] at hchain
    let midWord : Word G :=
      { toList := mid
        ne_one := fun l hl ↦ u.toWord.ne_one l (by simp [NeWord.toWord, hlist, hl])
        chain_ne := hchain.tail.left_of_append }
    have hfst : midWord.fstIdx ≠ some i := by
      rcases hmid_cons : mid with _ | ⟨c, midTail⟩
      · exact False.elim (hmid_ne hmid_cons)
      · rw [hmid_cons] at hchain
        have hic : i ≠ c.1 := (List.isChain_cons_cons.mp hchain).1
        simp [midWord, Word.fstIdx, hmid_cons, hic.symm]
    let w : Word G := Word.rcons ⟨u.last * u.head, midWord, hfst⟩
    have hu_prod : u.prod = of u.head * (midWord.prod * of u.last) := by
      simp [NeWord.prod, Word.prod, NeWord.toWord, hlist, midWord]
    have hw_prod : w.prod = of u.last * of u.head * midWord.prod := by
      simp [w, Word.prod_rcons, map_mul]
    refine ⟨w, isConj_iff.mpr ⟨of u.last, by simp [hu_prod, hw_prod, mul_assoc]⟩, ?_⟩
    have hlen : u.toList.length = mid.length + 2 := by
      simp [hlist]
    rw [← hu_cons, hlen]
    dsimp only [w, Word.rcons]
    split_ifs <;> simp [midWord]

private theorem word_prod_eq_one_or_exists_isConj_of :
    ∀ (n : ℕ) (w : Word G), w.toList.length = n → IsOfFinOrder w.prod →
      w.prod = 1 ∨ ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsOfFinOrder x ∧ IsConj w.prod (of x) := by
  intro n
  refine Nat.strongRecOn n fun n ih w hn hfin ↦ ?_
  by_cases hw : w = Word.empty
  · exact Or.inl (by simp [hw])
  · obtain ⟨i, j, u, rfl⟩ := NeWord.of_word w hw
    have hlen : u.toList.length = n := by simpa [NeWord.toWord] using hn
    by_cases h1 : u.toList.length = 1
    · right
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      have ha1 : a.2 ≠ 1 := u.toWord.ne_one a (by simp [NeWord.toWord, ha])
      have hprod : u.toWord.prod = of a.2 := by simp [Word.prod, NeWord.toWord, ha]
      have hafin : IsOfFinOrder a.2 := (of_injective a.1).isOfFinOrder_iff.mp (hprod ▸ hfin)
      exact ⟨a.1, a.2, ha1, hafin, hprod ▸ IsConj.refl _⟩
    · by_cases hij : i = j
      · subst hij
        have hpos : 0 < u.toList.length := List.length_pos_iff.mpr u.toList_ne_nil
        obtain ⟨w', hconj, hlt⟩ := u.exists_isConj_length_lt (by omega)
        rw [NeWord.prod] at hconj
        rcases ih w'.toList.length (hlen ▸ hlt) w' rfl (hconj.isOfFinOrder hfin) with
          hw'1 | ⟨k, z, hz1, hzfin, hconj_z⟩
        · exact Or.inl (isConj_one_left.mp (hw'1 ▸ hconj))
        · exact Or.inr ⟨k, z, hz1, hzfin, hconj.trans hconj_z⟩
      · exact False.elim (u.not_isOfFinOrder_prod_of_ne hij hfin)

/-- **Torsion in an indexed free product of groups.** Every element of finite order in `CoprodI G`
is either `1` or conjugate to `of x` for a nonidentity element `x` of finite order in some factor
`G i`. -/
theorem eq_one_or_exists_isConj_of_of_isOfFinOrder {g : CoprodI G} (hg : IsOfFinOrder g) :
    g = 1 ∨ ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsOfFinOrder x ∧ IsConj g (of x) := by
  obtain ⟨w, rfl⟩ := Word.prod_surjective g
  exact word_prod_eq_one_or_exists_isConj_of w.toList.length w rfl hg

/-- An element of `CoprodI G` has finite order if and only if it is `1` or conjugate to `of x` for
a nonidentity finite-order element `x` of some factor `G i`. -/
theorem isOfFinOrder_iff {g : CoprodI G} :
    IsOfFinOrder g ↔ g = 1 ∨ ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsOfFinOrder x ∧ IsConj g (of x) := by
  refine ⟨eq_one_or_exists_isConj_of_of_isOfFinOrder, ?_⟩
  rintro (rfl | ⟨i, x, -, hx, hconj⟩)
  · exact IsOfFinOrder.one
  · exact hconj.symm.isOfFinOrder (of.isOfFinOrder hx)

/-- For `1 < n`, an element of `CoprodI G` has order `n` if and only if it is conjugate to `of x`
for an element `x` of order `n` in some factor `G i`. -/
theorem orderOf_eq_iff {g : CoprodI G} {n : ℕ} (hn : 1 < n) :
    orderOf g = n ↔ ∃ (i : ι) (x : G i), orderOf x = n ∧ IsConj g (of x) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases eq_one_or_exists_isConj_of_of_isOfFinOrder hfin with rfl | ⟨i, x, -, -, hconj⟩
    · simp at hg
      omega
    · let ⟨_, hc⟩ := hconj
      refine ⟨i, x, ?_, hconj⟩
      rw [← orderOf_injective of (of_injective i) x, ← hc.orderOf_eq, hg]
  · rintro ⟨i, x, hx, ⟨_, hc⟩⟩
    rw [hc.orderOf_eq, orderOf_injective of (of_injective i) x, hx]

end Group

end Monoid.CoprodI
