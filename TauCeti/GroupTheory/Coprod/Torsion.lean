/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement
import Mathlib.Algebra.Group.ULift
import TauCeti.GroupTheory.CoprodI

/-!
# Conjugacy on factors and torsion in free products

In a free product of monoids, the canonical retractions onto the factors separate conjugacy: two
elements of the same factor are conjugate in the free product if and only if they are conjugate in
that factor, while elements of distinct factors are conjugate only when both are `1`. Furthermore,
any nonempty reduced word whose first and last letters lie in distinct factors is cyclically
reduced of length at least `2`, so its powers concatenate without boundary cancellation and hence
it has infinite order.

When the factors are groups, combining boundary conjugation with this infinite-order obstruction
classifies all elements of finite order in a free product: every torsion element of `CoprodI G`
(respectively `G ∗ H`) is either `1` or conjugate to a nonidentity torsion element of a single
factor, of the same order.

## Main results

* `Monoid.CoprodI.isConj_of_iff`: conjugacy in an indexed free product restricts faithfully to each
  factor (see `TauCeti.GroupTheory.Coprod.Conj` for the binary free product).
* `Monoid.CoprodI.isConj_of_of_ne`, `Monoid.CoprodI.eq_of_isConj_of`: elements of distinct factors
  of an indexed free product are conjugate only when both are `1`.
* `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`: a nonempty reduced word whose endpoints lie
  in distinct factors has infinite order.
* `Monoid.CoprodI.NeWord.exists_isConj_length_lt`: a nonempty reduced word of length at least `2`
  whose endpoints lie in the same factor is conjugate to a strictly shorter reduced word.
* `Monoid.CoprodI.eq_one_or_exists_isConj_of_of_isOfFinOrder`, `Monoid.CoprodI.isOfFinOrder_iff`,
  `Monoid.CoprodI.orderOf_eq_iff`: classification of finite-order elements and elements of given
  finite order `n > 1` in an indexed free product of groups.
* `Monoid.Coprod.not_isOfFinOrder_inl_mul_inr`, `Monoid.Coprod.orderOf_inl_mul_inr_eq_zero`: the
  product of two nonidentity elements from distinct factors of `M ∗ N` has infinite order.
* `Monoid.Coprod.isOfFinOrder_iff`, `Monoid.Coprod.orderOf_eq_iff`: the corresponding
  classifications for a binary free product `G ∗ H` of groups.

## References

* R. C. Lyndon, P. E. Schupp, *Combinatorial Group Theory*, Springer, 1977, Chapter IV, §1,
  Theorem 1.4.
* J.-P. Serre, *Trees*, Springer, 1980, Chapter I, §4.2, Corollary 1.
-/

public section

open scoped Monoid.Coprod

namespace Monoid.CoprodI

section Monoid

variable {ι : Type*} {M : ι → Type*} [∀ i, Monoid (M i)]

/-- Two elements of the same factor `M i` are conjugate in `CoprodI M` if and only if they are
conjugate in `M i`.

Not `@[simp]`: when the factors are groups, `isConj_iff` simplifies the left-hand side. -/
theorem isConj_of_iff {i : ι} {x y : M i} :
    IsConj (of x : CoprodI M) (of y) ↔ IsConj x y := by
  refine ⟨fun h ↦ ?_, of.map_isConj⟩
  classical
  simpa using (lift (Pi.mulSingle i (.id (M i)))).map_isConj h

/-- Elements from distinct factors of `CoprodI M` are conjugate if and only if both are `1`. -/
theorem isConj_of_of_ne {i j : ι} (hij : i ≠ j) {x : M i} {y : M j} :
    IsConj (of x : CoprodI M) (of y) ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · classical
    have hx : IsConj x 1 := by
      simpa [Pi.mulSingle_eq_of_ne hij.symm] using
        (lift (Pi.mulSingle i (.id (M i)))).map_isConj h
    have hy : IsConj 1 y := by
      simpa [Pi.mulSingle_eq_of_ne hij] using
        (lift (Pi.mulSingle j (.id (M j)))).map_isConj h
    exact ⟨isConj_one_left.mp hx, isConj_one_right.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- If a nonidentity element of `M i` is conjugate in `CoprodI M` to an element of `M j`, then
`i = j`. -/
theorem eq_of_isConj_of {i j : ι} {x : M i} {y : M j} (hx : x ≠ 1)
    (h : IsConj (of x : CoprodI M) (of y)) : i = j := by
  by_contra hij
  exact hx ((isConj_of_of_ne hij).mp h).1

namespace NeWord

/-- The `(n + 1)`-fold reduced concatenation of a `NeWord M i j` with `i ≠ j`. -/
private def npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) : ℕ → NeWord M i j
  | 0 => w
  | n + 1 => append w hij.symm (npowSucc hij w n)

private theorem prod_npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    ∀ n : ℕ, (npowSucc hij w n).prod = w.prod ^ (n + 1)
  | 0 => (pow_one w.prod).symm
  | n + 1 => by rw [npowSucc, append_prod, prod_npowSucc hij w n, ← pow_succ']

private theorem length_toList_npowSucc {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    ∀ n : ℕ, (npowSucc hij w n).toList.length = (n + 1) * w.toList.length
  | 0 => (one_mul _).symm
  | n + 1 => by
      rw [npowSucc, toList, List.length_append, length_toList_npowSucc hij w n,
        Nat.add_mul (n + 1) 1 w.toList.length, one_mul, add_comm]

/-- A nonempty reduced word whose first and last letters lie in distinct factors has injective
power map `n ↦ w.prod ^ n`: adjacent copies of `w` do not cancel at their boundary. -/
theorem injective_pow_prod_of_ne {i j : ι} (hij : i ≠ j) (w : NeWord M i j) :
    Function.Injective (w.prod ^ · : ℕ → CoprodI M) := by
  classical
  have hlen : ∀ n : ℕ, (Word.equiv (w.prod ^ n)).toList.length = n * w.toList.length := by
    rintro (_ | n)
    · have hemp : Word.equiv (1 : CoprodI M) = Word.empty :=
        Word.equiv.symm.injective (by simp [Word.equiv])
      simp [hemp]
    · have heq : Word.equiv (w.prod ^ (n + 1)) = (npowSucc hij w n).toWord := by
        apply Word.equiv.symm.injective
        simpa [Word.equiv, NeWord.prod] using (prod_npowSucc hij w n).symm
      rw [heq]
      exact length_toList_npowSucc hij w n
  have hpos : 0 < w.toList.length := List.length_pos_iff.mpr w.toList_ne_nil
  intro m n (hmn : w.prod ^ m = w.prod ^ n)
  exact Nat.eq_of_mul_eq_mul_right hpos ((hlen m).symm.trans (by rw [hmn, hlen n]))

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
    have hpos : 0 < u.toList.length := List.length_pos_iff.mpr u.toList_ne_nil
    by_cases h1 : u.toList.length = 1
    · right
      obtain ⟨a, ha⟩ := List.length_eq_one_iff.mp h1
      have ha1 : a.2 ≠ 1 := u.toWord.ne_one a (by simp [NeWord.toWord, ha])
      have hprod : u.toWord.prod = of a.2 := by simp [Word.prod, NeWord.toWord, ha]
      have hafin : IsOfFinOrder a.2 := (of_injective a.1).isOfFinOrder_iff.mp (hprod ▸ hfin)
      exact ⟨a.1, a.2, ha1, hafin, hprod ▸ IsConj.refl _⟩
    · by_cases hij : i = j
      · subst hij
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
  classical
  have hprod : (Word.equiv g).prod = g := Word.equiv.symm_apply_apply g
  simpa only [hprod] using
    word_prod_eq_one_or_exists_isConj_of (Word.equiv g).toList.length (Word.equiv g) rfl
      (hprod.symm ▸ hg)

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

namespace Monoid.Coprod

section Monoid

private abbrev FinTwoFamily (M : Type u₁) (N : Type u₂) : Fin 2 → Type (max u₁ u₂)
  | ⟨0, _⟩ => ULift.{u₂} M
  | ⟨1, _⟩ => ULift.{u₁} N

private instance instMonoidFinTwoFamily (M : Type u₁) (N : Type u₂) [Monoid M] [Monoid N] :
    ∀ i, Monoid (FinTwoFamily M N i)
  | ⟨0, _⟩ => inferInstanceAs (Monoid (ULift.{u₂} M))
  | ⟨1, _⟩ => inferInstanceAs (Monoid (ULift.{u₁} N))

private def finTwoFamilyEquivCoprod (M : Type u₁) (N : Type u₂) [Monoid M] [Monoid N] :
    CoprodI (FinTwoFamily M N) ≃* M ∗ N :=
  (CoprodI.finTwoEquivCoprod (FinTwoFamily M N)).trans
    (MulEquiv.coprodCongr MulEquiv.ulift MulEquiv.ulift)

private theorem finTwoFamilyEquivCoprod_of_zero (M : Type u₁) (N : Type u₂)
    [Monoid M] [Monoid N] (x : FinTwoFamily M N 0) :
    finTwoFamilyEquivCoprod M N (CoprodI.of (i := 0) x) = inl x.down := by
  simp [finTwoFamilyEquivCoprod]
  rfl

private theorem finTwoFamilyEquivCoprod_of_one (M : Type u₁) (N : Type u₂)
    [Monoid M] [Monoid N] (y : FinTwoFamily M N 1) :
    finTwoFamilyEquivCoprod M N (CoprodI.of (i := 1) y) = inr y.down := by
  simp [finTwoFamilyEquivCoprod]
  rfl

variable {M : Type u₁} {N : Type u₂} [Monoid M] [Monoid N]

/-- In `M ∗ N`, the product `inl x * inr y` of two nonidentity elements from distinct factors does
not have finite order. -/
theorem not_isOfFinOrder_inl_mul_inr {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    ¬ IsOfFinOrder (inl x * inr y : M ∗ N) := by
  let x' : FinTwoFamily M N 0 := ULift.up.{u₂} x
  let y' : FinTwoFamily M N 1 := ULift.up.{u₁} y
  have hx' : x' ≠ 1 := fun h ↦ hx (congrArg ULift.down h)
  have hy' : y' ≠ 1 := fun h ↦ hy (congrArg ULift.down h)
  let w : CoprodI.NeWord (FinTwoFamily M N) 0 1 :=
    .append (.singleton x' hx') (by decide) (.singleton y' hy')
  have hw : finTwoFamilyEquivCoprod M N w.prod = inl x * inr y := by
    rw [CoprodI.NeWord.append_prod, CoprodI.NeWord.prod_singleton,
      CoprodI.NeWord.prod_singleton, map_mul, finTwoFamilyEquivCoprod_of_zero,
      finTwoFamilyEquivCoprod_of_one]
  intro hfin
  exact w.not_isOfFinOrder_prod_of_ne (by decide)
    (((finTwoFamilyEquivCoprod M N).injective.isOfFinOrder_iff
      (f := (finTwoFamilyEquivCoprod M N).toMonoidHom)).mp (by simpa [hw] using hfin))

/-- In `M ∗ N`, the product `inl x * inr y` of two nonidentity elements from distinct factors has
infinite order (`orderOf = 0`). -/
theorem orderOf_inl_mul_inr_eq_zero {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    orderOf (inl x * inr y : M ∗ N) = 0 :=
  orderOf_eq_zero (not_isOfFinOrder_inl_mul_inr hx hy)

/-- In `M ∗ N`, the product `inr y * inl x` of two nonidentity elements from distinct factors has
infinite order (`orderOf = 0`). -/
theorem orderOf_inr_mul_inl_eq_zero {x : M} {y : N} (hx : x ≠ 1) (hy : y ≠ 1) :
    orderOf (inr y * inl x : M ∗ N) = 0 := by
  let e : M ∗ N ≃* N ∗ M := MulEquiv.coprodComm M N
  rw [← orderOf_injective e.toMonoidHom e.injective]
  simpa [e] using orderOf_inl_mul_inr_eq_zero hy hx

end Monoid

section Group

private abbrev BoolFamily (G : Type u₁) (H : Type u₂) : Bool → Type (max u₁ u₂)
  | false => ULift.{u₂} G
  | true => ULift.{u₁} H

private instance instGroupBoolFamily (G : Type u₁) (H : Type u₂) [Group G] [Group H] :
    ∀ b, Group (BoolFamily G H b)
  | false => inferInstanceAs (Group (ULift.{u₂} G))
  | true => inferInstanceAs (Group (ULift.{u₁} H))

private def boolFamilyEquivCoprod (G : Type u₁) (H : Type u₂) [Group G] [Group H] :
    CoprodI (BoolFamily G H) ≃* G ∗ H :=
  (CoprodI.boolEquivCoprod (BoolFamily G H)).trans
    (MulEquiv.coprodCongr MulEquiv.ulift MulEquiv.ulift)

private theorem boolFamilyEquivCoprod_of_false (G : Type u₁) (H : Type u₂) [Group G] [Group H]
    (x : BoolFamily G H false) :
    boolFamilyEquivCoprod G H (CoprodI.of (i := false) x) = inl x.down := by
  simp [boolFamilyEquivCoprod]
  rfl

private theorem boolFamilyEquivCoprod_of_true (G : Type u₁) (H : Type u₂) [Group G] [Group H]
    (x : BoolFamily G H true) :
    boolFamilyEquivCoprod G H (CoprodI.of (i := true) x) = inr x.down := by
  simp [boolFamilyEquivCoprod]
  rfl

variable {G : Type u₁} {H : Type u₂} [Group G] [Group H]

/-- **Torsion in a binary free product of groups.** An element of `G ∗ H` has finite order if and
only if it is conjugate to `inl x` for a finite-order element `x : G` or to `inr y` for a
finite-order element `y : H`. -/
theorem isOfFinOrder_iff {g : G ∗ H} :
    IsOfFinOrder g ↔
      (∃ x : G, IsOfFinOrder x ∧ IsConj g (inl x)) ∨
        (∃ y : H, IsOfFinOrder y ∧ IsConj g (inr y)) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · let e := boolFamilyEquivCoprod G H
    have hg' : IsOfFinOrder (e.symm g) :=
      (e.symm.injective.isOfFinOrder_iff (f := e.symm.toMonoidHom)).mpr hg
    rcases CoprodI.eq_one_or_exists_isConj_of_of_isOfFinOrder hg' with h1 | ⟨b, x, -, hx, hconj⟩
    · have hg1 : g = 1 := e.symm.injective (by simpa using h1)
      exact Or.inl ⟨1, IsOfFinOrder.one, by simp [hg1]⟩
    · cases b
      · refine Or.inl ⟨x.down, (MulEquiv.ulift : ULift.{u₂} G ≃* G).toMonoidHom.isOfFinOrder hx, ?_⟩
        have hc := e.toMonoidHom.map_isConj hconj
        rw [MulEquiv.coe_toMonoidHom, e.apply_symm_apply,
          boolFamilyEquivCoprod_of_false G H x] at hc
        exact hc
      · refine Or.inr ⟨x.down, (MulEquiv.ulift : ULift.{u₁} H ≃* H).toMonoidHom.isOfFinOrder hx, ?_⟩
        have hc := e.toMonoidHom.map_isConj hconj
        rw [MulEquiv.coe_toMonoidHom, e.apply_symm_apply,
          boolFamilyEquivCoprod_of_true G H x] at hc
        exact hc
  · rintro (⟨x, hx, hconj⟩ | ⟨y, hy, hconj⟩)
    · exact hconj.symm.isOfFinOrder ((inl : G →* G ∗ H).isOfFinOrder hx)
    · exact hconj.symm.isOfFinOrder ((inr : H →* G ∗ H).isOfFinOrder hy)

/-- For `1 < n`, an element of `G ∗ H` has order `n` if and only if it is conjugate to `inl x` for
some `x : G` of order `n` or to `inr y` for some `y : H` of order `n`. -/
theorem orderOf_eq_iff {g : G ∗ H} {n : ℕ} (hn : 1 < n) :
    orderOf g = n ↔
      (∃ x : G, orderOf x = n ∧ IsConj g (inl x)) ∨
        (∃ y : H, orderOf y = n ∧ IsConj g (inr y)) := by
  refine ⟨fun hg ↦ ?_, ?_⟩
  · have hfin : IsOfFinOrder g := orderOf_pos_iff.mp (by omega)
    rcases isOfFinOrder_iff.mp hfin with ⟨x, -, hconj⟩ | ⟨y, -, hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inl ⟨x, by rw [← orderOf_injective (inl : G →* G ∗ H) inl_injective x,
        ← hc.orderOf_eq, hg], hconj⟩
    · let ⟨_, hc⟩ := hconj
      exact Or.inr ⟨y, by rw [← orderOf_injective (inr : H →* G ∗ H) inr_injective y,
        ← hc.orderOf_eq, hg], hconj⟩
  · rintro (⟨x, hx, ⟨_, hc⟩⟩ | ⟨y, hy, ⟨_, hc⟩⟩)
    · rw [hc.orderOf_eq, orderOf_injective (inl : G →* G ∗ H) inl_injective x, hx]
    · rw [hc.orderOf_eq, orderOf_injective (inr : H →* G ∗ H) inr_injective y, hy]

end Group

end Monoid.Coprod
