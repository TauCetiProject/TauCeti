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

* `Monoid.CoprodI.isConj_of_iff`, `Monoid.Coprod.isConj_inl_iff`, `Monoid.Coprod.isConj_inr_iff`:
  conjugacy in a free product restricts faithfully to each factor.
* `Monoid.CoprodI.isConj_of_of_ne`, `Monoid.Coprod.isConj_inl_inr_iff`,
  `Monoid.Coprod.isConj_inr_inl_iff`: elements of distinct factors are conjugate only when both
  are `1`.
* `Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`: a nonempty reduced word whose endpoints lie
  in distinct factors has infinite order.
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

private theorem isChain_of_append_singleton {α : Type*} {R : α → α → Prop} {b : α} :
    ∀ {mid : List α}, (mid ++ [b]).IsChain R → mid.IsChain R
  | [], _ => List.isChain_nil
  | [c], _ => List.isChain_singleton c
  | c :: d :: rest', h => by
      simp only [List.cons_append, List.isChain_cons_cons] at h ⊢
      exact ⟨h.1, isChain_of_append_singleton h.2⟩

private theorem word_prod_eq_one_or_exists_isConj_of :
    ∀ (n : ℕ) (w : Word G), w.toList.length = n → IsOfFinOrder w.prod →
      w.prod = 1 ∨ ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsOfFinOrder x ∧ IsConj w.prod (of x) := by
  classical
  intro n
  refine Nat.strongRecOn n fun n ih w hn hfin ↦ ?_
  rcases hw : w.toList with _ | ⟨a, rest⟩
  · left
    have hw0 : w = Word.empty := Word.ext hw
    simp [hw0]
  · rcases eq_or_ne rest [] with rfl | hrest
    · right
      have ha1 : a.2 ≠ 1 := w.ne_one a (by simp [hw])
      have hprod : w.prod = of a.2 := by simp [Word.prod, hw]
      have hafin : IsOfFinOrder a.2 :=
        (of_injective a.1).isOfFinOrder_iff.mp (hprod ▸ hfin)
      exact ⟨a.1, a.2, ha1, hafin, hprod ▸ IsConj.refl _⟩
    · set b := rest.getLast hrest
      set mid := rest.dropLast
      have hrest_eq : rest = mid ++ [b] := (List.dropLast_append_getLast hrest).symm
      have hw' : w.toList = a :: (mid ++ [b]) := by rw [hw, hrest_eq]
      by_cases hab : a.1 = b.1
      · rcases a with ⟨i, x⟩
        rcases b with ⟨j, y⟩
        dsimp only at hab
        subst hab
        -- `mid` cannot be empty, else `w.toList = [⟨i, x⟩, ⟨i, y⟩]` violates `chain_ne`.
        have hmid_ne : mid ≠ [] := by
          intro hmid0
          have hc := w.chain_ne
          simp [hw', hmid0] at hc
        let midWord : Word G :=
          { toList := mid
            ne_one := fun l hl ↦ w.ne_one l (by simp [hw', hl])
            chain_ne := by
              have hc := w.chain_ne
              rw [hw'] at hc
              exact isChain_of_append_singleton hc.tail }
        have hfst : midWord.fstIdx ≠ some i := by
          rcases hmid_cons : mid with _ | ⟨c, midTail⟩
          · exact False.elim (hmid_ne hmid_cons)
          · have hc := w.chain_ne
            rw [hw', hmid_cons] at hc
            have hic : i ≠ c.1 := (List.isChain_cons_cons.mp hc).1
            simp [midWord, Word.fstIdx, hmid_cons, hic.symm]
        let w' : Word G := Word.rcons ⟨y * x, midWord, hfst⟩
        have hw_prod : w.prod = of x * (midWord.prod * of y) := by
          simp [Word.prod, hw', midWord]
        have hw'_prod : w'.prod = of y * of x * midWord.prod := by
          simp [w', Word.prod_rcons, map_mul]
        have hconj : IsConj w.prod w'.prod := by
          rw [isConj_iff]
          exact ⟨of y, by simp [hw_prod, hw'_prod, mul_assoc]⟩
        have hlen_w : n = mid.length + 2 := by
          have hlen := congrArg List.length hw'
          simp only [hn, List.length_cons, List.length_append, List.length_nil, zero_add] at hlen
          omega
        have hlen_w' : w'.toList.length < n := by
          dsimp only [w', Word.rcons]
          split_ifs <;> simp [midWord, hlen_w]
        rcases ih w'.toList.length hlen_w' w' rfl (hconj.isOfFinOrder hfin) with
          hw'1 | ⟨k, z, hz1, hzfin, hconj_z⟩
        · exact Or.inl (isConj_one_left.mp (hw'1 ▸ hconj))
        · exact Or.inr ⟨k, z, hz1, hzfin, hconj.trans hconj_z⟩
      · have hw_ne : w ≠ Word.empty := by
          intro he
          simp [he, Word.empty] at hw
        obtain ⟨i, j, u, hu⟩ := NeWord.of_word w hw_ne
        have h2 : u.toList = a :: (mid ++ [b]) := (congrArg Word.toList hu).trans hw'
        have hi : i = a.1 := by
          have h1 := u.toList_head?
          simp only [h2, List.head?_cons, Option.some.injEq] at h1
          exact (congrArg Sigma.fst h1).symm
        have hj : j = b.1 := by
          have h1 := u.toList_getLast?
          have hlast : (a :: (mid ++ [b])).getLast? = some b := by
            rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (by simp : [b] ≠ []),
              List.getLast?_singleton]
          rw [h2, hlast, Option.some.injEq] at h1
          exact (congrArg Sigma.fst h1).symm
        have hij : i ≠ j := by rwa [hi, hj]
        have hup : u.prod = w.prod := congrArg Word.prod hu
        exact False.elim (u.not_isOfFinOrder_prod_of_ne hij (hup.symm ▸ hfin))

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

/-- Two elements of `M` are conjugate in `M ∗ N` if and only if they are conjugate in `M`.

Not `@[simp]`: when `M` and `N` are groups, `isConj_iff` simplifies the left-hand side. -/
theorem isConj_inl_iff {x y : M} : IsConj (inl x : M ∗ N) (inl y) ↔ IsConj x y :=
  ⟨fun h ↦ by simpa using fst.map_isConj h, (inl : M →* M ∗ N).map_isConj⟩

/-- Two elements of `N` are conjugate in `M ∗ N` if and only if they are conjugate in `N`.

Not `@[simp]`: when `M` and `N` are groups, `isConj_iff` simplifies the left-hand side. -/
theorem isConj_inr_iff {x y : N} : IsConj (inr x : M ∗ N) (inr y) ↔ IsConj x y :=
  ⟨fun h ↦ by simpa using snd.map_isConj h, (inr : N →* M ∗ N).map_isConj⟩

/-- An element of `M` and an element of `N` are conjugate in `M ∗ N` if and only if both are `1`. -/
theorem isConj_inl_inr_iff {x : M} {y : N} :
    IsConj (inl x : M ∗ N) (inr y) ↔ x = 1 ∧ y = 1 := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · have hx : IsConj x 1 := by simpa using fst.map_isConj h
    have hy : IsConj 1 y := by simpa using snd.map_isConj h
    exact ⟨isConj_one_left.mp hx, isConj_one_right.mp hy⟩
  · rintro ⟨rfl, rfl⟩
    simp

/-- An element of `N` and an element of `M` are conjugate in `M ∗ N` if and only if both are `1`. -/
theorem isConj_inr_inl_iff {x : N} {y : M} :
    IsConj (inr x : M ∗ N) (inl y) ↔ x = 1 ∧ y = 1 := by
  rw [isConj_comm, isConj_inl_inr_iff, and_comm]

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
