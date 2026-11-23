/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.CoprodI
public import Mathlib.GroupTheory.OrderOfElement
import TauCeti.Algebra.Group.Conj
import TauCeti.GroupTheory.CoprodI.Word

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

The torsion classification on `CoprodI G` uses Mathlib's reduced-word normal form
`Monoid.CoprodI.Word.equiv`. A reduced word of length at least `2` whose first and last letters lie
in distinct factors has no cancellation between adjacent copies, so all of its positive powers are
nonempty reduced words (`Monoid.CoprodI.NeWord.not_isOfFinOrder_prod_of_ne`). When the first and
last letters lie in the same factor `G i`, conjugating by the inverse of the first letter and taking
the inverse merges those two letters into a strictly shorter reduced word.

## References

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

/-- Cyclic reduction step: if a reduced word `Word.cons a v hfv ha1` with `v` nonempty represents an
element of finite order, its first and last letters lie in the same factor `G i`, so conjugating by
`(of a)⁻¹` and inverting yields a strictly shorter reduced word `w'`. -/
private theorem exists_word_length_lt_of_cons
    {i : ι} (a : G i) (v : Word G) (hfv : v.fstIdx ≠ some i) (ha1 : a ≠ 1)
    (hv : v ≠ Word.empty) (hg : IsOfFinOrder (Word.cons a v hfv ha1).prod) :
    ∃ w' : Word G,
      w'.toList.length < (Word.cons a v hfv ha1).toList.length ∧
        IsConj (Word.cons a v hfv ha1).prod w'.prod⁻¹ := by
  classical
  let w : Word G := Word.cons a v hfv ha1
  have hw_ne : w ≠ Word.empty := fun h => List.cons_ne_nil _ _ (congrArg Word.toList h)
  obtain ⟨i₀, j₀, u, hu⟩ := NeWord.of_word w hw_ne
  have hij : i₀ = j₀ := by
    by_contra hne
    exact u.not_isOfFinOrder_prod_of_ne hne (by rwa [NeWord.prod, hu])
  subst hij
  have hi₀ : i = i₀ :=
    Option.some.inj ((Word.fstIdx_cons a v hfv ha1).symm.trans
      ((congrArg Word.fstIdx hu).symm.trans u.fstIdx_toWord))
  subst i₀
  obtain ⟨k, j, q, hq⟩ := NeWord.of_word v hv
  have hj : j = i := by
    have h₁ := q.toWord_getLast?_map_fst
    have h₂ := u.toWord_getLast?_map_fst
    rw [hq] at h₁
    rw [hu, Word.getLast?_map_fst_cons_of_ne_empty a hfv ha1 hv, h₁] at h₂
    exact Option.some.inj h₂
  subst j
  let z : Word G := q.inv.toWord
  let w' : Word G := of a⁻¹ • z
  have hz_fst : z.fstIdx = some i := q.inv.fstIdx_toWord
  have hw'_len : w'.toList.length < w.toList.length := by
    have hle : w'.toList.length ≤ z.toList.length :=
      Word.length_toList_of_smul_le_of_fstIdx_eq a⁻¹ hz_fst
    have hz_len : z.toList.length = v.toList.length := by
      rw [← hq]
      exact q.length_toList_inv
    exact (hz_len ▸ hle).trans_lt (by simp [w])
  refine ⟨w', hw'_len, isConj_iff.mpr ⟨(of a)⁻¹, ?_⟩⟩
  have hz_prod : z.prod = v.prod⁻¹ := by
    rw [← hq, ← NeWord.prod, ← NeWord.prod, NeWord.inv_prod]
  rw [Word.prod_cons, Word.prod_smul, hz_prod]
  simp

/-- Every nontrivial element of finite order in an indexed free product of groups `CoprodI G` is
conjugate to a nontrivial element of finite order in one of the factor groups `G i`. -/
theorem exists_isConj_of_isOfFinOrder_of_ne_one {g : CoprodI G}
    (hg : IsOfFinOrder g) (hg1 : g ≠ 1) :
    ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsConj g (of x) ∧ IsOfFinOrder x := by
  classical
  suffices ∀ n : ℕ, ∀ w : Word G, w.toList.length = n →
      IsOfFinOrder w.prod → w.prod ≠ 1 →
      ∃ (i : ι) (x : G i), x ≠ 1 ∧ IsConj w.prod (of x) ∧ IsOfFinOrder x by
    have hprod : (Word.equiv g).prod = g := Word.equiv.symm_apply_apply g
    simpa [hprod] using this _ (Word.equiv g) rfl (hprod.symm ▸ hg) (hprod.symm ▸ hg1)
  intro n
  induction n using Nat.strong_induction_on with
  | ind n ih =>
    intro w hlen hg hg1
    revert hlen hg hg1
    refine Word.consRecOn w ?_ ?_
    · intro _ _ hg1
      exact (hg1 Word.prod_empty).elim
    · intro i a v hfv ha1 _ hlen hg hg1
      by_cases hv : v = Word.empty
      · subst hv
        rw [Word.prod_cons, Word.prod_empty, mul_one] at hg ⊢
        exact ⟨i, a, ha1, IsConj.refl _, isOfFinOrder_of_iff.mp hg⟩
      · obtain ⟨w', hw'_lt, hconj_inv⟩ := exists_word_length_lt_of_cons a v hfv ha1 hv hg
        have hw'_fin : IsOfFinOrder w'.prod :=
          isOfFinOrder_inv_iff.mp (hconj_inv.isOfFinOrder hg)
        have hw'_ne : w'.prod ≠ 1 := fun h1 =>
          hg1 (isConj_one_left.mp (by simpa [h1] using hconj_inv))
        obtain ⟨r, y, hy1, hconj_y, hy_fin⟩ :=
          ih w'.toList.length (hlen ▸ hw'_lt) w' rfl hw'_fin hw'_ne
        refine ⟨r, y⁻¹, inv_ne_one.mpr hy1, ?_, isOfFinOrder_inv_iff.mpr hy_fin⟩
        rw [map_inv]
        exact hconj_inv.trans (TauCeti.isConj_inv_iff.mpr hconj_y)

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
