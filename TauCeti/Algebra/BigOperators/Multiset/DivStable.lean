/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Int.Even
import Mathlib.Tactic.Ring

/-!
# Multisets stable under `x ↦ c / x`

Let `S` be a multiset of nonzero elements of a field which is stable under the involution
`x ↦ c / x`, that is `S.map (c / ·) = S`, and let `s * s = c`. The fixed points of the involution
are `s` and `-s`, and the other elements of `S` come in pairs `{x, c / x}` whose product is
`c = s * s`. Hence

* `S.prod = (-1) ^ count (-s) S * s ^ card S`
  (`Multiset.prod_eq_neg_one_pow_count_mul_pow_card_of_map_div_eq`), in any characteristic;
* if `2 ≠ 0`, so that `s ≠ -s`, the number `card S - count s S - count (-s) S` of elements other
  than `±s` is even (`Multiset.even_card_sub_count_sub_count_of_map_div_eq`). In characteristic
  two this fails: `S = {s}` has `card S - count s S - count (-s) S = -1`.

The main example is the multiset of eigenvalues, with algebraic multiplicity, of a similitude of
multiplier `c` of a nondegenerate bilinear form: it is stable under `x ↦ c / x`, which gives the
determinant of the similitude up to the sign `(-1) ^ count (-s) S`.

## References

* P. Deligne, *La conjecture de Weil. I*, Publ. Math. IHÉS 43 (1974), (2.6).
-/

public section

namespace Multiset

variable {K : Type*} [Field K] {c s : K}

/-- **Induction on a multiset stable under `x ↦ c / x`.** A multiset of nonzero elements stable
under `x ↦ c / x` is built from `0` by adding fixed points `a` of the involution (`a * a = c`) and
pairs `{a, c / a}` of distinct elements. -/
private theorem induction_of_map_div_eq {P : Multiset K → Prop} (zero : P 0)
    (fixed : ∀ a T, a ≠ 0 → a * a = c → P T → P (a ::ₘ T))
    (pair : ∀ a T, a ≠ 0 → c ≠ 0 → a * a ≠ c → P T → P (a ::ₘ c / a ::ₘ T)) :
    ∀ S : Multiset K, S.map (c / ·) = S → (0 : K) ∉ S → P S := by
  classical
  intro S
  induction hn : card S using Nat.strong_induction_on generalizing S with
  | _ n ih =>
  intro hS h0
  rcases S.empty_or_exists_mem with rfl | ⟨a, ha⟩
  · exact zero
  have ha0 : a ≠ 0 := fun h ↦ h0 (h ▸ ha)
  have hca : c / a ∈ S := hS ▸ mem_map_of_mem (c / ·) ha
  -- For `c = 0` the element `c / a = 0` would lie in `S`.
  have hc : c ≠ 0 := fun hc ↦ h0 (by simpa [hc] using hca)
  have hinv : Function.Involutive (c / · : K → K) := fun x ↦ div_div_cancel₀ hc
  have herase : (S.erase a).map (c / ·) = S.erase (c / a) := by
    rw [map_erase _ hinv.injective, hS]
  have hcard : card (S.erase a) < n := hn ▸ card_erase_lt_of_mem ha
  have h0a : (0 : K) ∉ S.erase a := fun h ↦ h0 (mem_of_mem_erase h)
  by_cases hfix : c / a = a
  · rw [← cons_erase ha]
    exact fixed a _ ha0 ((div_eq_iff ha0).1 hfix).symm
      (ih _ hcard _ rfl (by rwa [hfix] at herase) h0a)
  · have hca' : c / a ∈ S.erase a := mem_erase_of_ne hfix |>.2 hca
    rw [← cons_erase ha, ← cons_erase hca']
    refine pair a _ ha0 hc (fun h ↦ hfix ((div_eq_iff ha0).2 h.symm))
      (ih _ ((card_erase_lt_of_mem hca').trans hcard) _ rfl ?_ fun h ↦ h0a (mem_of_mem_erase h))
    rw [map_erase _ hinv.injective, herase, div_div_cancel₀ hc, erase_comm]

/-- If `s * s = c` and `c ≠ 0`, the elements `s` and `-s` are not the left half of a pair
`{a, c / a}` with `a * a ≠ c`, nor its right half. -/
private theorem ne_of_mul_self_ne {a : K} (hs : s * s = c) (ha0 : a ≠ 0) (hc : c ≠ 0)
    (haa : a * a ≠ c) : a ≠ s ∧ a ≠ -s ∧ c / a ≠ s ∧ c / a ≠ -s := by
  have hb : c / a * (c / a) ≠ c := fun h ↦ haa <| by
    rw [div_mul_div_comm, div_eq_iff (mul_ne_zero ha0 ha0)] at h
    exact (mul_left_cancel₀ hc h).symm
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rintro h
  · exact haa (h ▸ hs)
  · exact haa (by rw [h, neg_mul_neg, hs])
  · exact hb (h ▸ hs)
  · exact hb (by rw [h, neg_mul_neg, hs])

/-- **The product of a multiset stable under `x ↦ c / x`.** If `S` consists of nonzero elements,
`S.map (c / ·) = S` and `s * s = c`, then `S.prod = (-1) ^ count (-s) S * s ^ card S`: the
elements other than `±s` pair off into pairs of product `c = s * s`. No assumption on the
characteristic is needed. -/
theorem prod_eq_neg_one_pow_count_mul_pow_card_of_map_div_eq [DecidableEq K] {S : Multiset K}
    (hs : s * s = c) (hS : S.map (c / ·) = S) (h0 : (0 : K) ∉ S) :
    S.prod = (-1) ^ S.count (-s) * s ^ card S := by
  refine induction_of_map_div_eq (P := fun S ↦ S.prod = (-1) ^ S.count (-s) * s ^ card S)
    (by simp) (fun a T _ haa ih ↦ ?_) (fun a T ha0 hc haa ih ↦ ?_) S hS h0
  · rw [← hs, mul_self_eq_mul_self_iff] at haa
    rw [prod_cons, ih, card_cons]
    by_cases ha : a = -s
    · rw [ha, count_cons_self]
      ring
    · rw [count_cons_of_ne (Ne.symm ha), haa.resolve_right ha]
      ring
  · obtain ⟨-, ha, -, hca⟩ := ne_of_mul_self_ne hs ha0 hc haa
    rw [prod_cons, prod_cons, ih, count_cons_of_ne (Ne.symm ha), count_cons_of_ne (Ne.symm hca),
      card_cons, card_cons, ← mul_assoc, mul_div_cancel₀ c ha0, ← hs]
    ring

/-- **Elements other than `±s` of a multiset stable under `x ↦ c / x` are even in number.** If
`2 ≠ 0`, `S` consists of nonzero elements, `S.map (c / ·) = S` and `s * s = c`, then
`card S - count s S - count (-s) S` is even. -/
theorem even_card_sub_count_sub_count_of_map_div_eq [DecidableEq K] (h2 : (2 : K) ≠ 0)
    {S : Multiset K} (hs : s * s = c) (hS : S.map (c / ·) = S) (h0 : (0 : K) ∉ S) :
    Even ((card S : ℤ) - S.count s - S.count (-s)) := by
  refine induction_of_map_div_eq
    (P := fun S ↦ Even ((card S : ℤ) - S.count s - S.count (-s)))
    (by simp) (fun a T ha0 haa ih ↦ ?_) (fun a T ha0 hc haa ih ↦ ?_) S hS h0
  · have hsne : s ≠ -s := fun h ↦ ha0 <| by
      have hs0 : s = 0 := by
        rw [eq_neg_iff_add_eq_zero, ← two_mul, mul_eq_zero] at h
        exact h.resolve_left h2
      rw [← mul_self_eq_zero, haa, ← hs, hs0, mul_zero]
    rw [← hs, mul_self_eq_mul_self_iff] at haa
    rcases haa with rfl | rfl
    · rwa [card_cons, count_cons_self, count_cons_of_ne hsne.symm, Nat.cast_add, Nat.cast_add,
        Nat.cast_one, add_sub_add_right_eq_sub]
    · rw [card_cons, count_cons_of_ne hsne, count_cons_self, Nat.cast_add, Nat.cast_add,
        Nat.cast_one]
      convert ih using 1
      ring
  · obtain ⟨ha, ha', hca, hca'⟩ := ne_of_mul_self_ne hs ha0 hc haa
    rw [card_cons, card_cons, count_cons_of_ne (Ne.symm ha), count_cons_of_ne (Ne.symm hca),
      count_cons_of_ne (Ne.symm ha'), count_cons_of_ne (Ne.symm hca')]
    convert ih.add (even_two (α := ℤ)) using 1
    push_cast
    ring

end Multiset
