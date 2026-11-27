/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.BigOperators.Ring.Nat
import Mathlib.Algebra.GroupWithZero.Units.Fintype
import Mathlib.Algebra.Ring.CharZero
import Mathlib.Combinatorics.Enumerative.DoubleCounting
import Mathlib.Data.Int.Interval

/-!
# Tucker's lemma for a flag of hemispheres

This file proves `TauCeti.flag_tucker`, the combinatorial form of Tucker's lemma from which the
octahedral and lattice forms of Tucker's lemma, Kneser's conjecture and the Borsuk–Ulam theorem
are derived. The data are a type of vertices with an involution `ι`, playing the antipodal map,
finite families `H 0, H 1, …` of finite sets of vertices, playing the simplices that lie in the
hemispheres of a flag on a centrally symmetric triangulation of a sphere, and an integer
labelling. The four hypotheses on the families are the facts about such a flag that the proof
uses; no ambient sphere appears.

The proof is the counting form of the path-following argument of Prescott and Su. A finite set of
nonzero integers is alternating when its elements have distinct absolute values and, listed by
increasing absolute value, alternate in sign. Assuming that no member of `H n` carries two
opposite labels, the number of `d`-simplices of `H d` whose labels form an alternating set is odd
for `d = 0` and zero for `d = n`, while a double count of the alternating facets shows that its
parity does not depend on `d`.

## Main results

* `TauCeti.flag_tucker`: Tucker's lemma for a flag of hemispheres.

## References

* T. Prescott and F. E. Su, *A constructive proof of Ky Fan's generalization of Tucker's lemma*,
  J. Combin. Theory Ser. A 111 (2005), 257–265, arXiv:math/0310444: Theorem 1 and its proof
  (pp. 3–5), and Theorem 2 (p. 6).
-/

public section

open Finset

namespace TauCeti

section Alternating

/-- A finite set `S` of integers is alternating of sign `ε` when its elements have distinct
absolute values and, listed by increasing absolute value, have the signs `ε, -ε, ε, …`: the
element preceded by `k` elements of smaller absolute value has sign `ε * (-1) ^ k`. -/
private def IsAlternating (ε : ℤˣ) (S : Finset ℤ) : Prop :=
  Set.InjOn (|·|) (S : Set ℤ) ∧ ∀ x ∈ S, x.sign * (-1) ^ #{y ∈ S | |y| < |x|} = ε

private instance (ε : ℤˣ) : DecidablePred (IsAlternating ε) := fun S =>
  decidable_of_iff (#(S.image (|·|)) = #S ∧ ∀ x ∈ S, x.sign * (-1) ^ #{y ∈ S | |y| < |x|} = ε)
    (by rw [card_image_iff]; rfl)

private lemma sign_mul_neg_one_pow_eq_or {x : ℤ} (hx : x ≠ 0) (k : ℕ) :
    x.sign * (-1) ^ k = 1 ∨ x.sign * (-1) ^ k = -1 := by
  rcases neg_one_pow_eq_or ℤ k with h | h <;> rw [h] <;>
    rcases lt_or_gt_of_ne hx with h' | h' <;>
    simp [Int.sign_eq_neg_one_of_neg, Int.sign_eq_one_of_pos, *]

private lemma IsAlternating.ne_zero {ε : ℤˣ} {S : Finset ℤ} (h : IsAlternating ε S) :
    (0 : ℤ) ∉ S := fun h0 => by
  have := h.2 0 h0
  rcases Int.isUnit_eq_one_or ε.isUnit with h' | h' <;> simp_all

private lemma IsAlternating.eq {ε ε' : ℤˣ} {S : Finset ℤ} (hS : S.Nonempty)
    (h : IsAlternating ε S) (h' : IsAlternating ε' S) : ε = ε' := by
  obtain ⟨x, hx⟩ := hS
  exact Units.ext ((h.2 x hx).symm.trans (h'.2 x hx))

private lemma IsAlternating.card_le {ε : ℤˣ} {S : Finset ℤ} (h : IsAlternating ε S) {n : ℕ}
    (hn : ∀ x ∈ S, |x| ≤ n) : #S ≤ n := by
  have h0 := h.ne_zero
  calc #S ≤ #(Icc (1 : ℤ) n) := card_le_card_of_injOn (|·|)
          (fun x hx => mem_Icc.2 ⟨Int.one_le_abs (by rintro rfl; exact h0 hx), hn x hx⟩) h.1
    _ = n := by simp

private lemma isAlternating_singleton {x : ℤ} (hx : x ≠ 0) : ∃ ε, IsAlternating ε {x} := by
  rcases sign_mul_neg_one_pow_eq_or hx 0 with h | h
  · exact ⟨1, by simpa [IsAlternating, Set.injOn_singleton, filter_singleton] using h⟩
  · exact ⟨-1, by simpa [IsAlternating, Set.injOn_singleton, filter_singleton] using h⟩

private lemma isAlternating_image_neg {ε : ℤˣ} {S : Finset ℤ} :
    IsAlternating ε (S.image (-·)) ↔ IsAlternating (-ε) S := by
  have hrank (x : ℤ) : #{y ∈ S.image (-·) | |y| < |x|} = #{y ∈ S | |y| < |x|} := by
    rw [filter_image, card_image_of_injective _ neg_injective]
    simp
  unfold IsAlternating
  simp only [Set.InjOn, coe_image, Set.mem_image, mem_coe, forall_exists_index, and_imp,
    forall_apply_eq_imp_iff₂, abs_neg, neg_inj, forall_mem_image, hrank, Int.sign_neg,
    Units.val_neg]
  refine and_congr Iff.rfl (forall₂_congr fun x _ => ?_)
  rw [neg_mul, neg_eq_iff_eq_neg]

/-- The set `S` with `x` removed is alternating of sign `ε` exactly when the other elements `y`
with `y.sign * (-1) ^ k = ε`, where `k` counts the elements of `S` of smaller absolute value, are
those of absolute value below `|x|`. -/
private lemma isAlternating_erase_iff {ε : ℤˣ} {S : Finset ℤ}
    (hinj : Set.InjOn (|·|) (S : Set ℤ)) (h0 : (0 : ℤ) ∉ S) {x : ℤ} (hx : x ∈ S) :
    IsAlternating ε (S.erase x) ↔
      ∀ y ∈ S, y ≠ x → (y.sign * (-1) ^ #{z ∈ S | |z| < |y|} = ε ↔ |y| < |x|) := by
  have key (y : ℤ) (hy : y ∈ S) (hyx : y ≠ x) :
      y.sign * (-1) ^ #{z ∈ S.erase x | |z| < |y|} = ε ↔
        (y.sign * (-1) ^ #{z ∈ S | |z| < |y|} = ε ↔ |y| < |x|) := by
    have hy0 : y ≠ 0 := fun h => h0 (h ▸ hy)
    have hne : |y| ≠ |x| := fun h => hyx (hinj hy hx h)
    rw [filter_erase]
    rcases lt_or_gt_of_ne hne with hlt | hlt
    · rw [erase_eq_of_notMem (by simp [not_lt.2 hlt.le])]
      simp [hlt]
    · have hmem : x ∈ ({z ∈ S | |z| < |y|} : Finset ℤ) := mem_filter.2 ⟨hx, hlt⟩
      obtain ⟨k, hk⟩ : ∃ k, #{z ∈ S | |z| < |y|} = k + 1 :=
        Nat.exists_eq_add_one.2 (card_pos.2 ⟨x, hmem⟩)
      rw [card_erase_of_mem hmem, hk, Nat.add_sub_cancel, pow_succ, ← mul_assoc,
        iff_false_intro (not_lt.2 hlt.le), iff_false]
      have := sign_mul_neg_one_pow_eq_or hy0 k
      have := Int.isUnit_eq_one_or ε.isUnit
      generalize y.sign * (-1) ^ k = g at *
      omega
  rw [IsAlternating, and_iff_right (hinj.mono (coe_subset.2 (erase_subset x S)))]
  simp only [mem_erase, and_imp]
  exact ⟨fun h y hy hyx => (key y hy hyx).1 (h y hyx hy),
    fun h y hyx hy => (key y hy hyx).2 (h y hy hyx)⟩

section Split

variable {β α : Type*} [DecidableEq β] [LinearOrder α] {T : Finset β} {f : β → α}
  (p : β → Prop) [DecidablePred p]

/-- If `p` holds on all of `T`, only the largest element of `T` splits it. -/
private lemma card_filter_split_eq_one_of_forall (hT : T.Nonempty) (hf : Set.InjOn f T)
    (hp : ∀ y ∈ T, p y) : #{x ∈ T | ∀ y ∈ T, y ≠ x → (p y ↔ f y < f x)} = 1 := by
  obtain ⟨m, hm, hmax⟩ := T.exists_max_image f hT
  refine card_eq_one.2 ⟨m, ?_⟩
  ext x
  simp only [mem_filter, mem_singleton]
  refine ⟨fun ⟨hx, h⟩ => by_contra fun hxm =>
    ((h m hm (Ne.symm hxm)).1 (hp m hm)).not_ge (hmax x hx), ?_⟩
  rintro rfl
  exact ⟨hm, fun y hy hym => iff_of_true (hp y hy)
    ((hmax y hy).lt_of_ne fun h => hym (hf hy hm h))⟩

/-- If `p` holds nowhere on `T`, only the smallest element of `T` splits it. -/
private lemma card_filter_split_eq_one_of_forall_not (hT : T.Nonempty) (hf : Set.InjOn f T)
    (hp : ∀ y ∈ T, ¬p y) : #{x ∈ T | ∀ y ∈ T, y ≠ x → (p y ↔ f y < f x)} = 1 := by
  obtain ⟨m, hm, hmin⟩ := T.exists_min_image f hT
  refine card_eq_one.2 ⟨m, ?_⟩
  ext x
  simp only [mem_filter, mem_singleton]
  refine ⟨fun ⟨hx, h⟩ => by_contra fun hxm => hxm (hf hx hm (le_antisymm
    (not_lt.1 fun hlt => hp m hm ((h m hm (Ne.symm hxm)).2 hlt)) (hmin x hx))), ?_⟩
  rintro rfl
  exact ⟨hm, fun y hy _ => iff_of_false (hp y hy) (not_lt.2 (hmin y hy))⟩

/-- If `p` holds somewhere but not everywhere on `T`, then `T` is split either by none of its
elements or by exactly two: the largest element `a` satisfying `p` and the smallest element `b`
violating it, when `a` lies below `b`. -/
private lemma even_card_filter_split (hf : Set.InjOn f T) (ha₀ : ∃ y ∈ T, p y)
    (hb₀ : ∃ y ∈ T, ¬p y) : Even #{x ∈ T | ∀ y ∈ T, y ≠ x → (p y ↔ f y < f x)} := by
  obtain ⟨a₀, ha₀, hpa₀⟩ := ha₀
  obtain ⟨b₀, hb₀, hpb₀⟩ := hb₀
  obtain ⟨a, ha, ha'⟩ := exists_max_image {y ∈ T | p y} f ⟨a₀, mem_filter.2 ⟨ha₀, hpa₀⟩⟩
  obtain ⟨b, hb, hb'⟩ := exists_min_image {y ∈ T | ¬p y} f ⟨b₀, mem_filter.2 ⟨hb₀, hpb₀⟩⟩
  simp only [mem_filter, and_imp] at ha hb ha' hb'
  have hab : a ≠ b := fun h => hb.2 (h ▸ ha.2)
  set D := {x ∈ T | ∀ y ∈ T, y ≠ x → (p y ↔ f y < f x)}
  have hD : D ⊆ {a, b} := by
    intro x hx
    obtain ⟨hx, h⟩ := mem_filter.1 hx
    rw [mem_insert, mem_singleton]
    by_cases hpx : p x
    · exact Or.inl (by_contra fun hxa => ((h a ha.1 (Ne.symm hxa)).1 ha.2).not_ge (ha' x hx hpx))
    · refine Or.inr (by_contra fun hxb => hxb (hf hx hb.1 (le_antisymm ?_ (hb' x hx hpx))))
      exact not_lt.1 fun hlt => hb.2 ((h b hb.1 (Ne.symm hxb)).2 hlt)
  have haD : a ∈ D ↔ f a < f b := by
    refine ⟨fun h => ?_, fun hlt => mem_filter.2 ⟨ha.1, fun y hy hya => ?_⟩⟩
    · refine (not_lt.1 fun hlt => hb.2 (((mem_filter.1 h).2 b hb.1 hab.symm).2 hlt)).lt_of_ne ?_
      exact fun h => hab (hf ha.1 hb.1 h)
    · by_cases hpy : p y
      · exact iff_of_true hpy ((ha' y hy hpy).lt_of_ne fun h => hya (hf hy ha.1 h))
      · exact iff_of_false hpy (not_lt.2 (hlt.trans_le (hb' y hy hpy)).le)
  have hbD : b ∈ D ↔ f a < f b := by
    refine ⟨fun h => ((mem_filter.1 h).2 a ha.1 hab).1 ha.2,
      fun hlt => mem_filter.2 ⟨hb.1, fun y hy _ => ?_⟩⟩
    by_cases hpy : p y
    · exact iff_of_true hpy ((ha' y hy hpy).trans_lt hlt)
    · exact iff_of_false hpy (not_lt.2 (hb' y hy hpy))
  by_cases hlt : f a < f b
  · rw [Subset.antisymm hD (insert_subset (haD.2 hlt) (singleton_subset_iff.2 (hbD.2 hlt))),
      card_pair hab]
    exact even_two
  · rw [eq_empty_of_forall_notMem (s := D) fun x hx => by
      rcases mem_insert.1 (hD hx) with rfl | h
      · exact hlt (haD.1 hx)
      · exact hlt (hbD.1 (mem_singleton.1 h ▸ hx))]
    simp

/-- In a nonempty finite set `T` ordered injectively by a key `f`, say that `x` splits `T` when
the elements of `T` below `x` are exactly the elements other than `x` satisfying `p`. There is an
odd number of such `x` exactly when `p` holds everywhere or nowhere on `T`. -/
private lemma odd_card_filter_split_iff (hT : T.Nonempty) (hf : Set.InjOn f T) :
    Odd #{x ∈ T | ∀ y ∈ T, y ≠ x → (p y ↔ f y < f x)} ↔ (∀ y ∈ T, p y) ∨ (∀ y ∈ T, ¬p y) := by
  by_cases hA : ∀ y ∈ T, p y
  · simpa [card_filter_split_eq_one_of_forall p hT hf hA] using Or.inl hA
  by_cases hB : ∀ y ∈ T, ¬p y
  · simpa [card_filter_split_eq_one_of_forall_not p hT hf hB] using Or.inr hB
  push Not at hA hB
  exact iff_of_false (Nat.not_odd_iff_even.2 (even_card_filter_split p hf hB hA)) (by tauto)

end Split

/-- The number of elements whose removal leaves an alternating set of sign `ε` is odd exactly
when the set itself is alternating. -/
private lemma odd_card_filter_isAlternating_erase_iff (ε : ℤˣ) {S : Finset ℤ} (hS : S.Nonempty)
    (hinj : Set.InjOn (|·|) (S : Set ℤ)) (h0 : (0 : ℤ) ∉ S) :
    Odd #{x ∈ S | IsAlternating ε (S.erase x)} ↔ ∃ ε', IsAlternating ε' S := by
  rw [filter_congr fun x hx => isAlternating_erase_iff hinj h0 hx,
    odd_card_filter_split_iff _ hS hinj]
  constructor
  · rintro (h | h)
    · exact ⟨ε, hinj, h⟩
    · refine ⟨-ε, hinj, fun y hy => ?_⟩
      have := h y hy
      have := sign_mul_neg_one_pow_eq_or (ne_of_mem_of_not_mem hy h0) #{z ∈ S | |z| < |y|}
      have := Int.isUnit_eq_one_or ε.isUnit
      rw [Units.val_neg]
      generalize y.sign * (-1) ^ #{z ∈ S | |z| < |y|} = g at *
      omega
  · rintro ⟨ε', -, h⟩
    rcases (or_iff_not_imp_left.2 Int.units_ne_iff_eq_neg.1 : ε' = ε ∨ ε' = -ε) with rfl | rfl
    · exact Or.inl h
    · exact Or.inr fun y hy h' => units_ne_neg_self ε (Units.ext (h'.symm.trans (h y hy)))

end Alternating

section Simplex

variable {V : Type*}

/-- A finite set of vertices is alternating of sign `ε` for the labelling `lab` when its labels
are distinct and form an alternating set of sign `ε`. -/
private def IsAlternatingSimplex (lab : V → ℤ) (ε : ℤˣ) (s : Finset V) : Prop :=
  #(s.image lab) = #s ∧ IsAlternating ε (s.image lab)

private instance (lab : V → ℤ) (ε : ℤˣ) : DecidablePred (IsAlternatingSimplex lab ε) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

private lemma isAlternatingSimplex_singleton {lab : V → ℤ} {v : V} (hv : lab v ≠ 0) :
    ∃ ε, IsAlternatingSimplex lab ε {v} := by
  obtain ⟨ε, h⟩ := isAlternating_singleton hv
  exact ⟨ε, by simp, by simpa using h⟩

private lemma IsAlternatingSimplex.eq {lab : V → ℤ} {ε ε' : ℤˣ} {s : Finset V} (hs : s.Nonempty)
    (h : IsAlternatingSimplex lab ε s) (h' : IsAlternatingSimplex lab ε' s) : ε = ε' :=
  h.2.eq (hs.image lab) h'.2

private lemma IsAlternatingSimplex.card_le {lab : V → ℤ} {ε : ℤˣ} {s : Finset V}
    (h : IsAlternatingSimplex lab ε s) {n : ℕ} (hn : ∀ v ∈ s, |lab v| ≤ n) : #s ≤ n :=
  h.1 ▸ h.2.card_le (forall_mem_image.2 hn)

/-- An injective map that negates the labels of `s` carries the alternating sets of sign `-ε`
to those of sign `ε`. -/
private lemma isAlternatingSimplex_image [DecidableEq V] {lab : V → ℤ} {ι : V → V}
    (hι : Function.Injective ι) {ε : ℤˣ} {s : Finset V} (h : ∀ v ∈ s, lab (ι v) = -lab v) :
    IsAlternatingSimplex lab ε (s.image ι) ↔ IsAlternatingSimplex lab (-ε) s := by
  have : (s.image ι).image lab = (s.image lab).image (-·) := by
    rw [image_image, image_image]
    exact image_congr fun v hv => h v hv
  rw [IsAlternatingSimplex, IsAlternatingSimplex, this, isAlternating_image_neg,
    card_image_of_injective _ hι, card_image_of_injective _ neg_injective]

private lemma odd_card_filter_isAlternatingSimplex_erase_iff_of_injOn [DecidableEq V]
    (lab : V → ℤ) (ε : ℤˣ) {τ : Finset V} (hτ : τ.Nonempty) (h0 : ∀ v ∈ τ, lab v ≠ 0)
    (hinj : Set.InjOn (fun v => |lab v|) τ) :
    Odd #{v ∈ τ | IsAlternatingSimplex lab ε (τ.erase v)} ↔
      ∃ ε', IsAlternatingSimplex lab ε' τ := by
  have hlab : Set.InjOn lab τ := fun u hu w hw h => hinj hu hw (by simp [h])
  have hcard (s : Finset V) (hs : s ⊆ τ) : #(s.image lab) = #s :=
    card_image_of_injOn (hlab.mono hs)
  have himg (v : V) (hv : v ∈ τ) : (τ.erase v).image lab = (τ.image lab).erase (lab v) := by
    ext y
    simp only [mem_image, mem_erase]
    constructor
    · rintro ⟨w, ⟨hwv, hw⟩, rfl⟩
      exact ⟨fun h => hwv (hlab hw hv h), w, hw, rfl⟩
    · rintro ⟨hy, w, hw, rfl⟩
      exact ⟨w, ⟨fun h => hy (h ▸ rfl), hw⟩, rfl⟩
  have : #{v ∈ τ | IsAlternatingSimplex lab ε (τ.erase v)} =
      #{x ∈ τ.image lab | IsAlternating ε ((τ.image lab).erase x)} := by
    rw [filter_image, card_image_of_injOn (hlab.mono (filter_subset _ _))]
    refine congrArg card (filter_congr fun v hv => ?_)
    rw [IsAlternatingSimplex, hcard _ (erase_subset v τ), himg v hv, eq_self, true_and]
  rw [this, odd_card_filter_isAlternating_erase_iff ε (hτ.image lab)]
  · simp only [IsAlternatingSimplex, hcard τ subset_rfl, true_and]
  · intro x hx y hy h
    obtain ⟨u, hu, rfl⟩ := mem_image.1 hx
    obtain ⟨w, hw, rfl⟩ := mem_image.1 hy
    exact congrArg lab (hinj hu hw h)
  · simpa using h0

private lemma even_card_filter_isAlternatingSimplex_erase [DecidableEq V] (lab : V → ℤ) (ε : ℤˣ)
    {τ : Finset V} (hinj : ¬Set.InjOn lab τ) :
    Even #{v ∈ τ | IsAlternatingSimplex lab ε (τ.erase v)} := by
  obtain ⟨u, hu, w, hw, huw, hne⟩ : ∃ u ∈ τ, ∃ w ∈ τ, lab u = lab w ∧ u ≠ w := by
    simpa [Set.InjOn] using hinj
  -- the facets omitting `u` and `w` carry the same labels
  have himg {u w : V} (hu : u ∈ τ) (huw : lab u = lab w) (hne : u ≠ w) :
      (τ.erase u).image lab ⊆ (τ.erase w).image lab := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.1 hy
    by_cases hzw : z = w
    · subst hzw
      exact mem_image.2 ⟨u, mem_erase.2 ⟨hne, hu⟩, huw⟩
    · exact mem_image.2 ⟨z, mem_erase.2 ⟨hzw, (mem_erase.1 hz).2⟩, rfl⟩
  have huw' : IsAlternatingSimplex lab ε (τ.erase u) ↔
      IsAlternatingSimplex lab ε (τ.erase w) := by
    rw [IsAlternatingSimplex, IsAlternatingSimplex,
      Subset.antisymm (himg hu huw hne) (himg hw huw.symm hne.symm),
      card_erase_of_mem hu, card_erase_of_mem hw]
  set D := {v ∈ τ | IsAlternatingSimplex lab ε (τ.erase v)}
  -- any other facet contains both `u` and `w`, so its labels are not distinct
  have hD : D ⊆ {u, w} := by
    intro v hv
    obtain ⟨-, h⟩ := mem_filter.1 hv
    by_contra hvuw
    simp only [mem_insert, mem_singleton, not_or] at hvuw
    exact hne (card_image_iff.1 h.1 (mem_erase.2 ⟨Ne.symm hvuw.1, hu⟩)
      (mem_erase.2 ⟨Ne.symm hvuw.2, hw⟩) huw)
  by_cases hu' : u ∈ D
  · rw [Subset.antisymm hD (insert_subset hu' (singleton_subset_iff.2
      (mem_filter.2 ⟨hw, huw'.1 (mem_filter.1 hu').2⟩))), card_pair hne]
    exact even_two
  · rw [eq_empty_of_forall_notMem (s := D) fun v hv => by
      rcases mem_insert.1 (hD hv) with rfl | h
      · exact hu' hv
      · rw [mem_singleton.1 h] at hv
        exact hu' (mem_filter.2 ⟨hu, huw'.2 (mem_filter.1 hv).2⟩)]
    simp

/-- A simplex whose labels are nonzero and never opposite has an odd number of facets that are
alternating of a given sign exactly when it is alternating itself. -/
private lemma odd_card_filter_isAlternatingSimplex_erase_iff [DecidableEq V] (lab : V → ℤ) (ε : ℤˣ)
    {τ : Finset V} (hτ : τ.Nonempty) (h0 : ∀ v ∈ τ, lab v ≠ 0)
    (habs : ∀ u ∈ τ, ∀ w ∈ τ, |lab u| = |lab w| → lab u = lab w) :
    Odd #{v ∈ τ | IsAlternatingSimplex lab ε (τ.erase v)} ↔
      ∃ ε', IsAlternatingSimplex lab ε' τ := by
  by_cases hinj : Set.InjOn lab τ
  · exact odd_card_filter_isAlternatingSimplex_erase_iff_of_injOn lab ε hτ h0
      fun u hu w hw h => hinj hu hw (habs u hu w hw h)
  · exact iff_of_false (Nat.not_odd_iff_even.2 (even_card_filter_isAlternatingSimplex_erase lab ε
      hinj)) fun ⟨_, h, _⟩ => hinj (card_image_iff.1 h)

end Simplex

section Flag

variable {V : Type*} [DecidableEq V]

/-- The facets of `τ` in `X` with a property `P` correspond to the vertices whose removal from
`τ` gives a set with property `P`. -/
private lemma card_filter_subset_eq_card_filter_erase {X : Finset (Finset V)} {τ : Finset V}
    {d : ℕ} (hτ : #τ = d + 2) (herase : ∀ v ∈ τ, τ.erase v ∈ X) (P : Finset V → Prop)
    [DecidablePred P] :
    #{ρ ∈ {ρ ∈ X | #ρ = d + 1 ∧ P ρ} | ρ ⊆ τ} = #{v ∈ τ | P (τ.erase v)} := by
  symm
  refine card_bij (fun v _ => τ.erase v) (fun v hv => ?_)
    (fun v hv w hw h => erase_injOn τ (mem_filter.1 hv).1 (mem_filter.1 hw).1 h) fun ρ hρ => ?_
  · obtain ⟨hv, hP⟩ := mem_filter.1 hv
    exact mem_filter.2 ⟨mem_filter.2 ⟨herase v hv, by rw [card_erase_of_mem hv, hτ]; rfl, hP⟩,
      erase_subset v τ⟩
  · obtain ⟨hρ, hsub⟩ := mem_filter.1 hρ
    obtain ⟨-, hcard, hP⟩ := mem_filter.1 hρ
    obtain ⟨v, hv, hvρ⟩ := exists_mem_notMem_of_card_lt_card (s := ρ) (t := τ) (by omega)
    have : ρ = τ.erase v := eq_of_subset_of_card_le
      (fun x hx => mem_erase.2 ⟨ne_of_mem_of_not_mem hx hvρ, hsub hx⟩)
      (by rw [card_erase_of_mem hv]; omega)
    exact ⟨v, mem_filter.2 ⟨hv, this ▸ hP⟩, this.symm⟩

/-- The facets of the members of `X` that are alternating of sign `1` and lie in `Y` or in its
image under `ι` are counted, through `ι`, by the alternating members of `Y` of both signs. -/
private lemma card_filter_isAlternatingSimplex_boundary {ι : V → V} (hι : Function.Involutive ι)
    {lab : V → ℤ} {X Y : Finset (Finset V)} {d : ℕ} (hmono : ∀ s ∈ Y, s ∈ X ∧ s.image ι ∈ X)
    (hnoanti : ∀ s ∈ Y, #s = d + 1 → s.image ι ∉ Y)
    (hanti : ∀ s ∈ Y, ∀ v ∈ s, lab (ι v) = -lab v) :
    #{ρ ∈ {ρ ∈ X | #ρ = d + 1 ∧ IsAlternatingSimplex lab 1 ρ} | ρ ∈ Y ∨ ρ.image ι ∈ Y} =
      #{σ ∈ Y | #σ = d + 1 ∧ ∃ ε, IsAlternatingSimplex lab ε σ} := by
  have hιι (s : Finset V) : (s.image ι).image ι = s := by
    rw [image_image, hι.comp_self, image_id]
  have hcardι (s : Finset V) : #(s.image ι) = #s := card_image_of_injective _ hι.injective
  -- the facets in `Y`
  have h₁ : {ρ ∈ {ρ ∈ X | #ρ = d + 1 ∧ IsAlternatingSimplex lab 1 ρ} | ρ ∈ Y} =
      {σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab 1 σ} := by
    ext ρ
    simp only [mem_filter]
    exact ⟨fun ⟨⟨_, h⟩, hY⟩ => ⟨hY, h⟩, fun ⟨hY, h⟩ => ⟨⟨(hmono ρ hY).1, h⟩, hY⟩⟩
  -- the facets in the image of `Y`, which `ι` carries to the facets in `Y` of sign `-1`
  have h₂ : #{ρ ∈ {ρ ∈ X | #ρ = d + 1 ∧ IsAlternatingSimplex lab 1 ρ} | ρ.image ι ∈ Y} =
      #{σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab (-1) σ} := by
    refine card_nbij' (image ι) (image ι) (fun ρ hρ => ?_) (fun σ hσ => ?_)
      (fun ρ _ => hιι ρ) fun σ _ => hιι σ
    · simp only [mem_coe, mem_filter] at hρ ⊢
      obtain ⟨⟨-, hcard, h⟩, hY⟩ := hρ
      refine ⟨hY, by rw [hcardι, hcard], ?_⟩
      rw [← isAlternatingSimplex_image hι.injective (hanti _ hY), hιι]
      exact h
    · simp only [mem_coe, mem_filter] at hσ ⊢
      obtain ⟨hY, hcard, h⟩ := hσ
      exact ⟨⟨(hmono σ hY).2, by rw [hcardι, hcard],
        (isAlternatingSimplex_image hι.injective (hanti σ hY)).2 h⟩, by rw [hιι]; exact hY⟩
  -- an alternating simplex has exactly one sign
  have h₃ : {σ ∈ Y | #σ = d + 1 ∧ ∃ ε, IsAlternatingSimplex lab ε σ} =
      {σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab 1 σ} ∪
        {σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab (-1) σ} := by
    rw [← filter_or]
    refine filter_congr fun σ _ => ?_
    rw [← and_or_left]
    refine and_congr_right fun _ => ⟨fun ⟨ε, h⟩ => ?_, fun h => h.elim (⟨1, ·⟩) (⟨-1, ·⟩)⟩
    rcases Int.units_eq_one_or ε with rfl | rfl
    exacts [Or.inl h, Or.inr h]
  have hdisj : Disjoint {σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab 1 σ}
      {σ ∈ Y | #σ = d + 1 ∧ IsAlternatingSimplex lab (-1) σ} :=
    disjoint_filter.2 fun σ _ ⟨hcard, h⟩ ⟨_, h'⟩ =>
      units_ne_neg_self (1 : ℤˣ) (h.eq (card_pos.1 (hcard ▸ d.succ_pos)) h')
  rw [filter_or, card_union_of_disjoint, h₁, h₂, h₃, card_union_of_disjoint hdisj]
  exact disjoint_filter.2 fun ρ hρ hY hY' =>
    hnoanti ρ hY (mem_filter.1 hρ).2.1 hY'

/-- One step of the parity count: the members of size `d + 2` of `X` that are alternating and
the members of size `d + 1` of `Y` that are alternating are equal in number modulo `2`. -/
private lemma odd_card_filter_isAlternatingSimplex_iff {ι : V → V} (hι : Function.Involutive ι)
    {lab : V → ℤ} {X Y : Finset (Finset V)} {d : ℕ} (h0 : ∀ s ∈ X, ∀ v ∈ s, lab v ≠ 0)
    (habs : ∀ s ∈ X, ∀ u ∈ s, ∀ w ∈ s, |lab u| = |lab w| → lab u = lab w)
    (herase : ∀ s ∈ X, ∀ v ∈ s, s.erase v ∈ X) (hmono : ∀ s ∈ Y, s ∈ X ∧ s.image ι ∈ X)
    (hnoanti : ∀ s ∈ Y, #s = d + 1 → s.image ι ∉ Y)
    (hincid : ∀ ρ ∈ X, #ρ = d + 1 →
      #{τ ∈ X | #τ = d + 2 ∧ ρ ⊆ τ} = if ρ ∈ Y ∨ ρ.image ι ∈ Y then 1 else 2)
    (hanti : ∀ s ∈ Y, ∀ v ∈ s, lab (ι v) = -lab v) :
    Odd #{τ ∈ X | #τ = d + 2 ∧ ∃ ε, IsAlternatingSimplex lab ε τ} ↔
      Odd #{σ ∈ Y | #σ = d + 1 ∧ ∃ ε, IsAlternatingSimplex lab ε σ} := by
  set D := {ρ ∈ X | #ρ = d + 1 ∧ IsAlternatingSimplex lab 1 ρ}
  set T := {τ ∈ X | #τ = d + 2}
  -- a member of `T` has an odd number of facets in `D` exactly when it is alternating
  have hT : #{τ ∈ X | #τ = d + 2 ∧ ∃ ε, IsAlternatingSimplex lab ε τ} =
      #{τ ∈ T | Odd #(D.bipartiteAbove (fun τ ρ => ρ ⊆ τ) τ)} := by
    rw [filter_filter]
    refine congrArg card (filter_congr fun τ hτ => and_congr_right fun hcard => ?_)
    rw [bipartiteAbove, card_filter_subset_eq_card_filter_erase hcard (herase τ hτ),
      odd_card_filter_isAlternatingSimplex_erase_iff lab 1 (card_pos.1 (by omega)) (h0 τ hτ)
        (habs τ hτ)]
  -- a member of `D` lies in an odd number of members of `T` exactly when it lies in `Y` or in
  -- the image of `Y` under `ι`
  have hD : #{ρ ∈ D | Odd #(T.bipartiteBelow (fun τ ρ => ρ ⊆ τ) ρ)} =
      #{ρ ∈ D | ρ ∈ Y ∨ ρ.image ι ∈ Y} := by
    refine congrArg card (filter_congr fun ρ hρ => ?_)
    obtain ⟨hρ, hcard, -⟩ := mem_filter.1 hρ
    rw [bipartiteBelow, filter_filter, hincid ρ hρ hcard]
    split_ifs with h <;> simp [h]
  rw [hT, ← odd_sum_iff_odd_card_odd, sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow,
    odd_sum_iff_odd_card_odd, hD, card_filter_isAlternatingSimplex_boundary hι hmono hnoanti hanti]

end Flag

/-- **Tucker's lemma for a flag of hemispheres.** Let `ι` be an involution of a type `V` of
vertices and `H 0, H 1, …` finite families of finite sets of vertices; a member of `H d` with
`k + 1` elements is a `k`-simplex of `H d`. Assume that for every `d < n`:

* deleting one vertex of a member of `H (d + 1)` gives a member of `H (d + 1)`;
* every member `s` of `H d` lies in `H (d + 1)`, and so does its image `ι s`;
* no `d`-simplex `s` of `H d` has `ι s` in `H d`;
* every `d`-simplex `ρ` of `H (d + 1)` lies in exactly one `(d + 1)`-simplex of `H (d + 1)` when
  `ρ` or `ι ρ` is in `H d`, and in exactly two otherwise;

and that `H 0` has exactly one `0`-simplex. If every vertex of a member of `H n` has a nonzero
label of absolute value at most `n`, and the labelling is antipodal, `lab (ι v) = -lab v`, at the
vertices of the members of the `H d` with `d < n`, then some member of `H n` has two distinct
vertices with opposite labels.

Think of `H d` as the simplices of a centrally symmetric triangulation of the sphere `Sⁿ` that
lie in the `d`-th hemisphere of a flag of hemispheres; the hypotheses are the combinatorial facts
about such a flag used in the proof of Prescott and Su. -/
theorem flag_tucker {V : Type*} [DecidableEq V] {ι : V → V} (hι : Function.Involutive ι)
    {n : ℕ} {H : ℕ → Finset (Finset V)} {lab : V → ℤ}
    (herase : ∀ d < n, ∀ s ∈ H (d + 1), ∀ v ∈ s, s.erase v ∈ H (d + 1))
    (hmono : ∀ d < n, ∀ s ∈ H d, s ∈ H (d + 1) ∧ s.image ι ∈ H (d + 1))
    (hnoanti : ∀ d < n, ∀ s ∈ H d, #s = d + 1 → s.image ι ∉ H d)
    (hincid : ∀ d < n, ∀ ρ ∈ H (d + 1), #ρ = d + 1 →
      #{τ ∈ H (d + 1) | #τ = d + 2 ∧ ρ ⊆ τ} = if ρ ∈ H d ∨ ρ.image ι ∈ H d then 1 else 2)
    (hzero : #{s ∈ H 0 | #s = 1} = 1)
    (hlab : ∀ s ∈ H n, ∀ v ∈ s, lab v ≠ 0 ∧ |lab v| ≤ n)
    (hanti : ∀ d < n, ∀ s ∈ H d, ∀ v ∈ s, lab (ι v) = -lab v) :
    ∃ s ∈ H n, ∃ u ∈ s, ∃ w ∈ s, u ≠ w ∧ lab u = -lab w := by
  by_contra hcon
  push Not at hcon
  -- every member of an `H d` with `d ≤ n` is a member of `H n`
  have hsub (k : ℕ) : ∀ d, d + k = n → ∀ s ∈ H d, s ∈ H n := by
    induction k with
    | zero => rintro d rfl s hs; exact hs
    | succ k ih => exact fun d hd s hs => ih (d + 1) (by omega) s (hmono d (by omega) s hs).1
  -- so their labels are nonzero, and two labels of equal absolute value are equal
  have h0 (d : ℕ) (hd : d ≤ n) : ∀ s ∈ H d, ∀ v ∈ s, lab v ≠ 0 := fun s hs v hv =>
    (hlab s (hsub (n - d) d (by omega) s hs) v hv).1
  have habs (d : ℕ) (hd : d ≤ n) :
      ∀ s ∈ H d, ∀ u ∈ s, ∀ w ∈ s, |lab u| = |lab w| → lab u = lab w := by
    intro s hs u hu w hw h
    refine (abs_eq_abs.1 h).resolve_right fun h' => ?_
    by_cases huw : u = w
    · subst huw
      exact h0 d hd s hs u hu (by omega)
    · exact hcon s (hsub (n - d) d (by omega) s hs) u hu w hw huw h'
  set A : ℕ → ℕ := fun d => #{s ∈ H d | #s = d + 1 ∧ ∃ ε, IsAlternatingSimplex lab ε s}
  -- the parity of `A d` does not depend on `d`
  have hstep (d : ℕ) (hd : d < n) : Odd (A (d + 1)) ↔ Odd (A d) :=
    odd_card_filter_isAlternatingSimplex_iff hι (h0 (d + 1) hd) (habs (d + 1) hd) (herase d hd)
      (hmono d hd) (hnoanti d hd) (hincid d hd) (hanti d hd)
  have hpar (d : ℕ) (hd : d ≤ n) : Odd (A d) ↔ Odd (A 0) := by
    induction d with
    | zero => rfl
    | succ d ih => exact (hstep d (by omega)).trans (ih (by omega))
  -- `A 0 = 1`: every vertex is an alternating `0`-simplex
  have hA0 : A 0 = 1 := by
    rw [← hzero]
    refine congrArg card (filter_congr fun s hs => and_iff_left_of_imp fun hcard => ?_)
    obtain ⟨v, rfl⟩ := card_eq_one.1 hcard
    exact isAlternatingSimplex_singleton (h0 0 (Nat.zero_le n) _ hs v (mem_singleton_self v))
  -- `A n = 0`: `n + 1` labels of distinct absolute values do not fit into `±1, …, ±n`
  have hAn : A n = 0 := by
    refine card_eq_zero.2 (filter_eq_empty_iff.2 fun s hs ⟨hcard, ε, h⟩ => ?_)
    have := h.card_le fun v hv => (hlab s hs v hv).2
    rw [hcard] at this
    omega
  have := hpar n le_rfl
  rw [hAn, hA0] at this
  simp at this

end TauCeti
