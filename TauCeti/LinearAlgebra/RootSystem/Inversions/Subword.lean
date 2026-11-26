/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Inversions.Length

/-!
# The deletion condition and the subword property

A word in the simple reflections whose length exceeds the number of inversions of the element it
spells is wasteful, and the strong exchange condition says exactly where the waste is: two of its
letters can be deleted without changing the element. Iterating the deletion until no waste is left
extracts from any word a *subword* of least length spelling the same element.

The deletion is located by walking along the word until the first prefix that is already wasteful.
The prefix one letter shorter is not wasteful, so the letter just read is an inversion of the
element that prefix spells, and the strong exchange condition deletes a letter from that prefix.
Deleting the letter just read as well leaves a word two letters shorter spelling the same element.

The subword form is what makes these statements usable downstream. The deleted positions are named,
so the same deletions can be replayed verbatim on the corresponding word over any other family of
generators indexed by `b.support`, in particular over the generators of the presented Coxeter
group. The bare existence of some shorter word inside the Weyl group names no word over those
generators to carry the assertion back through the presentation map; this is the form in which the
deletion condition enters the word property behind Tits' theorem.

## Main results

* `TauCeti.exists_wordProd_eraseIdx_eraseIdx_eq` is the deletion condition: a word longer than the
  inversion count of the element it spells has two letters that can be deleted.
* `TauCeti.exists_sublist_wordProd_eq_and_length_eq_ncard_inversions` is the subword property:
  every word contains a subword of least length spelling the same element.
* `TauCeti.ncard_inversions_wordProd_eq_length_iff` records that a word is of least length exactly
  when no two of its letters can be deleted.
* `TauCeti.ncard_inversions_wordProd_eq_length_of_nodup` and
  `TauCeti.ncard_inversions_wordProd_eq_card_support`: any duplicate-free list of simple
  reflections is reduced, and in particular every Coxeter element has `b.support.card` inversions.

## References

This file carries the theory of inversion sets and the exchange step towards the Coxeter
presentation `weylCoxeterSystem`, whose completeness half is proved through the exchange condition
at root level. The deletion condition and the subword property are the standard packaging of that
step; see J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), §1.7 and §5.8, and
Bourbaki, *Lie Groups and Lie Algebras*, Chapters 4--6, Ch. IV, §1.5.
-/

public section

namespace TauCeti

open Set

universe u v w x

variable {ι : Type u} {R : Type v} {M : Type w} {N : Type x}
  [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (P : RootPairing ι R M N) [Finite ι] [CharZero R] [IsDomain R]
  [P.IsCrystallographic] [P.IsReduced] (b : P.Base)

/-- **The deletion condition.** If a word has more letters than the element it spells has
inversions, then two of its letters can be deleted without changing the element it spells. -/
theorem exists_wordProd_eraseIdx_eraseIdx_eq (l : List b.support)
    (h : (inversions P b (wordProd P b l)).ncard < l.length) :
    ∃ j k, j < k ∧ k < l.length ∧
      wordProd P b ((l.eraseIdx k).eraseIdx j) = wordProd P b l ∧
      ((l.eraseIdx k).eraseIdx j).length + 2 = l.length := by
  classical
  -- Some prefix is already too long for the element it spells; the whole word is one.
  have hex : ∃ k, k < l.length ∧
      (inversions P b (wordProd P b (l.take (k + 1)))).ncard < k + 1 := by
    refine ⟨l.length - 1, by omega, ?_⟩
    have hsub : l.length - 1 + 1 = l.length := by omega
    rw [hsub, List.take_length]
    exact h
  -- Take the shortest such prefix.
  obtain ⟨k, ⟨hklt, hkinv⟩, hkmin⟩ :
      ∃ k, (k < l.length ∧ (inversions P b (wordProd P b (l.take (k + 1)))).ncard < k + 1) ∧
        ∀ m < k, ¬(m < l.length ∧
          (inversions P b (wordProd P b (l.take (m + 1)))).ncard < m + 1) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun _ hm ↦ Nat.find_min hex hm⟩
  -- One letter earlier the prefix is of least length.
  have hprefix : (inversions P b (wordProd P b (l.take k))).ncard = k := by
    have hle := ncard_inversions_wordProd_le_length P b (l.take k)
    rw [List.length_take] at hle
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simp [wordProd_nil]
    · have hnot := hkmin (k - 1) (by omega)
      push Not at hnot
      have hge := hnot (by omega)
      rw [Nat.sub_add_cancel hkpos] at hge
      omega
  -- The letter just read is an inversion of the element the shorter prefix spells.
  have hsucc : l.take (k + 1) = l.take k ++ [l[k]] := by
    rw [List.take_add_one, List.getElem?_eq_getElem hklt]
    rfl
  have hword : wordProd P b (l.take (k + 1)) =
      wordProd P b (l.take k) * RootPairing.weylGroup.ofIdx P (l[k] : ι) := by
    rw [hsucc, wordProd_append, wordProd_cons, wordProd_nil, mul_one]
  have hmem : (l[k] : ι) ∈ inversions P b (wordProd P b (l.take k)) := by
    rw [← ncard_inversions_mul_ofIdx_lt_iff P b _ (b.isPos_of_mem_support l[k].property), ← hword,
      hprefix]
    have hstep := ncard_inversions_mul_ofIdx P (wordProd P b (l.take k)) b l[k].property
    rw [← hword, hprefix] at hstep
    omega
  obtain ⟨hmempos, hmemneg⟩ := (mem_inversions P b _ _).mp hmem
  -- The strong exchange condition deletes a letter from the shorter prefix.
  obtain ⟨j, hj, -, hjeq⟩ :=
    P.exists_wordProd_drop_apply_eq_and_wordProd_eraseIdx_eq_mul_ofIdx b hmempos (l.take k) hmemneg
  rw [List.length_take] at hj
  have hjk : j < k := by omega
  have hjlt : j < (l.take k).length := by rw [List.length_take]; omega
  have hinner : l.eraseIdx k = l.take k ++ l.drop (k + 1) := List.eraseIdx_eq_take_drop_succ ..
  have hlist : (l.eraseIdx k).eraseIdx j = (l.take k).eraseIdx j ++ l.drop (k + 1) := by
    rw [hinner, List.eraseIdx_append_of_lt_length hjlt]
  refine ⟨j, k, hjk, hklt, ?_, ?_⟩
  · rw [hlist, wordProd_append, hjeq, ← hword, ← wordProd_append, List.take_append_drop]
  · have h₁ := List.length_eraseIdx_add_one hklt
    have h₂ : j < (l.eraseIdx k).length := by omega
    have h₃ := List.length_eraseIdx_add_one h₂
    omega

/-- **The subword property.** Every word in the simple reflections has a sublist that spells the
same Weyl-group element and whose length is the inversion count of that element, hence is of least
length. -/
theorem exists_sublist_wordProd_eq_and_length_eq_ncard_inversions (l : List b.support) :
    ∃ l' : List b.support, l'.Sublist l ∧ wordProd P b l' = wordProd P b l ∧
      l'.length = (inversions P b (wordProd P b l)).ncard := by
  suffices H : ∀ n : ℕ, ∀ l : List b.support, l.length ≤ n →
      ∃ l' : List b.support, l'.Sublist l ∧ wordProd P b l' = wordProd P b l ∧
        l'.length = (inversions P b (wordProd P b l)).ncard from H l.length l le_rfl
  intro n
  induction n with
  | zero =>
    intro l hl
    exact ⟨l, List.Sublist.refl l, rfl, by
      have := ncard_inversions_wordProd_le_length P b l
      omega⟩
  | succ n ih =>
    intro l hl
    rcases eq_or_lt_of_le (ncard_inversions_wordProd_le_length P b l) with heq | hlt
    · exact ⟨l, List.Sublist.refl l, rfl, heq.symm⟩
    · obtain ⟨j, k, -, -, hword, hlen⟩ := exists_wordProd_eraseIdx_eraseIdx_eq P b l hlt
      obtain ⟨l', hsub, hl'word, hl'len⟩ := ih ((l.eraseIdx k).eraseIdx j) (by omega)
      exact ⟨l', hsub.trans ((List.eraseIdx_sublist (l.eraseIdx k) j).trans
        (List.eraseIdx_sublist l k)), hl'word.trans hword, by rw [hl'len, hword]⟩

/-- **A word is of least length exactly when no two of its letters can be deleted.** -/
theorem ncard_inversions_wordProd_eq_length_iff (l : List b.support) :
    (inversions P b (wordProd P b l)).ncard = l.length ↔
      ∀ j k, j < k → k < l.length →
        wordProd P b ((l.eraseIdx k).eraseIdx j) ≠ wordProd P b l := by
  refine ⟨fun heq j k hjk hk hword ↦ ?_, fun h ↦ ?_⟩
  · -- A deletion would spell the same element with two letters fewer than its inversion count.
    have h₁ := List.length_eraseIdx_add_one hk
    have h₂ : j < (l.eraseIdx k).length := by omega
    have h₃ := List.length_eraseIdx_add_one h₂
    have hle := ncard_inversions_wordProd_le_length P b ((l.eraseIdx k).eraseIdx j)
    rw [hword, heq] at hle
    omega
  · by_contra hne
    have hlt : (inversions P b (wordProd P b l)).ncard < l.length :=
      lt_of_le_of_ne (ncard_inversions_wordProd_le_length P b l) hne
    obtain ⟨j, k, hjk, hk, hword, -⟩ := exists_wordProd_eraseIdx_eraseIdx_eq P b l hlt
    exact h j k hjk hk hword

omit [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced] in
private lemma wordProd_smul_sub_root_mem_span [DecidableEq ι] (s : b.support)
    (m : List b.support) (hm : s ∉ m) :
    wordProd P b m • P.root s - P.root s ∈
      Submodule.span R (P.root '' ((b.support.erase (s : ι) : Finset ι) : Set ι)) := by
  induction m with
  | nil => simp [wordProd_nil]
  | cons j m ih =>
    have hj_ne : (j : ι) ≠ (s : ι) := fun h ↦ hm (by simp [Subtype.ext h])
    have ih' := ih fun h ↦ hm (List.mem_cons_of_mem j h)
    have hsub : wordProd P b (j :: m) • P.root s - P.root s =
        -(P.coroot' (j : ι) (wordProd P b m • P.root s)) • P.root (j : ι) +
          (wordProd P b m • P.root s - P.root s) := by
      rw [wordProd_cons, mul_smul, RootPairing.weylGroup.ofIdx_smul,
        RootPairing.Equiv.reflection_smul, RootPairing.reflection_apply, neg_smul]
      abel
    rw [hsub]
    refine Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span ?_)) ih'
    exact ⟨j, Finset.mem_coe.mpr (Finset.mem_erase.mpr ⟨hj_ne, j.property⟩), rfl⟩

/-- **Every word without duplicate simple reflections is reduced**: its inversion count equals its
length. -/
theorem ncard_inversions_wordProd_eq_length_of_nodup (l : List b.support) (hl : l.Nodup) :
    (inversions P b (wordProd P b l)).ncard = l.length := by
  classical
  induction l with
  | nil => simp [wordProd_nil]
  | cons s l ih =>
    rw [List.nodup_cons] at hl
    have ih' := ih hl.2
    have hnot : (s : ι) ∉ inversions P b (wordProd P b l)⁻¹ := by
      intro hmem
      have hneg := ((mem_inversions P b (wordProd P b l)⁻¹ s).mp hmem).2
      rw [← wordProd_reverse] at hneg
      have hs_rev : s ∉ l.reverse := by simpa using hl.1
      have hspan := wordProd_smul_sub_root_mem_span P b s l.reverse hs_rev
      rw [Submodule.mem_span_image_finset_iff_exists_fun] at hspan
      obtain ⟨c, hc⟩ := hspan
      set c' : ι → R := fun k ↦ if hk : k ∈ b.support.erase (s : ι) then c ⟨k, hk⟩ else 0
      have hc' : ∑ k ∈ b.support.erase (s : ι), c' k • P.root k =
          wordProd P b l.reverse • P.root s - P.root s := by
        rw [← hc, ← Finset.sum_coe_sort (b.support.erase (s : ι))]
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        dsimp [c']
        split_ifs with hk
        · rfl
        · exact absurd k.property hk
      set j : ι := P.weylGroupToPerm (wordProd P b l.reverse) s
      have hneg' : b.IsPos (P.reflectionPerm j j) := by
        let := P.indexNeg
        rw [← RootPairing.indexNeg_neg]
        exact (RootPairing.Base.IsPos.neg_iff_not b j).mpr hneg
      obtain ⟨f, -, hf⟩ :=
        exists_root_eq_sum_nat_of_mem_posRoots P b ((mem_posRoots P b _).mpr hneg')
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self] at hf
      have hroot_eq : wordProd P b l.reverse • P.root s = P.root j :=
        P.weylGroup_apply_root _ _
      have hzero : ∑ k ∈ b.support,
          (if k = (s : ι) then 1 + (f k : R) else c' k + (f k : R)) • P.root k = 0 := by
        have hadd : -P.root j = ∑ k ∈ b.support, (f k : R) • P.root k := by
          simpa only [Nat.cast_smul_eq_nsmul] using hf
        have h1 : ∑ k ∈ b.support, (if k = (s : ι) then (1 : R) else 0) • P.root k =
            P.root (s : ι) := by
          simp [s.property]
        have h2 : ∑ k ∈ b.support, (if k = (s : ι) then (0 : R) else c' k) • P.root k =
            ∑ k ∈ b.support.erase (s : ι), c' k • P.root k := by
          rw [← Finset.add_sum_erase _ _ s.property]
          simp only [↓reduceIte, zero_smul, zero_add]
          refine Finset.sum_congr rfl fun k hk ↦ ?_
          simp [Finset.ne_of_mem_erase hk]
        calc
          ∑ k ∈ b.support, (if k = (s : ι) then 1 + (f k : R) else c' k + (f k : R)) • P.root k
              = ∑ k ∈ b.support, ((if k = (s : ι) then (1 : R) else 0) +
                  (if k = (s : ι) then (0 : R) else c' k) + (f k : R)) • P.root k := by
                refine Finset.sum_congr rfl fun k _ ↦ ?_
                split_ifs <;> simp
          _ = P.root (s : ι) + ∑ k ∈ b.support.erase (s : ι), c' k • P.root k + (-P.root j) := by
                simp only [add_smul, Finset.sum_add_distrib, h1, h2, ← hadd]
          _ = 0 := by rw [hc', hroot_eq]; abel
      have hcoeff := linearIndepOn_iff'.mp b.linearIndepOn_root b.support _ subset_rfl hzero
        s.val s.property
      simp only [↓reduceIte] at hcoeff
      have hnat : ((1 + f s.val : ℕ) : R) = 0 := by simpa [Nat.cast_add] using hcoeff
      exact Nat.succ_ne_zero (f s.val) (by simpa [Nat.add_comm] using Nat.cast_eq_zero.mp hnat)
    have hlt : (inversions P b (wordProd P b l)).ncard <
        (inversions P b (wordProd P b (s :: l))).ncard := by
      rw [wordProd_cons]
      exact (lt_ncard_inversions_ofIdx_mul_iff P b (wordProd P b l)
        (b.isPos_of_mem_support s.property)).mpr hnot
    have hle := ncard_inversions_wordProd_le_length P b (s :: l)
    rw [List.length_cons] at hle ⊢
    omega

/-- **Every Coxeter element is a reduced word**:
`#(inversions (wordProd P b l)) = b.support.card`. -/
theorem ncard_inversions_wordProd_eq_card_support {l : List b.support} (hl : l.Nodup)
    (hall : ∀ i, i ∈ l) : (inversions P b (wordProd P b l)).ncard = b.support.card := by
  classical
  rw [ncard_inversions_wordProd_eq_length_of_nodup P b l hl, ← List.toFinset_card_of_nodup hl,
    Finset.eq_univ_iff_forall.mpr fun i ↦ List.mem_toFinset.mpr (hall i), Finset.card_univ,
    Fintype.card_coe]

end TauCeti
