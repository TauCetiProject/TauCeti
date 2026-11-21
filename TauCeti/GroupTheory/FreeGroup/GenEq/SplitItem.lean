/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Fin.Embedding
public import Mathlib.Data.Fin.Tuple.Basic
public import TauCeti.GroupTheory.FreeGroup.GenEq.Section
import TauCeti.Data.Fin.Basic
import TauCeti.Data.Fin.Tuple.Basic

/-!
# Splitting an item of a generalised equation

The second kind of the elementary transformation ET5 of Makanin's process
(Kharlampovich–Myasnikov, §5.1) introduces a new boundary inside an item `h_k` of a generalised
equation `Ω` and renames the boundaries. This file makes the splitting
(`TauCeti.GenEq.splitItem`): the result has the items `h′_0, …, h′_ρ`, where `h′_k h′_{k+1}`
replaces `h_k` and every other item keeps its place; the boundary `j` of `Ω` becomes `j` for
`j ≤ k` and `j + 1` otherwise, so that the new boundary is `k + 1`. Bases, constant bases and
boundary connections move with the boundaries and items (`TauCeti.GenEq.mem_baseItems_splitItem`,
`TauCeti.GenEq.mem_constBases_splitItem`, `TauCeti.GenEq.mem_connections_splitItem`).

The substitution `h_k ↦ h′_k h′_{k+1}` (`TauCeti.GenEq.splitList` on words with letters,
`TauCeti.GenEq.splitWord` as a tuple of words in the new items) contracts the two adjacent items
`h′_k`, `h′_{k+1}` (`Fin.contractNth`). It carries the words `h[i, j]` of `Ω` to the words of
the result between the renumbered boundaries (`TauCeti.GenEq.segment_splitItem`; for the words up
to and from the new boundary, `TauCeti.GenEq.segment_splitItem_succAbove_succ_castSucc` and
`TauCeti.GenEq.cons_segment_splitItem_succ_castSucc_succAbove`), hence the equations of `Ω` to
those of the result, when `h_k` carries no constant base (`TauCeti.GenEq.equations_splitItem`).
Consequently a tuple is a point of the system of the result exactly when its image under the
substitution is a point of `Ω*` (`TauCeti.GenEq.mem_V_splitItem_iff`), and substituting words into
a side of the result is substituting into the corresponding side of `Ω`, with the words of the two
halves of `h_k` contracted by concatenation (`TauCeti.GenEq.substituteVars_splitList`).

On solutions: if the words of a solution of `Ω` are those of a solution of the result with the
words of `h′_k` and `h′_{k+1}` concatenated, every boundary of `Ω` keeps its position in the words
(`TauCeti.GenEq.Solution.prefixLength_succAbove_of_word_eq`). Conversely, cutting the word of
`h_k` in a solution of `Ω` strictly inside, after `d` letters, gives a solution of the result
(`TauCeti.GenEq.Solution.splitItem`), whose two halves concatenate back to the solution
(`TauCeti.GenEq.Solution.contractNth_splitItem_word`) and whose new boundary sits `d` letters after
the boundary `k` (`TauCeti.GenEq.Solution.prefixLength_splitItem_add_one`).

A constant base on `h_k` is moved to `h′_{k+1}`; that case does not occur in ET5, where the split
item carries no constant base, and every statement about equations excludes it. A solution never
cuts a constant item: its word has a single letter.

## Main definitions

* `TauCeti.GenEq.splitItem`: split the item `h_k` by a new boundary.
* `TauCeti.GenEq.splitList`, `TauCeti.GenEq.splitWord`: the substitution `h_k ↦ h′_k h′_{k+1}` on
  words with letters, and as a tuple of words in the new items.
* `TauCeti.GenEq.Solution.splitItem`: a solution with the word of `h_k` cut strictly inside.

## Main results

* `TauCeti.GenEq.segment_splitItem`, `TauCeti.GenEq.equations_splitItem`: the words and the
  equations of the result are the images of those of `Ω`.
* `TauCeti.GenEq.mem_V_splitItem_iff`: the points of the system of the result are the tuples
  whose image under the substitution is a point of `Ω*`, in every `F(A)`-group.
* `TauCeti.GenEq.Solution.prefixLength_succAbove_of_word_eq`: a boundary of `Ω` keeps its
  position in the words of a solution.
* `TauCeti.GenEq.Solution.contractNth_splitItem_word`,
  `TauCeti.GenEq.Solution.prefixLength_splitItem_add_one`: cutting a solution inside `h_k` and
  merging the halves back are inverse, and the new boundary sits at the cut.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §5.1, ET5.
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod
open FreeGroup (substituteVars)

variable {A : Type*} (Ω : GenEq A)

/-! ### Splitting an item -/

/-- Split the item `h_k` into two items by a new boundary: the items `h′_k` and `h′_{k+1}` of the
result replace `h_k`, and the boundary `j` of `Ω` becomes the boundary `j` if `j ≤ k` and `j + 1`
otherwise, so that the new boundary is `k + 1`. The bases, signs, duality, constant bases and
boundary connections are those of `Ω` at the renumbered boundaries and items; a constant base on
`h_k` goes to `h′_{k+1}`. -/
abbrev splitItem (k : Fin Ω.numItems) : GenEq A where
  numItems := Ω.numItems + 1
  numBases := Ω.numBases
  left μ := k.succ.castSucc.succAbove (Ω.left μ)
  right μ := k.succ.castSucc.succAbove (Ω.right μ)
  left_lt_right μ := Fin.strictMono_succAbove _ (Ω.left_lt_right μ)
  sign := Ω.sign
  dual := Ω.dual
  dual_involutive := Ω.dual_involutive
  constBases := Ω.constBases.map
    ((Fin.succAboveEmb k.castSucc).prodMap (Function.Embedding.refl _))
  connections := Ω.connections.map
    ((Fin.succAboveEmb k.succ.castSucc).prodMap
      ((Function.Embedding.refl _).prodMap (Fin.succAboveEmb k.succ.castSucc)))
  bounds_of_mem_connections := by
    simp only [Finset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    obtain ⟨h₁, h₂, h₃, h₄⟩ := Ω.bounds_of_mem_connections c hc
    have hs := Fin.strictMono_succAbove k.succ.castSucc
    exact ⟨hs h₁, hs h₂, hs h₃, hs h₄⟩
  dual_mem_connections := by
    simp only [Finset.mem_map]
    rintro _ ⟨c, hc, rfl⟩
    exact ⟨_, Ω.dual_mem_connections c hc, rfl⟩

/-- The substitution `h_k ↦ h′_k h′_{k+1}` on words in the items of `Ω` and the letters of `A`,
renumbering the other items as in `Ω.splitItem k`. No free reduction takes place. -/
def splitList (k : Fin Ω.numItems) (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    List ((Fin (Ω.numItems + 1) ⊕ A) × Bool) :=
  w.flatMap (FreeGroup.substituteLetter (Sum.elim
    (Fin.contractNth k.castSucc (· ++ ·) fun j => [(Sum.inl j, true)])
    fun a => [(Sum.inr a, true)]))

/-- The substitution `h_k ↦ h′_k h′_{k+1}` of ET5 for a split item, as a tuple of words in
`F(A)[h′]`: the product of the adjacent items `h′_k`, `h′_{k+1}` replaces `h_k`, and every other
item goes to the item with its new number. -/
def splitWord (k : Fin Ω.numItems) : Fin Ω.numItems → GX (FreeGroup A) (Fin (Ω.numItems + 1)) :=
  Fin.contractNth k.castSucc (· * ·) fun j => inr (FreeGroup.of j)

variable {Ω} {k : Fin Ω.numItems}

/-- The constant bases of `Ω.splitItem k` are those of `Ω` with their items renumbered (`h_k` goes
to `h′_{k+1}`). -/
theorem mem_constBases_splitItem {b : Fin (Ω.numItems + 1) × (A × Bool)} :
    b ∈ (Ω.splitItem k).constBases ↔
      ∃ b' ∈ Ω.constBases, (k.castSucc.succAbove b'.1, b'.2) = b :=
  Finset.mem_map

/-- The boundary connections of `Ω.splitItem k` are those of `Ω` with their boundaries
renumbered. -/
theorem mem_connections_splitItem
    {c : Fin (Ω.numItems + 2) × Fin Ω.numBases × Fin (Ω.numItems + 2)} :
    c ∈ (Ω.splitItem k).connections ↔ ∃ c' ∈ Ω.connections,
      (k.succ.castSucc.succAbove c'.1, c'.2.1, k.succ.castSucc.succAbove c'.2.2) = c :=
  Finset.mem_map

/-- The renumbering of the boundaries of `Ω` in `Ω.splitItem k`: `j ↦ j` for `j ≤ k`, and
`j ↦ j + 1` otherwise. -/
private theorem val_succAbove_succ_castSucc (i : Fin (Ω.numItems + 1)) :
    (k.succ.castSucc.succAbove i : ℕ) = if (i : ℕ) ≤ k then (i : ℕ) else i + 1 := by
  simp [Fin.val_succAbove, Nat.lt_succ_iff]

/-- A renumbered boundary of `Ω.splitItem k` crosses a base exactly when the boundary of `Ω`
does. -/
theorem crosses_splitItem_succAbove_iff {i : Fin (Ω.numItems + 1)} {μ : Fin Ω.numBases} :
    (Ω.splitItem k).Crosses (k.succ.castSucc.succAbove i) μ ↔ Ω.Crosses i μ := by
  simp only [crosses_iff, (Fin.strictMono_succAbove _).lt_iff_lt]

/-- The new boundary of `Ω.splitItem k` crosses exactly the bases containing the item `h_k`. -/
theorem crosses_splitItem_succ_castSucc_iff {μ : Fin Ω.numBases} :
    (Ω.splitItem k).Crosses k.succ.castSucc μ ↔ k ∈ Ω.baseItems μ := by
  rw [mem_baseItems, crosses_iff, Fin.lt_def, Fin.lt_def, val_succAbove_succ_castSucc,
    val_succAbove_succ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_succ]
  split_ifs <;> lia

/-- The items of a base of `Ω.splitItem k` are the items sent into the base of `Ω` when `h′_k` and
`h′_{k+1}` are merged back into `h_k` (`Fin.predAbove`). -/
theorem mem_baseItems_splitItem {ν : Fin Ω.numBases} {x : Fin (Ω.numItems + 1)} :
    x ∈ (Ω.splitItem k).baseItems ν ↔ k.predAbove x ∈ Ω.baseItems ν := by
  rw [mem_baseItems, mem_baseItems, val_succAbove_succ_castSucc, val_succAbove_succ_castSucc,
    Fin.val_predAbove]
  split_ifs <;> lia

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes the empty word to the empty word. -/
@[simp]
theorem splitList_nil : Ω.splitList k [] = [] :=
  List.flatMap_nil

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes concatenations to concatenations. -/
@[simp]
theorem splitList_append (w w' : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    Ω.splitList k (w ++ w') = Ω.splitList k w ++ Ω.splitList k w' :=
  List.flatMap_append

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes formal inverses to formal inverses. -/
theorem splitList_invRev (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    Ω.splitList k (FreeGroup.invRev w) = FreeGroup.invRev (Ω.splitList k w) :=
  FreeGroup.flatMap_substituteLetter_invRev _ w

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes the item `h_k` to `h′_k h′_{k+1}`. -/
@[simp]
theorem splitList_singleton_inl_self :
    Ω.splitList k [(Sum.inl k, true)] = [(Sum.inl k.castSucc, true), (Sum.inl k.succ, true)] := by
  simp [splitList, Fin.contractNth_apply_of_eq k.castSucc _ _ k rfl]

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes `h_k⁻¹` to `h′_{k+1}⁻¹ h′_k⁻¹`. -/
@[simp]
theorem splitList_singleton_inl_self_false :
    Ω.splitList k [(Sum.inl k, false)] =
      [(Sum.inl k.succ, false), (Sum.inl k.castSucc, false)] := by
  simp [splitList, Fin.contractNth_apply_of_eq k.castSucc _ _ k rfl, FreeGroup.invRev]

/-- The substitution `h_k ↦ h′_k h′_{k+1}` takes an item `h_j ^ ±1` other than `h_k ^ ±1` to the
item with its new number. -/
@[simp]
theorem splitList_singleton_inl_of_ne {j : Fin Ω.numItems} (hj : j ≠ k) (b : Bool) :
    Ω.splitList k [(Sum.inl j, b)] = [(Sum.inl (k.castSucc.succAbove j), b)] := by
  cases b <;> simp [splitList, FreeGroup.invRev,
    Fin.contractNth_apply_of_ne k.castSucc _ _ j (Fin.val_ne_of_ne hj).symm]

/-- The substitution `h_k ↦ h′_k h′_{k+1}` keeps the letters of `A^{±1}`. -/
@[simp]
theorem splitList_singleton_inr (a : A) (b : Bool) :
    Ω.splitList k [(Sum.inr a, b)] = [(Sum.inr a, b)] := by
  cases b <;> simp [splitList, FreeGroup.invRev]

/-- The item `h_j` of `Ω` becomes the items between the renumbered boundaries `j` and `j + 1`
of `Ω.splitItem k`: `h′_k h′_{k+1}` for `j = k`, and a single item otherwise. -/
private theorem segment_splitItem_castSucc_succ (x : Fin Ω.numItems) :
    (Ω.splitItem k).segment (k.succ.castSucc.succAbove x.castSucc)
        (k.succ.castSucc.succAbove x.succ) true = Ω.splitList k [(Sum.inl x, true)] := by
  have h₁ := (Ω.splitItem k).segment_succ x.castSucc true
  have h₂ := (Ω.splitItem k).segment_succ x.succ true
  simp only [Fin.val_castSucc, Fin.val_succ] at h₁ h₂
  rw [val_succAbove_succ_castSucc, val_succAbove_succ_castSucc]
  simp only [Fin.val_castSucc, Fin.val_succ]
  rcases lt_trichotomy x k with h | h | h
  · have : (x : ℕ) < k := h
    simp only [(by lia : (x : ℕ) ≤ k), (by lia : (x : ℕ) + 1 ≤ k), ite_true, h₁,
      splitList_singleton_inl_of_ne h.ne,
      Fin.succAbove_of_castSucc_lt _ _ (Fin.castSucc_lt_castSucc_iff.2 h)]
  · subst h
    simp only [le_refl, ite_true, (by lia : ¬ (x : ℕ) + 1 ≤ x), ite_false,
      splitList_singleton_inl_self]
    rw [← (Ω.splitItem x).segment_append (Nat.le_succ _) (Nat.le_succ _), h₁, h₂]
    rfl
  · have : (k : ℕ) < x := h
    simp only [(by lia : ¬ (x : ℕ) ≤ k), (by lia : ¬ (x : ℕ) + 1 ≤ k), ite_false,
      splitList_singleton_inl_of_ne h.ne',
      Fin.succAbove_of_le_castSucc _ _ (Fin.castSucc_le_castSucc_iff.2 h.le)]
    simpa only [Fin.val_succ] using h₂

/-- The words `h′[0, j′]` of `Ω.splitItem k` from the start to a renumbered boundary are the
words `h[0, j]` of `Ω` with `h_k` replaced by `h′_k h′_{k+1}`. -/
private theorem segment_zero_splitItem (i : Fin (Ω.numItems + 1)) :
    (Ω.splitItem k).segment 0 (k.succ.castSucc.succAbove i) true =
      Ω.splitList k (Ω.segment 0 i true) := by
  induction i using Fin.induction with
  | zero =>
    rw [Fin.val_zero, Ω.segment_eq_nil_of_le le_rfl, (Ω.splitItem k).segment_eq_nil_of_le
      (by rw [val_succAbove_succ_castSucc]; simp), splitList_nil]
  | succ x ih =>
    have hm := Fin.strictMono_succAbove k.succ.castSucc x.castSucc_lt_succ
    rw [← (Ω.splitItem k).segment_append (Nat.zero_le _) (Fin.le_def.1 hm.le), ih,
      segment_splitItem_castSucc_succ, ← splitList_append, Fin.val_succ, Fin.val_castSucc,
      ← Ω.segment_succ x true, Ω.segment_append (Nat.zero_le _) (Nat.le_succ _)]

/-- The word `h′[i′, j′] ^ ±1` between the renumbered boundaries `i′`, `j′` of `Ω.splitItem k`
is the word `h[i, j] ^ ±1` of `Ω` with `h_k` replaced by `h′_k h′_{k+1}`. -/
theorem segment_splitItem (i j : Fin (Ω.numItems + 1)) (s : Bool) :
    (Ω.splitItem k).segment (k.succ.castSucc.succAbove i) (k.succ.castSucc.succAbove j) s =
      Ω.splitList k (Ω.segment i j s) := by
  have htrue : (Ω.splitItem k).segment (k.succ.castSucc.succAbove i)
      (k.succ.castSucc.succAbove j) true = Ω.splitList k (Ω.segment i j true) := by
    rcases le_or_gt i j with hij | hji
    · have hm := (Fin.strictMono_succAbove k.succ.castSucc).monotone hij
      refine List.append_cancel_left (as := (Ω.splitItem k).segment 0
        (k.succ.castSucc.succAbove i) true) ?_
      rw [(Ω.splitItem k).segment_append (Nat.zero_le _) (Fin.le_def.1 hm),
        segment_zero_splitItem, segment_zero_splitItem, ← splitList_append,
        Ω.segment_append (Nat.zero_le _) (Fin.le_def.1 hij)]
    · have hm := Fin.strictMono_succAbove k.succ.castSucc hji
      rw [Ω.segment_eq_nil_of_le (Fin.le_def.1 hji.le),
        (Ω.splitItem k).segment_eq_nil_of_le (Fin.le_def.1 hm.le), splitList_nil]
  cases s
  · rw [segment_false, segment_false, htrue, splitList_invRev]
  · exact htrue

/-- The word of `Ω.splitItem k` from a renumbered boundary `i ≤ k` to the new boundary is the image
of the word `h[i, k]` of `Ω` followed by `h′_k`. -/
theorem segment_splitItem_succAbove_succ_castSucc {i : Fin (Ω.numItems + 1)} (hi : (i : ℕ) ≤ k) :
    (Ω.splitItem k).segment (k.succ.castSucc.succAbove i) (k.succ.castSucc : ℕ) true =
      Ω.splitList k (Ω.segment i k true) ++ [(Sum.inl k.castSucc, true)] := by
  have h := segment_splitItem (k := k) i k.castSucc true
  rw [(by simp : (k.succ.castSucc.succAbove k.castSucc : ℕ) = k), Fin.val_castSucc] at h
  rw [← h, ← (Ω.splitItem k).segment_succ k.castSucc true]
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact ((Ω.splitItem k).segment_append
    (by rw [val_succAbove_succ_castSucc, ite_eq_left hi]; exact hi) (Nat.le_add_right _ 1)).symm

/-- The letter `h′_k` followed by the word of `Ω.splitItem k` from the new boundary to a
renumbered boundary `j > k` is the image of the word `h[k, j]` of `Ω`. -/
theorem cons_segment_splitItem_succ_castSucc_succAbove {j : Fin (Ω.numItems + 1)}
    (hj : (k : ℕ) < j) :
    (Sum.inl k.castSucc, true) ::
        (Ω.splitItem k).segment (k.succ.castSucc : ℕ) (k.succ.castSucc.succAbove j) true =
      Ω.splitList k (Ω.segment k j true) := by
  have h := segment_splitItem (k := k) k.castSucc j true
  rw [(by simp : (k.succ.castSucc.succAbove k.castSucc : ℕ) = k), Fin.val_castSucc] at h
  rw [← h, ← List.singleton_append, ← (Ω.splitItem k).segment_succ k.castSucc true]
  simp only [Fin.val_castSucc, Fin.val_succ]
  exact (Ω.splitItem k).segment_append (Nat.le_add_right _ 1)
    (by rw [val_succAbove_succ_castSucc, ite_eq_right hj.not_ge]; lia)

/-- The basic equation of a base of `Ω.splitItem k` is the basic equation of the base in `Ω`
with `h_k` replaced by `h′_k h′_{k+1}`. -/
theorem basicEquation_splitItem (μ : Fin Ω.numBases) :
    (Ω.splitItem k).basicEquation μ =
      Prod.map (Ω.splitList k) (Ω.splitList k) (Ω.basicEquation μ) :=
  Prod.ext (by simp only [basicEquation_fst, Prod.map_fst]; exact segment_splitItem _ _ _)
    (by simp only [basicEquation_snd, Prod.map_snd]; exact segment_splitItem _ _ _)

/-- The coefficient equation of a constant base of `Ω` on an item other than `h_k`, moved to
`Ω.splitItem k`, is the coefficient equation in `Ω` with the item renumbered. -/
theorem coeffEquation_splitItem {b : Fin Ω.numItems × (A × Bool)} (hb : b.1 ≠ k) :
    (Ω.splitItem k).coeffEquation (k.castSucc.succAbove b.1, b.2) =
      Prod.map (Ω.splitList k) (Ω.splitList k) (Ω.coeffEquation b) := by
  obtain ⟨j, a, t⟩ := b
  have hj : j ≠ k := hb
  exact Prod.ext (by simp [hj]) (by simp)

/-- The boundary equation of a triple of `Ω.splitItem k` at renumbered boundaries is the boundary
equation of the triple in `Ω` with `h_k` replaced by `h′_k h′_{k+1}`. -/
theorem boundaryEquation_splitItem
    (c : Fin (Ω.numItems + 1) × Fin Ω.numBases × Fin (Ω.numItems + 1)) :
    (Ω.splitItem k).boundaryEquation
        (k.succ.castSucc.succAbove c.1, c.2.1, k.succ.castSucc.succAbove c.2.2) =
      Prod.map (Ω.splitList k) (Ω.splitList k) (Ω.boundaryEquation c) := by
  obtain ⟨p, μ, q⟩ := c
  refine Prod.ext (by simpa using segment_splitItem _ _ _) ?_
  by_cases hs : Ω.sign μ = Ω.sign (Ω.dual μ)
  · rw [Prod.map_snd, Ω.boundaryEquation_snd_of_sign_eq (c := (p, μ, q)) hs,
      (Ω.splitItem k).boundaryEquation_snd_of_sign_eq (c := (_, μ, _)) hs]
    exact segment_splitItem _ _ _
  · rw [Prod.map_snd, Ω.boundaryEquation_snd_of_sign_ne (c := (p, μ, q)) hs,
      (Ω.splitItem k).boundaryEquation_snd_of_sign_ne (c := (_, μ, _)) hs]
    exact segment_splitItem _ _ _

/-- When `h_k` carries no constant base, the equations of `Ω.splitItem k` are the equations of
`Ω` with `h_k` replaced by `h′_k h′_{k+1}`. -/
theorem equations_splitItem (hk' : ¬ Ω.IsConstantItem k) :
    (Ω.splitItem k).equations = Prod.map (Ω.splitList k) (Ω.splitList k) '' Ω.equations := by
  have hne {b : Fin Ω.numItems × (A × Bool)} (hb : b ∈ Ω.constBases) : b.1 ≠ k :=
    fun h => hk' (Ω.isConstantItem_iff.2 ⟨b, hb, h⟩)
  refine Set.Subset.antisymm ((forall_mem_equations _).2 ⟨fun μ => ⟨_, Ω.basicEquation_mem_equations
    μ, (basicEquation_splitItem (k := k) μ).symm⟩, fun b hb => ?_, fun c hc => ?_⟩)
    (Set.image_subset_iff.2 ((forall_mem_equations _).2 ⟨fun μ => ?_, fun b hb => ?_,
      fun c hc => ?_⟩))
  · obtain ⟨b, hb', rfl⟩ := mem_constBases_splitItem.1 hb
    exact ⟨_, Ω.coeffEquation_mem_equations hb', (coeffEquation_splitItem (hne hb')).symm⟩
  · obtain ⟨c, hc', rfl⟩ := mem_connections_splitItem.1 hc
    exact ⟨_, Ω.boundaryEquation_mem_equations hc', (boundaryEquation_splitItem (k := k) c).symm⟩
  · rw [Set.mem_preimage, ← basicEquation_splitItem (k := k)]
    exact (Ω.splitItem k).basicEquation_mem_equations μ
  · rw [Set.mem_preimage, ← coeffEquation_splitItem (hne hb)]
    exact (Ω.splitItem k).coeffEquation_mem_equations (mem_constBases_splitItem.2 ⟨b, hb, rfl⟩)
  · rw [Set.mem_preimage, ← boundaryEquation_splitItem (k := k)]
    exact (Ω.splitItem k).boundaryEquation_mem_equations
      (mem_connections_splitItem.2 ⟨c, hc, rfl⟩)

/-- Evaluating the image of an item under `h_k ↦ h′_k h′_{k+1}` multiplies the values at `h′_k`
and `h′_{k+1}`, and reads every other item at its new number. -/
@[simp]
theorem eval_splitWord {H : Type*} [Group H] (ι : FreeGroup A →* H) (v : Fin (Ω.numItems + 1) → H)
    (j : Fin Ω.numItems) :
    eval ι v (Ω.splitWord k j) = Fin.contractNth k.castSucc (· * ·) v j := by
  rw [splitWord, ← Function.comp_apply (f := eval ι v),
    Fin.comp_contractNth _ _ (map_mul (eval ι v))]
  simp [Function.comp_def]

/-- Evaluating a word with `h_k` replaced by `h′_k h′_{k+1}` is evaluating the word at the image
of the point under the word map of the substitution. -/
theorem lift_mk_splitList {H : Type*} [Group H] (ι : FreeGroup A →* H)
    (v : Fin (Ω.numItems + 1) → H) (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk (Ω.splitList k w)) =
      FreeGroup.lift (Sum.elim (wordMap ι (Ω.splitWord k) v) (ι ∘ FreeGroup.of))
        (FreeGroup.mk w) := by
  rw [splitList, FreeGroup.mk_flatMap_substituteLetter, ← MonoidHom.comp_apply]
  congr 1
  refine FreeGroup.ext_hom _ _ fun x => ?_
  rcases x with j | a
  · -- Evaluation commutes with contracting the words of `h′_k` and `h′_{k+1}`.
    have h := congr_fun (Fin.comp_contractNth (· ++ ·) (· * ·)
      (f := fun l => FreeGroup.lift (Sum.elim v (ι ∘ FreeGroup.of)) (FreeGroup.mk l))
      (fun _ _ => by rw [← FreeGroup.mul_mk, map_mul]) k.castSucc fun i => [(Sum.inl i, true)]) j
    simpa [FreeGroup.lift_mk, Function.comp_def] using h
  · simp [FreeGroup.lift_mk]

/-- Substituting words for the items of `Ω.splitItem k` into a word with `h_k` replaced by
`h′_k h′_{k+1}` is substituting into the word itself, with the concatenation of the words of
`h′_k` and `h′_{k+1}` for `h_k`. -/
theorem substituteVars_splitList (W : Fin (Ω.numItems + 1) → List (A × Bool))
    (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    substituteVars W (Ω.splitList k w) =
      substituteVars (Fin.contractNth k.castSucc (· ++ ·) W) w := by
  -- Substitution commutes with contracting the words of `h′_k` and `h′_{k+1}`.
  have hW (j : Fin Ω.numItems) : substituteVars W
      (Fin.contractNth k.castSucc (· ++ ·) (fun i => [(Sum.inl i, true)]) j) =
        Fin.contractNth k.castSucc (· ++ ·) W j := by
    simpa [Function.comp_def] using congr_fun (Fin.comp_contractNth (· ++ ·) (· ++ ·)
      (FreeGroup.substituteVars_append W) k.castSucc fun i => [(Sum.inl i, true)]) j
  induction w with
  | nil => simp
  | cons x w ih =>
    rw [← List.singleton_append, splitList_append, FreeGroup.substituteVars_append,
      FreeGroup.substituteVars_append, ih]
    obtain ⟨j | a, b⟩ := x
    · cases b <;> simp [splitList, hW, FreeGroup.substituteVars_invRev]
    · simp

/-- When `h_k` carries no constant base, a tuple is a point of the system of `Ω.splitItem k`
exactly when its image under `h_k ↦ h′_k h′_{k+1}` is a point of `Ω*`. -/
theorem mem_V_splitItem_iff (hk' : ¬ Ω.IsConstantItem k) {H : Type*} [Group H]
    (ι : FreeGroup A →* H) {v : Fin (Ω.numItems + 1) → H} :
    v ∈ V ι (Ω.splitItem k).toSystem ↔ wordMap ι (Ω.splitWord k) v ∈ V ι Ω.toSystem := by
  rw [mem_V_toSystem_iff, mem_V_toSystem_iff, equations_splitItem hk', Set.forall_mem_image]
  refine forall₂_congr fun e _ => ?_
  rw [Prod.map_fst, Prod.map_snd, lift_mk_splitList, lift_mk_splitList]

/-- If the words of a solution `U` of `Ω` are the words of a solution `U′` of `Ω.splitItem k`
with those of `h′_k` and `h′_{k+1}` concatenated, a boundary of `Ω` sits in the words of `U` at
the position of its renumbered boundary in the words of `U′`. -/
theorem Solution.prefixLength_succAbove_of_word_eq (U' : (Ω.splitItem k).Solution) (U : Ω.Solution)
    (h : U.word = Fin.contractNth k.castSucc (· ++ ·) U'.word) (i : Fin (Ω.numItems + 1)) :
    U'.prefixLength (k.succ.castSucc.succAbove i) = U.prefixLength i := by
  have h₁ := U'.length_substituteVars_segment_eq_sub true (k.succ.castSucc.succAbove 0)
    (k.succ.castSucc.succAbove i)
  have h₂ := U.length_substituteVars_segment_eq_sub true 0 i
  have h₀ : ((k.succ.castSucc.succAbove 0 : Fin (Ω.numItems + 2)) : ℕ) = 0 := by simp
  rw [segment_splitItem, substituteVars_splitList, ← h, Fin.val_zero, h₂, h₀] at h₁
  simpa using h₁.symm

/-! ### Cutting a solution inside an item -/

/-- When `h_k` carries no constant base, a property of the two sides of every equation of `Ω`,
substituted with the words of `h′_k` and `h′_{k+1}` concatenated for `h_k`, is the property of the
two sides of every equation of `Ω.splitItem k`, substituted with the words. -/
private theorem forall_mem_equations_splitItem (hk' : ¬ Ω.IsConstantItem k)
    (W : Fin (Ω.numItems + 1) → List (A × Bool)) (P : List (A × Bool) → List (A × Bool) → Prop)
    (h : ∀ e ∈ Ω.equations, P (substituteVars (Fin.contractNth k.castSucc (· ++ ·) W) e.1)
      (substituteVars (Fin.contractNth k.castSucc (· ++ ·) W) e.2)) :
    ∀ e ∈ (Ω.splitItem k).equations, P (substituteVars W e.1) (substituteVars W e.2) := by
  rw [equations_splitItem hk', Set.forall_mem_image]
  intro e he
  rw [Prod.map_fst, Prod.map_snd, substituteVars_splitList, substituteVars_splitList]
  exact h e he

namespace Solution

/-- A solution of `Ω` with the word of `h_k` cut strictly inside, after its first `d` letters, as a
solution of `Ω.splitItem k`: `h′_k` gets the first `d` letters of the word of `h_k`, `h′_{k+1}`
the others, and every other item keeps its word. -/
def splitItem (U : Ω.Solution) {d : ℕ} (hd₀ : 0 < d) (hd : d < (U.word k).length) :
    (Ω.splitItem k).Solution :=
  -- The word of a constant item has one letter, so `h_k` carries no constant base.
  have hk' : ¬ Ω.IsConstantItem k := fun hc => by
    obtain ⟨b, hb, rfl⟩ := Ω.isConstantItem_iff.1 hc
    rw [U.word_of_mem_constBases hb, List.length_singleton] at hd
    lia
  -- Concatenating the two halves of the word of `h_k` gives back the words of `U`.
  have hW : Fin.contractNth k.castSucc (· ++ ·) (Fin.insertNth (α := fun _ => List (A × Bool))
      k.castSucc ((U.word k).take d) (Function.update U.word k ((U.word k).drop d))) = U.word := by
    rw [Fin.contractNth_castSucc_insertNth_castSucc]
    simp
  { word := Fin.insertNth (α := fun _ => List (A × Bool)) k.castSucc ((U.word k).take d)
      (Function.update U.word k ((U.word k).drop d))
    isReduced_word x := by
      rcases Fin.eq_self_or_eq_succAbove k.castSucc x with rfl | ⟨j, rfl⟩
      · rw [Fin.insertNth_apply_same]
        exact (U.isReduced_word k).infix (List.take_prefix _ _).isInfix
      · rw [Fin.insertNth_apply_succAbove]
        rcases eq_or_ne j k with hj | hj
        · rw [hj, Function.update_self]
          exact (U.isReduced_word k).infix (List.drop_suffix _ _).isInfix
        · rw [Function.update_of_ne hj]
          exact U.isReduced_word j
    word_ne_nil x := by
      rcases Fin.eq_self_or_eq_succAbove k.castSucc x with rfl | ⟨j, rfl⟩
      · rw [Fin.insertNth_apply_same, Ne, List.take_eq_nil_iff]
        exact fun h => h.elim hd₀.ne' (U.word_ne_nil k)
      · rw [Fin.insertNth_apply_succAbove]
        rcases eq_or_ne j k with hj | hj
        · rw [hj, Function.update_self, Ne, List.drop_eq_nil_iff]
          lia
        · rw [Function.update_of_ne hj]
          exact U.word_ne_nil j
    isReduced_subst := forall_mem_equations_splitItem hk' _
      (fun u w => FreeGroup.IsReduced u ∧ FreeGroup.IsReduced w)
      (by rw [hW]; exact U.isReduced_subst)
    subst_eq := forall_mem_equations_splitItem hk' _ (· = ·)
      (by rw [hW]; exact U.subst_eq) }

variable (U : Ω.Solution) {d : ℕ} (hd₀ : 0 < d) (hd : d < (U.word k).length)

/-- The item `h′_k` of the cut solution carries the first `d` letters of the word of `h_k`. -/
@[simp]
theorem splitItem_word_castSucc : (U.splitItem hd₀ hd).word k.castSucc = (U.word k).take d := by
  dsimp only [Solution.splitItem]
  exact Fin.insertNth_apply_same _ _ _

/-- The item `h′_{k+1}` of the cut solution carries the word of `h_k` without its first `d`
letters. -/
@[simp]
theorem splitItem_word_succ : (U.splitItem hd₀ hd).word k.succ = (U.word k).drop d := by
  dsimp only [Solution.splitItem]
  rw [Fin.insertNth_castSucc_apply_succ, Function.update_self]

/-- Every item other than `h′_k`, `h′_{k+1}` keeps its word in the cut solution. -/
@[simp]
theorem splitItem_word_succAbove {j : Fin Ω.numItems} (hj : j ≠ k) :
    (U.splitItem hd₀ hd).word (k.castSucc.succAbove j) = U.word j := by
  dsimp only [Solution.splitItem]
  exact (Fin.insertNth_apply_succAbove _ _ _ _).trans (Function.update_of_ne hj _ _)

/-- Concatenating the words of `h′_k` and `h′_{k+1}` of the cut solution gives back the words of
the solution. -/
theorem contractNth_splitItem_word :
    Fin.contractNth k.castSucc (· ++ ·) (U.splitItem hd₀ hd).word = U.word := by
  dsimp only [Solution.splitItem]
  rw [Fin.contractNth_castSucc_insertNth_castSucc]
  simp

/-- The new boundary of the cut solution sits `d` letters after the boundary `k`. -/
theorem prefixLength_splitItem_add_one :
    (U.splitItem hd₀ hd).prefixLength (k + 1) = U.prefixLength k + d := by
  have h := (U.splitItem hd₀ hd).length_substituteVars_segment_add_prefixLength true
    (Nat.le_add_right (k : ℕ) 1)
  have h₁ := (Ω.splitItem k).segment_succ k.castSucc true
  have h₂ := (U.splitItem hd₀ hd).prefixLength_succAbove_of_word_eq U
    (U.contractNth_splitItem_word hd₀ hd).symm k.castSucc
  simp only [Fin.val_castSucc] at h₁
  rw [(by simp : (k.succ.castSucc.succAbove k.castSucc : ℕ) = k), Fin.val_castSucc] at h₂
  rw [h₁, FreeGroup.substituteVars_singleton_inl, h₂, splitItem_word_castSucc, List.length_take,
    min_eq_left hd.le] at h
  lia

end Solution

end GenEq

end TauCeti
