/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.InfWord.Int
public import TauCeti.GroupTheory.InfWord.Mul

/-!
# Cyclically reduced and cyclically decomposable infinite words

Let `Λ` be a discretely ordered abelian group and `X` a set. A reduced `Λ`-word `w : InfWord Λ X`
is *cyclically reduced* (`TauCeti.InfWord.IsCyclicallyReduced`) when `w ++ w` is reduced,
equivalently when `w` is reduced and (if nonempty) its first letter is not the inverse of its last
letter. It is *cyclically decomposable* (`w ∈ TauCeti.InfWord.CDR Λ X`) when `w` is reduced and
admits a reduced factorisation `w = c⁻¹ ++ v ++ c` with `v` cyclically reduced.

The cyclic decomposition `w = c⁻¹ ++ v ++ c` is unique whenever it exists
(`TauCeti.InfWord.cyclic_decomp_unique`), and for every `w ∈ CDR Λ X` the square `w ∗ w` is defined
and equals `c⁻¹ ++ v ++ v ++ c` (`TauCeti.InfWord.isMul_self_of_cyclic_decomp`). In particular,
when `w ≠ ε` the cyclically reduced core `v` is nonempty and `|w| < |w ∗ w|`
(`TauCeti.InfWord.length_lt_of_isMul_self_of_mem_CDR`). This is axiom (L5) for subgroups of
`CDR Λ X`.

Over `Λ = ℤ`, every reduced word admits a cyclic decomposition (`TauCeti.InfWord.CDR_int_eq`), and
`InfWord.IsCyclicallyReduced` matches `FreeGroup.IsCyclicallyReduced`
(`TauCeti.InfWord.isCyclicallyReduced_ofList`). Over a non-Archimedean `Λ`, `CDR Λ X` is a strict
subset of the reduced words; see `TauCeti.GroupTheory.InfWord.Examples`.

## Main definitions

* `TauCeti.InfWord.IsCyclicallyReduced`: cyclically reduced `Λ`-words (`(w ++ w).IsReduced`).
* `TauCeti.InfWord.CDR`: the set `CDR(Λ, X)` of cyclically decomposable reduced `Λ`-words.

## Main results

* `TauCeti.InfWord.isCyclicallyReduced_iff`: `w` is cyclically reduced iff `w` is reduced and its
  first and last letters do not cancel.
* `TauCeti.InfWord.isCyclicallyReduced_inv`, `TauCeti.InfWord.inv_mem_CDR_iff`: both properties are
  closed under inversion.
* `TauCeti.InfWord.cyclic_decomp_unique`: uniqueness of the cyclic decomposition `c⁻¹ ++ v ++ c`.
* `TauCeti.InfWord.isMul_self_of_cyclic_decomp`: `(c⁻¹ ++ v ++ c) ∗ (c⁻¹ ++ v ++ c)` is defined
  and equals `c⁻¹ ++ v ++ v ++ c`.
* `TauCeti.InfWord.length_lt_of_isMul_self_of_mem_CDR`: if `w ∈ CDR Λ X` is nonempty and
  `IsMul w w z`, then `|w| < |z|`.
* `TauCeti.InfWord.isCyclicallyReduced_ofList`, `TauCeti.InfWord.isCyclicallyReduced_toList`:
  compatibility with `FreeGroup.IsCyclicallyReduced` for `Λ = ℤ`.
* `TauCeti.InfWord.CDR_int_eq`: over `Λ = ℤ`, `CDR ℤ X` is the set of all reduced words.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.1 and §4, Theorem 4.1.
-/

public section

namespace TauCeti

namespace InfWord

section General

variable {Λ X : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ]
  {u v w z c c₁ c₂ : InfWord Λ X}

/-- A `Λ`-word `w` is *cyclically reduced* when `w ++ w` is reduced, equivalently when `w` is
reduced and (if nonempty) its first letter is not the inverse of its last letter. -/
def IsCyclicallyReduced (w : InfWord Λ X) : Prop :=
  (w ++ w).IsReduced

/-- A `Λ`-word is cyclically reduced iff it is reduced and (when nonempty) its first letter is not
the inverse of its last letter. -/
theorem isCyclicallyReduced_iff :
    w.IsCyclicallyReduced ↔ w.IsReduced ∧
      (0 < w.length → w.letter (Order.succ 0) ≠ (w.letter w.length).map (Prod.map id not)) := by
  simp [IsCyclicallyReduced, isReduced_append_iff]

/-- Every cyclically reduced word is reduced. -/
@[grind →]
theorem IsCyclicallyReduced.isReduced (h : w.IsCyclicallyReduced) : w.IsReduced :=
  h.left_of_append

/-- The empty word is cyclically reduced. -/
@[simp]
theorem isCyclicallyReduced_empty : (empty Λ X).IsCyclicallyReduced := by
  simp [IsCyclicallyReduced]

/-- A word is cyclically reduced iff its inverse is. -/
@[simp]
theorem isCyclicallyReduced_inv : w⁻¹.IsCyclicallyReduced ↔ w.IsCyclicallyReduced := by
  simp [IsCyclicallyReduced, ← inv_append]

/-- Every constant word `x ^ α` is cyclically reduced. -/
theorem isCyclicallyReduced_ofFun_const (α : Λ) (l : X × Bool) :
    (ofFun α fun _ => l).IsCyclicallyReduced := by
  rw [isCyclicallyReduced_iff]
  refine ⟨isReduced_ofFun_const α l, fun hα => ?_⟩
  rw [length_ofFun] at hα
  have hα' : 0 < α := by grind
  rw [length_ofFun, max_eq_left hα'.le,
    letter_ofFun_of_pos_of_le (fun _ => l) (Order.lt_succ_self_of_lt hα') (Order.succ_le_of_lt hα'),
    letter_ofFun_of_pos_of_le (fun _ => l) hα' le_rfl]
  rcases l with ⟨x, s⟩
  cases s <;> simp [Prod.map]

/-- For a cyclically reduced word `w`, the product `w ∗ w` is defined and equals `w ++ w`. -/
theorem IsCyclicallyReduced.isMul_self (h : w.IsCyclicallyReduced) : IsMul w w (w ++ w) :=
  isMul_append h

/-- The set `CDR(Λ, X)` of *cyclically decomposable* reduced `Λ`-words: reduced words admitting a
reduced factorisation `w = c⁻¹ ++ v ++ c` with `v` cyclically reduced. -/
def CDR (Λ X : Type*) [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ] [SuccOrder Λ] :
    Set (InfWord Λ X) :=
  {w | w.IsReduced ∧ ∃ c v : InfWord Λ X, v.IsCyclicallyReduced ∧ w = c⁻¹ ++ v ++ c}

/-- Unfolding membership in `CDR Λ X`. -/
theorem mem_CDR_iff :
    w ∈ CDR Λ X ↔ w.IsReduced ∧ ∃ c v : InfWord Λ X, v.IsCyclicallyReduced ∧ w = c⁻¹ ++ v ++ c :=
  Iff.rfl

/-- Every word in `CDR Λ X` is reduced. -/
@[grind →]
theorem isReduced_of_mem_CDR (h : w ∈ CDR Λ X) : w.IsReduced := h.1

/-- Every cyclically reduced word lies in `CDR Λ X`. -/
theorem IsCyclicallyReduced.mem_CDR (h : w.IsCyclicallyReduced) : w ∈ CDR Λ X :=
  ⟨h.isReduced, empty Λ X, w, h, by simp⟩

/-- The empty word lies in `CDR Λ X`. -/
@[simp]
theorem empty_mem_CDR : empty Λ X ∈ CDR Λ X :=
  isCyclicallyReduced_empty.mem_CDR

/-- `CDR Λ X` is closed under inversion. -/
@[simp]
theorem inv_mem_CDR_iff : w⁻¹ ∈ CDR Λ X ↔ w ∈ CDR Λ X := by
  have key : ∀ {u : InfWord Λ X}, u ∈ CDR Λ X → u⁻¹ ∈ CDR Λ X := by
    rintro u ⟨hu, c, v, hv, rfl⟩
    refine ⟨hu.inv, c, v⁻¹, isCyclicallyReduced_inv.2 hv, ?_⟩
    simp [inv_append, append_assoc]
  exact ⟨fun h => by simpa using key h, key⟩

/-- If `c⁻¹ ++ v ++ c` is reduced and `v` is empty, then `c` is empty. -/
theorem eq_empty_of_isReduced_inv_append_empty_append (h : (c⁻¹ ++ v ++ c).IsReduced)
    (hv : v = empty Λ X) : c = empty Λ X := by
  subst hv
  simpa using h

/-- If `c⁻¹ ++ v ++ c` is reduced and `v` is cyclically reduced, then `c⁻¹ ++ (v ++ v) ++ c` is
also reduced. -/
theorem isReduced_inv_append_double_append (h : (c⁻¹ ++ v ++ c).IsReduced)
    (hv : v.IsCyclicallyReduced) : (c⁻¹ ++ (v ++ v) ++ c).IsReduced := by
  by_cases hve : v = empty Λ X
  · subst hve
    obtain rfl := eq_empty_of_isReduced_inv_append_empty_append h rfl
    simp
  have hvpos : 0 < v.length := length_pos_iff.2 hve
  have hcv : (c⁻¹ ++ v).IsReduced := h.left_of_append
  have hvc : (v ++ c).IsReduced := by
    rw [append_assoc] at h
    exact h.right_of_append
  have h1 : (c⁻¹ ++ (v ++ v)).IsReduced := by
    refine isReduced_append_iff.2 ⟨hcv.left_of_append, hv, fun hc _ => ?_⟩
    rw [letter_append_of_le v (Order.succ_le_of_lt hvpos)]
    exact hcv.letter_succ_zero_ne_of_append hc hvpos
  refine isReduced_append_iff.2 ⟨h1, hvc.right_of_append, fun _ hc => ?_⟩
  rw [← append_assoc, length_append, letter_append_length_add (c⁻¹ ++ v) v hvpos]
  exact hvc.letter_succ_zero_ne_of_append hvpos hc

/-- The product of a cyclically decomposed reduced word `c⁻¹ ++ v ++ c` with itself is defined and
equals `c⁻¹ ++ v ++ v ++ c`. -/
theorem isMul_self_of_cyclic_decomp (h : (c⁻¹ ++ v ++ c).IsReduced)
    (hv : v.IsCyclicallyReduced) :
    IsMul (c⁻¹ ++ v ++ c) (c⁻¹ ++ v ++ c) (c⁻¹ ++ v ++ v ++ c) := by
  have h1 : (c⁻¹ ++ (v ++ c)).IsReduced := by simpa [append_assoc] using h
  have h2 : ((c⁻¹ ++ v) ++ (v ++ c)).IsReduced := by
    simpa [append_assoc] using isReduced_inv_append_double_append h hv
  have hmul : IsMul ((c⁻¹ ++ v) ++ c) (c⁻¹ ++ (v ++ c)) ((c⁻¹ ++ v) ++ (v ++ c)) :=
    (isMul_append_inv_append_iff' h h1).2 (isMul_append h2)
  simpa [append_assoc] using hmul

/-- Every word in `CDR Λ X` has a defined square under `∗`. -/
theorem exists_isMul_self_of_mem_CDR (hw : w ∈ CDR Λ X) : ∃ z, IsMul w w z := by
  obtain ⟨hred, c, v, hv, rfl⟩ := hw
  exact ⟨_, isMul_self_of_cyclic_decomp hred hv⟩

/-- For every word `w ∈ CDR Λ X`, the partial product `w.mul w` is defined. -/
theorem mul_self_dom_of_mem_CDR (hw : w ∈ CDR Λ X) : (w.mul w).Dom :=
  mul_dom_iff.2 (exists_isMul_self_of_mem_CDR hw)

/-- Squaring a nonempty word in `CDR Λ X` strictly increases its length. -/
theorem length_lt_of_isMul_self_of_mem_CDR (hw : w ∈ CDR Λ X) (hne : w ≠ empty Λ X)
    (hz : IsMul w w z) : w.length < z.length := by
  obtain ⟨hred, c, v, hv, rfl⟩ := hw
  obtain rfl := hz.unique (isMul_self_of_cyclic_decomp hred hv)
  have hvne : v ≠ empty Λ X := by
    intro hve
    obtain rfl := eq_empty_of_isReduced_inv_append_empty_append hred hve
    exact hne (by simp [hve])
  have hvpos : 0 < v.length := length_pos_iff.2 hvne
  simp only [length_append, length_inv]
  grind

/-- Uniqueness of a cyclic decomposition `c⁻¹ ++ v ++ c` with `v` cyclically reduced. -/
theorem cyclic_decomp_unique {v₁ v₂ : InfWord Λ X} (hv₁ : v₁.IsCyclicallyReduced)
    (hv₂ : v₂.IsCyclicallyReduced) (heq : c₁⁻¹ ++ v₁ ++ c₁ = c₂⁻¹ ++ v₂ ++ c₂) :
    c₁ = c₂ ∧ v₁ = v₂ := by
  have key : ∀ {a₁ a₂ b₁ b₂ : InfWord Λ X}, b₁.IsCyclicallyReduced →
      a₁⁻¹ ++ b₁ ++ a₁ = a₂⁻¹ ++ b₂ ++ a₂ → a₁.length ≤ a₂.length → a₁ = a₂ ∧ b₁ = b₂ := by
    intro a₁ a₂ b₁ b₂ hb₁ h hle
    have htake : a₂⁻¹.take a₁.length = a₁⁻¹ := by
      have h1 := congrArg (·.take a₁.length) h
      have hlen1 : (a₁⁻¹ ++ b₁ ++ a₁).take a₁.length = a₁⁻¹ := by
        rw [append_assoc, ← length_inv a₁, take_append_length]
      have hlen2 : (a₂⁻¹ ++ b₂ ++ a₂).take a₁.length = a₂⁻¹.take a₁.length := by
        rw [append_assoc, take_append_of_le_length _ (by simpa using hle)]
      rw [hlen1, hlen2] at h1
      exact h1.symm
    set d := a₂⁻¹.drop a₁.length
    have ha₂inv : a₂⁻¹ = a₁⁻¹ ++ d := by rw [← htake, take_append_drop]
    have ha₂ : a₂ = d⁻¹ ++ a₁ := by rw [← inv_inv a₂, ha₂inv, inv_append, inv_inv]
    rw [ha₂inv, ha₂] at h
    have hb₁eq : b₁ = d ++ b₂ ++ d⁻¹ := by
      have h1 : a₁⁻¹ ++ (b₁ ++ a₁) = a₁⁻¹ ++ ((d ++ b₂ ++ d⁻¹) ++ a₁) := by
        simpa [append_assoc] using h
      exact (append_left_inj a₁).1 ((append_right_inj a₁⁻¹).1 h1)
    have hd : d = empty Λ X := by
      have hdbl : ((d ++ b₂) ++ (d⁻¹ ++ d) ++ (b₂ ++ d⁻¹)).IsReduced := by
        have : b₁ ++ b₁ = (d ++ b₂) ++ (d⁻¹ ++ d) ++ (b₂ ++ d⁻¹) := by
          simp [hb₁eq, append_assoc]
        rwa [← this]
      exact isReduced_inv_append_self_iff.1 hdbl.left_of_append.right_of_append
    refine ⟨?_, ?_⟩
    · simp [ha₂, hd]
    · simp [hb₁eq, hd]
  rcases le_total c₁.length c₂.length with hle | hle
  · exact key hv₁ heq hle
  · exact (key hv₂ heq.symm hle).imp Eq.symm Eq.symm

end General

section Int

variable {X : Type*}

/-- A list of letters is cyclically reduced as a `ℤ`-word iff it is cyclically reduced in the sense
of `FreeGroup.IsCyclicallyReduced`. -/
@[simp]
theorem isCyclicallyReduced_ofList {L : List (X × Bool)} :
    (ofList L).IsCyclicallyReduced ↔ FreeGroup.IsCyclicallyReduced L := by
  rw [isCyclicallyReduced_iff, isReduced_ofList, FreeGroup.isCyclicallyReduced_iff]
  refine and_congr_right fun _ => ?_
  cases L with
  | nil => simp
  | cons hd tl =>
    have hpos : (0 : ℤ) < (ofList (hd :: tl)).length := by simp
    have hlast : (ofList (hd :: tl)).letter (ofList (hd :: tl)).length = (hd :: tl).getLast? := by
      have hlen : ((hd :: tl).length : ℤ) = (((hd :: tl).length - 1 : ℕ) : ℤ) + 1 := by simp
      rw [length_ofList, hlen, letter_ofList_natCast_add_one, List.getLast?_eq_getElem?]
    rw [Order.succ_eq_add_one, zero_add, letter_ofList_one, hlast, List.head?_cons]
    obtain ⟨a, ha⟩ : ∃ a, (hd :: tl).getLast? = some a :=
      Option.ne_none_iff_exists'.1 (by simp)
    rw [ha]
    simp only [hpos, true_implies, Option.map_some, ne_eq, Option.some.injEq,
      Option.mem_def, forall_eq']
    rcases a with ⟨x, s⟩
    rcases hd with ⟨y, t⟩
    cases s <;> cases t <;> simp [Prod.map, eq_comm]

/-- A `ℤ`-word is cyclically reduced iff its list of letters is cyclically reduced. -/
@[simp]
theorem isCyclicallyReduced_toList {w : InfWord ℤ X} :
    FreeGroup.IsCyclicallyReduced w.toList ↔ w.IsCyclicallyReduced := by
  rw [← isCyclicallyReduced_ofList, ofList_toList]

/-- Over `Λ = ℤ`, every reduced word admits a cyclic decomposition. -/
theorem isReduced_mem_CDR_int {w : InfWord ℤ X} (hw : w.IsReduced) : w ∈ CDR ℤ X := by
  classical
  refine ⟨hw, (ofList (FreeGroup.reduceCyclically.conjugator w.toList))⁻¹,
    ofList (FreeGroup.reduceCyclically w.toList),
    isCyclicallyReduced_ofList.2
      (FreeGroup.reduceCyclically.isCyclicallyReduced (isReduced_toList.2 hw)), ?_⟩
  have h := congrArg ofList (FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically w.toList)
  simpa [ofList_append, ofList_invRev, ofList_toList] using h.symm

/-- Over `Λ = ℤ`, `CDR ℤ X` is the set of all reduced words. -/
theorem CDR_int_eq : CDR ℤ X = {w : InfWord ℤ X | w.IsReduced} :=
  Set.ext fun _ => ⟨isReduced_of_mem_CDR, isReduced_mem_CDR_int⟩

end Int

end InfWord

end TauCeti
