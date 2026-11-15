/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.CDR
public import TauCeti.GroupTheory.InfWord.Int
public import TauCeti.GroupTheory.LyndonLength.FreeGroup
import Mathlib.Order.Int.LeastGreatest

/-!
# Reduced `ℤ`-words and the free group

For `Λ = ℤ`, infinite words are finite words (`TauCeti.InfWord.equivList`). Unlike over a
non-Archimedean group, every bounded nonempty set of integers has a greatest element, so the
partial multiplication `∗` is defined on all pairs of reduced `ℤ`-words
(`TauCeti.InfWord.exists_isMul_of_isReduced_int`) and every reduced `ℤ`-word admits a cyclic
decomposition (`TauCeti.InfWord.CDR_int_eq`).

Consequently, the set `R(ℤ, X)` of all reduced `ℤ`-words forms the top element
`⊤ : TauCeti.InfWord.ReducedSubgroup ℤ X`, and its group structure under `∗` is canonically
isomorphic to `FreeGroup X` (`TauCeti.InfWord.equivFreeGroup`), matching word length with
`FreeGroup.norm` and `TauCeti.LyndonLength.freeGroupNorm`.

## Main definitions

* `TauCeti.InfWord.ReducedSubgroup.instTopInt`: `R(ℤ, X)` as the largest subgroup
  `⊤ : ReducedSubgroup ℤ X` of reduced `ℤ`-words.
* `TauCeti.InfWord.equivFreeGroup`: the group isomorphism `(⊤ : ReducedSubgroup ℤ X) ≃* FreeGroup X`
  sending `w` to `FreeGroup.mk w.toList` and having inverse `g ↦ ofList g.toWord`.

## Main results

* `TauCeti.InfWord.isCyclicallyReduced_ofList`, `TauCeti.InfWord.isCyclicallyReduced_toList`:
  compatibility of `InfWord.IsCyclicallyReduced` with `FreeGroup.IsCyclicallyReduced`.
* `TauCeti.InfWord.CDR_int_eq`: `CDR ℤ X = {w | w.IsReduced}`.
* `TauCeti.InfWord.exists_isMul_of_isReduced_int`, `TauCeti.InfWord.isMul_ofList_reduce`:
  `u ∗ v` is defined for all reduced `ℤ`-words `u`, `v` and equals
  `ofList (FreeGroup.reduce (u.toList ++ v.toList))`.
* `TauCeti.InfWord.toWord_equivFreeGroup`, `TauCeti.InfWord.coe_equivFreeGroup_symm`,
  `TauCeti.InfWord.natCast_norm_equivFreeGroup`,
  `TauCeti.InfWord.comap_freeGroupNorm_equivFreeGroup`: `equivFreeGroup` matches reduced words and
  word length with `FreeGroup.toWord`, `FreeGroup.norm`, and `LyndonLength.freeGroupNorm`.
* `TauCeti.InfWord.ReducedSubgroup.isFree_lyndonLength_int`,
  `TauCeti.InfWord.ReducedSubgroup.isRegular_lyndonLength_top`: word length on `R(ℤ, X)` is free
  (on every subgroup) and regular.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.1–3.2 (Example 3.5) and §4.
-/

public section

namespace TauCeti

namespace InfWord

variable {X : Type*}

/-! ### Cyclically reduced `ℤ`-words and `CDR(ℤ, X)` -/

/-- A list of letters is cyclically reduced as a `ℤ`-word if and only if it is cyclically reduced in
the sense of `FreeGroup.IsCyclicallyReduced`. -/
@[simp]
theorem isCyclicallyReduced_ofList {L : List (X × Bool)} :
    (ofList L).IsCyclicallyReduced ↔ FreeGroup.IsCyclicallyReduced L := by
  rcases L with _ | ⟨x, L⟩
  · simp
  · rw [isCyclicallyReduced_iff, FreeGroup.isCyclicallyReduced_iff, isReduced_ofList]
    refine and_congr_right fun _ => ?_
    have hlast : (x :: L)[L.length]? = (x :: L).getLast? := by
      rw [List.getLast?_eq_getElem?, List.length_cons, Nat.add_sub_cancel]
    have hlen : ((x :: L).length : ℤ) = (L.length : ℤ) + 1 := by simp
    have hpos : (0 : ℤ) < (L.length : ℤ) + 1 := by omega
    simp only [length_ofList, hlen, Order.succ_eq_add_one, zero_add, hpos, forall_true_left,
      letter_ofList_one, List.getElem?_cons_zero, letter_ofList_natCast_add_one, hlast,
      List.getLast?_eq_some_getLast (List.cons_ne_nil x L), List.head?_cons, Option.mem_def,
      Option.some.injEq, forall_eq', Option.map_some, ne_eq]
    obtain ⟨a, s⟩ := (x :: L).getLast (List.cons_ne_nil x L)
    obtain ⟨b, t⟩ := x
    cases s <;> cases t <;> simp [eq_comm]

/-- A `ℤ`-word is cyclically reduced if and only if its list of letters is cyclically reduced. -/
@[simp]
theorem isCyclicallyReduced_toList {w : InfWord ℤ X} :
    FreeGroup.IsCyclicallyReduced w.toList ↔ w.IsCyclicallyReduced := by
  rw [← isCyclicallyReduced_ofList, ofList_toList]

/-- Over `Λ = ℤ`, Mathlib's `FreeGroup.reduceCyclically` and `conjugator` give the cyclic
decomposition of any reduced word `w`. -/
theorem isCyclicDecomposition_ofList_conjugator_reduceCyclically [DecidableEq X]
    {w : InfWord ℤ X} (hw : w.IsReduced) :
    IsCyclicDecomposition w
      (ofList (FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator w.toList)))
      (ofList (FreeGroup.reduceCyclically w.toList)) := by
  refine isCyclicDecomposition_iff.2 ⟨isCyclicallyReduced_ofList.2
    (FreeGroup.reduceCyclically.isCyclicallyReduced (isReduced_toList.2 hw)), hw, ?_⟩
  rw [← ofList_invRev, FreeGroup.invRev_invRev, ← ofList_append, ← ofList_append,
    FreeGroup.reduceCyclically.conj_conjugator_reduceCyclically, ofList_toList]

/-- By uniqueness of cyclic decompositions, the conjugator and cyclically reduced core of a
`ℤ`-word coincide with `FreeGroup.reduceCyclically.conjugator` and `FreeGroup.reduceCyclically`. -/
theorem IsCyclicDecomposition.eq_ofList_conjugator_and_reduceCyclically [DecidableEq X]
    {w c v : InfWord ℤ X} (h : IsCyclicDecomposition w c v) :
    c = ofList (FreeGroup.invRev (FreeGroup.reduceCyclically.conjugator w.toList)) ∧
      v = ofList (FreeGroup.reduceCyclically w.toList) :=
  h.unique (isCyclicDecomposition_ofList_conjugator_reduceCyclically h.isReduced)

/-- Over `Λ = ℤ`, every reduced word admits a cyclic decomposition: `CDR(ℤ, X) = R(ℤ, X)`. -/
@[simp]
theorem CDR_int_eq (X : Type*) : CDR ℤ X = {w : InfWord ℤ X | w.IsReduced} := by
  classical
  ext w
  exact ⟨isReduced_of_mem_CDR,
    fun hw => (isCyclicDecomposition_ofList_conjugator_reduceCyclically hw).mem_CDR⟩

theorem mem_CDR_int_iff {w : InfWord ℤ X} : w ∈ CDR ℤ X ↔ w.IsReduced := by
  simp

/-! ### Total multiplication on reduced `ℤ`-words and `⊤ : ReducedSubgroup ℤ X` -/

/-- Over `Λ = ℤ`, the partial product `u ∗ v` is defined for every pair of reduced words `u`, `v`,
since every nonempty bounded-above set of integers has a greatest element. -/
theorem exists_isMul_of_isReduced_int {u v : InfWord ℤ X} (hu : u.IsReduced) (hv : v.IsReduced) :
    ∃ w, IsMul u v w :=
  (exists_isMul_iff hu hv).2 <|
    Int.exists_greatest_of_bdd ⟨u.length, fun _ h => h.2.1⟩
      ⟨0, le_rfl, u.length_nonneg, v.length_nonneg, by simp⟩

theorem mul_dom_of_isReduced_int {u v : InfWord ℤ X} (hu : u.IsReduced) (hv : v.IsReduced) :
    (u.mul v).Dom :=
  mul_dom_iff.2 (exists_isMul_of_isReduced_int hu hv)

/-- For `ℤ`-words, `IsMul u v w` turns `∗` into multiplication in `FreeGroup X`. -/
theorem IsMul.mk_toList_mul {u v w : InfWord ℤ X} (h : IsMul u v w) :
    FreeGroup.mk u.toList * FreeGroup.mk v.toList = FreeGroup.mk w.toList := by
  obtain ⟨-, -, a, b, c, rfl, rfl, rfl, -⟩ := isMul_iff.1 h
  rw [toList_append, toList_inv, toList_append, toList_append, ← FreeGroup.mul_mk,
    ← FreeGroup.inv_mk, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk, mul_assoc, inv_mul_cancel_left]

/-- For reduced `ℤ`-words `u` and `v`, `u ∗ v` is the `ℤ`-word of
`FreeGroup.reduce (u.toList ++ v.toList)`. -/
theorem isMul_ofList_reduce [DecidableEq X] {u v : InfWord ℤ X}
    (hu : u.IsReduced) (hv : v.IsReduced) :
    IsMul u v (ofList (FreeGroup.reduce (u.toList ++ v.toList))) := by
  obtain ⟨w, hw⟩ := exists_isMul_of_isReduced_int hu hv
  have hmk : FreeGroup.mk w.toList = FreeGroup.mk (FreeGroup.reduce (u.toList ++ v.toList)) := by
    rw [← hw.mk_toList_mul, FreeGroup.mul_mk, FreeGroup.reduce.self]
  have heq : w.toList = FreeGroup.reduce (u.toList ++ v.toList) :=
    (isReduced_toList.2 hw.isReduced).eq_of_mk_eq (FreeGroup.IsReduced.of_reduce_eq (by simp)) hmk
  rwa [← heq, ofList_toList]

theorem mul_eq_some_ofList_reduce [DecidableEq X] {u v : InfWord ℤ X}
    (hu : u.IsReduced) (hv : v.IsReduced) :
    u.mul v = Part.some (ofList (FreeGroup.reduce (u.toList ++ v.toList))) :=
  mul_eq_some_iff.2 (isMul_ofList_reduce hu hv)

/-- For `Λ = ℤ`, the set `R(ℤ, X)` of *all* reduced `ℤ`-words is closed under `∗`, forming the top
element of `ReducedSubgroup ℤ X`. -/
instance ReducedSubgroup.instTopInt : Top (ReducedSubgroup ℤ X) where
  top :=
    { carrier := {w | w.IsReduced}
      mul_mem' := fun hu hv =>
        let ⟨w, hw⟩ := exists_isMul_of_isReduced_int hu hv
        ⟨w, hw.isReduced, hw⟩
      empty_mem' := isReduced_empty
      inv_mem' := IsReduced.inv }

@[simp]
theorem ReducedSubgroup.mem_top {w : InfWord ℤ X} :
    w ∈ (⊤ : ReducedSubgroup ℤ X) ↔ w.IsReduced :=
  Iff.rfl

@[simp]
theorem ReducedSubgroup.coe_top (X : Type*) :
    ((⊤ : ReducedSubgroup ℤ X) : Set (InfWord ℤ X)) = {w | w.IsReduced} :=
  (rfl)

instance ReducedSubgroup.instOrderTopInt : OrderTop (ReducedSubgroup ℤ X) where
  le_top H _ hw := H.isReduced_of_mem hw

/-- Over `Λ = ℤ`, word length is a free Lyndon length function on every subgroup of reduced
`ℤ`-words. -/
theorem ReducedSubgroup.isFree_lyndonLength_int (H : ReducedSubgroup ℤ X) :
    H.lyndonLength.IsFree :=
  H.isFree_lyndonLength fun _ hw => mem_CDR_int_iff.2 (H.isReduced_of_mem hw)

/-! ### Group isomorphism with `FreeGroup X` -/

/-- The group `⊤ : ReducedSubgroup ℤ X` of all reduced `ℤ`-words under `∗` is canonically
isomorphic to `FreeGroup X`, sending `w` to `FreeGroup.mk w.toList` and having inverse
`g ↦ ofList g.toWord`. -/
noncomputable def equivFreeGroup (X : Type*) :
    (⊤ : ReducedSubgroup ℤ X) ≃* FreeGroup X :=
  MulEquiv.ofBijective
    ({ toFun := fun u => FreeGroup.mk (u : InfWord ℤ X).toList
       map_one' := by simp [ReducedSubgroup.coe_one, FreeGroup.one_eq_mk]
       map_mul' := fun u v =>
         ((⊤ : ReducedSubgroup ℤ X).isMul_coe_mul u v).mk_toList_mul.symm } :
      (⊤ : ReducedSubgroup ℤ X) →* FreeGroup X)
    ⟨fun u v h => Subtype.ext <| toList_injective <|
        (isReduced_toList.2 u.2).eq_of_mk_eq (isReduced_toList.2 v.2) h,
      fun g => by
        classical
        exact ⟨⟨ofList g.toWord, isReduced_ofList.2 FreeGroup.isReduced_toWord⟩,
          by simp [FreeGroup.mk_toWord]⟩⟩

@[simp]
theorem equivFreeGroup_apply (u : (⊤ : ReducedSubgroup ℤ X)) :
    equivFreeGroup X u = FreeGroup.mk (u : InfWord ℤ X).toList :=
  (rfl)

/-- Under `equivFreeGroup`, the reduced word `FreeGroup.toWord` of the image of `u` is
`u.toList`. -/
theorem toWord_equivFreeGroup [DecidableEq X] (u : (⊤ : ReducedSubgroup ℤ X)) :
    (equivFreeGroup X u).toWord = (u : InfWord ℤ X).toList := by
  rw [equivFreeGroup_apply, FreeGroup.toWord_mk, (isReduced_toList.2 u.2).reduce_eq]

/-- The inverse of `equivFreeGroup` sends `g : FreeGroup X` to the reduced `ℤ`-word
`ofList g.toWord`. -/
@[simp]
theorem coe_equivFreeGroup_symm [DecidableEq X] (g : FreeGroup X) :
    ((equivFreeGroup X).symm g : InfWord ℤ X) = ofList g.toWord := by
  apply toList_injective
  rw [← toWord_equivFreeGroup, MulEquiv.apply_symm_apply, toList_ofList]

theorem toList_coe_equivFreeGroup_symm [DecidableEq X] (g : FreeGroup X) :
    ((equivFreeGroup X).symm g : InfWord ℤ X).toList = g.toWord := by
  simp

/-- `equivFreeGroup` identifies the word length of a reduced `ℤ`-word with `FreeGroup.norm`. -/
theorem norm_equivFreeGroup [DecidableEq X] (u : (⊤ : ReducedSubgroup ℤ X)) :
    (equivFreeGroup X u).norm = (u : InfWord ℤ X).length.toNat := by
  rw [FreeGroup.norm, toWord_equivFreeGroup, length_toList]

theorem natCast_norm_equivFreeGroup [DecidableEq X] (u : (⊤ : ReducedSubgroup ℤ X)) :
    ((equivFreeGroup X u).norm : ℤ) = (u : InfWord ℤ X).length := by
  rw [norm_equivFreeGroup, Int.toNat_of_nonneg (u : InfWord ℤ X).length_nonneg]

theorem length_coe_equivFreeGroup_symm [DecidableEq X] (g : FreeGroup X) :
    ((equivFreeGroup X).symm g : InfWord ℤ X).length = g.norm := by
  simp [FreeGroup.norm]

/-- Pulling back `LyndonLength.freeGroupNorm` along `equivFreeGroup` yields word length on
`⊤ : ReducedSubgroup ℤ X`. -/
@[simp]
theorem comap_freeGroupNorm_equivFreeGroup [DecidableEq X] :
    (LyndonLength.freeGroupNorm X).comap (equivFreeGroup X : (⊤ : ReducedSubgroup ℤ X) →* _) =
      (⊤ : ReducedSubgroup ℤ X).lyndonLength := by
  ext u
  simpa using natCast_norm_equivFreeGroup u

/-- Pulling back word length on `⊤ : ReducedSubgroup ℤ X` along `(equivFreeGroup X).symm` yields
`LyndonLength.freeGroupNorm`. -/
@[simp]
theorem comap_lyndonLength_top_equivFreeGroup_symm [DecidableEq X] :
    (⊤ : ReducedSubgroup ℤ X).lyndonLength.comap ((equivFreeGroup X).symm : FreeGroup X →* _) =
      LyndonLength.freeGroupNorm X := by
  ext g
  simpa using length_coe_equivFreeGroup_symm g

/-- Word length on the full group `⊤ : ReducedSubgroup ℤ X` of reduced `ℤ`-words is a regular Lyndon
length function. -/
theorem ReducedSubgroup.isRegular_lyndonLength_top (X : Type*) :
    (⊤ : ReducedSubgroup ℤ X).lyndonLength.IsRegular := by
  classical
  rw [← comap_freeGroupNorm_equivFreeGroup]
  exact LyndonLength.isRegular_freeGroupNorm.comap_of_bijective (equivFreeGroup X).bijective

end InfWord

end TauCeti
