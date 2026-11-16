/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.InfWord.LyndonLength
public import TauCeti.GroupTheory.LyndonLength.FreeGroup
import Mathlib.Order.Int.LeastGreatest

/-!
# Reduced `ℤ`-words form the free group

Over `Λ = ℤ`, the set of common initial segment lengths of any two reduced words is nonempty
(containing `0`) and bounded above (by the length of the first word), hence has a greatest element.
Therefore the partial multiplication `∗` is total on reduced `ℤ`-words
(`TauCeti.InfWord.exists_isMul_int`), and the reduced `ℤ`-words form a subgroup
`TauCeti.InfWord.reducedIntSubgroup X : WordSubgroup ℤ X` equal to `CDR ℤ X`.

The map sending a reduced `ℤ`-word `w` to `FreeGroup.mk w.toList` is a group isomorphism
`TauCeti.InfWord.equivFreeGroup X : reducedIntSubgroup X ≃* FreeGroup X`. When `[DecidableEq X]`
is available, its inverse is `g ↦ ofList g.toWord`, partial multiplication of `ofList g.toWord`
and `ofList h.toWord` computes `ofList (g * h).toWord`, word length matches `FreeGroup.norm`, and
the Lyndon length function on `reducedIntSubgroup X` agrees with
`TauCeti.LyndonLength.freeGroupNorm X`.

## Main definitions

* `TauCeti.InfWord.reducedIntSubgroup`: the `WordSubgroup ℤ X` of all reduced `ℤ`-words.
* `TauCeti.InfWord.equivFreeGroup`: the group isomorphism `reducedIntSubgroup X ≃* FreeGroup X`.
* `TauCeti.InfWord.ZFreeGroup`: specialization of `equivFreeGroup` to `X = Fin 2`.

## Main results

* `TauCeti.InfWord.exists_isMul_int`: the partial multiplication `∗` is total on reduced `ℤ`-words.
* `TauCeti.InfWord.mk_toList_of_isMul`: `u ∗ v = w` implies
  `FreeGroup.mk u.toList * FreeGroup.mk v.toList = FreeGroup.mk w.toList`.
* `TauCeti.InfWord.toWord_equivFreeGroup`, `TauCeti.InfWord.equivFreeGroup_symm_apply`:
  compatibility of `equivFreeGroup` with `FreeGroup.toWord`.
* `TauCeti.InfWord.norm_equivFreeGroup`, `TauCeti.InfWord.length_equivFreeGroup_symm`,
  `TauCeti.InfWord.lyndonLength_comap_equivFreeGroup_symm`: word length on reduced `ℤ`-words agrees
  with `FreeGroup.norm` and `TauCeti.LyndonLength.freeGroupNorm`.
* `TauCeti.InfWord.isMul_ofList_toWord`, `TauCeti.InfWord.mul_ofList_toWord`: `∗` on `ofList` of
  reduced normal forms matches multiplication in `FreeGroup X`.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.2, Example 3.5.
-/

public section

namespace TauCeti

namespace InfWord

section General

variable {X : Type*}

/-- Over `Λ = ℤ`, the partial multiplication `∗` is defined for every pair of reduced words. -/
theorem exists_isMul_int {u v : InfWord ℤ X} (hu : u.IsReduced) (hv : v.IsReduced) :
    ∃ w, IsMul u v w := by
  rw [exists_isMul_iff hu hv]
  obtain ⟨δ, hδ, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun β => 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u⁻¹.take β = v.take β)
    ⟨u.length, fun _ h => h.2.1⟩
    ⟨0, le_rfl, u.length_nonneg, v.length_nonneg, by simp⟩
  exact ⟨δ, hδ, hmax⟩

/-- Over `Λ = ℤ`, the partial product `u.mul v` is defined for every pair of reduced words. -/
theorem mul_dom_int {u v : InfWord ℤ X} (hu : u.IsReduced) (hv : v.IsReduced) : (u.mul v).Dom :=
  mul_dom_iff.2 (exists_isMul_int hu hv)

/-- Over `Λ = ℤ`, all reduced words form a `WordSubgroup ℤ X`. -/
def reducedIntSubgroup (X : Type*) : WordSubgroup ℤ X where
  carrier := {w : InfWord ℤ X | w.IsReduced}
  empty_mem' := isReduced_empty
  inv_mem' hw := hw.inv
  mul_mem' hu hv :=
    let ⟨w, hw⟩ := exists_isMul_int hu hv
    ⟨w, hw.isReduced, hw⟩

/-- Membership in `reducedIntSubgroup X` is reducedness. -/
@[simp]
theorem mem_reducedIntSubgroup {w : InfWord ℤ X} : w ∈ reducedIntSubgroup X ↔ w.IsReduced :=
  Iff.rfl

/-- Every reduced `ℤ`-word lies in `CDR ℤ X`. -/
theorem reducedIntSubgroup_subset_CDR (X : Type*) :
    (reducedIntSubgroup X : Set (InfWord ℤ X)) ⊆ CDR ℤ X :=
  fun _ hw => isReduced_mem_CDR_int hw

/-- The underlying set of `reducedIntSubgroup X` equals `CDR ℤ X`. -/
theorem reducedIntSubgroup_eq_CDR (X : Type*) :
    (reducedIntSubgroup X : Set (InfWord ℤ X)) = CDR ℤ X :=
  CDR_int_eq.symm

/-- Word length on the group of reduced `ℤ`-words is a free Lyndon length function. -/
theorem isFree_lyndonLength_reducedIntSubgroup (X : Type*) :
    (reducedIntSubgroup X).lyndonLength.IsFree :=
  length_isLyndon (reducedIntSubgroup X) (reducedIntSubgroup_subset_CDR X)

/-- Multiplication of reduced `ℤ`-words respects `FreeGroup.mk`. -/
theorem mk_toList_of_isMul {u v w : InfWord ℤ X} (h : IsMul u v w) :
    FreeGroup.mk u.toList * FreeGroup.mk v.toList = FreeGroup.mk w.toList := by
  obtain ⟨-, -, a, b, c, rfl, rfl, rfl, -⟩ := isMul_iff.1 h
  simp only [toList_append, toList_inv, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk]
  rw [mul_assoc, inv_mul_cancel_left]

/-- The group isomorphism between the reduced `ℤ`-words under `∗` and `FreeGroup X`. -/
noncomputable def equivFreeGroup (X : Type*) : reducedIntSubgroup X ≃* FreeGroup X :=
  MulEquiv.ofBijective
    ({ toFun := fun w => FreeGroup.mk w.1.toList
       map_one' := by simp [FreeGroup.one_eq_mk]
       map_mul' := fun u v => (mk_toList_of_isMul (WordSubgroup.isMul_mul u v)).symm } :
      reducedIntSubgroup X →* FreeGroup X)
    ⟨fun u v h => Subtype.ext <| toList_injective <|
        FreeGroup.IsReduced.eq_of_mk_eq (isReduced_toList.2 u.2) (isReduced_toList.2 v.2) h,
      fun g => by
        classical
        exact ⟨⟨ofList g.toWord, isReduced_ofList.2 FreeGroup.isReduced_toWord⟩, by
          simp [FreeGroup.mk_toWord]⟩⟩

/-- Evaluation of `InfWord.equivFreeGroup`. -/
@[simp]
theorem equivFreeGroup_apply (w : reducedIntSubgroup X) :
    equivFreeGroup X w = FreeGroup.mk w.1.toList := (rfl)

end General

section Decidable

variable {X : Type*} [DecidableEq X]

/-- The inverse of `equivFreeGroup` sends `g : FreeGroup X` to `ofList g.toWord`. -/
@[simp]
theorem equivFreeGroup_symm_apply (g : FreeGroup X) :
    ((equivFreeGroup X).symm g : InfWord ℤ X) = ofList g.toWord := by
  have h : (equivFreeGroup X).symm g =
      ⟨ofList g.toWord, isReduced_ofList.2 FreeGroup.isReduced_toWord⟩ := by
    rw [MulEquiv.symm_apply_eq, equivFreeGroup_apply, toList_ofList, FreeGroup.mk_toWord]
  exact congrArg Subtype.val h

/-- `equivFreeGroup` matches `toList` with `FreeGroup.toWord`. -/
theorem toWord_equivFreeGroup (w : reducedIntSubgroup X) :
    (equivFreeGroup X w).toWord = w.1.toList := by
  rw [equivFreeGroup_apply, FreeGroup.toWord_mk, (isReduced_toList.2 w.2).reduce_eq]

/-- `equivFreeGroup` matches `FreeGroup.norm` with `InfWord.length`. -/
theorem norm_equivFreeGroup (w : reducedIntSubgroup X) :
    ((equivFreeGroup X w).norm : ℤ) = w.1.length := by
  rw [FreeGroup.norm, toWord_equivFreeGroup, natCast_length_toList]

/-- The length of `(equivFreeGroup X).symm g` equals `g.norm`. -/
theorem length_equivFreeGroup_symm (g : FreeGroup X) :
    ((equivFreeGroup X).symm g : InfWord ℤ X).length = g.norm := by
  rw [equivFreeGroup_symm_apply, length_ofList, FreeGroup.norm]

/-- Partial multiplication of `ofList g.toWord` and `ofList h.toWord` gives
`ofList (g * h).toWord`. -/
theorem isMul_ofList_toWord (g h : FreeGroup X) :
    IsMul (ofList g.toWord) (ofList h.toWord) (ofList (g * h).toWord) := by
  have hmul := WordSubgroup.isMul_mul ((equivFreeGroup X).symm g) ((equivFreeGroup X).symm h)
  rwa [← map_mul, equivFreeGroup_symm_apply, equivFreeGroup_symm_apply,
    equivFreeGroup_symm_apply] at hmul

/-- As a partial function, `(ofList g.toWord).mul (ofList h.toWord)` equals
`Part.some (ofList (g * h).toWord)`. -/
theorem mul_ofList_toWord (g h : FreeGroup X) :
    (ofList g.toWord).mul (ofList h.toWord) = Part.some (ofList (g * h).toWord) :=
  mul_eq_some_iff.2 (isMul_ofList_toWord g h)

/-- Pulling back the Lyndon length function on `reducedIntSubgroup X` along
`(equivFreeGroup X).symm` recovers `TauCeti.LyndonLength.freeGroupNorm X`. -/
theorem lyndonLength_comap_equivFreeGroup_symm (X : Type*) [DecidableEq X] :
    (reducedIntSubgroup X).lyndonLength.comap (equivFreeGroup X).symm.toMonoidHom =
      LyndonLength.freeGroupNorm X := by
  ext g
  simp only [LyndonLength.comap_apply, MulEquiv.coe_toMonoidHom, WordSubgroup.lyndonLength_apply,
    LyndonLength.freeGroupNorm_apply, length_equivFreeGroup_symm]

/-- Pulling back `TauCeti.LyndonLength.freeGroupNorm X` along `equivFreeGroup X` recovers the Lyndon
length function on `reducedIntSubgroup X`. -/
theorem freeGroupNorm_comap_equivFreeGroup (X : Type*) [DecidableEq X] :
    (LyndonLength.freeGroupNorm X).comap (equivFreeGroup X).toMonoidHom =
      (reducedIntSubgroup X).lyndonLength := by
  ext w
  simp only [LyndonLength.comap_apply, MulEquiv.coe_toMonoidHom, LyndonLength.freeGroupNorm_apply,
    WordSubgroup.lyndonLength_apply, norm_equivFreeGroup]

end Decidable

/-! ### Rank-2 free group specialization -/

/-- For `Λ = ℤ` and `X = Fin 2`, the group of reduced `ℤ`-words under `∗` is isomorphic to
`FreeGroup (Fin 2)`. -/
noncomputable def ZFreeGroup : reducedIntSubgroup (Fin 2) ≃* FreeGroup (Fin 2) :=
  equivFreeGroup (Fin 2)

/-- `ZFreeGroup` sends a reduced `ℤ`-word on `Fin 2` to the element whose reduced word is
`w.1.toList`. -/
@[simp]
theorem toWord_ZFreeGroup (w : reducedIntSubgroup (Fin 2)) :
    (ZFreeGroup w).toWord = w.1.toList :=
  toWord_equivFreeGroup w

/-- The inverse of `ZFreeGroup` sends `g : FreeGroup (Fin 2)` to `ofList g.toWord`. -/
@[simp]
theorem ZFreeGroup_symm_apply (g : FreeGroup (Fin 2)) :
    (ZFreeGroup.symm g : InfWord ℤ (Fin 2)) = ofList g.toWord :=
  equivFreeGroup_symm_apply g

/-- `ZFreeGroup` matches word length with `FreeGroup.norm`. -/
@[simp]
theorem norm_ZFreeGroup (w : reducedIntSubgroup (Fin 2)) :
    ((ZFreeGroup w).norm : ℤ) = w.1.length :=
  norm_equivFreeGroup w

end InfWord

end TauCeti
