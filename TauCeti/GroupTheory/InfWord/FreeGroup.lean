/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.MinimalAxioms
public import TauCeti.GroupTheory.InfWord.Int
public import TauCeti.GroupTheory.InfWord.Mul
import Mathlib.Order.Int.LeastGreatest

/-!
# The reduced `ℤ`-words form the free group

For a discretely ordered abelian group `Λ` the partial product `u ∗ v` of reduced `Λ`-words is
defined only when the common initial segments of `u⁻¹` and `v` have a longest element, and the set
`R(Λ, X)` of reduced words is in general not a group. For `Λ = ℤ` these segments are finite words
of bounded length, so a longest one always exists: any two reduced `ℤ`-words have a product, and
`u ∗ v` is the free reduction of the concatenation of `u` and `v`.

Consequently the reduced `ℤ`-words form a group under `∗`, with the empty word as identity and
`w ↦ w⁻¹` as inversion. It is isomorphic to the free group on `X`: a reduced word is sent to the
element it spells, an element to its reduced word `FreeGroup.toWord`, and the length `|w|` of a word
is the word length `FreeGroup.norm` of the corresponding element. This identifies the group of
infinite words with the free group in the Archimedean case, and is the base case of the
representation of groups with free Lyndon length functions by infinite words.

## Main definitions

* The `Group` instance on the reduced `ℤ`-words `{w : InfWord ℤ X // w.IsReduced}`, whose
  multiplication is the product `∗`.
* `TauCeti.InfWord.equivFreeGroup`: the isomorphism of this group with `FreeGroup X`.

## Main results

* `TauCeti.InfWord.exists_isMul_iff_isReduced`: two `ℤ`-words have a product exactly when both are
  reduced.
* `TauCeti.InfWord.isMul_iff_toList_eq_reduce`: the product `u ∗ v` of reduced `ℤ`-words is the
  free reduction `FreeGroup.reduce` of the concatenation of their letters.
* `TauCeti.InfWord.IsMul.mk_toList`: a product of `ℤ`-words spells the product of the elements
  spelled by its factors.
* `TauCeti.InfWord.norm_equivFreeGroup`: the word length of the element spelled by a reduced word
  is its length.

## References

* A. Myasnikov, V. Remeslennikov, D. Serbin, *Regular free length functions on Lyndon's free
  `ℤ[t]`-group `F^{ℤ[t]}`*, Contemp. Math. 378 (2005), 37–77, §3.2, Example 3.5.
-/

public section

namespace TauCeti

namespace InfWord

variable {X : Type*} {u v w : InfWord ℤ X}

/-- Over `ℤ` any two reduced words have a product: the common initial segments of `u⁻¹` and `v`
have lengths bounded by `|u|`, so there is a longest one. -/
theorem exists_isMul_of_isReduced (hu : u.IsReduced) (hv : v.IsReduced) : ∃ w, IsMul u v w := by
  obtain ⟨δ, hδ, hmax⟩ := Int.exists_greatest_of_bdd
    (P := fun β => 0 ≤ β ∧ β ≤ u.length ∧ β ≤ v.length ∧ u⁻¹.take β = v.take β)
    ⟨u.length, fun _ hβ => hβ.2.1⟩ ⟨0, by simp⟩
  exact (exists_isMul_iff hu hv).2 ⟨δ, hδ, hmax⟩

/-- Over `ℤ` two words have a product exactly when both are reduced. -/
@[simp]
theorem exists_isMul_iff_isReduced : (∃ w, IsMul u v w) ↔ u.IsReduced ∧ v.IsReduced :=
  ⟨fun ⟨_, h⟩ => ⟨h.isReduced_left, h.isReduced_right⟩,
    fun ⟨hu, hv⟩ => exists_isMul_of_isReduced hu hv⟩

/-- A product of `ℤ`-words spells the product, in the free group, of the elements spelled by its
factors. -/
theorem IsMul.mk_toList (h : IsMul u v w) :
    FreeGroup.mk w.toList = FreeGroup.mk u.toList * FreeGroup.mk v.toList := by
  obtain ⟨-, -, a, b, c, rfl, rfl, rfl, -⟩ := isMul_iff.1 h
  simp only [toList_append, toList_inv, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_assoc,
    inv_mul_cancel_left]

/-- Over `ℤ` the product `u ∗ v` of reduced words is the free reduction of the concatenation of
their letters. -/
theorem isMul_iff_toList_eq_reduce [DecidableEq X] : IsMul u v w ↔
    u.IsReduced ∧ v.IsReduced ∧ w.toList = FreeGroup.reduce (u.toList ++ v.toList) := by
  refine ⟨fun h => ⟨h.isReduced_left, h.isReduced_right, ?_⟩, fun ⟨hu, hv, hw⟩ => ?_⟩
  · rw [← (isReduced_toList.2 h.isReduced).reduce_eq]
    exact FreeGroup.reduce.sound (h.mk_toList.trans FreeGroup.mul_mk)
  · obtain ⟨w', h'⟩ := exists_isMul_of_isReduced hu hv
    obtain rfl : w = w' := by
      rw [← toList_inj, hw, ← (isReduced_toList.2 h'.isReduced).reduce_eq]
      exact (FreeGroup.reduce.sound (h'.mk_toList.trans FreeGroup.mul_mk)).symm
    exact h'

/-! ### The group of reduced `ℤ`-words -/

/-- The product `∗` of two reduced `ℤ`-words. -/
noncomputable instance : Mul {w : InfWord ℤ X // w.IsReduced} where
  mul u v :=
    ⟨(u.1.mul v.1).get (mul_dom_iff.2 (exists_isMul_of_isReduced u.2 v.2)), (isMul_get _).isReduced⟩

/-- The empty word, as a reduced `ℤ`-word. -/
instance : One {w : InfWord ℤ X // w.IsReduced} where
  one := ⟨empty ℤ X, isReduced_empty⟩

/-- The inverse `w⁻¹` of a reduced `ℤ`-word. -/
instance : Inv {w : InfWord ℤ X // w.IsReduced} where
  inv w := ⟨w.1⁻¹, w.2.inv⟩

/-- The product of two reduced `ℤ`-words in their group is their product `∗`. -/
theorem isMul_coe_mul (u v : {w : InfWord ℤ X // w.IsReduced}) :
    IsMul (u : InfWord ℤ X) v ↑(u * v) :=
  isMul_get _

/-- The product of two reduced `ℤ`-words in their group is `w` exactly when `u ∗ v = w`. -/
theorem coe_mul_eq_iff {u v : {w : InfWord ℤ X // w.IsReduced}} :
    ((u * v : {w : InfWord ℤ X // w.IsReduced}) : InfWord ℤ X) = w ↔ IsMul (u : InfWord ℤ X) v w :=
  ⟨fun h => h ▸ isMul_coe_mul u v, (isMul_coe_mul u v).unique⟩

/-- The partial product of two reduced `ℤ`-words is their product in the group of reduced words. -/
theorem mul_coe_eq_some (u v : {w : InfWord ℤ X // w.IsReduced}) :
    (u : InfWord ℤ X).mul v = Part.some ↑(u * v) :=
  mul_eq_some_iff.2 (isMul_coe_mul u v)

/-- The identity of the group of reduced `ℤ`-words is the empty word. -/
@[simp]
theorem coe_one : ((1 : {w : InfWord ℤ X // w.IsReduced}) : InfWord ℤ X) = empty ℤ X := (rfl)

/-- The inverse in the group of reduced `ℤ`-words is the inverse word. -/
@[simp]
theorem coe_inv (w : {w : InfWord ℤ X // w.IsReduced}) :
    ((w⁻¹ : {w : InfWord ℤ X // w.IsReduced}) : InfWord ℤ X) = (w : InfWord ℤ X)⁻¹ := (rfl)

/-- The reduced `ℤ`-words form a group under the product `∗`. The group laws are Stallings'
pregroup axioms (P1), (P2) and (P4) for the product, which is everywhere defined over `ℤ`. -/
noncomputable instance : Group {w : InfWord ℤ X // w.IsReduced} :=
  Group.ofLeftAxioms
    (fun u v w => Subtype.ext <|
      ((isMul_coe_mul u v).assoc_left (isMul_coe_mul v w) (isMul_coe_mul _ w)).unique
        (isMul_coe_mul u _))
    (fun u => Subtype.ext ((isMul_empty_left_iff.1 (isMul_coe_mul 1 u)).2))
    (fun u => Subtype.ext ((isMul_inv_self_iff.1 (isMul_coe_mul u⁻¹ u)).2))

/-- The group of reduced `ℤ`-words is the free group on `X`: a reduced word is sent to the element
it spells, and an element to its reduced word `FreeGroup.toWord`. -/
noncomputable def equivFreeGroup [DecidableEq X] :
    {w : InfWord ℤ X // w.IsReduced} ≃* FreeGroup X where
  toFun w := FreeGroup.mk w.1.toList
  invFun g := ⟨ofList g.toWord, isReduced_ofList.2 FreeGroup.isReduced_toWord⟩
  left_inv w := Subtype.ext <| by
    simp only [FreeGroup.toWord_mk, (isReduced_toList.2 w.2).reduce_eq, ofList_toList]
  right_inv g := by simp only [toList_ofList, FreeGroup.mk_toWord]
  map_mul' u v := (isMul_coe_mul u v).mk_toList

variable [DecidableEq X]

/-- A reduced `ℤ`-word is sent to the element of the free group it spells. -/
@[simp]
theorem equivFreeGroup_apply (w : {w : InfWord ℤ X // w.IsReduced}) :
    equivFreeGroup w = FreeGroup.mk (w : InfWord ℤ X).toList := (rfl)

/-- An element of the free group is sent to its reduced word. -/
@[simp]
theorem coe_equivFreeGroup_symm_apply (g : FreeGroup X) :
    ((equivFreeGroup.symm g : {w : InfWord ℤ X // w.IsReduced}) : InfWord ℤ X) =
      ofList g.toWord := (rfl)

/-- The reduced word of the element spelled by a reduced `ℤ`-word is the word itself. -/
theorem toWord_equivFreeGroup (w : {w : InfWord ℤ X // w.IsReduced}) :
    (equivFreeGroup w).toWord = (w : InfWord ℤ X).toList := by
  rw [equivFreeGroup_apply, FreeGroup.toWord_mk, (isReduced_toList.2 w.2).reduce_eq]

/-- The length of a reduced `ℤ`-word is the word length of the element it spells. -/
theorem norm_equivFreeGroup (w : {w : InfWord ℤ X // w.IsReduced}) :
    ((equivFreeGroup w).norm : ℤ) = (w : InfWord ℤ X).length := by
  rw [FreeGroup.norm, toWord_equivFreeGroup, natCast_length_toList]

/-- The reduced word of an element of the free group has its word length as length. -/
theorem length_coe_equivFreeGroup_symm (g : FreeGroup X) :
    ((equivFreeGroup.symm g : {w : InfWord ℤ X // w.IsReduced}) : InfWord ℤ X).length =
      g.norm := by
  rw [← norm_equivFreeGroup, MulEquiv.apply_symm_apply]

end InfWord

end TauCeti
