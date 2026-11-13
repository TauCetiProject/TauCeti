/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PresentedGroup
import Mathlib.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.FreeGroup.Basic

/-!
# Words and changes of relators in presented groups

A signed word is a list of pairs `(x, b)`, with `true` denoting a generator and `false` its
inverse. This file gives the product formula for the image of such a word under the quotient map
to a presented group. The corresponding formulas for free groups are in
`TauCeti.GroupTheory.FreeGroup.Basic`.

Equality of the normal closures of two relator sets gives a canonical isomorphism of the
presented groups, preserving the image of every word.

Generators that occur in no relator span a free factor of the presented group.

## Main results

* `PresentedGroup.mk_mk`: the class of a word is the product of its signed generators.
* `PresentedGroup.emptyEquivFreeGroup`: the group presented without relators is free.
* `PresentedGroup.coprodFreeGroupEquiv`: if the relators only involve the generators from a part
  `α` of the generators `α ⊕ β`, the presented group is the free product of the group presented
  on `α` and the free group on `β`.
-/

public section

namespace PresentedGroup

/-- Lifting the canonical generators is the quotient map on every free-group element. -/
@[simp]
theorem lift_of_eq_mk {α : Type*} {rels : Set (FreeGroup α)} (x : FreeGroup α) :
    FreeGroup.lift (of : α → PresentedGroup rels) x = mk rels x :=
  (FreeGroup.lift_unique (mk rels) (fun _ => rfl)).symm

/-- The induced homomorphism evaluates a presented word by the free-group lift. -/
@[simp]
theorem toGroup_mk {α G : Type*} [Group G] {f : α → G} {rels : Set (FreeGroup α)}
    (h : ∀ r ∈ rels, FreeGroup.lift f r = 1) (x : FreeGroup α) :
    toGroup h (mk rels x) = FreeGroup.lift f x := (rfl)

/-- The homomorphism of presented groups induced by a homomorphism of free groups sends the class
of a word to the class of its image. -/
@[simp]
theorem map_mk {α β : Type*} (f : FreeGroup α →* FreeGroup β) {s : Set (FreeGroup α)}
    {t : Set (FreeGroup β)} (hst : s.MapsTo f t) (x : FreeGroup α) :
    PresentedGroup.map f hst (mk s x) = mk t (f x) := (rfl)

/-- The homomorphism of presented groups induced by a homomorphism of free groups sends a
generator to the class of its image. -/
@[simp]
theorem map_of {α β : Type*} (f : FreeGroup α →* FreeGroup β) {s : Set (FreeGroup α)}
    {t : Set (FreeGroup β)} (hst : s.MapsTo f t) (a : α) :
    PresentedGroup.map f hst (of a) = mk t (f (FreeGroup.of a)) := (rfl)

/-- Relator sets with the same normal closure present canonically isomorphic groups. -/
def equivOfNormalClosureEq {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) :
    PresentedGroup S ≃* PresentedGroup T where
  toFun := QuotientGroup.quotientMulEquivOfEq h
  invFun := (QuotientGroup.quotientMulEquivOfEq h).symm
  left_inv := (QuotientGroup.quotientMulEquivOfEq h).left_inv
  right_inv := (QuotientGroup.quotientMulEquivOfEq h).right_inv
  map_mul' := (QuotientGroup.quotientMulEquivOfEq h).map_mul

/-- The canonical change of relators preserves every word. -/
@[simp]
theorem equivOfNormalClosureEq_mk {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup α) :
    equivOfNormalClosureEq h (mk S w) = mk T w :=
  QuotientGroup.quotientMulEquivOfEq_mk h w

/-- The canonical change of relators preserves every generator. -/
@[simp]
theorem equivOfNormalClosureEq_of {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (a : α) :
    equivOfNormalClosureEq h (of a) = of a :=
  equivOfNormalClosureEq_mk h (FreeGroup.of a)

/-- The inverse change of relators also preserves every word. -/
@[simp]
theorem equivOfNormalClosureEq_symm_mk {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup α) :
    (equivOfNormalClosureEq h).symm (mk T w) = mk S w := by
  apply (equivOfNormalClosureEq h).injective
  simp

/-- The inverse change of relators also preserves every generator. -/
@[simp]
theorem equivOfNormalClosureEq_symm_of {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (a : α) :
    (equivOfNormalClosureEq h).symm (of a) = of a :=
  equivOfNormalClosureEq_symm_mk h (FreeGroup.of a)

/-- Relabeling generators relabels every word by the induced free-group isomorphism. -/
@[simp]
theorem equivPresentedGroup_mk {α β : Type*} (S : Set (FreeGroup α)) (e : α ≃ β)
    (w : FreeGroup α) :
    equivPresentedGroup S e (mk S w) = mk _ (FreeGroup.freeGroupCongr e w) :=
  (rfl)

/-- A group presented by generators and no relators is the free group on these generators. -/
def emptyEquivFreeGroup {α : Type*} : PresentedGroup (∅ : Set (FreeGroup α)) ≃* FreeGroup α :=
  (QuotientGroup.quotientMulEquivOfEq Subgroup.normalClosure_empty).trans QuotientGroup.quotientBot

@[simp]
theorem emptyEquivFreeGroup_mk {α : Type*} (w : FreeGroup α) :
    emptyEquivFreeGroup (mk ∅ w) = w := (rfl)

@[simp]
theorem emptyEquivFreeGroup_of {α : Type*} (a : α) :
    emptyEquivFreeGroup (of (rels := ∅) a) = FreeGroup.of a := (rfl)

@[simp]
theorem emptyEquivFreeGroup_symm_apply {α : Type*} (w : FreeGroup α) :
    emptyEquivFreeGroup.symm w = mk ∅ w := (rfl)

/-- The image of a word in a presented group is the product of the images of its signed
letters. -/
theorem mk_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    mk S (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (of p.1) (of p.1)⁻¹).prod :=
  (mk S).apply_freeGroup_mk L

section CoprodFreeGroup

variable {α β γ : Type*} (rels : Set (FreeGroup α)) (e : α ⊕ β ≃ γ)

/-- Generators occurring in no relator span a free factor: if the generators `γ` split as
`α ⊕ β` and the relators are words in the generators from `α`, then the presented group is the
free product of the group presented by these relators on `α` and the free group on `β`. This is
the free product of presentations `PresentedGroup.coprodPresentations`, with no relators on `β`. -/
def coprodFreeGroupEquiv :
    PresentedGroup (FreeGroup.map (e ∘ Sum.inl) '' rels) ≃*
      Monoid.Coprod (PresentedGroup rels) (FreeGroup β) :=
  (equivOfNormalClosureEq <| congrArg _ <| by
      simp [Set.image_image, ← FreeGroup.map.comp]).trans <|
    (equivPresentedGroup _ e).symm.trans <| (coprodPresentations rels ∅).trans <|
      MulEquiv.coprodCongr (.refl _) emptyEquivFreeGroup

/-- The free-factor isomorphism sends a generator of `γ` to the generator of the factor it comes
from. -/
@[simp]
theorem coprodFreeGroupEquiv_of (c : γ) :
    coprodFreeGroupEquiv rels e (of c) =
      Sum.elim (fun a => Monoid.Coprod.inl (of a)) (fun b => Monoid.Coprod.inr (FreeGroup.of b))
        (e.symm c) := by
  obtain ⟨c, rfl⟩ := e.surjective c
  cases c <;>
    simp [coprodFreeGroupEquiv, coprodPresentations, toCoprod, equivPresentedGroup_symm_apply_of]

/-- The free-factor isomorphism sends the class of a word to the product of the images of its
letters. -/
@[simp]
theorem coprodFreeGroupEquiv_mk (w : FreeGroup γ) :
    coprodFreeGroupEquiv rels e (mk _ w) =
      FreeGroup.lift (fun c => Sum.elim (fun a => Monoid.Coprod.inl (of a))
        (fun b => Monoid.Coprod.inr (FreeGroup.of b)) (e.symm c)) w := by
  induction w with
  | one => simp
  | of c => exact (coprodFreeGroupEquiv_of rels e c).trans FreeGroup.lift_apply_of.symm
  | inv_of c h => simp [h]
  | mul u v hu hv => simp [hu, hv]

theorem coprodFreeGroupEquiv_of_inl (a : α) :
    coprodFreeGroupEquiv rels e (of (e (Sum.inl a))) = Monoid.Coprod.inl (of a) := by
  simp

theorem coprodFreeGroupEquiv_of_inr (b : β) :
    coprodFreeGroupEquiv rels e (of (e (Sum.inr b))) = Monoid.Coprod.inr (FreeGroup.of b) := by
  simp

@[simp]
theorem coprodFreeGroupEquiv_symm_inl_of (a : α) :
    (coprodFreeGroupEquiv rels e).symm (Monoid.Coprod.inl (of a)) = of (e (Sum.inl a)) := by
  simp [MulEquiv.symm_apply_eq]

/-- The inverse of the free-factor isomorphism relabels a word of the presented factor along
`e ∘ Sum.inl`. -/
@[simp]
theorem coprodFreeGroupEquiv_symm_inl_mk (w : FreeGroup α) :
    (coprodFreeGroupEquiv rels e).symm (Monoid.Coprod.inl (mk rels w)) =
      mk _ (FreeGroup.map (e ∘ Sum.inl) w) := by
  rw [MulEquiv.symm_apply_eq]
  induction w with
  | one => simp
  | of a => exact (coprodFreeGroupEquiv_of_inl rels e a).symm
  | inv_of a h => simp [h]
  | mul u v hu hv => simp [hu, hv]

@[simp]
theorem coprodFreeGroupEquiv_symm_inr_of (b : β) :
    (coprodFreeGroupEquiv rels e).symm (Monoid.Coprod.inr (FreeGroup.of b)) =
      of (e (Sum.inr b)) := by
  simp [MulEquiv.symm_apply_eq]

end CoprodFreeGroup

end PresentedGroup
