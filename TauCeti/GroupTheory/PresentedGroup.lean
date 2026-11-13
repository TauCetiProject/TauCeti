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
presented groups, preserving the image of every word. Imposing further relators `S` on the group
presented by `R` is the quotient by the normal closure of their images.

## Main definitions

* `PresentedGroup.unionEquivQuotient`: the group presented by `R ∪ S` is the quotient of the
  group presented by `R` by the normal closure of the images of `S`.

## Main results

* `PresentedGroup.mk_mk`: the class of a word is the product of its signed generators.
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

/-- The inverse change of relators also preserves every word. -/
@[simp]
theorem equivOfNormalClosureEq_symm_mk {α : Type*} {S T : Set (FreeGroup α)}
    (h : Subgroup.normalClosure S = Subgroup.normalClosure T) (w : FreeGroup α) :
    (equivOfNormalClosureEq h).symm (mk T w) = mk S w := by
  apply (equivOfNormalClosureEq h).injective
  simp

/-- Relabeling generators relabels every word by the induced free-group isomorphism. -/
@[simp]
theorem equivPresentedGroup_mk {α β : Type*} (S : Set (FreeGroup α)) (e : α ≃ β)
    (w : FreeGroup α) :
    equivPresentedGroup S e (mk S w) = mk _ (FreeGroup.freeGroupCongr e w) :=
  (rfl)

/-- The image of a word in a presented group is the product of the images of its signed
letters. -/
theorem mk_mk {α : Type*} (S : Set (FreeGroup α)) (L : List (α × Bool)) :
    mk S (FreeGroup.mk L) =
      (L.map fun p => cond p.2 (of p.1) (of p.1)⁻¹).prod :=
  (mk S).apply_freeGroup_mk L

section Union

variable {α : Type*} (R S : Set (FreeGroup α))

-- The relators `R ∪ S` hold in the quotient of the group presented by `R` by the normal closure
-- of the images of `S`.
private def toUnionQuotient :
    PresentedGroup (R ∪ S) →* PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S) :=
  toGroup (f := fun a => ((of a : PresentedGroup R) : _ ⧸ Subgroup.normalClosure (mk R '' S))) <| by
    intro r hr
    rw [← FreeGroup.lift_unique (f := fun a => ((of a : PresentedGroup R) :
        _ ⧸ Subgroup.normalClosure (mk R '' S))) ((QuotientGroup.mk' _).comp (mk R))
        (fun _ => rfl) (x := r), MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    rcases hr with hr | hr
    · rw [one_of_mem hr]
      exact one_mem _
    · exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩

-- The relators `R` hold in the group presented by `R ∪ S`, and the images of `S` are trivial
-- there.
private def ofUnionQuotient :
    PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S) →* PresentedGroup (R ∪ S) :=
  QuotientGroup.lift _ (toGroup (f := of) fun r hr => by
      simpa using one_of_mem (rels := R ∪ S) (Or.inl hr)) <|
    Subgroup.normalClosure_le_normal <| by
      rintro _ ⟨r, hr, rfl⟩
      simpa using one_of_mem (rels := R ∪ S) (Or.inr hr)

/-- **Imposing further relators is passing to a quotient.** The group presented by the relators
`R ∪ S` is the quotient of the group presented by `R` by the normal closure of the images of the
relators `S`; every word is sent to the class of its image. -/
def unionEquivQuotient :
    PresentedGroup (R ∪ S) ≃* PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S) :=
  MonoidHom.toMulEquiv (toUnionQuotient R S) (ofUnionQuotient R S)
    (PresentedGroup.ext fun a => by simp [toUnionQuotient, ofUnionQuotient])
    (QuotientGroup.monoidHom_ext _ <| PresentedGroup.ext fun a => by
      simp [toUnionQuotient, ofUnionQuotient])

/-- The quotient description of `PresentedGroup (R ∪ S)` sends a word to the class of its
image in `PresentedGroup R`. -/
@[simp]
theorem unionEquivQuotient_mk (w : FreeGroup α) :
    unionEquivQuotient R S (mk (R ∪ S) w) =
      ((mk R w : PresentedGroup R) : PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S)) := by
  rw [unionEquivQuotient, MonoidHom.toMulEquiv_apply, toUnionQuotient, toGroup_mk]
  exact (FreeGroup.lift_unique ((QuotientGroup.mk' _).comp (mk R)) fun _ => rfl).symm

/-- The quotient description sends a generator to the class of the generator. -/
@[simp]
theorem unionEquivQuotient_of (a : α) :
    unionEquivQuotient R S (of a) =
      ((of a : PresentedGroup R) : PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S)) :=
  unionEquivQuotient_mk R S (FreeGroup.of a)

/-- The inverse of the quotient description sends the class of the image of a word to the class
of the word. -/
@[simp]
theorem unionEquivQuotient_symm_mk (w : FreeGroup α) :
    (unionEquivQuotient R S).symm
        ((mk R w : PresentedGroup R) : PresentedGroup R ⧸ Subgroup.normalClosure (mk R '' S)) =
      mk (R ∪ S) w := by
  rw [MulEquiv.symm_apply_eq, unionEquivQuotient_mk]

end Union

end PresentedGroup
