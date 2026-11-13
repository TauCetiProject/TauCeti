/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coprod.Basic
public import Mathlib.GroupTheory.FreeGroup.IsFreeGroup
public import TauCeti.GroupTheory.FreeGroup.Primitive

/-!
# Free products of free groups

The free product `G ∗ H` of two free groups is free: free bases `b` of `G` and `b'` of `H` give
the free basis `b.coprod b'` of `G ∗ H`, indexed by the disjoint union of their index types, whose
elements are the images of the basis elements of the two factors. This is the binary analogue of
Mathlib's `FreeGroupBasis.coprodI` for the indexed free product `Monoid.CoprodI`.

## Main definitions

* `FreeGroupBasis.coprod`: the free basis of `G ∗ H` given by free bases of `G` and `H`.

## Main results

* `FreeGroupBasis.coprod_apply_inl`, `FreeGroupBasis.coprod_apply_inr`: its elements.
* The instance `IsFreeGroup (G ∗ H)` for free groups `G` and `H`.
* `Monoid.Coprod.isPrimitive_inl`, `Monoid.Coprod.isPrimitive_inr`: a primitive element of a free
  group stays primitive in its free product with any free group.
-/

public section

open Monoid Coprod

namespace FreeGroupBasis

variable {ι ι' G H : Type*} [Group G] [Group H]

/-- The free basis of the free product `G ∗ H` indexed by `ι ⊕ ι'`, given by free bases of `G`
indexed by `ι` and of `H` indexed by `ι'`; the binary analogue of `FreeGroupBasis.coprodI`. -/
def coprod (b : FreeGroupBasis ι G) (b' : FreeGroupBasis ι' H) :
    FreeGroupBasis (ι ⊕ ι') (G ∗ H) :=
  .ofRepr <| MonoidHom.toMulEquiv
    (Coprod.lift ((FreeGroup.map Sum.inl).comp b.repr.toMonoidHom)
      ((FreeGroup.map Sum.inr).comp b'.repr.toMonoidHom))
    (FreeGroup.lift (Sum.elim (inl ∘ b) (inr ∘ b')))
    (hom_ext (b.ext_hom _ _ fun i ↦ by simp) (b'.ext_hom _ _ fun i ↦ by simp))
    (FreeGroup.ext_hom _ _ (by rintro (i | i) <;> simp))

@[simp]
theorem coprod_apply_inl (b : FreeGroupBasis ι G) (b' : FreeGroupBasis ι' H) (i : ι) :
    b.coprod b' (.inl i) = inl (b i) :=
  -- `b.coprod b' j` is by definition the image of `FreeGroup.of j` under the inverse isomorphism.
  FreeGroup.lift_apply_of (f := Sum.elim (inl ∘ b) (inr ∘ b')) (x := .inl i)

@[simp]
theorem coprod_apply_inr (b : FreeGroupBasis ι G) (b' : FreeGroupBasis ι' H) (i : ι') :
    b.coprod b' (.inr i) = inr (b' i) :=
  FreeGroup.lift_apply_of (f := Sum.elim (inl ∘ b) (inr ∘ b')) (x := .inr i)

end FreeGroupBasis

namespace Monoid.Coprod

variable {G H : Type*} [Group G] [Group H]

/-- The free product of two free groups is free. -/
instance [IsFreeGroup G] [IsFreeGroup H] : IsFreeGroup (G ∗ H) :=
  ((IsFreeGroup.basis G).coprod (IsFreeGroup.basis H)).isFreeGroup

/-- A primitive element of `G`, an element of some free basis of `G`, is primitive in `G ∗ H` for
every free group `H`. -/
theorem isPrimitive_inl [IsFreeGroup H] {x : G} (hx : Group.IsPrimitive x) :
    Group.IsPrimitive (inl x : G ∗ H) := by
  obtain ⟨ι, b, i, rfl⟩ := Group.isPrimitive_iff.1 hx
  simpa using (b.coprod (IsFreeGroup.basis H)).isPrimitive (.inl i)

/-- A primitive element of `H`, an element of some free basis of `H`, is primitive in `G ∗ H` for
every free group `G`. -/
theorem isPrimitive_inr [IsFreeGroup G] {x : H} (hx : Group.IsPrimitive x) :
    Group.IsPrimitive (inr x : G ∗ H) := by
  obtain ⟨ι, b, i, rfl⟩ := Group.isPrimitive_iff.1 hx
  simpa using ((IsFreeGroup.basis G).coprod b).isPrimitive (.inr i)

end Monoid.Coprod
