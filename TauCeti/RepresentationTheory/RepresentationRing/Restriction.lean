/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Action.Monoidal
public import TauCeti.RepresentationTheory.RepresentationRing.Basic

/-!
# Restriction is a homomorphism of representation rings

For a monoid homomorphism `φ : G →* H` over a field `k`, restricting a finite-dimensional
representation of `H` along `φ` is Mathlib's `CategoryTheory.Action.res (FGModuleCat k) φ`, under
the definitional identification `FDRep k G = Action (FGModuleCat k) G`. This file passes that
functor to the representation rings of
`TauCeti/RepresentationTheory/RepresentationRing/Basic.lean`:

`TauCeti.repRingRes k φ : R(H) →+* R(G)`.

It is a homomorphism of **rings**, not merely of additive groups, and for a strong reason:
restriction does not merely commute with the tensor product up to a comparison isomorphism, it
preserves it *on the nose*. The action of `H` on `X ⊗ Y` is `g ↦ X.ρ g ⊗ₘ Y.ρ g`, so precomposing
with `φ` is the same as precomposing in each factor, and likewise the restriction of the trivial
one-dimensional representation is the trivial one-dimensional representation. That is the content
of the monoidal structure on `Action.res` recorded in
`TauCeti/CategoryTheory/Action/Monoidal.lean`, whose unit and tensorator are identities, and it is
what `TauCeti.SplitK0.mapRingHom` consumes here.

On characters everything is as expected: the character of a restriction is the character
precomposed with `φ` (`TauCeti.repRingCharacter_repRingRes`), so the square formed by the two
character homomorphisms and the two restrictions commutes. Read elementwise, that square says that
a virtual character of `H` pulls back to a virtual character of `G`
(`TauCeti.comp_mem_virtualCharacters`), a fact about class functions with no representation ring
in its statement.

## Main definitions

* `TauCeti.repRingRes`: restriction along a monoid homomorphism, as a ring homomorphism of
  representation rings.
* `TauCeti.repRingResEquiv`: restriction along an isomorphism of monoids, as a ring isomorphism.

## Main statements

* `TauCeti.repRingRes_of`: restriction sends the class of a representation to the class of its
  restriction. For a subgroup `S ≤ G`, restriction along `S.subtype` is restriction to `S`.
* `TauCeti.repRingRes_id` and `TauCeti.repRingRes_comp`: restriction is functorial, contravariantly
  in the homomorphism.
* `TauCeti.repRingCharacter_repRingRes` and `TauCeti.repRingCharacter_repRingRes_apply`: the
  character of a restricted virtual representation is the character precomposed with `φ`.
* `TauCeti.comp_mem_virtualCharacters`: pulling a virtual character back along a monoid
  homomorphism gives a virtual character.

## Implementation notes

The three monoids are left in three independent universes: nothing here needs them to agree, and
the subgroup case `S.subtype : S →* G` lands in the same universe as `G` anyway.

Induction in the other direction is *not* a ring homomorphism -- it is a homomorphism of
`R(G)`-modules, by the projection formula `TauCeti.indProjection` -- and is not built here.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Springer GTM 42 (1977), Part II, §9.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v v' v''

section Monoid

variable {k : Type u} [Field k] {G : Type v} {H : Type v'} {K : Type v''} [Monoid G] [Monoid H]
  [Monoid K]

/-- **Restriction of representations, on the representation ring**: the ring homomorphism
`R(H) →+* R(G)` induced by a monoid homomorphism `φ : G →* H`, sending the class of a
representation of `H` to the class of its restriction along `φ`.

It is Mathlib's restriction functor `CategoryTheory.Action.res` fed to
`TauCeti.SplitK0.mapRingHom`, and it is multiplicative because that functor is monoidal
(`Action.resMonoidal`). -/
noncomputable def repRingRes (k : Type u) [Field k] {G : Type v} {H : Type v'} [Monoid G]
    [Monoid H] (φ : G →* H) : repRing k H →+* repRing k G :=
  SplitK0.mapRingHom (Action.res (FGModuleCat.{u} k) φ)

/-- Restriction sends the class of a representation to the class of its restriction. -/
@[simp]
theorem repRingRes_of (φ : G →* H) (V : FDRep k H) :
    repRingRes k φ (SplitK0.of V) =
      SplitK0.of ((Action.res (FGModuleCat.{u} k) φ).obj V) :=
  SplitK0.mapRingHom_of _ V

/-- **Restricting along the identity does nothing.** -/
@[simp]
theorem repRingRes_id : repRingRes k (MonoidHom.id G) = RingHom.id (repRing k G) :=
  (SplitK0.mapRingHom_congr (G := 𝟭 _)
    fun V => ⟨(Action.resId (FGModuleCat.{u} k)).app V⟩).trans SplitK0.mapRingHom_id

/-- **Restriction is contravariantly functorial**: restricting along a composite is restricting
twice over. The two functors agree on the nose, so the comparison of classes is the identity
isomorphism. -/
@[simp]
theorem repRingRes_comp (φ : G →* H) (ψ : H →* K) :
    repRingRes k (ψ.comp φ) = (repRingRes k φ).comp (repRingRes k ψ) :=
  (SplitK0.mapRingHom_congr (G := Action.res _ ψ ⋙ Action.res _ φ)
    fun V => ⟨((Action.resComp (FGModuleCat.{u} k) φ ψ).app V).symm⟩).trans
      (SplitK0.mapRingHom_comp _ _)

/-- **The character of a restricted virtual representation, elementwise**: it is the character of
the original, evaluated at the image of the element. -/
@[simp]
theorem repRingCharacter_repRingRes_apply (φ : G →* H) (x : repRing k H) (g : G) :
    repRingCharacter k G (repRingRes k φ x) g = repRingCharacter k H x (φ g) := by
  induction x using SplitK0.induction_on with
  | zero => simp
  | of V =>
    -- The restricted representation *is* the composite `V.ρ ∘ φ`, so the traces agree by
    -- definition.
    simp only [repRingRes_of, repRingCharacter_of]
    exact (rfl)
  | add a b ha hb => simp [ha, hb]
  | neg a ha => simp [ha]

/-- **The character homomorphism intertwines restriction with precomposition.** This is the
commuting square relating the two character homomorphisms to restriction on the two sides. -/
@[simp]
theorem repRingCharacter_repRingRes (φ : G →* H) (x : repRing k H) :
    repRingCharacter k G (repRingRes k φ x) = repRingCharacter k H x ∘ φ :=
  funext fun g => repRingCharacter_repRingRes_apply φ x g

/-- **A virtual character pulls back to a virtual character** along a monoid homomorphism: the
elementwise form of `TauCeti.repRingCharacter_repRingRes`, read through the description of the
virtual characters as the image of the character homomorphism. -/
theorem comp_mem_virtualCharacters (φ : G →* H) {f : H → k}
    (hf : f ∈ virtualCharacters k H) : f ∘ φ ∈ virtualCharacters k G := by
  obtain ⟨x, hx⟩ := (mem_range_repRingCharacter_iff (k := k) (G := H)).2 hf
  have hfx : f ∘ φ = repRingCharacter k G (repRingRes k φ x) := by
    rw [repRingCharacter_repRingRes, ← hx, AddMonoidHom.coe_coe]
  rw [hfx]
  exact repRingCharacter_mem_virtualCharacters _

/-- **Restriction along an isomorphism of monoids is an isomorphism of representation rings**,
with inverse restriction along the inverse isomorphism. -/
noncomputable def repRingResEquiv (e : G ≃* H) : repRing k H ≃+* repRing k G :=
  have comp_symm : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H :=
    MulEquiv.coe_monoidHom_comp_coe_monoidHom_symm e
  have symm_comp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G :=
    MulEquiv.coe_monoidHom_symm_comp_coe_monoidHom e
  { repRingRes k e.toMonoidHom with
    invFun := repRingRes k e.symm.toMonoidHom
    left_inv := fun x => by
      have h := congrArg (fun r : repRing k H →+* repRing k H => r x)
        (repRingRes_comp (k := k) e.symm.toMonoidHom e.toMonoidHom)
      rw [comp_symm, repRingRes_id] at h
      simpa using h.symm
    right_inv := fun x => by
      have h := congrArg (fun r : repRing k G →+* repRing k G => r x)
        (repRingRes_comp (k := k) e.toMonoidHom e.symm.toMonoidHom)
      rw [symm_comp, repRingRes_id] at h
      simpa using h.symm }

/-- `TauCeti.repRingResEquiv` is restriction along the isomorphism. -/
@[simp]
theorem repRingResEquiv_apply (e : G ≃* H) (x : repRing k H) :
    repRingResEquiv (k := k) e x = repRingRes k e.toMonoidHom x :=
  (rfl)

/-- The inverse of `TauCeti.repRingResEquiv` is restriction along the inverse isomorphism. -/
@[simp]
theorem repRingResEquiv_symm_apply (e : G ≃* H) (x : repRing k G) :
    (repRingResEquiv (k := k) e).symm x = repRingRes k e.symm.toMonoidHom x :=
  (rfl)

end Monoid

end TauCeti
