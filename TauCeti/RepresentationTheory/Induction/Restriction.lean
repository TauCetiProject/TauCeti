/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.FDRep
public import TauCeti.RepresentationTheory.Subrepresentation
public import TauCeti.CategoryTheory.Action.Restriction
public import TauCeti.RepresentationTheory.Rep.ChangeOfGroup
public import TauCeti.RepresentationTheory.Simple.Basic

/-!
# Restriction of representations

This file collects restriction infrastructure shared by the induction files: how the restriction
functors `Rep.resFunctor` and `Action.res` behave under composing and inverting the homomorphism
restricted along, and, for a subgroup `S` of a group `G`, the restriction of a finitely generated
representation of `G` to `S` together with its character and the class function that character
carries (`Subgroup.comap_subtype_ofFDRep`).  Restricting along a surjective
homomorphism changes nothing essential: it identifies the lattices of invariant subspaces, and
hence preserves irreducibility. In particular a representation trivial on a normal subgroup is
irreducible exactly when the representation of the quotient group it factors through is, which
makes simplicity of that quotient representation independent of the normal subgroup chosen.

`FDRep k G` is by definition `Action (FGModuleCat k) G`, so Mathlib's `Action.res` along
`S.subtype` *is* the restriction functor `FDRep k G ⥤ FDRep k S`; nothing has to be built.
Accordingly `Subgroup.resFDRep` is a reducible abbreviation for that functor on objects, exactly as
Mathlib's `Rep.res` is one for `Rep.resFunctor` on objects, and everything functorial —
restriction of an intertwiner, the functor laws, naturality — is used straight from
`Action.res (FGModuleCat k) S.subtype` and its `@[simps]` lemmas (`Action.res_obj_V`,
`Action.res_obj_ρ`, `Action.res_map_hom`) rather than restated here.

## Main definitions

* `MulEquiv.resFunctorEquiv`: restriction along a monoid isomorphism, as an equivalence of
  categories.
* `MonoidHom.resSubrepresentationOrderIso`: restriction along a surjective monoid homomorphism
  identifies the lattices of invariant subspaces.
* `Subgroup.resFDRep`: restriction of a finitely generated representation to a subgroup.

## Main statements

* `MonoidHom.resFunctor_comp`, `MonoidHom.actionRes_comp`: restriction along a composite is
  restriction twice over.
* `MonoidHom.finrank_hom_actionRes_of_surjective`: restriction along a surjective monoid
  homomorphism preserves the dimension of an intertwining space.
* `MonoidHom.isIrreducible_comp_surjective_iff`: restriction along a surjective monoid homomorphism
  preserves irreducibility, with `MulEquiv.isIrreducible_comp_equiv_iff` as the isomorphism case.
* `Representation.isIrreducible_ofQuotient_iff`, `Rep.simple_ofQuotient_iff`: a representation
  trivial on a normal subgroup `S` is irreducible, respectively simple, exactly when the
  representation of `G ⧸ S` it factors through is.

## Implementation notes

The abbreviation is over a ring, matching Mathlib's `FDRep`. Irreducibility and
characters use a field, as their Mathlib definitions require.
-/

public section

open CategoryTheory

namespace TauCeti

universe u v w

variable {k : Type u} {G : Type v} [Group G]

section Irreducible

variable [Field k]

/-- A representation trivial on a normal subgroup `S` is irreducible exactly when the
representation of `G ⧸ S` it factors through is irreducible. -/
@[simp]
theorem _root_.Representation.isIrreducible_ofQuotient_iff {V : Type*} [AddCommGroup V]
    [Module k V] (ρ : Representation k G V) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (ρ.comp S.subtype)] :
    (ρ.ofQuotient S).IsIrreducible ↔ ρ.IsIrreducible := by
  have h : (ρ.ofQuotient S).comp (QuotientGroup.mk' S) = ρ :=
    MonoidHom.ext fun g ↦ LinearMap.ext fun v ↦ ρ.ofQuotient_coe_apply S g v
  rw [← MonoidHom.isIrreducible_comp_surjective_iff (QuotientGroup.mk' S)
    (QuotientGroup.mk'_surjective S), h]

/-- An object of `Rep k G` on which a normal subgroup `S` acts trivially is simple exactly when the
object of `Rep k (G ⧸ S)` it factors through is simple. In particular simplicity of
`A.ofQuotient S` does not depend on the normal subgroup `S` acting trivially on `A`. -/
@[simp]
theorem _root_.Rep.simple_ofQuotient_iff (A : Rep.{w} k G) (S : Subgroup G) [S.Normal]
    [Representation.IsTrivial (A.ρ.comp S.subtype)] :
    Simple (A.ofQuotient S) ↔ Simple A := by
  rw [Rep.simple_iff_isIrreducible, Rep.simple_iff_isIrreducible, Rep.of_ρ,
    Representation.isIrreducible_ofQuotient_iff]

end Irreducible

section Representation

variable [Ring k]

/-- Restriction of a finitely generated representation of `G` to a subgroup `S`: Mathlib's
`Action.res` along `S.subtype`, under the definitional identification
`FDRep k G = Action (FGModuleCat k) G`.

This is a reducible abbreviation, so Mathlib's `Action.res` API applies to it unchanged; in
particular `(Action.res (FGModuleCat k) S.subtype).map f : S.resFDRep B ⟶ S.resFDRep B'`
restricts an intertwiner, and is functorial by `Functor.map_id` and `Functor.map_comp`. -/
abbrev _root_.Subgroup.resFDRep (S : Subgroup G) (B : FDRep k G) : FDRep k S :=
  (Action.res (FGModuleCat k) S.subtype).obj B

/-- Restriction commutes with forgetting finite generation: after forgetting,
`Subgroup.resFDRep` is Mathlib's `Rep.res`, on the nose rather than up to isomorphism. -/
@[simp]
theorem _root_.Subgroup.forget₂_obj_resFDRep (S : Subgroup G) (B : FDRep k G) :
    (forget₂ (FDRep k S) (Rep k S)).obj (Subgroup.resFDRep S B) =
      Rep.res S.subtype ((forget₂ (FDRep k G) (Rep k G)).obj B) :=
  rfl

end Representation

section Character

variable [Field k]

/-- Pulling the class function of a representation back along the inclusion of a subgroup gives
the class function of the restricted representation: `ClassFunction.comap S.subtype` is
restriction of class functions. -/
@[simp]
theorem _root_.Subgroup.comap_subtype_ofFDRep (S : Subgroup G) (B : FDRep k G) :
    ClassFunction.comap S.subtype (ClassFunction.ofFDRep B) =
      ClassFunction.ofFDRep (Subgroup.resFDRep S B) := by
  ext s
  simp [Subgroup.resFDRep]

end Character

end TauCeti
