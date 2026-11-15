/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.CategoryTheory.MorphismProperty.Descent
import TauCeti.AlgebraicGeometry.Morphisms.Flat.Reduced

/-!
# Geometrically integral morphisms and surjective descent

Mathlib's `AlgebraicGeometry.GeometricallyIntegral` is stable under base change. This file records
its compatibility with isomorphisms, Zariski-local descent on the target, and descent along
arbitrary surjective morphisms of schemes:

* `TauCeti.AlgebraicGeometry.geometricallyIntegral_of_isIso`: an isomorphism of schemes is
  geometrically integral.
* `TauCeti.AlgebraicGeometry.isClosedUnderIsomorphisms_isIntegral`: `AlgebraicGeometry.IsIntegral`
  is closed under scheme isomorphisms.
* `TauCeti.AlgebraicGeometry.respectsIso_geometricallyIntegral` and
  `TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_geometricallyIntegral`: `GeometricallyIntegral`
  respects isomorphisms and is Zariski-local on the target.
* `TauCeti.AlgebraicGeometry.isReduced_of_flat_of_surjective`,
  `TauCeti.AlgebraicGeometry.irreducibleSpace_of_surjective`, and
  `TauCeti.AlgebraicGeometry.isIntegral_of_flat_of_surjective`: reducedness, irreducibility, and
  integrality of schemes descend along flat surjective morphisms without Noetherian hypotheses.
* `TauCeti.AlgebraicGeometry.geometrically_descendsAlong_surjective`: if an object property `P`
  descends along flat surjective morphisms, then `geometrically P` descends along arbitrary
  surjective morphisms.
* `TauCeti.AlgebraicGeometry.descendsAlong_surjective_geometricallyReduced`,
  `TauCeti.AlgebraicGeometry.descendsAlong_surjective_geometricallyIrreducible`, and
  `TauCeti.AlgebraicGeometry.descendsAlong_surjective_geometricallyIntegral`:
  `GeometricallyReduced`, `GeometricallyIrreducible`, and `GeometricallyIntegral` satisfy
  `MorphismProperty.DescendsAlong` along `@Surjective`, so they are invariant under base change
  along any surjective morphism (in particular any field extension `Spec L ⟶ Spec k`).
-/

public section

open CategoryTheory Limits MorphismProperty AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- An isomorphism of schemes is geometrically integral. -/
lemma geometricallyIntegral_of_isIso {X Y : Scheme.{u}} (f : X ⟶ Y) [IsIso f] :
    GeometricallyIntegral f :=
  ⟨fun _ _ _ _ _ snd h ↦ have := h.isIso_snd_of_isIso; .of_isIso (inv snd)⟩

/-- `AlgebraicGeometry.IsIntegral` is closed under isomorphisms of schemes. -/
instance isClosedUnderIsomorphisms_isIntegral :
    ObjectProperty.IsClosedUnderIsomorphisms _root_.AlgebraicGeometry.IsIntegral :=
  ⟨fun e _ ↦ .of_isIso e.hom⟩

/-- `GeometricallyIntegral` respects isomorphisms on both source and target. -/
instance respectsIso_geometricallyIntegral : MorphismProperty.RespectsIso @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

/-- `GeometricallyIntegral` is Zariski-local on the target. -/
instance isZariskiLocalAtTarget_geometricallyIntegral :
    IsZariskiLocalAtTarget @GeometricallyIntegral :=
  GeometricallyIntegral.eq_geometrically ▸ inferInstance

/-- Reducedness of a scheme descends along any flat surjective morphism, with no Noetherian or
irreducible-component finiteness assumption. -/
theorem isReduced_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsReduced X] : IsReduced Y := by
  have (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    exact f.isReduced_stalk_of_flat x
  exact isReduced_of_isReduced_stalk Y

/-- Irreducibility of the underlying topological space descends along any surjective morphism of
schemes. -/
theorem irreducibleSpace_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    [IrreducibleSpace X] : IrreducibleSpace Y := by
  refine (irreducibleSpace_def Y).mpr ?_
  rw [Set.top_eq_univ, ← range_eq_univ f, ← Set.image_univ]
  exact (IrreducibleSpace.isIrreducible_univ X).image f f.continuous.continuousOn

/-- Integrality of a scheme descends along any flat surjective morphism, with no Noetherian
assumption. -/
theorem isIntegral_of_flat_of_surjective {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f]
    [IsIntegral X] : IsIntegral Y := by
  have : IsReduced Y := isReduced_of_flat_of_surjective f
  have : IrreducibleSpace Y := irreducibleSpace_of_surjective f
  exact isIntegral_of_irreducibleSpace_of_isReduced Y

/-- If an object property `P` of schemes descends along flat surjective morphisms, then
`geometrically P` descends along arbitrary surjective morphisms: every field-valued point
`y : Spec K ⟶ Z` lifts through the surjective base change `X ×_Z Spec K ⟶ Spec K` to the residue
field `L` of a point of that fibre, and `Spec L ⟶ Spec K` is flat and surjective. -/
theorem geometrically_descendsAlong_surjective (P : ObjectProperty Scheme.{u})
    (hP : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f], P X → P Y) :
    (geometrically P).DescendsAlong @Surjective.{u} where
  of_isPullback {A X Y Z fst snd f g} h hf hfst := by
    intro K _ y W₀ pY pK hW₀
    have : Surjective f := hf
    obtain ⟨t, -⟩ := (pullback.snd f y).surjective (IsLocalRing.closedPoint K)
    let α : Spec (.of ((pullback f y).residueField t)) ⟶ Spec (.of K) :=
      (pullback f y).fromSpecResidueField t ≫ pullback.snd f y
    let β : Spec (.of ((pullback f y).residueField t)) ⟶ X :=
      (pullback f y).fromSpecResidueField t ≫ pullback.fst f y
    have hαy : α ≫ y = β ≫ f := by simp [α, β, ← pullback.condition]
    have hsq₁ := IsPullback.of_hasPullback pK α
    exact hP (pullback.fst pK α)
      (hfst β _ _ (IsPullback.of_right' (hαy ▸ hsq₁.paste_horiz hW₀) h.flip))

/-- `GeometricallyReduced` descends along arbitrary surjective morphisms of schemes. -/
instance descendsAlong_surjective_geometricallyReduced :
    DescendsAlong @GeometricallyReduced.{u} @Surjective.{u} :=
  GeometricallyReduced.eq_geometrically ▸
    geometrically_descendsAlong_surjective IsReduced fun f _ _ hX ↦
      @isReduced_of_flat_of_surjective _ _ f _ _ hX

/-- `GeometricallyIrreducible` descends along arbitrary surjective morphisms of schemes. -/
instance descendsAlong_surjective_geometricallyIrreducible :
    DescendsAlong @GeometricallyIrreducible.{u} @Surjective.{u} :=
  GeometricallyIrreducible.eq_geometrically ▸
    geometrically_descendsAlong_surjective (IrreducibleSpace ·) fun f _ _ hX ↦
      @irreducibleSpace_of_surjective _ _ f _ hX

/-- `GeometricallyIntegral` descends along arbitrary surjective morphisms of schemes. -/
instance descendsAlong_surjective_geometricallyIntegral :
    DescendsAlong @GeometricallyIntegral.{u} @Surjective.{u} :=
  GeometricallyIntegral.eq_geometrically ▸
    geometrically_descendsAlong_surjective IsIntegral fun f _ _ hX ↦
      @isIntegral_of_flat_of_surjective _ _ f _ _ hX

/-- In a pullback square along a surjective morphism `f : X ⟶ Z`, the pullback `fst` is
geometrically integral if and only if `g` is geometrically integral. -/
theorem geometricallyIntegral_iff_of_isPullback_of_surjective {A X Y Z : Scheme.{u}}
    {fst : A ⟶ X} {snd : A ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback fst snd f g) [Surjective f] :
    GeometricallyIntegral fst ↔ GeometricallyIntegral g :=
  MorphismProperty.iff_of_isPullback (P := @GeometricallyIntegral) (Q := @Surjective) h
    inferInstance

end AlgebraicGeometry

end TauCeti
