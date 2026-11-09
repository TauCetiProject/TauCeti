/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors, Axel Delaval, Jie Xu, Shitan Xu
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import TauCeti.RingTheory.TensorProduct.IsDomain

/-!
# Geometric irreducibility, images, and dense opens

Over an algebraically closed field `K`, the spectrum of every domain is geometrically irreducible:
for every field `M` over `K`, the fibre product `Spec A ×_K Spec M ≅ Spec (A ⊗[K] M)` is irreducible
because `A ⊗[K] M` is a domain (`TauCeti.isDomain_tensorProduct_of_isAlgClosed`). In particular a
morphism `Spec L ⟶ Spec K` from the spectrum of a field extension is geometrically irreducible.

Such a morphism is also universally open, as is every morphism to the spectrum of a field. Hence,
for a scheme `X` over `K`, the projection `p : X ×_K Spec L ⟶ X` is geometrically irreducible and
open, and Mathlib's `AlgebraicGeometry.Scheme.Hom.irreducibleComponentsEquiv` identifies the
irreducible components of `X ×_K Spec L` with those of `X`: a component `E` of `X` corresponds to
its preimage `p ⁻¹' E`, and a component `E'` of `X ×_K Spec L` to its image `p '' E'`. So the
irreducible components of a geometric fibre do not depend on the chosen algebraically closed
field.

The file also transports geometric irreducibility through surjective images and dominant maps
over a field, and supplies geometric connectedness. Mathlib supplies the corresponding transport
to nonempty open subschemes.

## Main results

* `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isAlgClosed`: over an algebraically
  closed field, a morphism from the spectrum of a domain is geometrically irreducible.

* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.geometricallyConnected`: the low-priority
  instance that geometric irreducibility implies geometric connectedness.
* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.of_comp_surjective`: geometric irreducibility
  descends along a surjective morphism.
* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.of_comp_isDominant`: geometric irreducibility
  descends along a dominant morphism over a field.

The image and dense-open results are adapted from Axel Delaval, Jie Xu, and Shitan Xu's Jacobian
library, release `baef7723da528551b7d2f93bd9a9a53303b04dbc`,
`Jacobian/AlgebraicGeometry/Geometrically/Irreducible.lean`, declarations
`GeometricallyIrreducible.geometricallyConnected`, `GeometricallyIrreducible.of_surjective`,
`GeometricallyIrreducible.of_dense_open`.

## References

* The Stacks Project, Chapter *Varieties*, Section *Geometrically irreducible schemes*.
-/

public section

open CategoryTheory Limits AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- Over an algebraically closed field `K`, every morphism `Spec A ⟶ Spec K` from the spectrum of a
domain is geometrically irreducible. -/
instance geometricallyIrreducible_Spec_of_isAlgClosed {K A : Type u} [Field K] [IsAlgClosed K]
    [CommRing A] [IsDomain A] {g : Spec (.of A) ⟶ Spec (.of K)} : GeometricallyIrreducible g := by
  obtain ⟨φ, rfl⟩ := Spec.map_surjective g
  algebraize [φ.hom]
  rw [geometricallyIrreducible_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro M _ _
  -- The fibre product is `Spec (A ⊗[K] M)`, the spectrum of a domain.
  exact (pullbackSpecIso K A M).inv.homeomorph.irreducibleSpace_iff.mp inferInstance

/-! ### Images and dense opens -/

/-- Every geometrically irreducible morphism is geometrically connected. -/
instance (priority := low) GeometricallyIrreducible.geometricallyConnected
    {source target : Scheme.{u}} (morphism : source ⟶ target)
    [GeometricallyIrreducible morphism] : GeometricallyConnected morphism := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace fiber :=
    GeometricallyIrreducible.geometrically_irreducibleSpace point first second square
  infer_instance

/-- Base-changing the source of a geometrically irreducible composite to a field gives an
irreducible scheme. -/
lemma GeometricallyIrreducible.irreducibleSpace_pullback_of_comp
    {source target base fiber : Scheme.{u}} (f : source ⟶ target) (g : target ⟶ base)
    [GeometricallyIrreducible (f ≫ g)] {field : Type u} [Field field]
    {point : Spec (.of field) ⟶ base} {first : fiber ⟶ target}
    {second : fiber ⟶ Spec (.of field)} (square : IsPullback first second g point) :
    IrreducibleSpace (pullback f first : Scheme.{u}) :=
  GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _
    ((IsPullback.of_hasPullback f first).paste_vert square)

/-- Geometric irreducibility descends along a surjective morphism of schemes. -/
lemma GeometricallyIrreducible.of_comp_surjective {source target base : Scheme.{u}}
    (sourceToTarget : source ⟶ target) (targetToBase : target ⟶ base)
    [Surjective sourceToTarget] [GeometricallyIrreducible (sourceToTarget ≫ targetToBase)] :
    GeometricallyIrreducible targetToBase := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace (pullback sourceToTarget first : Scheme.{u}) :=
    GeometricallyIrreducible.irreducibleSpace_pullback_of_comp
      sourceToTarget targetToBase square
  exact Function.Surjective.irreducibleSpace (pullback.snd sourceToTarget first).continuous
    (pullback.snd sourceToTarget first).surjective

/-- Geometric irreducibility of a composite over a field descends along a dominant morphism. -/
lemma GeometricallyIrreducible.of_comp_isDominant {field : Type u} [Field field]
    {source target : Scheme.{u}} (morphism : source ⟶ target) [IsDominant morphism]
    (structureMap : target ⟶ Spec (.of field))
    [GeometricallyIrreducible (morphism ≫ structureMap)] :
    GeometricallyIrreducible structureMap := by
  refine ⟨fun extensionField _ point fiber first second square ↦ ?_⟩
  have : IrreducibleSpace (pullback morphism first : Scheme.{u}) :=
    GeometricallyIrreducible.irreducibleSpace_pullback_of_comp morphism structureMap square
  have : UniversallyOpen first := MorphismProperty.of_isPullback square.flip inferInstance
  have denseImage : Dense (Set.range (pullback.snd morphism first)) := by
    rw [Scheme.Pullback.range_snd]
    exact morphism.denseRange.preimage first.isOpenMap
  have irreducibleImage : IsIrreducible (Set.range (pullback.snd morphism first)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (pullback morphism first : Scheme.{u})).image
        (pullback.snd morphism first) (pullback.snd morphism first).continuous.continuousOn
  apply (irreducibleSpace_def fiber).mpr
  simpa only [denseImage.closure_eq, Set.top_eq_univ] using irreducibleImage.closure

end AlgebraicGeometry

end TauCeti
