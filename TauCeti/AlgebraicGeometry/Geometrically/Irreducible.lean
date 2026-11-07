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

## Main results

* `TauCeti.AlgebraicGeometry.geometricallyIrreducible_Spec_of_isAlgClosed`: over an algebraically
  closed field, a morphism from the spectrum of a domain is geometrically irreducible.

* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.of_surjective`: geometric irreducibility
  descends along a surjective morphism.
* `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.comp_of_isOpenImmersion` and
  `TauCeti.AlgebraicGeometry.GeometricallyIrreducible.of_dense_open`: geometric irreducibility
  passes to nonempty opens and extends from dense opens.

The image and dense-open results are adapted from Axel Delaval, Jie Xu, and Shitan Xu's Jacobian
library, release `baef7723da528551b7d2f93bd9a9a53303b04dbc`,
`Jacobian/AlgebraicGeometry/Geometrically/Irreducible.lean`, declarations
`GeometricallyIrreducible.geometricallyConnected`, `GeometricallyIrreducible.of_surjective`,
`GeometricallyIrreducible.comp_of_isOpenImmersion`, and
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

/-- Geometric irreducibility descends along a surjective morphism of schemes. -/
lemma GeometricallyIrreducible.of_surjective {source target base : Scheme.{u}}
    (sourceToTarget : source ⟶ target) (targetToBase : target ⟶ base)
    [Surjective sourceToTarget] [GeometricallyIrreducible (sourceToTarget ≫ targetToBase)] :
    GeometricallyIrreducible targetToBase := by
  refine ⟨fun field _ point fiber first second square ↦ ?_⟩
  have compositeSquare : IsPullback (pullback.fst sourceToTarget first)
      (pullback.snd sourceToTarget first ≫ second) (sourceToTarget ≫ targetToBase) point :=
    (IsPullback.of_hasPullback sourceToTarget first).paste_vert square
  have : IrreducibleSpace (pullback sourceToTarget first : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ compositeSquare
  exact Function.Surjective.irreducibleSpace (pullback.snd sourceToTarget first).continuous
    (pullback.snd sourceToTarget first).surjective

/-- A nonempty open subscheme of a geometrically irreducible scheme over a field is again
geometrically irreducible over that field. -/
lemma GeometricallyIrreducible.comp_of_isOpenImmersion {field : Type u} [Field field]
    {source target : Scheme.{u}} (immersion : source ⟶ target) [IsOpenImmersion immersion]
    [Nonempty source] (structureMap : target ⟶ Spec (.of field))
    [GeometricallyIrreducible structureMap] :
    GeometricallyIrreducible (immersion ≫ structureMap) := by
  have : Surjective (immersion ≫ structureMap) :=
    ⟨fun point ↦ ⟨Classical.choice ‹Nonempty source›, Subsingleton.elim _ point⟩⟩
  infer_instance

/-- Geometric irreducibility over a field extends from a dense open subscheme. -/
lemma GeometricallyIrreducible.of_dense_open {field : Type u} [Field field]
    {source target : Scheme.{u}} (immersion : source ⟶ target) [IsOpenImmersion immersion]
    (structureMap : target ⟶ Spec (.of field)) (denseRange : DenseRange immersion)
    [GeometricallyIrreducible (immersion ≫ structureMap)] :
    GeometricallyIrreducible structureMap := by
  refine ⟨fun extensionField _ point fiber first second square ↦ ?_⟩
  have compositeSquare : IsPullback (pullback.fst immersion first)
      (pullback.snd immersion first ≫ second) (immersion ≫ structureMap) point :=
    (IsPullback.of_hasPullback immersion first).paste_vert square
  let : IrreducibleSpace (pullback immersion first : Scheme.{u}) :=
    GeometricallyIrreducible.geometrically_irreducibleSpace _ _ _ compositeSquare
  let : UniversallyOpen first := MorphismProperty.of_isPullback square.flip inferInstance
  have denseImage : Dense (Set.range (pullback.snd immersion first)) := by
    rw [IsOpenImmersion.range_pullbackSnd]
    exact (show Dense (Set.range immersion) from denseRange).preimage first.isOpenMap
  have irreducibleImage : IsIrreducible (Set.range (pullback.snd immersion first)) := by
    simpa only [Set.image_univ] using
      (IrreducibleSpace.isIrreducible_univ (pullback immersion first : Scheme.{u})).image
        (pullback.snd immersion first) (pullback.snd immersion first).continuous.continuousOn
  apply (irreducibleSpace_def fiber).mpr
  simpa only [denseImage.closure_eq, Set.top_eq_univ] using irreducibleImage.closure

end AlgebraicGeometry

end TauCeti
