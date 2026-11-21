/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.FieldTheory.Perfect
import TauCeti.RingTheory.TensorProduct.Reduced

/-!
# Geometrically reduced morphisms and schemes over perfect fields

Mathlib's `AlgebraicGeometry.GeometricallyReduced` is stable under base change. This file records
its compatibility with isomorphisms and Zariski-local descent on the target, reducedness of base
changes along morphisms from integral subsingleton schemes (such as spectra of fields, without a
flatness or Noetherian hypothesis), and shows that every reduced scheme over a perfect field is
geometrically reduced over that field, without any finiteness hypothesis. In particular, typeclass
search supplies `GeometricallyReduced` for reduced schemes over algebraically closed, finite, and
characteristic-zero fields.

## Main declarations

* `TauCeti.AlgebraicGeometry.respectsIso_geometricallyReduced`: `GeometricallyReduced` respects
  isomorphisms on both source and target.
* `TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_geometricallyReduced`: `GeometricallyReduced`
  is Zariski-local on the target.
* `TauCeti.AlgebraicGeometry.isReduced_pullback_of_geometricallyReduced` and
  `TauCeti.AlgebraicGeometry.isReduced_over_pullback_obj_left`: pulling back a geometrically
  reduced morphism along a morphism from an integral subsingleton scheme (such as `Spec K` for a
  field `K`) yields a reduced scheme.
* `TauCeti.AlgebraicGeometry.geometricallyReduced_of_perfectField`: a reduced scheme over a
  perfect field is geometrically reduced over that field.

## References

* The Stacks Project, [Tag 035Z](https://stacks.math.columbia.edu/tag/035Z),
  geometrically reduced schemes over perfect fields.
-/

public section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- `GeometricallyReduced` respects isomorphisms on both source and target. -/
instance respectsIso_geometricallyReduced : MorphismProperty.RespectsIso @GeometricallyReduced :=
  GeometricallyReduced.eq_geometrically ▸ inferInstance

/-- `GeometricallyReduced` is Zariski-local on the target. -/
instance isZariskiLocalAtTarget_geometricallyReduced :
    IsZariskiLocalAtTarget @GeometricallyReduced :=
  GeometricallyReduced.eq_geometrically ▸ inferInstance

/-- Pulling back a geometrically reduced morphism along a morphism from an integral subsingleton
scheme (in particular, `Spec K` for a field `K`) gives a reduced scheme, without any flatness or
Noetherian hypothesis. -/
instance isReduced_pullback_of_geometricallyReduced {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    [GeometricallyReduced f] [IsIntegral Y] [Subsingleton Y] :
    IsReduced (pullback f g) :=
  self_of_isIntegral_of_geometrically
    (inferInstance : GeometricallyReduced (pullback.snd f g)).geometrically_isReduced

/-- Base change of an object in `Over S` with geometrically reduced structure morphism along a
morphism from an integral subsingleton scheme (such as `Spec K` for a field `K`) has a reduced
underlying scheme. -/
instance isReduced_over_pullback_obj_left {S S' : Scheme.{u}} (f : S' ⟶ S)
    [IsIntegral S'] [Subsingleton S'] (Y : Over S) [GeometricallyReduced Y.hom] :
    IsReduced ((Over.pullback f).obj Y).left := by
  dsimp only [Over.pullback, Over.mk_left]
  infer_instance

private theorem geometricallyReduced_Spec_of_perfectField {k : Type u} [Field k]
    [PerfectField k] (A : CommRingCat.{u}) [IsReduced (Spec A)] (f : Spec A ⟶ Spec (.of k)) :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have : _root_.IsReduced A := (affine_isReduced_iff A).mp ‹_›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have halg : Spec.map (CommRingCat.ofHom (algebraMap k A)) = f := by
    rw [RingHom.algebraMap_toAlgebra, CommRingCat.ofHom_hom, hφ]
  let e : pullback f (Spec.algebraMap k K) ≅ Spec (.of (A ⊗[k] K)) :=
    pullback.congrHom halg.symm rfl ≪≫ pullbackSpecIso k A K
  have : _root_.IsReduced (A ⊗[k] K) := TauCeti.instIsReducedTensorProductOfPerfectField k A K
  exact isReduced_of_isOpenImmersion e.hom

/-- Every reduced scheme over a perfect field is geometrically reduced over that field, without a
finite-type hypothesis. -/
instance (priority := low) geometricallyReduced_of_perfectField {k : Type u} [Field k]
    [PerfectField k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsReduced X] :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  let g := Spec.algebraMap k K
  refine @IsReduced.of_openCover _ (Scheme.Pullback.openCoverOfLeft X.affineCover f g)
    fun (i : X.affineCover.I₀) ↦ ?_
  have hSpec : GeometricallyReduced
      ((X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i ≫ f) :=
    geometricallyReduced_Spec_of_perfectField Γ(X.affineCover.X i, ⊤) _
  have : GeometricallyReduced (X.affineCover.f i ≫ f) :=
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyReduced
      (X.affineCover.X i).isoSpec.inv _).mp hSpec
  exact isReduced_pullback_of_geometricallyReduced (X.affineCover.f i ≫ f) g

end AlgebraicGeometry

end TauCeti
