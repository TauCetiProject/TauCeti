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
its compatibility with isomorphisms and Zariski-local descent on the target, and shows that every
reduced scheme over a perfect field is geometrically reduced over that field, without any
finiteness hypothesis. In particular, typeclass search supplies `GeometricallyReduced` for reduced
schemes over algebraically closed, finite, and characteristic-zero fields.

## Main declarations

* `TauCeti.AlgebraicGeometry.respectsIso_geometricallyReduced`: `GeometricallyReduced` respects
  isomorphisms on both source and target.
* `TauCeti.AlgebraicGeometry.isZariskiLocalAtTarget_geometricallyReduced`: `GeometricallyReduced`
  is Zariski-local on the target.
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

private theorem geometricallyReduced_Spec_of_perfectField {k : Type u} [Field k]
    [PerfectField k] (A : CommRingCat.{u}) [IsReduced (Spec A)] (f : Spec A ⟶ Spec (.of k)) :
    GeometricallyReduced f := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  intro K _ _
  have : _root_.IsReduced A := (affine_isReduced_iff A).mp ‹_›
  obtain ⟨φ, hφ⟩ := Spec.map_surjective f
  algebraize [φ.hom]
  have halg : Spec.map (CommRingCat.ofHom (algebraMap k A)) = f := hφ
  let e : pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) ≅ Spec (.of (A ⊗[k] K)) :=
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
  let g : Spec (.of K) ⟶ Spec (.of k) := Spec.map (CommRingCat.ofHom (algebraMap k K))
  refine @IsReduced.of_openCover _ (Scheme.Pullback.openCoverOfLeft X.affineCover f g)
    fun (i : X.affineCover.I₀) ↦ ?_
  have hSpec : GeometricallyReduced
      ((X.affineCover.X i).isoSpec.inv ≫ X.affineCover.f i ≫ f) :=
    geometricallyReduced_Spec_of_perfectField Γ(X.affineCover.X i, ⊤) _
  have hChart : GeometricallyReduced (X.affineCover.f i ≫ f) :=
    (MorphismProperty.cancel_left_of_respectsIso @GeometricallyReduced
      (X.affineCover.X i).isoSpec.inv _).mp hSpec
  exact pullback_of_geometrically hChart.1 K g

end AlgebraicGeometry

end TauCeti
