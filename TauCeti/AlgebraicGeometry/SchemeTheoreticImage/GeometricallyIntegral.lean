/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Basic
import Mathlib.AlgebraicGeometry.Morphisms.Flat
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.CategoryTheory.Comma.Over

/-!
# Geometric integrality of a schematic image over a field

Geometric integrality descends along a quasi-compact schematically dominant morphism over a
field. After extending scalars, schematic dominance is preserved by flat base change.
The base-changed source is integral, so the target is both reduced and irreducible.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u

variable {k : Type u} [Field k] {X Y : Scheme.{u}}

/-- Over a field, geometric integrality descends along quasi-compact schematically dominant
morphisms. -/
theorem GeometricallyIntegral.of_comp_of_isSchemeTheoreticallyDominant
    (f : X ⟶ Y) (g : Y ⟶ Spec (.of k)) [QuasiCompact f]
    [IsSchemeTheoreticallyDominant f] [GeometricallyIntegral (f ≫ g)] :
    GeometricallyIntegral g := by
  rw [GeometricallyIntegral.eq_geometrically]
  intro K _ y Z fst snd H
  let a : Over.mk (f ≫ g) ⟶ Over.mk g := Over.homMk f
  let a' : pullback (f ≫ g) y ⟶ pullback g y := ((Over.pullback y).map a).left
  have h : IsPullback a' (pullback.fst (f ≫ g) y) (pullback.fst g y) f :=
    Over.isPullback_pullback_map_left y a
  have : IsIntegral (pullback (f ≫ g) y) :=
    pullback_of_geometrically GeometricallyIntegral.geometrically_isIntegral K y
  have : IsSchemeTheoreticallyDominant a' := .of_isPullback h.flip
  have : QuasiCompact a' := MorphismProperty.of_isPullback h.flip inferInstance
  have : IsReduced (pullback g y) := IsSchemeTheoreticallyDominant.isReduced a'
  have : IrreducibleSpace (pullback (C := Scheme) g y) := a'.irreducibleSpace_of_isDominant
  have : IsIntegral (pullback g y) := isIntegral_of_irreducibleSpace_of_isReduced _
  exact .of_isIso H.isoPullback.inv

/-- The scheme-theoretic image of a quasi-compact morphism from a geometrically integral
scheme over a field is geometrically integral over that field. -/
instance Scheme.Hom.geometricallyIntegral_imageι_comp (f : X ⟶ Y) (g : Y ⟶ Spec (.of k))
    [QuasiCompact f] [GeometricallyIntegral (f ≫ g)] : GeometricallyIntegral (f.imageι ≫ g) := by
  have : GeometricallyIntegral (f.toImage ≫ f.imageι ≫ g) := by
    rwa [f.toImage_imageι_assoc]
  exact GeometricallyIntegral.of_comp_of_isSchemeTheoreticallyDominant f.toImage _

end AlgebraicGeometry
