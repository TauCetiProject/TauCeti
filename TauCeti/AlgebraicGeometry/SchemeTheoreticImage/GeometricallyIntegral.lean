/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
import TauCeti.AlgebraicGeometry.Morphisms.Dominant
import TauCeti.AlgebraicGeometry.SchemeTheoreticImage.Over
import TauCeti.CategoryTheory.Comma.Over

/-!
# Geometrically integral scheme-theoretic images over a field

The scheme-theoretic image of a quasi-compact morphism from a geometrically integral scheme over
a field is geometrically integral. Schematic dominance of the map to the image survives scalar
extension and transfers reducedness and irreducibility to the image over each extension field.

## References

* The Stacks Project, Lemma 29.26.16, Tag 081I, on flat base change of scheme-theoretic images.
-/

public section

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme.Hom

universe u

/-- The scheme-theoretic image of a geometrically integral scheme over a field is geometrically
integral over that field. -/
theorem geometricallyIntegral_imageι_comp {K : Type u} [Field K] {X Y : Scheme.{u}}
    (f : X ⟶ Y) [QuasiCompact f] (p : Y ⟶ Spec (.of K))
    [GeometricallyIntegral (f ≫ p)] : GeometricallyIntegral (f.imageι ≫ p) := by
  constructor
  intro L _ b Z a c h
  let fOver : Over.mk (f ≫ p) ⟶ Over.mk p := Over.homMk f
  let q := fOver.toImageOver
  let qL : pullback (f ≫ p) b ⟶ pullback (f.imageι ≫ p) b :=
    ((Over.pullback b).map q).left
  have hq := (Over.isPullback_pullback_map_left b q).flip
  have : QuasiCompact fOver.left := inferInstanceAs (QuasiCompact f)
  have hflat : Flat (pullback.fst fOver.imageOver.hom b) :=
    inferInstanceAs (Flat (pullback.fst (f.imageι ≫ p) b))
  have : IsSchemeTheoreticallyDominant qL :=
    @IsSchemeTheoreticallyDominant.of_isPullback _ _ _ _ _ _ _ _ hq
      inferInstance inferInstance hflat
  have : QuasiCompact qL := MorphismProperty.of_isPullback hq inferInstance
  have : IsIntegral (pullback (f ≫ p) b) :=
    pullback_of_geometrically (GeometricallyIntegral.geometrically_isIntegral) L b
  let r := qL ≫ h.isoPullback.inv
  have : IsSchemeTheoreticallyDominant r := inferInstanceAs
    (IsSchemeTheoreticallyDominant (qL ≫ h.isoPullback.inv))
  have : QuasiCompact r := inferInstanceAs (QuasiCompact (qL ≫ h.isoPullback.inv))
  have : IrreducibleSpace Z := r.irreducibleSpace_of_isDominant
  have : IsReduced Z := IsSchemeTheoreticallyDominant.isReduced r
  exact isIntegral_of_irreducibleSpace_of_isReduced Z

end AlgebraicGeometry.Scheme.Hom
