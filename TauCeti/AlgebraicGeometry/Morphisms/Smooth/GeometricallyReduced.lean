/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.RingTheory.Smooth.GeometricallyReduced

/-!
# Smooth morphisms are geometrically reduced

A smooth scheme over a reduced base is reduced. On affine charts, the coordinate algebras
are reduced by `TauCeti.isReduced_of_smooth`. After base change to a field, this also shows
that a smooth morphism has geometrically reduced fibres.

The main results are `AlgebraicGeometry.Scheme.Hom.isReduced_of_smooth` and the instance
`TauCeti.AlgebraicGeometry.Smooth.geometricallyReduced`. Smooth,
geometrically connected morphisms are also shown to be geometrically integral in
`TauCeti.AlgebraicGeometry.Morphisms.Smooth.GeometricallyIntegral`.

No formalization is vendored. The commutative-algebra input is
`TauCeti.isReduced_of_smooth`; the passage from affine opens to the whole scheme uses
Mathlib's `AlgebraicGeometry.IsReduced.of_openCover`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- The source of a smooth morphism over a reduced base is reduced. -/
theorem _root_.AlgebraicGeometry.Scheme.Hom.isReduced_of_smooth
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f] [IsReduced Y] : IsReduced X := by
  have hred (i : Y.affineCover.I₀) : IsReduced ((Y.affineCover.pullback₁ f).X i) := by
    let Z := (Y.affineCover.pullback₁ f).X i
    let g : Z ⟶ Y.affineCover.X i := Y.affineCover.pullbackHom f i
    have : Smooth g :=
      MorphismProperty.of_isPullback (IsPullback.of_hasPullback f (Y.affineCover.f i))
        (inferInstance : Smooth f)
    have (j : Z.affineCover.I₀) : IsReduced (Z.affineCover.X j) := by
      have hg := HasRingHomProperty.appTop @Smooth (Z.affineCover.f j ≫ g)
        (inferInstance : Smooth (Z.affineCover.f j ≫ g))
      let _ : Algebra Γ(Y.affineCover.X i, ⊤) Γ(Z.affineCover.X j, ⊤) :=
        ((Z.affineCover.f j ≫ g).appTop).hom.toAlgebra
      have : Algebra.Smooth Γ(Y.affineCover.X i, ⊤) Γ(Z.affineCover.X j, ⊤) := hg.toAlgebra
      have : _root_.IsReduced Γ(Z.affineCover.X j, ⊤) :=
        TauCeti.isReduced_of_smooth Γ(Y.affineCover.X i, ⊤) Γ(Z.affineCover.X j, ⊤)
      exact isReduced_of_isAffine_isReduced _
    exact IsReduced.of_openCover Z Z.affineCover
  exact @IsReduced.of_openCover X (Y.affineCover.pullback₁ f) hred

/-- Every smooth morphism of schemes is geometrically reduced. -/
instance (priority := low) Smooth.geometricallyReduced {X Y : Scheme.{u}} (f : X ⟶ Y)
    [Smooth f] : GeometricallyReduced f := by
  constructor
  intro K _ y Z fst snd h
  let _ : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  exact snd.isReduced_of_smooth

end AlgebraicGeometry

end TauCeti
