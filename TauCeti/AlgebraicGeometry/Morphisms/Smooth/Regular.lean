/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Geometrically.Connected
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.IrreducibleOfConnectedDomainStalk
public import TauCeti.RingTheory.Smooth.Regular

/-!
# Smooth schemes over regular schemes are regular, and geometric integrality

If `f : X ⟶ Y` is a smooth morphism and `Y` is a locally Noetherian scheme all of whose local
rings are regular, then every local ring of `X` is regular. On affine opens `U ⊆ f⁻¹ V` this is
`TauCeti.IsRegularRing.of_smooth`, since the ring of sections of `Y` over an affine open is a
regular ring exactly when the local rings at its points are regular. In particular every local
ring of a scheme smooth over a field is regular.

Consequently a smooth, geometrically connected morphism is geometrically integral: after base
change to a field the scheme is smooth over that field, hence locally Noetherian with regular,
so integral, local rings, and a connected such scheme is integral
(`TauCeti.AlgebraicGeometry.isIntegral_of_connected_of_isRegularLocalRing_stalk`). For a smooth,
proper, geometrically connected curve over a field this is its geometric integrality.

## Main declarations

* `TauCeti.AlgebraicGeometry.isRegularRing_iff_isRegularLocalRing_stalk`: the sections over an
  affine open with Noetherian ring of sections form a regular ring exactly when the local rings
  at the points of the open are regular;
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_Spec`: the local rings of the spectrum of a
  regular ring are regular;
* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth`: a scheme smooth over a
  locally Noetherian scheme with regular local rings has regular local rings;
* `TauCeti.AlgebraicGeometry.Smooth.geometricallyIntegral`: a smooth, geometrically connected
  morphism is geometrically integral.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If the sections over an affine open `U` form a regular ring, the local rings at the points of
`U` are regular. -/
theorem isRegularLocalRing_stalk_of_isRegularRing {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsRegularRing Γ(X, U)] {x : X} (hx : x ∈ U) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hx⟩
  have := hU.isLocalization_stalk ⟨x, hx⟩
  exact .of_ringEquiv (IsLocalization.algEquiv (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
    (Localization.AtPrime (hU.primeIdealOf ⟨x, hx⟩).asIdeal) (X.presheaf.stalk x)).toRingEquiv

/-- The sections over an affine open `U` with Noetherian ring of sections form a regular ring
exactly when the local rings at the points of `U` are regular. -/
theorem isRegularRing_iff_isRegularLocalRing_stalk {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) [IsNoetherianRing Γ(X, U)] :
    IsRegularRing Γ(X, U) ↔ ∀ x ∈ U, IsRegularLocalRing (X.presheaf.stalk x) := by
  refine ⟨fun _ _ hx ↦ isRegularLocalRing_stalk_of_isRegularRing hU hx, fun h ↦ ?_⟩
  refine isRegularRing_iff.mpr fun p _ ↦ ?_
  -- The prime `p` is the prime of the point `hU.fromSpec y` of `U`, whose stalk is `Γ(X, U)_p`.
  let y : PrimeSpectrum Γ(X, U) := ⟨p, inferInstance⟩
  have hy : hU.fromSpec y ∈ U := hU.range_fromSpec.le ⟨y, rfl⟩
  let := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨hU.fromSpec y, hy⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk (hU.fromSpec y)) p :=
    hU.isLocalization_stalk' y hy
  have := h _ hy
  exact .of_ringEquiv (IsLocalization.algEquiv p.primeCompl
    (X.presheaf.stalk (hU.fromSpec y)) (Localization.AtPrime p)).toRingEquiv

/-- The local rings of the spectrum of a regular ring are regular. -/
instance isRegularLocalRing_stalk_Spec (R : CommRingCat.{u}) [IsRegularRing R] (x : Spec R) :
    IsRegularLocalRing ((Spec R).presheaf.stalk x) :=
  have : IsRegularRing Γ(Spec R, ⊤) :=
    .of_ringEquiv (Scheme.ΓSpecIso R).commRingCatIsoToRingEquiv.symm
  isRegularLocalRing_stalk_of_isRegularRing (isAffineOpen_top _) (Set.mem_univ x)

/-- If `f : X ⟶ Y` is smooth and `Y` is locally Noetherian with regular local rings, then the
local rings of `X` are regular. -/
theorem isRegularLocalRing_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [IsLocallyNoetherian Y] [∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (show f x ∈ (⊤ : Y.Opens) from trivial)
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (show x ∈ f ⁻¹ᵁ V from hxV)
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := (isRegularRing_iff_isRegularLocalRing_stalk hV).mpr fun y _ ↦ inferInstance
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Smooth Γ(Y, V) Γ(X, U) :=
    (HasRingHomProperty.appLE @Smooth f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV).toAlgebra
  have := IsRegularRing.of_smooth (R := Γ(Y, V)) (S := Γ(X, U))
  exact isRegularLocalRing_stalk_of_isRegularRing hU hxU

/-- A smooth, geometrically connected morphism of schemes is geometrically integral. -/
instance (priority := low) Smooth.geometricallyIntegral {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [GeometricallyConnected f] : GeometricallyIntegral f := by
  constructor
  intro K _ y Z fst snd h
  have : Smooth snd := MorphismProperty.of_isPullback h inferInstance
  have : ConnectedSpace Z := GeometricallyConnected.geometrically_connectedSpace y fst snd h
  have : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian snd
  have : ∀ z : Z, IsRegularLocalRing (Z.presheaf.stalk z) := isRegularLocalRing_stalk_of_smooth snd
  exact isIntegral_of_connected_of_isRegularLocalRing_stalk Z

end AlgebraicGeometry

end TauCeti
