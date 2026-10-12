/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import TauCeti.AlgebraicGeometry.Scheme.RegularLocalRing
public import TauCeti.RingTheory.Smooth.Regular

/-!
# Smooth schemes over regular schemes are regular

If `f : X ⟶ Y` is a smooth morphism and `Y` is a locally Noetherian scheme all of whose local
rings are regular, then every local ring of `X` is regular. On affine opens `U ⊆ f⁻¹ V` this is
`TauCeti.IsRegularRing.of_smooth`, since the ring of sections of `Y` over an affine open is a
regular ring exactly when the local rings at its points are regular. In particular every local
ring of a scheme smooth over a field is regular.

## Main declarations

* `TauCeti.AlgebraicGeometry.isRegularLocalRing_stalk_of_smooth`: a scheme smooth over a
  locally Noetherian scheme with regular local rings has regular local rings.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti

namespace AlgebraicGeometry

universe u

/-- If `f : X ⟶ Y` is smooth and `Y` is locally Noetherian with regular local rings, then the
local rings of `X` are regular. -/
theorem isRegularLocalRing_stalk_of_smooth {X Y : Scheme.{u}} (f : X ⟶ Y) [Smooth f]
    [IsLocallyNoetherian Y] [∀ y : Y, IsRegularLocalRing (Y.presheaf.stalk y)] (x : X) :
    IsRegularLocalRing (X.presheaf.stalk x) := by
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset
    (TopologicalSpace.Opens.mem_top (f x))
  obtain ⟨U, hU, hxU, hUV⟩ := exists_isAffineOpen_mem_and_subset (f.mem_preimage.mpr hxV)
  have : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian ⟨V, hV⟩
  have := (isRegularRing_iff_isRegularLocalRing_stalk hV).mpr fun y _ ↦ inferInstance
  let := (f.appLE V U hUV).hom.toAlgebra
  have : Algebra.Smooth Γ(Y, V) Γ(X, U) :=
    (HasRingHomProperty.appLE @Smooth f ‹_› ⟨V, hV⟩ ⟨U, hU⟩ hUV).toAlgebra
  have := IsRegularRing.of_smooth (R := Γ(Y, V)) (S := Γ(X, U))
  exact isRegularLocalRing_stalk_of_isRegularRing hU hxU

end AlgebraicGeometry

end TauCeti
