/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExteriorPower.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Restriction of exterior powers on schemes

Exterior powers of module sheaves commute with restriction along every open immersion.
The forward comparison sends a wedge of restricted sections to the restriction of their wedge.
It is the canonical pushforward comparison for the functor sending an open to its image,
with coefficient map the inverse structure-sheaf isomorphism. No quasicoherence, finiteness,
or flatness hypothesis is required.

The natural isomorphism is `TauCeti.AlgebraicGeometry.restrictExteriorPowerIso`;
`TauCeti.AlgebraicGeometry.restrictExteriorPowerIso_hom_app` identifies its forward map.

This is a comparison for `AlgebraicGeometry.Scheme.Modules.restrictFunctor`. Identifying its
inverse with the adjunction-defined exterior-power pullback comparison requires compatibility
with the restriction--pushforward adjunction; that identification is not asserted here.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

-- Adapted from `AlgebraicGeometry.Scheme.Modules.restrictSymmetricPowerIso`.
/-- Exterior powers commute with restriction along an open immersion, naturally in the module
sheaf. The forward map is the canonical exterior-power pushforward comparison. -/
def restrictExteriorPowerIso (n : ℕ) :
    restrictFunctor f ⋙ _root_.SheafOfModules.exteriorPower X.sheaf n ≅
      _root_.SheafOfModules.exteriorPower Y.sheaf n ⋙ restrictFunctor f :=
  @asIso _ _ _ _ (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison
    (restrictRingCatSheafHom f) n)
    -- The scheme and generic site sheaf categories have different instance heads;
    -- pass the coefficient-map isomorphism explicitly.
    (@TauCeti.SheafOfModules.isIso_pushforwardExteriorPowerComparison
      _ _ _ _ _ _ _ _ _ _ _ _ f.opensFunctor _ X.sheaf Y.sheaf
      (restrictRingCatSheafHom f) inferInstance
      (isIso_restrictRingCatSheafHom f) n)

/-- The forward restriction isomorphism is the canonical pushforward comparison. -/
-- Keep this equation named: expanding the forward map would obstruct simplification by the
-- generic isomorphism inverse laws in importing modules.
theorem restrictExteriorPowerIso_hom_app (n : ℕ) (M : Y.Modules) :
    (restrictExteriorPowerIso f n).hom.app M =
      (TauCeti.SheafOfModules.pushforwardExteriorPowerComparison
        (restrictRingCatSheafHom f) n).app M :=
  (rfl)

end

end TauCeti.AlgebraicGeometry
