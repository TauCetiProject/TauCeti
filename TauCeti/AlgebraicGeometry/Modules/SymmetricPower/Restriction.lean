/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Restriction of symmetric powers on schemes

Symmetric powers of module sheaves commute with restriction along every open immersion.
The comparison is the canonical pushforward comparison for the functor sending an open to
its image; its coefficient map is the inverse of the structure-sheaf isomorphism on that open.
No quasicoherence hypothesis is required.
-/

public section

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

universe u

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]

/-- Symmetric powers commute with restriction along an open immersion, naturally in the
module sheaf. The forward map is the canonical symmetric-power pushforward comparison. -/
def restrictSymmetricPowerIso (n : ℕ) :
    restrictFunctor f ⋙ SheafOfModules.symmetricPower X.sheaf n ≅
      SheafOfModules.symmetricPower Y.sheaf n ⋙ restrictFunctor f :=
  @asIso _ _ _ _ (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison
    (restrictRingCatSheafHom f) n)
    -- The scheme sheaf category and the generic site sheaf category have different
    -- instance heads; pass the same coefficient-map isomorphism explicitly.
    (@TauCeti.SheafOfModules.isIso_pushforwardSymmetricPowerComparison
      _ _ _ _ _ _ _ _ _ _ _ _ f.opensFunctor _ X.sheaf Y.sheaf
      (restrictRingCatSheafHom f) inferInstance (isIso_restrictRingCatSheafHom f) n)

/-- The forward restriction isomorphism is the canonical pushforward comparison. -/
-- Keep this equation named: expanding the forward map prevents the generic isomorphism
-- inverse laws from matching in ordinary importing simplification.
theorem restrictSymmetricPowerIso_hom_app (n : ℕ) (M : Y.Modules) :
    (restrictSymmetricPowerIso f n).hom.app M =
      (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison
        (restrictRingCatSheafHom f) n).app M :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules
