/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.SymmetricPower.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Quasicoherent

/-!
# Restriction of symmetric powers on schemes

Symmetric powers of module sheaves commute with restriction along every open immersion.
The comparison is the canonical pushforward comparison for the functor sending an open to
its image; its coefficient map is the inverse of the structure-sheaf isomorphism on that open.
No quasicoherence hypothesis is required. The unit of the restriction--pushforward adjunction
is compatible with this comparison and with the pushforward comparison
(`Scheme.Modules.restrictAdjunction_unit_app_symmetricPower`).
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

/-- The unit `M ⟶ f_* (M|_X)` of the restriction--pushforward adjunction along an open
immersion is compatible with the symmetric-power comparisons of pushforward and restriction. -/
theorem restrictAdjunction_unit_app_symmetricPower (n : ℕ) (M : Y.Modules) :
    (restrictAdjunction f).unit.app ((SheafOfModules.symmetricPower Y.sheaf n).obj M) =
      (SheafOfModules.symmetricPower Y.sheaf n).map ((restrictAdjunction f).unit.app M) ≫
        (TauCeti.SheafOfModules.pushforwardSymmetricPowerComparison f.toRingCatSheafHom n).app
          (M.restrict f) ≫
        (pushforward f).map ((restrictSymmetricPowerIso f n).hom.app M) := by
  rw [restrictSymmetricPowerIso_hom_app]
  -- As in `restrictAdjunction_unit_app_tensor`, the adjunction of opens is stated for
  -- `IsOpenMap.functor`, which is `f.opensFunctor`; `show` restates it in the form the sheaf-level
  -- lemma unifies with `restrictAdjunction f`.
  exact TauCeti.SheafOfModules.pushforwardPushforwardAdj_unit_app_symmetricPower
    (show f.opensFunctor ⊣ TopologicalSpace.Opens.map f.base from
      f.isOpenEmbedding.isOpenMap.adjunction) (restrictRingCatSheafHom f) f.toRingCatSheafHom
    _ _ n M

end AlgebraicGeometry.Scheme.Modules
