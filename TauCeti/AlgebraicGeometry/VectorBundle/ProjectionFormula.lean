/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Monoidal.Basic
public import TauCeti.AlgebraicGeometry.VectorBundle.Dual.Pullback

/-!
# The projection formula for finite locally free sheaves

Let `f : X ⟶ Y` be a morphism of schemes and `E` a finite locally free sheaf on `Y`. The
projection formula identifies, naturally in the sheaf of modules `N` on `X`,

`E ⊗ f_* N ≅ f_* (f^* E ⊗ N)`.

No hypothesis on `f` is needed. Both sides are right adjoint functors of `N`: tensoring with `E` is
right adjoint to tensoring with its dual `E^∨`, and tensoring with `f^* E` is right adjoint to
tensoring with `f^* E^∨`, the dual of `f^* E`
(`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.pullbackDualIso`). Their left adjoints
`T ↦ f^* (E^∨ ⊗ T)` and `T ↦ f^* E^∨ ⊗ f^* T` agree because pullback commutes with tensoring by
the quasi-coherent sheaf `E^∨` (`AlgebraicGeometry.Scheme.Modules.pullbackTensorLeftIso`), so the
right adjoints agree too.

For the closed subscheme `ι : Z ⟶ X` cut out by an ideal sheaf, the case `N = 𝒪_Z` identifies
`E ⊗ ι_* 𝒪_Z`, the restriction of `E` to `Z` seen on `X`, with the direct image of the pullback
`ι^* E` (`TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf.tensorPushforwardUnitIso`).

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.1(d) (the projection formula for a locally
  free sheaf of finite rank).
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf

open _root_.AlgebraicGeometry

universe u

noncomputable section

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (E : FiniteLocallyFreeSheaf Y)

/-- **The projection formula.** For a finite locally free sheaf `E` on `Y` and any morphism
`f : X ⟶ Y`, tensoring a direct image with `E` is the direct image of the tensor product with
`f^* E`: `E ⊗ f_* N ≅ f_* (f^* E ⊗ N)`, naturally in the sheaf of modules `N` on `X`. -/
def pushforwardTensorLeftIso :
    Scheme.Modules.pushforward f ⋙ tensorLeft E.obj ≅
      tensorLeft ((pullback f).obj E).obj ⋙ Scheme.Modules.pushforward f :=
  letI := exactPairingObjDual E
  letI := exactPairingObjDual ((pullback f).obj E)
  haveI : (dual E).obj.IsQuasicoherent := ((toQuasicoherent Y).obj (dual E)).property
  let d : (Scheme.Modules.pullback f).obj (dual E).obj ≅ (dual ((pullback f).obj E)).obj :=
    eqToIso (pullback_obj_obj f (dual E)).symm ≪≫
      (Scheme.Modules.isFiniteLocallyFree X).ι.mapIso (pullbackDualIso f E)
  -- Pullback commutes with tensoring by the quasi-coherent sheaf `E^∨`, whose pullback is the
  -- dual of `f^* E`.
  let e : tensorLeft (dual E).obj ⋙ Scheme.Modules.pullback f ≅
      Scheme.Modules.pullback f ⋙ tensorLeft (dual ((pullback f).obj E)).obj :=
    Scheme.Modules.pullbackTensorLeftIso f (dual E).obj ≪≫
      Functor.isoWhiskerLeft (Scheme.Modules.pullback f) ((curriedTensor X.Modules).mapIso d)
  ((tensorLeftAdjunction E.obj (dual E).obj).comp
      (Scheme.Modules.pullbackPushforwardAdjunction f)).rightAdjointUniq
    (((Scheme.Modules.pullbackPushforwardAdjunction f).comp
      (tensorLeftAdjunction ((pullback f).obj E).obj
        (dual ((pullback f).obj E)).obj)).ofNatIsoLeft e.symm)

/-- The projection formula for the direct image of the structure sheaf:
`E ⊗ f_* 𝒪_X ≅ f_* (f^* E)`. For a closed immersion `f` this identifies the restriction of `E` to
the closed subscheme, seen on `Y`, with the direct image of the pullback of `E`. -/
def tensorPushforwardUnitIso :
    E.obj ⊗ (Scheme.Modules.pushforward f).obj (𝟙_ X.Modules) ≅
      (Scheme.Modules.pushforward f).obj ((pullback f).obj E).obj :=
  (pushforwardTensorLeftIso f E).app (𝟙_ X.Modules) ≪≫
    (Scheme.Modules.pushforward f).mapIso (ρ_ _)

end

end TauCeti.AlgebraicGeometry.FiniteLocallyFreeSheaf
