/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
import TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Quasicoherent
import TauCeti.AlgebraicGeometry.Modules.Pullback.Basic

/-!
# Preservation of local finiteness and presentation properties under scheme pullback

Pullback of sheaves of modules along any morphism of schemes `f : X ⟶ Y` preserves
quasi-coherence, finite type, finite presentation, and local freeness, specializing the
ringed-space results of `TauCeti.Algebra.Category.ModuleCat.Sheaf.Pullback.Quasicoherent`.

## Main declarations

* `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_pullback`: pullback preserves
  quasi-coherence;
* `AlgebraicGeometry.Scheme.Modules.isFiniteType_pullback`: pullback preserves finite type;
* `AlgebraicGeometry.Scheme.Modules.isFinitePresentation_pullback`: pullback preserves finite
  presentation;
* `AlgebraicGeometry.Scheme.Modules.isLocallyFree_pullback`: pullback preserves local freeness.

## References

* [The Stacks Project, Tag 01BQ](https://stacks.math.columbia.edu/tag/01BQ)
-/

public section

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X Y : Scheme.{u}}

/-- The pullback of a quasi-coherent module along a morphism of schemes is quasi-coherent. -/
instance isQuasicoherent_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsQuasicoherent] :
    ((pullback f).obj M).IsQuasicoherent :=
  SheafOfModules.isQuasicoherent_pullback f.toRingCatSheafHom M

/-- The pullback of a module of finite type along a morphism of schemes is of finite type. -/
instance isFiniteType_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFiniteType] :
    ((pullback f).obj M).IsFiniteType :=
  SheafOfModules.isFiniteType_pullback f.toRingCatSheafHom M

/-- The pullback of a finitely presented module along a morphism of schemes is finitely
presented. -/
instance isFinitePresentation_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsFinitePresentation] :
    ((pullback f).obj M).IsFinitePresentation :=
  SheafOfModules.isFinitePresentation_pullback f.toRingCatSheafHom M

/-- The pullback of a locally free module along a morphism of schemes is locally free. -/
instance isLocallyFree_pullback (f : X ⟶ Y) (M : Y.Modules) [M.IsLocallyFree] :
    ((pullback f).obj M).IsLocallyFree :=
  SheafOfModules.isLocallyFree_pullback f.toRingCatSheafHom M

end

end AlgebraicGeometry.Scheme.Modules
