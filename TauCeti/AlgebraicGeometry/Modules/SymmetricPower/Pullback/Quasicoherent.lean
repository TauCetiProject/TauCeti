/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Pullback.Comparison
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Affine
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Pullback.Coherence
public import TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Restriction

/-!
# Symmetric powers commute with pullback of quasicoherent sheaves

For every morphism of schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical
comparison `f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` (`Scheme.Modules.pullbackSymmetricPowerComparison`) is
an isomorphism. There are no flatness, finiteness or characteristic hypotheses.

The three inputs of the local criterion
`TauCeti.AlgebraicGeometry.isIso_pullbackComparison_app_of_isQuasicoherent` are the composition
coherence `TauCeti.AlgebraicGeometry.pullbackSymmetricPowerComparison_comp`, invertibility along
open immersions for every sheaf of modules
(`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app_of_isOpenImmersion`, in
`TauCeti.AlgebraicGeometry.Modules.SymmetricPower.Restriction`), and invertibility on
quasicoherent modules between affine spectra, where the comparison is the scalar-extension
isomorphism (`TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_of_spec`).

## Main declaration

* `TauCeti.AlgebraicGeometry.isIso_pullbackSymmetricPowerComparison_app`: the comparison along
  an arbitrary morphism is invertible on every quasicoherent sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- **Symmetric powers commute with pullback of quasicoherent sheaves**: for every morphism of
schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical comparison
`f^* (Symⁿ M) ⟶ Symⁿ (f^* M)` is an isomorphism. -/
instance isIso_pullbackSymmetricPowerComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Y.Modules) [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackSymmetricPowerComparison f n).app M) :=
  isIso_pullbackComparison_app_of_isQuasicoherent
    (fun X : Scheme.{u} ↦ _root_.SheafOfModules.symmetricPower X.sheaf n)
    (fun f ↦ Scheme.Modules.pullbackSymmetricPowerComparison f n)
    (fun f g M ↦ pullbackSymmetricPowerComparison_comp f g n M)
    (fun _ _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) f M

end TauCeti.AlgebraicGeometry
