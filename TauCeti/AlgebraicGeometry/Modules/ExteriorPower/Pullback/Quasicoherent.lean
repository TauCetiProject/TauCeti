/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Affine
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Pullback.Coherence
public import TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Restriction
public import TauCeti.AlgebraicGeometry.Modules.Pullback.Comparison

/-!
# Exterior powers commute with pullback of quasicoherent sheaves

For every morphism of schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical
comparison `f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)` (`Scheme.Modules.pullbackExteriorPowerComparison`) is
an isomorphism. There are no flatness, finiteness or characteristic hypotheses.

The three inputs of the local criterion
`TauCeti.AlgebraicGeometry.isIso_pullbackComparison_app_of_isQuasicoherent` are the composition
coherence `TauCeti.AlgebraicGeometry.pullbackExteriorPowerComparison_comp`, invertibility along
open immersions for every sheaf of modules
(`TauCeti.AlgebraicGeometry.isIso_pullbackExteriorPowerComparison_app_of_isOpenImmersion`, in
`TauCeti.AlgebraicGeometry.Modules.ExteriorPower.Restriction`), and invertibility on
quasicoherent modules between affine spectra, where the comparison is the scalar-extension
isomorphism (`TauCeti.AlgebraicGeometry.isIso_pullbackExteriorPowerComparison_of_spec`).

## Main declaration

* `TauCeti.AlgebraicGeometry.isIso_pullbackExteriorPowerComparison_app`: the comparison along
  an arbitrary morphism is invertible on every quasicoherent sheaf.

## References

* R. Hartshorne, *Algebraic Geometry*, Exercise II.5.16.
* The Stacks Project, Lemma 10.13.6 (Tag 0C6F).
-/

public section

open CategoryTheory

namespace TauCeti.AlgebraicGeometry

open _root_.AlgebraicGeometry

universe u

/-- **Exterior powers commute with pullback of quasicoherent sheaves**: for every morphism of
schemes `f : X ⟶ Y` and every quasicoherent `𝒪_Y`-module `M`, the canonical comparison
`f^* (⋀ⁿ M) ⟶ ⋀ⁿ (f^* M)` is an isomorphism. -/
instance isIso_pullbackExteriorPowerComparison_app {X Y : Scheme.{u}} (f : X ⟶ Y) (n : ℕ)
    (M : Y.Modules) [M.IsQuasicoherent] :
    IsIso ((Scheme.Modules.pullbackExteriorPowerComparison f n).app M) :=
  isIso_pullbackComparison_app_of_isQuasicoherent
    (fun X : Scheme.{u} ↦ _root_.SheafOfModules.exteriorPower X.sheaf n)
    (fun f ↦ Scheme.Modules.pullbackExteriorPowerComparison f n)
    (fun f g M ↦ pullbackExteriorPowerComparison_comp f g n M)
    (fun _ _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) f M

end TauCeti.AlgebraicGeometry
