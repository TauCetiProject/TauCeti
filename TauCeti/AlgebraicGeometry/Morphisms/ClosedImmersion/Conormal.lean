/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Cotangent
public import TauCeti.AlgebraicGeometry.IdealSheaf.Pullback
public import TauCeti.AlgebraicGeometry.Modules.Tilde.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.ClosedImmersion.AffineChart
import TauCeti.AlgebraicGeometry.IdealSheaf.Affine
import TauCeti.AlgebraicGeometry.IdealSheaf.Tilde
import TauCeti.RingTheory.Ideal.Cotangent.ExtendScalars

/-!
# The conormal sheaf of a closed immersion on its affine charts

Let `j : X ⟶ Z` be a closed immersion with ideal sheaf `I`, and `U` an affine open of `Z`. On the
affine chart `Spec (Γ(Z, U) ⧸ I(U))` of `X` (`Scheme.Hom.affineChart`), the pullback `j^* I` of
`I` is the sheaf associated with the conormal module `I(U) ⧸ I(U)²`
(`Scheme.Hom.pullbackConormalAffineChartIsoTilde`). In particular it is free when `I(U) ⧸ I(U)²`
is (`Scheme.Hom.nonempty_pullback_conormal_affineChart_iso_free`).

## Main declarations

* `AlgebraicGeometry.Scheme.Hom.pullbackConormalAffineChartIsoTilde j U`: the pullback of `j^* I`
  to the affine chart over `U` is `(I(U) ⧸ I(U)²)~`.
* `AlgebraicGeometry.Scheme.Hom.nonempty_pullback_conormal_affineChart_iso_free`: if
  `I(U) ⧸ I(U)²` is free, so is the pullback of `j^* I` to the affine chart over `U`.
-/

public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Hom

open TauCeti.AlgebraicGeometry

variable {X Z : Scheme.{u}} (j : X ⟶ Z) [IsClosedImmersion j] (U : Z.affineOpens)

/-- For a closed immersion `j : X ⟶ Z` with ideal sheaf `I` and an affine open `U` of `Z`, the
pullback of `j^* I` to the affine chart `Spec (Γ(Z, U) ⧸ I(U))` of `X` is the sheaf associated with
the conormal module `I(U) ⧸ I(U)²`. -/
noncomputable def pullbackConormalAffineChartIsoTilde :
    (Scheme.Modules.pullback (j.affineChart U)).obj ((Scheme.Modules.pullback j).obj j.ker.sheaf) ≅
      tilde (ModuleCat.of _ (Ideal.Cotangent (j.ker.ideal U))) :=
  -- Pull `I` back along `Spec (Γ(Z, U) ⧸ I(U)) ⟶ Spec Γ(Z, U) ⟶ Z`: the open immersion
  -- `U.fromSpec` turns it into the ideal sheaf `I(U)~` of `I(U)`, and the closed immersion then
  -- extends scalars to `(Γ(Z, U) ⧸ I(U)) ⊗ I(U) = I(U) ⧸ I(U)²`. The pullback along
  -- `Spec (Γ(Z, U) ⧸ I(U)) ⟶ Spec Γ(Z, U)`, which is `Spec.map` of the quotient map, is extension
  -- of scalars along the quotient map (`tildeFunctorCompPullbackIso`), and that extension of
  -- scalars is `I(U) ⧸ I(U)²` (`Ideal.extendScalarsMkEquivCotangent`).
  have : IsOpenImmersion U.property.fromSpec := U.property.isOpenImmersion_fromSpec
  (Scheme.Modules.pullbackComp (j.affineChart U) j).app _ ≪≫
    (Scheme.Modules.pullbackCongr (j.affineChart_comp U)).app _ ≪≫
    ((Scheme.Modules.pullbackComp _ U.property.fromSpec).app _).symm ≪≫
    (Scheme.Modules.pullback _).mapIso (asIso (j.ker.pullbackSheafHom U.property.fromSpec) ≪≫
      eqToIso (congrArg IdealSheafData.sheaf (j.ker.comap_fromSpec_eq_ofIdealTop U.property)) ≪≫
      IdealSheafData.ofIdealTopSheafIsoTilde (j.ker.ideal U)) ≪≫
    (tildeFunctorCompPullbackIso _).app (ModuleCat.of _ _) ≪≫
    (tilde.functor _).mapIso (Ideal.extendScalarsMkEquivCotangent (j.ker.ideal U)).toModuleIso

/-- For a closed immersion `j : X ⟶ Z` with ideal sheaf `I`, and an affine open `U` of `Z` on
which the conormal module `I(U) ⧸ I(U)²` is free over `Γ(Z, U) ⧸ I(U)`, the pullback of
`j^* I` to the affine chart `Spec (Γ(Z, U) ⧸ I(U))` of `X` is free on the same index type. -/
theorem nonempty_pullback_conormal_affineChart_iso_free {ι : Type u}
    (b : Module.Basis ι (Γ(Z, U) ⧸ j.ker.ideal U) (Ideal.Cotangent (j.ker.ideal U))) :
    Nonempty ((Scheme.Modules.pullback (j.affineChart U)).obj
      ((Scheme.Modules.pullback j).obj j.ker.sheaf) ≅ SheafOfModules.free ι) :=
  ⟨j.pullbackConormalAffineChartIsoTilde U ≪≫ (tilde.functor _).mapIso b.repr.toModuleIso ≪≫
    tildeFinsupp ι⟩

end AlgebraicGeometry.Scheme.Hom
