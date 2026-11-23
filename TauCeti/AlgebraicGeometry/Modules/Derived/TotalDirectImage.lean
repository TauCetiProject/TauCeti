/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Homology
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Cohomology.HigherDirectImage.Basic

/-!
# The total direct image of complexes of module sheaves

For a morphism of schemes `f : X ⟶ Y`, the total direct image
`f.totalDirectImage : D(𝒪_X) ⥤ D(𝒪_Y)`, written `Rf_*`, is the right derived functor of the
pushforward of module sheaves on the unbounded derived categories. It is computed by applying
`f_*` termwise to K-injective replacements, which exist because module sheaves on `X` form a
Grothendieck abelian category (`TauCeti.hasKInjectiveResolutions_of_isGrothendieckAbelian`). No
hypothesis on `f` and no boundedness of complexes is needed.

As an instance of `CategoryTheory.Functor.rightDerivedFunctor`, it is a right derived functor in
the sense of `CategoryTheory.Functor.IsRightDerivedFunctor`, it is triangulated, and on a
K-injective complex `I` it is `f_* I`. On a single module sheaf `F`, its cohomology sheaves are the
higher direct images of `AlgebraicGeometry.Scheme.Hom.higherDirectImage`:
`Hⁿ(Rf_* F[0]) ≅ Rⁿf_* F`, naturally in `F`
(`AlgebraicGeometry.Scheme.Hom.totalDirectImageHomologyIso`). Along the identity of `X` it is the
identity functor (`AlgebraicGeometry.Scheme.Hom.totalDirectImageIdIso`).

The derived categories `D(𝒪_X)` and `D(𝒪_Y)` are any models of Mathlib's `HasDerivedCategory`,
for instance `HasDerivedCategory.standard`.

## References

* [Stacks Project, Section 20.28 (Tag 079V)](https://stacks.math.columbia.edu/tag/079V),
  Cohomology of unbounded complexes.
-/

public section

noncomputable section

open CategoryTheory DerivedCategory

universe w w' u

namespace AlgebraicGeometry.Scheme.Hom

variable {X Y : Scheme.{u}} [HasDerivedCategory.{w} X.Modules] [HasDerivedCategory.{w'} Y.Modules]

/-- The total direct image `Rf_* : D(𝒪_X) ⥤ D(𝒪_Y)` of a morphism of schemes `f : X ⟶ Y`: the right
derived functor of the pushforward of module sheaves, on unbounded complexes. -/
abbrev totalDirectImage (f : X ⟶ Y) : DerivedCategory X.Modules ⥤ DerivedCategory Y.Modules :=
  (Scheme.Modules.pushforward f).rightDerivedFunctor

/-- The cohomology sheaves of the total direct image of a module sheaf placed in degree `0` are its
higher direct images: `Hⁿ(Rf_* F[0]) ≅ Rⁿf_* F`, naturally in `F`. -/
def totalDirectImageHomologyIso (f : X ⟶ Y) (n : ℕ) :
    singleFunctor X.Modules 0 ⋙ f.totalDirectImage ⋙ homologyFunctor Y.Modules n ≅
      f.higherDirectImage n :=
  (Scheme.Modules.pushforward f).rightDerivedFunctorHomologyIso n

variable (X) in
/-- The total direct image along the identity of `X` is the identity functor of `D(𝒪_X)`. -/
def totalDirectImageIdIso : totalDirectImage (𝟙 X) ≅ 𝟭 (DerivedCategory X.Modules) :=
  NatIso.rightDerivedFunctor (Scheme.Modules.pushforwardId X) ≪≫
    Functor.rightDerivedFunctorIdIso X.Modules

end AlgebraicGeometry.Scheme.Hom
