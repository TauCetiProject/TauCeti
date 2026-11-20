/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.InternalHom
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Product

/-!
# The derived internal Hom of `𝒪_X`-modules

For a scheme `X`, the category `X.Modules` of `𝒪_X`-modules is closed monoidal and additive in
each variable (`AlgebraicGeometry.Scheme.Modules.instMonoidalClosed`,
`AlgebraicGeometry.Scheme.Modules.instMonoidalPreadditive`), has all products, and is
Grothendieck abelian, so every unbounded complex has a K-injective replacement
(`TauCeti.hasKInjectiveResolutions_of_isGrothendieckAbelian`). Hence the general constructions
apply to `𝒪_X`-modules:

* the derived internal Hom `R𝓗om(K, L)` on `D(𝒪_X)`;
* the internal Hom complex out of the structure sheaf in degree `0` is the target,
  `𝓗om^•(𝒪_X[0], L) ≅ L`;
* the global sections `Hom(𝒪_X, -)` of the internal Hom complex representing `R𝓗om(K, L)` have
  cohomology `Hom_{D(𝒪_X)}(K, L[n])` in degree `n`.

## References

* [Stacks Project, Section 20.42 (08DH)](https://stacks.math.columbia.edu/tag/08DH).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CochainComplex Opposite AlgebraicGeometry

namespace TauCeti.Examples.DerivedInternalHom

universe w' w u

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- The derived internal Hom `R𝓗om(K, L)` on the derived category of `𝒪_X`-modules. -/
example : (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  derivedInternalHom X.Modules

/-- The internal Hom complex out of `𝒪_X` placed in degree `0` is the target complex. -/
example (L : CochainComplex X.Modules ℤ) :
    internalHomComplex ((singleFunctor X.Modules 0).obj (𝟙_ X.Modules)) L ≅ L :=
  internalHomComplexSingleUnitIso L

/-- The `n`-th cohomology of the global sections `Hom(𝒪_X, -)` of the internal Hom complex
representing `R𝓗om(K, L)` is `Hom_{D(𝒪_X)}(K, L[n])`. -/
example [HasDerivedCategory.{w'} (ModuleCat.{u} ℤ)] (K L : DerivedCategory X.Modules) (n : ℤ) :
    ((((linearCoyoneda ℤ X.Modules).obj (op (𝟙_ X.Modules))).mapHomologicalComplex _).obj
      (internalHomComplex ((kInjectiveReplacement X.Modules).obj K).as
        ((kInjectiveReplacement X.Modules).obj L).as)).homology n ≃+ (K ⟶ L⟦n⟧) :=
  globalSectionsDerivedInternalHomHomologyAddEquiv K L n

end TauCeti.Examples.DerivedInternalHom
