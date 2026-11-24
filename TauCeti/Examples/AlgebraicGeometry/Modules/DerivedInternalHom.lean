/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat
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

* the derived internal Hom bifunctor on `D(𝒪_X)`, the internal Hom complex `𝓗om^•(I, J)` between
  K-injective replacements `I` of `K` and `J` of `L`, and its identification with `R𝓗om(K, L)`
  below;
* the internal Hom complex out of the structure sheaf in degree `0` is the target,
  `𝓗om^•(𝒪_X[0], L) ≅ L`;
* the global sections `Hom(𝒪_X, -)` of the internal Hom complex representing `R𝓗om(K, L)` have
  cohomology `Hom_{D(𝒪_X)}(K, L[n])` in degree `n`.

The internal Hom complex `𝓗om^•(K, J)` from `K` itself into `J` is `R𝓗om(K, L)` of
[Stacks, Section 20.42 (08DH)]. `TauCeti.derivedInternalHomQObjObjIso` identifies it with the
bifunctor above, given a separating family of objects `G` for which `- ⊗ G` preserves acyclic
complexes. For `𝒪_X`-modules the extensions by zero `j_! 𝒪_U` of the structure sheaf form such a
family: they separate (`SheafOfModules.isSeparating_freeYonedaFunctor`) and are flat
(`SheafOfModules.preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj`), so tensoring with them
is exact.

## References

* [Stacks Project, Section 20.42 (08DH)](https://stacks.math.columbia.edu/tag/08DH).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory CochainComplex Opposite AlgebraicGeometry

namespace TauCeti.Examples.DerivedInternalHom

universe w' w u

variable (X : Scheme.{u}) [HasDerivedCategory.{w} X.Modules]

/-- The derived internal Hom bifunctor `𝓗om^•(I, J)` on the derived category of `𝒪_X`-modules,
between K-injective replacements. -/
example : (DerivedCategory X.Modules)ᵒᵖ ⥤ DerivedCategory X.Modules ⥤ DerivedCategory X.Modules :=
  derivedInternalHom X.Modules

/-- The derived internal Hom of a complex `K` of `𝒪_X`-modules is `R𝓗om(K, L) = 𝓗om^•(K, J)`, the
internal Hom complex from `K` itself into the K-injective replacement `J` of `L`. -/
example (K : CochainComplex X.Modules ℤ) (L : DerivedCategory X.Modules) :
    ((derivedInternalHom X.Modules).obj (op (DerivedCategory.Q.obj K))).obj L ≅
      DerivedCategory.Q.obj (internalHomComplex K ((kInjectiveReplacement X.Modules).obj L).as) :=
  derivedInternalHomQObjObjIso (C := X.Modules)
    (P := (ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj :
      ObjectProperty X.Modules))
    (SheafOfModules.isSeparating_freeYonedaFunctor _) (by
      rintro _ ⟨U⟩ E hE i
      let G : X.Modules := (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj U
      have : PreservesFiniteLimits (tensorLeft G) :=
        SheafOfModules.preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj (R := X.sheaf) U
      have : PreservesFiniteLimits (tensorRight G) :=
        preservesFiniteLimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
      have : PreservesFiniteColimits (tensorRight G) :=
        preservesFiniteColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight G)
      have := hE i
      rw [HomologicalComplex.exactAt_iff] at this ⊢
      exact this.map (tensorRight G)) K L

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
