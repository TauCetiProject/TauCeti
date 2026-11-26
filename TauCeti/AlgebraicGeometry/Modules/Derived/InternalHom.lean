/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Flat
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.KFlat
public import TauCeti.Algebra.Homology.DerivedCategory.InternalHom.Adjunction
public import TauCeti.Algebra.Homology.ModelCategory.KInjective.Resolution
public import TauCeti.AlgebraicGeometry.Modules.Derived.Tensor

/-!
# The derived tensor–internal Hom adjunction on `D(𝒪_X)`

For a scheme `X`, the derived tensor product `L ⊗^L -` on the unbounded derived category
`D(𝒪_X)` of `𝒪_X`-modules is left adjoint to the derived internal Hom `R𝓗om(L, -)`:

`Hom_{D(𝒪_X)}(L ⊗^L K, M) ≃ Hom_{D(𝒪_X)}(K, R𝓗om(L, M))`

naturally in `K` and `M`, with no boundedness assumption
(`TauCeti.AlgebraicGeometry.Coherent.derivedTensorInternalHomAdj`, Stacks, Lemma 20.42.1 (08DI)).
Taking `L = 𝒪_X[0]` gives `R𝓗om(𝒪_X[0], M) ≅ M`
(`TauCeti.AlgebraicGeometry.Coherent.derivedInternalHomStructureSheafIso`).

These are the general results `TauCeti.derivedTensorInternalHomAdj` and
`TauCeti.derivedInternalHomSingleUnitIso` for the closed symmetric monoidal Grothendieck abelian
category `X.Modules`, on which the derived tensor product `TauCeti.derivedTensor X.Modules` exists
by `TauCeti.AlgebraicGeometry.Coherent.isLeftDerivabilityStructure_kFlat_localizerMorphism`
(`TauCeti/AlgebraicGeometry/Modules/Derived/Tensor.lean`). The separating family is the
extensions by zero `j_! 𝒪_U` of the structure sheaf of the opens `U` of `X`
(`SheafOfModules.isSeparating_freeYonedaFunctor`); they are flat, so tensoring with them preserves
acyclic complexes (`SheafOfModules.acyclic_tensorRight_freeYonedaFunctor_obj`).

## References

* [Stacks Project, Lemma 20.42.1 (08DI)](https://stacks.math.columbia.edu/tag/08DI) and
  [Stacks Project, Section 21.35 (08J7)](https://stacks.math.columbia.edu/tag/08J7).
-/

public section

noncomputable section

open CategoryTheory Limits MonoidalCategory Opposite AlgebraicGeometry

universe w u

namespace TauCeti.AlgebraicGeometry.Coherent

variable (X : Scheme.{u})

/-- The extensions by zero `j_! 𝒪_U` of the structure sheaf of the opens `U` of `X`, as a family
of `𝒪_X`-modules. -/
private abbrev separatingFamily : ObjectProperty X.Modules :=
  ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj

/-- The extensions by zero `j_! 𝒪_U` of the structure sheaf form a separating family of
`𝒪_X`-modules for which tensoring on the right preserves acyclic complexes. -/
private lemma acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj (G : X.Modules)
    (hG : separatingFamily X G)
    (E : CochainComplex X.Modules ℤ) (hE : E.Acyclic) :
    (((tensorRight G).mapHomologicalComplex _).obj E).Acyclic := by
  obtain ⟨U⟩ := hG
  exact SheafOfModules.acyclic_tensorRight_freeYonedaFunctor_obj (R := X.sheaf) U hE

variable [HasDerivedCategory.{w} X.Modules]

/-- **The derived tensor–internal Hom adjunction on `D(𝒪_X)`.** For an object `L` of the
unbounded derived category of `𝒪_X`-modules, the derived tensor product `L ⊗^L -` is left adjoint
to the derived internal Hom `R𝓗om(L, -)`, so that
`Hom(L ⊗^L K, M) ≃ Hom(K, R𝓗om(L, M))` naturally in `K` and `M` (Stacks, Lemma 20.42.1 (08DI)). -/
def derivedTensorInternalHomAdj (L : DerivedCategory X.Modules) :
    (derivedTensor X.Modules).obj L ⊣ (derivedInternalHom X.Modules).obj (op L) :=
  -- `X.Modules` and the separating family are given explicitly: otherwise the category is read
  -- off the type of `SheafOfModules.isSeparating_freeYonedaFunctor` as the unfolded
  -- `SheafOfModules X.ringCatSheaf`, on which the instances for `X.Modules` are not found.
  TauCeti.derivedTensorInternalHomAdj (C := X.Modules) (S := separatingFamily X)
    (SheafOfModules.isSeparating_freeYonedaFunctor _)
    (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X) (derivedTensor X.Modules)
    (derivedTensorCounit X.Modules) L

/-- The derived internal Hom `R𝓗om(𝒪_X[0], -)` out of the structure sheaf placed in degree `0`
is the identity functor of `D(𝒪_X)`. -/
def derivedInternalHomStructureSheafIso :
    (derivedInternalHom X.Modules).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (𝟙_ X.Modules))) ≅ 𝟭 _ :=
  derivedInternalHomSingleUnitIso X.Modules (S := separatingFamily X)
    (SheafOfModules.isSeparating_freeYonedaFunctor _)
    (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X)

end TauCeti.AlgebraicGeometry.Coherent
