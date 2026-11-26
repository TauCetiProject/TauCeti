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
acyclic complexes
(`TauCeti.AlgebraicGeometry.Coherent.acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj`).
The lemmas `TauCeti.AlgebraicGeometry.Coherent.derivedTensorInternalHomAdj_eq` and
`TauCeti.AlgebraicGeometry.Coherent.derivedInternalHomStructureSheafIso_eq` identify the two
constructions with the general ones, so that their API (for instance
`TauCeti.exists_derivedTensorInternalHomAdj_eq` and
`TauCeti.derivedInternalHomSingleUnitIso_hom_app`) applies to them.

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

/-- Tensoring on the right with a member of the family of extensions by zero `j_! 𝒪_U` of the
structure sheaf of the opens `U` of `X` preserves acyclic complexes, since these sheaves are flat
(`HomologicalComplex.Acyclic.mapHomologicalComplex_tensorRight`). -/
lemma acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj (G : X.Modules)
    (hG : ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj G)
    (E : CochainComplex X.Modules ℤ) (hE : E.Acyclic) :
    (((tensorRight G).mapHomologicalComplex _).obj E).Acyclic := by
  have : PreservesFiniteLimits (tensorLeft G) := by
    obtain ⟨U⟩ := hG
    exact SheafOfModules.preservesFiniteLimits_tensorLeft_freeYonedaFunctor_obj (R := X.sheaf) U
  exact hE.mapHomologicalComplex_tensorRight G

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
  TauCeti.derivedTensorInternalHomAdj (C := X.Modules)
    (S := ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj)
    (SheafOfModules.isSeparating_freeYonedaFunctor _)
    (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X) (derivedTensor X.Modules)
    (derivedTensorCounit X.Modules) L

/-- `Coherent.derivedTensorInternalHomAdj X L` is the general adjunction
`TauCeti.derivedTensorInternalHomAdj` for the separating family of the `j_! 𝒪_U`, so that its API
(`TauCeti.exists_derivedTensorInternalHomAdj_eq`,
`TauCeti.derivedTensorInternalHomAdjOfQuasiIso_homEquiv`) applies. -/
lemma derivedTensorInternalHomAdj_eq (L : DerivedCategory X.Modules) :
    derivedTensorInternalHomAdj X L =
      TauCeti.derivedTensorInternalHomAdj (C := X.Modules)
        (S := ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj)
        (SheafOfModules.isSeparating_freeYonedaFunctor _)
        (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X) (derivedTensor X.Modules)
        (derivedTensorCounit X.Modules) L :=
  (rfl)

/-- The derived internal Hom `R𝓗om(𝒪_X[0], -)` out of the structure sheaf placed in degree `0`
is the identity functor of `D(𝒪_X)`. -/
def derivedInternalHomStructureSheafIso :
    (derivedInternalHom X.Modules).obj
        (op ((DerivedCategory.singleFunctor X.Modules 0).obj (𝟙_ X.Modules))) ≅ 𝟭 _ :=
  derivedInternalHomSingleUnitIso X.Modules
    (S := ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj)
    (SheafOfModules.isSeparating_freeYonedaFunctor _)
    (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X)

/-- `Coherent.derivedInternalHomStructureSheafIso X` is the general isomorphism
`TauCeti.derivedInternalHomSingleUnitIso` for the separating family of the `j_! 𝒪_U`, so that its
components are given by `TauCeti.derivedInternalHomSingleUnitIso_hom_app` and
`TauCeti.derivedInternalHomSingleUnitIso_inv_app`. -/
lemma derivedInternalHomStructureSheafIso_eq :
    derivedInternalHomStructureSheafIso X =
      derivedInternalHomSingleUnitIso X.Modules
        (S := ObjectProperty.ofObj (SheafOfModules.freeYonedaFunctor X.ringCatSheaf).obj)
        (SheafOfModules.isSeparating_freeYonedaFunctor _)
        (acyclic_tensorRight_of_ofObj_freeYonedaFunctor_obj X) :=
  (rfl)

end TauCeti.AlgebraicGeometry.Coherent
