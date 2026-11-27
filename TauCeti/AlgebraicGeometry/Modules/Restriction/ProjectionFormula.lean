/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Modules.Restriction.ExtensionByZero
public import TauCeti.AlgebraicGeometry.Modules.Restriction.Closed
import TauCeti.CategoryTheory.Monoidal.Closed.ProjectionFormula

/-!
# The projection formula for extension by zero

For an open subscheme `U` of `X`, a module sheaf `M` on `X` and a module sheaf `N` on `U`,
extension by zero satisfies `j_! (j^* M ⊗ N) ≅ M ⊗ j_! N`. No finiteness or
quasicoherence hypothesis is required. This formula is the underived comparison used when
tensoring complexes with extension by zero.

The isomorphism is the conjugate, under the tensor--Hom and extension--restriction
adjunctions, of restriction's canonical internal-Hom comparison. The construction uses
`MonoidalClosed.ihomRightAdjointEquiv`.

## References

* [The Stacks Project, Lemma 18.27.9](https://stacks.math.columbia.edu/tag/0E8I).
-/

public section

noncomputable section

open CategoryTheory MonoidalCategory MonoidalClosed

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- The projection formula for extension by zero, natural in the module sheaf on `U`. -/
def extensionByZeroProjectionIso (M : X.Modules) :
    tensorLeft ((restrictFunctor U.ι).obj M) ⋙ extensionByZero U ≅
      extensionByZero U ⋙ tensorLeft M := by
  have : IsIso ((restrictFunctor U.ι).ihomComparison M) :=
    (NatTrans.isIso_iff_isIso_app _).mpr fun N ↦ inferInstance
  exact ((ihomRightAdjointEquiv (extensionByZeroAdjunction U) M
    ((restrictFunctor U.ι).obj M)).symm
      (asIso ((restrictFunctor U.ι).ihomComparison M)).symm).symm

/-- The projection isomorphism is the adjoint transpose of restriction's internal-Hom
comparison. -/
private lemma extensionByZeroProjectionIso_hom (M : X.Modules) :
    (extensionByZeroProjectionIso U M).hom =
      (conjugateEquiv ((extensionByZeroAdjunction U).comp (ihom.adjunction M))
        ((ihom.adjunction ((restrictFunctor U.ι).obj M)).comp
          (extensionByZeroAdjunction U))).symm
            ((restrictFunctor U.ι).ihomComparison M) := by
  simp only [extensionByZeroProjectionIso, Iso.symm_hom,
    ihomRightAdjointEquiv_symm_apply_inv, Iso.symm_inv, asIso_hom]

/-- Transposing the projection formula across extension--restriction gives the unit on
`N` followed by restriction's tensor comparison. -/
@[simp]
lemma extensionByZeroProjectionIso_homEquiv (M : X.Modules) (N : U.toScheme.Modules) :
    (extensionByZeroAdjunction U).homEquiv
        ((restrictFunctor U.ι).obj M ⊗ N) (M ⊗ (extensionByZero U).obj N)
        ((extensionByZeroProjectionIso U M).hom.app N) =
      ((restrictFunctor U.ι).obj M ◁ (extensionByZeroAdjunction U).unit.app N) ≫
        Functor.LaxMonoidal.μ (restrictFunctor U.ι) M ((extensionByZero U).obj N) := by
  -- Conjugation compares the composite adjunction units. Currying the desired formula
  -- reduces it to this unit equation and the coevaluation rule for internal-Hom comparison.
  have h := unit_conjugateEquiv_symm
    ((extensionByZeroAdjunction U).comp (ihom.adjunction M))
    ((ihom.adjunction ((restrictFunctor U.ι).obj M)).comp
      (extensionByZeroAdjunction U))
    ((restrictFunctor U.ι).ihomComparison M) N
  rw [← extensionByZeroProjectionIso_hom] at h
  apply curry_injective
  rw [curry_eq, Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  dsimp only [curriedTensor_obj_obj]
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app] at h
  dsimp only [Functor.comp_obj, Functor.comp_map, curriedTensor_obj_obj,
    ihom.ihom_adjunction_unit] at h
  rw [← h]
  rw [Category.assoc, Functor.coev_ihomComparison, curry_natural_left, curry_eq]
  dsimp only [Functor.comp_obj]

/-- The canonical adjunction formula for the projection isomorphism. -/
lemma extensionByZeroProjectionIso_hom_app (M : X.Modules) (N : U.toScheme.Modules) :
    (extensionByZeroProjectionIso U M).hom.app N =
      ((extensionByZeroAdjunction U).homEquiv _ _).symm
        (((restrictFunctor U.ι).obj M ◁ (extensionByZeroAdjunction U).unit.app N) ≫
          Functor.LaxMonoidal.μ (restrictFunctor U.ι) M ((extensionByZero U).obj N)) := by
  apply (Equiv.eq_symm_apply _).mpr
  exact extensionByZeroProjectionIso_homEquiv U M N

/-- The projection formula is natural in the module sheaf on the ambient scheme. -/
@[reassoc]
lemma extensionByZeroProjectionIso_hom_naturality_left {M M' : X.Modules} (f : M ⟶ M')
    (N : U.toScheme.Modules) :
    (extensionByZero U).map ((restrictFunctor U.ι).map f ▷ N) ≫
        (extensionByZeroProjectionIso U M').hom.app N =
      (extensionByZeroProjectionIso U M).hom.app N ≫ f ▷ (extensionByZero U).obj N := by
  apply ((extensionByZeroAdjunction U).homEquiv _ _).injective
  rw [Adjunction.homEquiv_naturality_left, Adjunction.homEquiv_naturality_right]
  dsimp only [Functor.comp_obj, curriedTensor_obj_obj]
  rw [extensionByZeroProjectionIso_homEquiv, extensionByZeroProjectionIso_homEquiv]
  rw [← whisker_exchange_assoc]
  dsimp only [Functor.comp_obj]
  rw [Functor.LaxMonoidal.μ_natural_left, Category.assoc]

end AlgebraicGeometry.Scheme.Modules

end
