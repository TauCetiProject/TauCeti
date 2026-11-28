/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.ExtensionByZero
import Mathlib.CategoryTheory.Adjunction.Triple

/-!
# Extension by zero from an open subscheme

For an open subscheme `U` of `X`, `Scheme.Modules.extendByZero U` is the exact left
adjoint of restriction. Its adjunction unit is invertible, so extending a module sheaf by
zero and then restricting to `U` recovers that module sheaf.

The construction transports Mathlib's module-sheaf pullback along `Over.forget U` through
`Scheme.Modules.overEquiv U`. Exactness is supplied by
`SheafOfModules.preservesFiniteLimits_pullback_over`; the unit isomorphism follows from the
adjoint triple with restriction and ordinary pushforward.

## References

* The Stacks Project, Modules on Sites, Section 18.19 (extension by zero).
-/

public section

noncomputable section

open CategoryTheory Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- Extension by zero of module sheaves from the open subscheme `U` to `X`. -/
def extendByZero : U.toScheme.Modules ⥤ X.Modules :=
  (overEquiv U).inverse ⋙
    SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U))

/-- Extension by zero is left adjoint to restriction to the open subscheme. -/
def extendByZeroAdjunction : extendByZero U ⊣ restrictFunctor U.ι :=
  ((overEquiv U).symm.toAdjunction.comp
    (SheafOfModules.pullbackPushforwardAdjunction (F := Over.forget U)
      (𝟙 (X.ringCatSheaf.over U)))).ofNatIsoRight (overFunctorEquiv U)

instance : (extendByZero U).IsLeftAdjoint :=
  (extendByZeroAdjunction U).isLeftAdjoint

/-- Extension by zero is left exact; together with its left-adjoint property this gives
exactness on arbitrary module sheaves. -/
instance preservesFiniteLimits_extendByZero : PreservesFiniteLimits (extendByZero U) :=
  inferInstanceAs (PreservesFiniteLimits ((overEquiv U).inverse ⋙
    SheafOfModules.pullback.{u} (F := Over.forget U) (𝟙 (X.ringCatSheaf.over U))))

instance : (extendByZero U).Additive :=
  (extendByZero U).additive_of_preserves_binary_products

/-- A module sheaf on `U` is recovered by restricting its extension by zero. -/
instance isIso_extendByZeroAdjunction_unit : IsIso (extendByZeroAdjunction U).unit :=
  (Adjunction.Triple.isIso_unit_iff_isIso_counit
    (⟨extendByZeroAdjunction U, restrictAdjunction U.ι⟩)).mpr inferInstance

/-- The inverse of the adjunction unit identifies restriction of extension by zero with
the identity functor on module sheaves on `U`. -/
def extendByZeroCompRestrictIso :
    extendByZero U ⋙ restrictFunctor U.ι ≅ 𝟭 U.toScheme.Modules :=
  (asIso (extendByZeroAdjunction U).unit).symm

@[simp]
lemma extendByZeroCompRestrictIso_hom_app (N : U.toScheme.Modules) :
    (extendByZeroCompRestrictIso U).hom.app N =
      inv ((extendByZeroAdjunction U).unit.app N) := by
  simp [extendByZeroCompRestrictIso]

@[simp]
lemma extendByZeroCompRestrictIso_inv_app (N : U.toScheme.Modules) :
    (extendByZeroCompRestrictIso U).inv.app N =
      (extendByZeroAdjunction U).unit.app N :=
  (rfl)

end AlgebraicGeometry.Scheme.Modules

end
