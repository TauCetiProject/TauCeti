/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.Rigid.OfClosed
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono

/-!
# The dual-tensor comparison for modules

The categorical map from the tensor product of the internal dual of `M` with `N` to the
internal Hom from `M` to `N` is Mathlib's contraction `dualTensorHom`. Its action on a pure
tensor is the familiar formula `f ⊗ n ↦ (m ↦ f m • n)`. This identification connects
categorical dualizability with the algebraic dual-basis criterion.

The contraction and dual-basis results are from Mathlib's `LinearAlgebra.Contraction`.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

variable {R : Type u} [CommRing R] (M N : ModuleCat.{u} R)

private def dualIso : (M ⟶[ModuleCat.{u} R] (𝟙_ (ModuleCat.{u} R))) ≅
    ModuleCat.of R (Module.Dual R M) := ModuleCat.homLinearEquiv.toModuleIso

private def contraction : ModuleCat.of R (Module.Dual R M) ⊗ N ⟶ (ihom M).obj N :=
  ModuleCat.ofHom (dualTensorHom R M N) ≫ ModuleCat.homLinearEquiv.toModuleIso.inv

private theorem dualTensorIhom_app_eq_aux :
    (dualIso M).hom ▷ N ≫ contraction M N = (dualTensorIhom M).app N := by
  ext t
  induction t using TensorProduct.inductionOn with
  | tmul f n =>
    apply ModuleCat.Hom.ext
    ext m
    rw [dualTensorIhom_app]
    dsimp [dualIso, contraction]
    -- The categorical wrappers conceal the underlying linear maps; expose their action on
    -- a pure tensor so the contraction and curry formulas have the same domain.
    change (dualTensorHom R M N ((ModuleCat.homLinearEquiv (S := R) f) ⊗ₜ[R] n)) m =
      ((curry ((α_ M ((ihom M).obj (𝟙_ (ModuleCat.{u} R))) N).inv ≫
        (ihom.ev M).app (𝟙_ (ModuleCat.{u} R)) ▷ N ≫ (λ_ N).hom)).hom
          (f ⊗ₜ[R] n)).hom m
    rw [ModuleCat.monoidalClosed_curry, dualTensorHom_apply]
    change (ModuleCat.homLinearEquiv (S := R) f) m • n =
      (λ_ N).hom (((ihom.ev M).app (𝟙_ (ModuleCat.{u} R)) ▷ N)
        ((α_ M ((ihom M).obj (𝟙_ (ModuleCat.{u} R))) N).inv
          (m ⊗ₜ[R] (f ⊗ₜ[R] n))))
    rw [ModuleCat.MonoidalCategory.associator_inv_apply,
      ModuleCat.MonoidalCategory.whiskerRight_apply,
      ModuleCat.MonoidalCategory.leftUnitor_hom_apply,
      ModuleCat.ihom_ev_app]
    rfl
  | add x y hx hy => simpa only [map_add] using congrArg₂ (· + ·) hx hy

/-- The categorical dual-tensor comparison is linear contraction, after identifying internal
Homs with linear maps. -/
theorem _root_.ModuleCat.dualTensorIhom_app_eq :
    (dualTensorIhom M).app N =
      ((ModuleCat.homLinearEquiv.toModuleIso :
        (ihom M).obj (𝟙_ (ModuleCat.{u} R)) ≅ ModuleCat.of R (Module.Dual R M)).hom ▷ N) ≫
      ModuleCat.ofHom (dualTensorHom R M N) ≫
      (ModuleCat.homLinearEquiv.toModuleIso :
        (ihom M).obj N ≅ ModuleCat.of R (M →ₗ[R] N)).inv := by
  exact (dualTensorIhom_app_eq_aux M N).symm

/-- At a target module `N`, the categorical dual-tensor comparison is invertible exactly when
linear contraction `Mᵛ ⊗ N → Hom(M,N)` is bijective. -/
theorem _root_.ModuleCat.isIso_dualTensorIhom_app_iff (N : ModuleCat.{u} R) :
    IsIso ((dualTensorIhom M).app N) ↔ Function.Bijective (dualTensorHom R M N) := by
  let d : (ihom M).obj (𝟙_ (ModuleCat.{u} R)) ≅ ModuleCat.of R (Module.Dual R M) :=
    ModuleCat.homLinearEquiv.toModuleIso
  let e : (ihom M).obj N ≅ ModuleCat.of R (M →ₗ[R] N) :=
    ModuleCat.homLinearEquiv.toModuleIso
  let φ : ModuleCat.of R (Module.Dual R M) ⊗ N ⟶ ModuleCat.of R (M →ₗ[R] N) :=
    ModuleCat.ofHom (dualTensorHom R M N)
  have hd : IsIso (d.hom ▷ N) := inferInstance
  have he : IsIso e.inv := inferInstance
  have hEq : (dualTensorIhom M).app N = (d.hom ▷ N) ≫ φ ≫ e.inv :=
    ModuleCat.dualTensorIhom_app_eq M N
  rw [hEq]
  rw [isIso_comp_left_iff, isIso_comp_right_iff]
  exact ConcreteCategory.isIso_iff_bijective φ

end TauCeti
