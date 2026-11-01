/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Coalgebra.Comodule.BaseChange
public import TauCeti.Algebra.Coalgebra.Comodule.Cat

import Mathlib.CategoryTheory.EqToHom

/-!
# Scalar extension of comodules

Let `C` be a coalgebra over a commutative semiring `R`, and let `A` be an
`R`-algebra. This file constructs scalar extension of the underlying-module functor on all
comodules:

```text
ComoduleCat R C ⥤ SemimoduleCat A,      M ↦ A ⊗[R] M.
```

When `A` is commutative, scalar extension also extends the coefficient coalgebra and retains
the coaction, giving a functor to `ComoduleCat A (A ⊗[R] C)`. It uses the unbundled
construction from `TauCeti.Algebra.Coalgebra.Comodule.BaseChange`.

No finiteness or bialgebra structure is needed for either construction.

## Main declarations

* `TauCeti.ComoduleCat.scalarExtensionFunctor`: scalar extension of underlying semimodules.
* `TauCeti.ComoduleCat.baseChange`: scalar extension of comodules and their coefficient coalgebra.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (C : Type v) [AddCommMonoid C] [Module R C] [Coalgebra R C]

namespace ComoduleCat

section Semiring

variable (A : Type x) [Semiring A] [Algebra R A]

/-- Scalar extension of the underlying-module functor on comodules. -/
noncomputable def scalarExtensionFunctor :
    ComoduleCat.{u, v, w} R C ⥤ SemimoduleCat.{max x w} A where
  obj M := SemimoduleCat.of A (A ⊗[R] M)
  map f := SemimoduleCat.ofHom (f.toLinearMap.baseChange A)
  map_id M := by
    apply SemimoduleCat.hom_ext
    -- `SemimoduleCat.hom_ext` leaves the bundled map of an identity comodule morphism;
    -- reducing that wrapper exposes precisely the linear-map base-change identity.
    change (LinearMap.id : M →ₗ[R] M).baseChange A = LinearMap.id
    exact LinearMap.baseChange_id
  map_comp f g := by
    apply SemimoduleCat.hom_ext
    -- As above, reduction turns composition of bundled comodule morphisms into composition
    -- of their underlying linear maps, where the base-change API applies.
    change (g.toLinearMap ∘ₗ f.toLinearMap).baseChange A =
      g.toLinearMap.baseChange A ∘ₗ f.toLinearMap.baseChange A
    exact LinearMap.baseChange_comp f.toLinearMap g.toLinearMap

/-- Scalar extension sends `M` to the semimodule `A ⊗[R] M`. -/
@[simp]
theorem scalarExtensionFunctor_obj (M : ComoduleCat.{u, v, w} R C) :
    (scalarExtensionFunctor R C A).obj M = SemimoduleCat.of A (A ⊗[R] M) :=
  (rfl)

/-- Scalar extension maps a comodule morphism to base change of its underlying linear map. -/
@[simp]
theorem scalarExtensionFunctor_map {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    (scalarExtensionFunctor R C A).map f =
      eqToHom (scalarExtensionFunctor_obj R C A M) ≫
        SemimoduleCat.ofHom (f.toLinearMap.baseChange A) ≫
          eqToHom (scalarExtensionFunctor_obj R C A N).symm :=
  (rfl)

end Semiring

section CommSemiring

variable (A : Type x) [CommSemiring A] [Algebra R A]

/-- Extend both the underlying module and the coefficient coalgebra of a bundled comodule. -/
-- Let typeclass synthesis compute the object carrier and its tensor-product module structure.
@[expose, implicit_reducible]
noncomputable def baseChange :
    ComoduleCat.{u, v, w} R C ⥤ ComoduleCat.{x, max x v, max x w} A (A ⊗[R] C) where
  obj M :=
    letI := Comodule.baseChange (R := R) (H := C) (M := M) A
    of A (A ⊗[R] C) (A ⊗[R] M)
  map f := Comodule.Hom.baseChange A f
  map_id M := Comodule.Hom.baseChange_id (R := R) (H := C) (M := M) A
  map_comp f g := Comodule.Hom.baseChange_comp A g f

/-- Base change equips the scalar-extended module with the base-changed coaction. -/
@[simp]
theorem baseChange_obj (M : ComoduleCat.{u, v, w} R C) :
    (baseChange R C A).obj M =
      (letI := Comodule.baseChange (R := R) (H := C) (M := M) A
       of A (A ⊗[R] C) (A ⊗[R] M)) :=
  (rfl)

/-- The coaction on a base-changed object is the base change of the original coaction. -/
@[simp]
theorem baseChange_obj_coact (M : ComoduleCat.{u, v, w} R C) :
    Comodule.coact (R := A) (C := A ⊗[R] C) (M := (baseChange R C A).obj M) =
      Comodule.baseChangeCoact (R := R) (H := C) (M := M) A :=
  Comodule.baseChange_coact (R := R) (H := C) (M := M) A

/-- The underlying linear map of a base-changed morphism is scalar extension of its
underlying linear map. -/
@[simp]
theorem baseChange_map_toLinearMap {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) :
    ((baseChange R C A).map f).toLinearMap = f.toLinearMap.baseChange A :=
  Comodule.Hom.baseChange_toLinearMap A f

/-- On pure tensors, base change applies the original morphism to the module factor. -/
@[simp]
theorem baseChange_map_tmul {M N : ComoduleCat.{u, v, w} R C} (f : M ⟶ N) (a : A) (m : M) :
    hom A (A ⊗[R] C) ((baseChange R C A).map f) (a ⊗ₜ[R] m) =
      a ⊗ₜ[R] hom R C f m :=
  Comodule.Hom.baseChange_tmul A f a m

/-- Forgetting the base-changed coaction recovers scalar extension of underlying semimodules. -/
@[simp]
theorem baseChange_comp_forget₂ :
    baseChange R C A ⋙
        forget₂ (ComoduleCat.{x, max x v, max x w} A (A ⊗[R] C))
          (SemimoduleCat.{max x w} A) = scalarExtensionFunctor R C A := by
  apply CategoryTheory.Functor.hext
  case h_obj =>
    intro M
    rfl
  case h_map =>
    intro M N f
    apply heq_of_eq
    apply SemimoduleCat.hom_ext
    exact baseChange_map_toLinearMap R C A f

end CommSemiring

end ComoduleCat

end TauCeti
