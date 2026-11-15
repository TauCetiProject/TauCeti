/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Equiv
public import Mathlib.CategoryTheory.Linear.Basic
public import Mathlib.CategoryTheory.Preadditive.SingleObj

/-!
# Linear structure on single-object categories

When `A` is a ring equipped with a central `R`-module structure, the single-object category
`CategoryTheory.SingleObj A` is an `R`-linear category, extending its preadditive structure from
`Mathlib.CategoryTheory.Preadditive.SingleObj`. For a commutative base semiring `R`, the canonical
multiplicative equivalence `SingleObj.toEnd` upgrades to an `R`-algebra equivalence
`SingleObj.toEndAlgEquiv`.
-/

public section

universe w u

namespace CategoryTheory

namespace SingleObj

instance instLinear {R : Type w} {A : Type u} [Semiring R] [Ring A] [Module R A]
    [SMulCommClass R A A] [IsScalarTower R A A] : Linear R (SingleObj A) where
  homModule _ _ := inferInstanceAs (Module R A)
  smul_comp _ _ _ r f g := mul_smul_comm r g f
  comp_smul _ _ _ f r g := smul_mul_assoc r g f

/-- The endomorphism algebra of the unique object of `SingleObj A` is canonically `R`-algebra
isomorphic to `A`. -/
def toEndAlgEquiv (R : Type w) (A : Type u) [CommSemiring R] [Ring A] [Algebra R A] :
    A ≃ₐ[R] End (SingleObj.star A) where
  __ := SingleObj.toEnd A
  map_add' _ _ := rfl
  commutes' r := by
    ext
    exact Algebra.algebraMap_eq_smul_one r

/-- Applying `SingleObj.toEndAlgEquiv` wraps an element of `A` as an endomorphism. -/
@[simp] theorem toEndAlgEquiv_apply {R : Type w} {A : Type u} [CommSemiring R] [Ring A]
    [Algebra R A] (a : A) : toEndAlgEquiv R A a = .of a := (rfl)

/-- The inverse of `SingleObj.toEndAlgEquiv` extracts the underlying morphism. -/
@[simp] theorem toEndAlgEquiv_symm_apply {R : Type w} {A : Type u} [CommSemiring R] [Ring A]
    [Algebra R A] (f : End (SingleObj.star A)) : (toEndAlgEquiv R A).symm f = f.asHom := (rfl)

/-- Forgetting linearity and addition from `SingleObj.toEndAlgEquiv` recovers `SingleObj.toEnd`. -/
@[simp] theorem toEndAlgEquiv_toMulEquiv (R : Type w) (A : Type u) [CommSemiring R] [Ring A]
    [Algebra R A] : (toEndAlgEquiv R A).toMulEquiv = SingleObj.toEnd A := (rfl)

end SingleObj

end CategoryTheory
