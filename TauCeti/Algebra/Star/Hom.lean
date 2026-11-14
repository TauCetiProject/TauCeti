/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Promoting unit-preserving non-unital star algebra homomorphisms

A non-unital `⋆`-algebra homomorphism `f : A →⋆ₙₐ[R] B` between unital `R`-algebras that sends
`1` to `1` automatically commutes with `algebraMap R` via `algebraMap R A r = r • 1`, and
therefore bundles as a unital `⋆`-algebra homomorphism `f.toStarAlgHom h₁ : A →⋆ₐ[R] B`.

## Main definitions

* `NonUnitalStarAlgHom.toStarAlgHom`: upgrades `f : A →⋆ₙₐ[R] B` with `h₁ : f 1 = 1` to
  `A →⋆ₐ[R] B`, inverse to `StarAlgHom.toNonUnitalStarAlgHom`.
-/

public section

namespace NonUnitalStarAlgHom

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]

/-- Promote a non-unital `⋆`-algebra homomorphism `f : A →⋆ₙₐ[R] B` satisfying `f 1 = 1` to a
unital `⋆`-algebra homomorphism `A →⋆ₐ[R] B`. -/
def toStarAlgHom (f : A →⋆ₙₐ[R] B) (h₁ : f 1 = 1) : A →⋆ₐ[R] B where
  toFun := f
  map_one' := h₁
  map_mul' := map_mul f
  map_zero' := map_zero f
  map_add' := map_add f
  commutes' r := by simp [Algebra.algebraMap_eq_smul_one, h₁]
  map_star' := map_star f

/-- Coercion of `f.toStarAlgHom h₁` to a function agrees with `f`. -/
@[simp]
theorem coe_toStarAlgHom (f : A →⋆ₙₐ[R] B) (h₁ : f 1 = 1) :
    ⇑(f.toStarAlgHom h₁) = f :=
  (rfl)

/-- Applying `f.toStarAlgHom h₁` agrees with applying `f`. -/
@[simp]
theorem toStarAlgHom_apply (f : A →⋆ₙₐ[R] B) (h₁ : f 1 = 1) (a : A) :
    f.toStarAlgHom h₁ a = f a :=
  (rfl)

/-- Forgetting unitality of `f.toStarAlgHom h₁` recovers `f`. -/
@[simp]
theorem toNonUnitalStarAlgHom_toStarAlgHom (f : A →⋆ₙₐ[R] B) (h₁ : f 1 = 1) :
    (f.toStarAlgHom h₁).toNonUnitalStarAlgHom = f :=
  (rfl)

end NonUnitalStarAlgHom

namespace StarAlgHom

variable {R A B : Type*} [CommSemiring R]
  [Semiring A] [Algebra R A] [Star A]
  [Semiring B] [Algebra R B] [Star B]

/-- Promoting `f.toNonUnitalStarAlgHom` back to a unital `⋆`-algebra homomorphism recovers `f`. -/
@[simp]
theorem toStarAlgHom_toNonUnitalStarAlgHom (f : A →⋆ₐ[R] B)
    (h₁ : f.toNonUnitalStarAlgHom 1 = 1) :
    f.toNonUnitalStarAlgHom.toStarAlgHom h₁ = f :=
  (rfl)

end StarAlgHom
