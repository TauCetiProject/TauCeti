/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Equiv.Defs
public import Mathlib.Algebra.Star.Module
public import Mathlib.CategoryTheory.Linear.Basic
public import TauCeti.CategoryTheory.Dagger.Basic

/-!
# Additive and conjugate-linear daggers

On a preadditive category, a dagger structure is *additive* (`TauCeti.DaggerPreadditive`) when
`dagger (f + g) = dagger f + dagger g`; on an `R`-linear category over a star semiring `R` it is
*conjugate-linear* (`TauCeti.DaggerLinear R`) when `dagger (r • f) = star r • dagger f`. Over `ℂ`
these are the dagger axioms of a complex linear dagger category, the carrier of C*-categories.
Both conditions are `Prop`-valued mixins on the native `Preadditive` and `Linear R` structures,
in the same way as Mathlib's `StarAddMonoid` and `StarModule` are mixins on `star`.

Under these mixins the dagger is an additive equivalence `(X ⟶ Y) ≃+ (Y ⟶ X)` and, over a
commutative star semiring, a semilinear equivalence `(X ⟶ Y) ≃ₗ⋆[R] (Y ⟶ X)` with respect to
`starRingEnd R`. Correspondingly, `End X` becomes a star ring and a star `R`-module.

## Main declarations

* `TauCeti.DaggerPreadditive` and `TauCeti.DaggerLinear`: additivity and conjugate-linearity of
  the dagger;
* `TauCeti.DaggerCategory.daggerAddEquiv` and `TauCeti.DaggerCategory.daggerLinearEquiv`: the
  dagger as an additive and as a semilinear equivalence;
* `CategoryTheory.End.instStarRing` and `CategoryTheory.End.instStarModule`: the star ring and
  star module structures on `End X`.
-/

public section

open CategoryTheory

universe w v₁ u₁

namespace TauCeti

open DaggerCategory

/-- A dagger structure on a preadditive category is *additive* if
`dagger (f + g) = dagger f + dagger g`. -/
class DaggerPreadditive (C : Type u₁) [Category.{v₁} C] [Preadditive C] [DaggerCategory C] :
    Prop where
  /-- The dagger is additive. -/
  dagger_add {X Y : C} (f g : X ⟶ Y) : dagger (f + g) = dagger f + dagger g

/-- A dagger structure on an `R`-linear category, for a semiring `R` with a star operation, is
*conjugate-linear* if `dagger (r • f) = star r • dagger f`. -/
class DaggerLinear (R : Type w) [Semiring R] [Star R] (C : Type u₁) [Category.{v₁} C]
    [Preadditive C] [Linear R C] [DaggerCategory C] : Prop where
  /-- The dagger is conjugate-linear. -/
  dagger_smul {X Y : C} (r : R) (f : X ⟶ Y) : dagger (r • f) = star r • dagger f

attribute [simp] DaggerPreadditive.dagger_add DaggerLinear.dagger_smul

namespace DaggerCategory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]
  [DaggerPreadditive C]

variable (C) in
/-- The additive dagger, as an additive equivalence `(X ⟶ Y) ≃+ (Y ⟶ X)`. -/
def daggerAddEquiv (X Y : C) : (X ⟶ Y) ≃+ (Y ⟶ X) where
  toFun := dagger
  invFun := dagger
  left_inv := dagger_dagger
  right_inv := dagger_dagger
  map_add' := DaggerPreadditive.dagger_add

@[simp]
theorem daggerAddEquiv_apply {X Y : C} (f : X ⟶ Y) : daggerAddEquiv C X Y f = dagger f :=
  (rfl)

@[simp]
theorem daggerAddEquiv_symm {X Y : C} : (daggerAddEquiv C X Y).symm = daggerAddEquiv C Y X :=
  (rfl)

@[simp]
theorem dagger_zero (X Y : C) : dagger (0 : X ⟶ Y) = 0 :=
  map_zero (daggerAddEquiv C X Y)

@[simp]
theorem dagger_neg {X Y : C} (f : X ⟶ Y) : dagger (-f) = -dagger f :=
  map_neg (daggerAddEquiv C X Y) f

@[simp]
theorem dagger_sub {X Y : C} (f g : X ⟶ Y) : dagger (f - g) = dagger f - dagger g :=
  map_sub (daggerAddEquiv C X Y) f g

@[simp]
theorem dagger_sum {X Y : C} {ι : Type*} (s : Finset ι) (f : ι → (X ⟶ Y)) :
    dagger (∑ i ∈ s, f i) = ∑ i ∈ s, dagger (f i) :=
  map_sum (daggerAddEquiv C X Y) f s

@[simp]
theorem dagger_eq_zero_iff {X Y : C} {f : X ⟶ Y} : dagger f = 0 ↔ f = 0 :=
  (daggerAddEquiv C X Y).map_eq_zero_iff

variable (R : Type w) [CommSemiring R] [StarRing R] [Linear R C] [DaggerLinear R C]

variable (C) in
/-- The additive and conjugate-linear dagger, as a semilinear equivalence
`(X ⟶ Y) ≃ₗ⋆[R] (Y ⟶ X)` with respect to `starRingEnd R`. -/
def daggerLinearEquiv (X Y : C) : (X ⟶ Y) ≃ₗ⋆[R] (Y ⟶ X) where
  __ := daggerAddEquiv C X Y
  map_smul' := DaggerLinear.dagger_smul

@[simp]
theorem daggerLinearEquiv_apply {X Y : C} (f : X ⟶ Y) :
    daggerLinearEquiv C R X Y f = dagger f :=
  (rfl)

@[simp]
theorem daggerLinearEquiv_symm {X Y : C} :
    (daggerLinearEquiv C R X Y).symm = daggerLinearEquiv C R Y X :=
  (rfl)

@[simp]
theorem toAddEquiv_daggerLinearEquiv {X Y : C} :
    (daggerLinearEquiv C R X Y).toAddEquiv = daggerAddEquiv C X Y :=
  (rfl)

end DaggerCategory

end TauCeti

namespace CategoryTheory.End

open TauCeti TauCeti.DaggerCategory

variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [DaggerCategory C]

/-- For an additive dagger, the star monoid `End X` is a star ring. -/
instance instStarRing [DaggerPreadditive C] (X : C) : StarRing (End X) where
  star_add f g := End.ext (DaggerPreadditive.dagger_add f.asHom g.asHom)

/-- For a conjugate-linear dagger, `End X` is a star `R`-module. -/
instance instStarModule (R : Type w) [Semiring R] [Star R] [Linear R C] [DaggerLinear R C]
    (X : C) : StarModule R (End X) where
  star_smul r f := End.ext (DaggerLinear.dagger_smul r f.asHom)

end CategoryTheory.End
