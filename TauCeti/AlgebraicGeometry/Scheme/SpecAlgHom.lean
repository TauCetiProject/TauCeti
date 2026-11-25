/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The spectrum of an algebra homomorphism

For commutative `R`-algebras `A` and `B`, an `R`-algebra homomorphism `f : A →ₐ[R] B` commutes with
the structure maps, `f ∘ algebraMap R A = algebraMap R B`. Hence `Spec f : Spec B ⟶ Spec A`
commutes with the structure morphisms to `Spec R`.

## Main declarations

* `AlgebraicGeometry.Spec.map_algHom_comp_map_algebraMap`: `Spec f` followed by the structure
  morphism `Spec A ⟶ Spec R` is the structure morphism `Spec B ⟶ Spec R`, for any `f` in a type of
  `R`-algebra homomorphisms (such as `A →ₐ[R] B` or `A ≃ₐ[R] B`).
-/

public section

open CategoryTheory

namespace AlgebraicGeometry.Spec

universe u

/-- An `R`-algebra map `f : A → B` gives a morphism `Spec f : Spec B ⟶ Spec A` over `Spec R`. In
particular, every `σ ∈ Gal(Ω/K)` gives an automorphism `Spec σ` of the geometric point
`Spec Ω ⟶ Spec K` over `Spec K`. -/
@[reassoc (attr := simp)]
theorem map_algHom_comp_map_algebraMap {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] {F : Type*} [FunLike F A B] [AlgHomClass F R A B] (f : F) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg _ (congrArg _ (RingHom.ext (AlgHomClass.commutes f)))

end AlgebraicGeometry.Spec
