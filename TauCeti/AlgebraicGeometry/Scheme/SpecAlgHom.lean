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

* `AlgHom.Spec_map_comp_Spec_map_algebraMap`: `Spec f` followed by the structure morphism
  `Spec A ⟶ Spec R` is the structure morphism `Spec B ⟶ Spec R`.
-/

public section

open CategoryTheory AlgebraicGeometry

namespace AlgHom

universe u

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]

/-- The spectrum of an `R`-algebra homomorphism `f : A →ₐ[R] B` commutes with the structure
morphisms: `Spec f` followed by `Spec A ⟶ Spec R` is `Spec B ⟶ Spec R`. -/
@[reassoc (attr := simp)]
theorem Spec_map_comp_Spec_map_algebraMap (f : A →ₐ[R] B) :
    Spec.map (CommRingCat.ofHom (f : A →+* B)) ≫ Spec.map (CommRingCat.ofHom (algebraMap R A)) =
      Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, f.comp_algebraMap]

end AlgHom
