/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic

/-!
# Scalar towers from morphisms of commutative algebras

A morphism `f : R ⟶ S` of commutative `k`-algebras makes `S` an `R`-algebra through
`f.hom.toRingHom.toAlgebra`. This file records the scalar towers carried by these algebra
structures: `k → R → S` for a single morphism, and `R → S → T` for morphisms `f : R ⟶ S`,
`g : S ⟶ T` and `fg : R ⟶ T` with `f ≫ g = fg`.

## Main statements

* `CommAlgCat.isScalarTower_toAlgebra`: the scalar tower `k → R → S`.
* `CommAlgCat.isScalarTower_toAlgebra_of_comp`: the scalar tower `R → S → T`.
-/

public section

open CategoryTheory

universe v u

namespace CommAlgCat

variable {k : Type u} [CommRing k] {R S T : CommAlgCat.{v} k}

/-- The scalar tower `k → R → S` of the `R`-algebra structure on `S` given by a morphism
`f : R ⟶ S` of commutative `k`-algebras. -/
lemma isScalarTower_toAlgebra (f : R ⟶ S) :
    letI := f.hom.toRingHom.toAlgebra
    IsScalarTower k R S :=
  letI := f.hom.toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq' f.hom.comp_algebraMap.symm

/-- The scalar tower `R → S → T` of the algebra structures given by morphisms `f : R ⟶ S`,
`g : S ⟶ T` and `fg : R ⟶ T` with `f ≫ g = fg`. -/
lemma isScalarTower_toAlgebra_of_comp (f : R ⟶ S) (g : S ⟶ T) (fg : R ⟶ T) (h : f ≫ g = fg) :
    letI := f.hom.toRingHom.toAlgebra
    letI := g.hom.toRingHom.toAlgebra
    letI := fg.hom.toRingHom.toAlgebra
    IsScalarTower R S T :=
  letI := f.hom.toRingHom.toAlgebra
  letI := g.hom.toRingHom.toAlgebra
  letI := fg.hom.toRingHom.toAlgebra
  IsScalarTower.of_algebraMap_eq fun r ↦ by
    subst h
    simp only [RingHom.algebraMap_toAlgebra, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
      CommAlgCat.hom_comp, AlgHom.comp_apply]

end CommAlgCat
