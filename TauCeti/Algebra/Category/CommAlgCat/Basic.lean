/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Basic facts about commutative algebras

A morphism `f : R ⟶ S` of commutative `k`-algebras makes `S` an `R`-algebra through
`f.hom.toRingHom.toAlgebra`. This file records the scalar tower `R → S → T` carried by these
algebra structures for morphisms `f : R ⟶ S`, `g : S ⟶ T` and `fg : R ⟶ T` with `f ≫ g = fg`.
The scalar tower `k → R → S` of a single morphism is Mathlib's `IsScalarTower.of_algHom f.hom`.

It also records that the forgetful functor from commutative `k`-algebras in any universe to
commutative rings reflects isomorphisms. Mathlib's `CommAlgCat.reflectsIsomorphisms_forget` covers
only algebras in the universe of `k`.

Finally, it reads the extension of ideals along morphisms of commutative `k`-algebras through the
underlying ring maps: along the image under the forgetful functor to commutative rings, along the
quotient map `R ⟶ R ⧸ J`, and along a composite.

## Main statements

* `CommAlgCat.isScalarTower_toAlgebra_of_comp`: the scalar tower `R → S → T`.
* `CommAlgCat.reflectsIsomorphisms_forget₂CommRingCat`: the forgetful functor to commutative rings
  reflects isomorphisms.
* `CommAlgCat.ideal_map_forget₂_map`, `CommAlgCat.ideal_map_ofHom_mkₐ`, `CommAlgCat.ideal_map_comp`:
  extension of ideals along morphisms of commutative `k`-algebras.
-/

public section

open CategoryTheory

universe v u

namespace CommAlgCat

variable {k : Type u} [CommRing k] {R S T : CommAlgCat.{v} k}

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

/-- The forgetful functor from commutative algebras to commutative rings reflects isomorphisms:
a morphism of algebras whose underlying ring map is an isomorphism is an isomorphism. -/
instance reflectsIsomorphisms_forget₂CommRingCat :
    (forget₂ (CommAlgCat.{v} k) CommRingCat.{v}).ReflectsIsomorphisms where
  reflects f _ :=
    let i := asIso ((forget CommRingCat.{v}).map ((forget₂ (CommAlgCat.{v} k) _).map f))
    (isoMk { f.hom, i.toEquiv with }).isIso_hom

/-! ### Extension of ideals -/

/-- The ring map that the forgetful functor to commutative rings makes of a morphism `f` of
commutative `k`-algebras extends ideals as `f` does. -/
lemma ideal_map_forget₂_map (f : R ⟶ S) (I : Ideal R) :
    I.map ((forget₂ (CommAlgCat.{v} k) CommRingCat.{v}).map f).hom = I.map f.hom :=
  (rfl)

/-- The quotient map `R ⟶ R ⧸ J` of commutative `k`-algebras extends ideals as
`Ideal.Quotient.mk J` does. -/
lemma ideal_map_ofHom_mkₐ (I J : Ideal R) :
    I.map (ofHom (Ideal.Quotient.mkₐ k J)).hom = I.map (Ideal.Quotient.mk J) := by
  rw [hom_ofHom, ← Ideal.map_coe, ← AlgHom.toRingHom_eq_coe, Ideal.Quotient.mkₐ_toRingHom]

/-- Extending an ideal along a composite of morphisms of commutative `k`-algebras extends it in
two steps. -/
lemma ideal_map_comp (f : R ⟶ S) (g : S ⟶ T) (I : Ideal R) :
    I.map (f ≫ g).hom = (I.map f.hom).map g.hom := by
  rw [hom_comp, ← Ideal.map_coe (g.hom.comp f.hom), AlgHom.comp_toRingHom, ← Ideal.map_map,
    Ideal.map_coe, Ideal.map_coe]

end CommAlgCat
