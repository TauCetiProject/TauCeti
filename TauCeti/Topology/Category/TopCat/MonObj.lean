/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Monoidal.Mon
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Category.TopCat.Monoidal

/-!
# Topological monoids as monoid objects in `TopCat`

A topological monoid `M` is a monoid object in the cartesian monoidal category `TopCat`: the
multiplication is the continuous map `M × M → M`, `(x, y) ↦ x * y`, and the unit is the point
`1`. This file records the instance `MonObj (TopCat.of M)`, the commutativity
`IsCommMonObj (TopCat.of M)` for a commutative topological monoid, and the fact that a continuous
monoid homomorphism `φ : M →ₜ* N` induces a morphism of monoid objects `TopCat.ofHom φ`.

These instances let constructions on monoid objects of `TopCat`, such as the Pontryagin product
on singular homology, be applied to topological monoids and topological groups.
-/

public section

open CategoryTheory MonoidalCategory MonObj

universe w

namespace TopCat

variable (M : Type w) [Monoid M] [TopologicalSpace M] [ContinuousMul M]

/-- A topological monoid is a monoid object in `TopCat`, with multiplication
`(x, y) ↦ x * y` and unit `1`. -/
instance instMonObjOf : MonObj (TopCat.of M) where
  one := ofHom ⟨fun _ ↦ 1, continuous_const⟩
  mul := ofHom ⟨fun x ↦ x.1 * x.2, continuous_mul⟩
  one_mul := by ext x; exact one_mul x.2
  mul_one := by ext x; exact mul_one x.1
  mul_assoc := by ext x; exact mul_assoc x.1.1 x.1.2 x.2

variable {M}

@[simp]
theorem of_mul_apply (x : ↑(TopCat.of M ⊗ TopCat.of M)) : μ[TopCat.of M] x = x.1 * x.2 :=
  (rfl)

@[simp]
theorem of_one_apply (x : ↑(𝟙_ TopCat.{w})) : η[TopCat.of M] x = 1 :=
  (rfl)

/-- A commutative topological monoid is a commutative monoid object in `TopCat`. -/
instance instIsCommMonObjOf (M : Type w) [CommMonoid M] [TopologicalSpace M] [ContinuousMul M] :
    IsCommMonObj (TopCat.of M) where
  mul_comm := by ext x; exact mul_comm x.2 x.1

/-- A continuous monoid homomorphism is a morphism of monoid objects in `TopCat`. -/
instance instIsMonHomOfHom {N : Type w} [Monoid N] [TopologicalSpace N] [ContinuousMul N]
    (φ : M →ₜ* N) : IsMonHom (ofHom (φ : C(M, N))) where
  one_hom := by ext; exact map_one φ
  mul_hom := by ext x; exact map_mul φ x.1 x.2

end TopCat
