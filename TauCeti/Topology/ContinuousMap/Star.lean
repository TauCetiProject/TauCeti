/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Star

/-!
# Nonunital star-algebra homomorphisms on spaces of continuous maps

`Mathlib.Topology.ContinuousMap.Star` equips `C(X, A)` with its pointwise star-ring and
star-module structures and bundles evaluation, precomposition, and postcomposition as unital
`StarAlgHom`s. For possibly nonunital topological star-algebras — such as nonunital C⋆-algebras
and path algebras `C([0, 1], B)` — this file provides the corresponding `NonUnitalStarAlgHom`
bundlings.

## Main definitions

* `ContinuousMap.evalNonUnitalStarAlgHom`: evaluation `C(X, A) →⋆ₙₐ[R] A` at a point `x : X`.
* `ContinuousMap.constNonUnitalStarAlgHom`: constant-map inclusion `A →⋆ₙₐ[R] C(X, A)`.
* `ContinuousMap.compNonUnitalStarAlgHom'`: precomposition `C(Y, A) →⋆ₙₐ[R] C(X, A)` along a
  continuous map `f : C(X, Y)`.
* `ContinuousMap.postcompNonUnitalStarAlgHom`: postcomposition `C(X, A) →⋆ₙₐ[R] C(X, B)` along a
  continuous nonunital star-algebra homomorphism `g : A →⋆ₙₐ[R] B`.
-/

public section

namespace ContinuousMap

section NonUnitalStarAlgHom

variable (R : Type*) {X Y : Type*} (A B : Type*) [Semiring R]
  [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace A] [TopologicalSpace B]
  [NonUnitalNonAssocSemiring A] [IsTopologicalSemiring A] [Star A] [ContinuousStar A]
  [Module R A] [ContinuousConstSMul R A]
  [NonUnitalNonAssocSemiring B] [IsTopologicalSemiring B] [Star B] [ContinuousStar B]
  [Module R B] [ContinuousConstSMul R B]

/-- Pointwise evaluation `C(X, A) →⋆ₙₐ[R] A` at `x : X` as a nonunital `⋆`-algebra homomorphism. -/
def evalNonUnitalStarAlgHom (x : X) : C(X, A) →⋆ₙₐ[R] A :=
  { toFun := fun f ↦ f x, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem evalNonUnitalStarAlgHom_apply (x : X) (f : C(X, A)) :
    evalNonUnitalStarAlgHom R A x f = f x := (rfl)

variable (X) in
/-- Constant-map inclusion `A →⋆ₙₐ[R] C(X, A)` as a nonunital `⋆`-algebra homomorphism. -/
def constNonUnitalStarAlgHom : A →⋆ₙₐ[R] C(X, A) :=
  { toFun := ContinuousMap.const X, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem constNonUnitalStarAlgHom_apply (a : A) (x : X) :
    constNonUnitalStarAlgHom R X A a x = a := (rfl)

/-- Precomposition `C(Y, A) →⋆ₙₐ[R] C(X, A)` along `f : C(X, Y)` as a nonunital `⋆`-algebra
homomorphism. -/
def compNonUnitalStarAlgHom' (f : C(X, Y)) : C(Y, A) →⋆ₙₐ[R] C(X, A) :=
  { toFun := fun g ↦ g.comp f, map_smul' := fun _ _ ↦ rfl, map_zero' := rfl,
    map_add' := fun _ _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_star' := fun _ ↦ rfl }

@[simp]
theorem compNonUnitalStarAlgHom'_apply (f : C(X, Y)) (g : C(Y, A)) (x : X) :
    compNonUnitalStarAlgHom' R A f g x = g (f x) := (rfl)

/-- Postcomposition `C(X, A) →⋆ₙₐ[R] C(X, B)` along a continuous nonunital `⋆`-algebra homomorphism.
-/
def postcompNonUnitalStarAlgHom (g : A →⋆ₙₐ[R] B) (hg : Continuous g) :
    C(X, A) →⋆ₙₐ[R] C(X, B) where
  toFun f := ⟨g ∘ f, hg.comp f.continuous⟩
  map_smul' c f := by ext x; exact map_smul g c (f x)
  map_zero' := by ext _; exact map_zero g
  map_add' f₁ f₂ := by ext x; exact map_add g (f₁ x) (f₂ x)
  map_mul' f₁ f₂ := by ext x; exact map_mul g (f₁ x) (f₂ x)
  map_star' f := by ext x; exact map_star g (f x)

@[simp]
theorem postcompNonUnitalStarAlgHom_apply (g : A →⋆ₙₐ[R] B) (hg : Continuous g)
    (f : C(X, A)) (x : X) : postcompNonUnitalStarAlgHom R A B g hg f x = g (f x) := (rfl)

end NonUnitalStarAlgHom

end ContinuousMap
