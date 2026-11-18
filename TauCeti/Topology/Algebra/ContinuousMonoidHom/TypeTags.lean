/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Constructions

/-!
# Type-tag transport for continuous monoid homomorphisms

`Multiplicative` and `Additive` carry the topology of their underlying type via
`Mathlib.Topology.Constructions`, with `continuous_ofAdd`, `continuous_toAdd`, `continuous_ofMul`,
and `continuous_toMul`. This file upgrades Mathlib's algebraic type-tag maps on `AddMonoidHom` and
`MonoidHom` to `ContinuousAddMonoidHom.toMultiplicative` and `ContinuousMonoidHom.toAdditive`,
together with their evaluation, algebraic projection, and functoriality lemmas.
-/

public section

section Hom

variable {A B M N : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace M] [TopologicalSpace N]

/-- Reinterpret a continuous additive homomorphism `A →ₜ+ B` as a continuous multiplicative
homomorphism `Multiplicative A →ₜ* Multiplicative B`. -/
def ContinuousAddMonoidHom.toMultiplicative [AddMonoid A] [AddMonoid B] (φ : A →ₜ+ B) :
    Multiplicative A →ₜ* Multiplicative B where
  toMonoidHom := φ.toAddMonoidHom.toMultiplicative
  continuous_toFun := continuous_ofAdd.comp (φ.continuous.comp continuous_toAdd)

/-- Evaluating `φ.toMultiplicative` unwraps `x`, applies `φ`, and rewraps with
`Multiplicative.ofAdd`. -/
@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_apply [AddMonoid A] [AddMonoid B]
    (φ : A →ₜ+ B) (x : Multiplicative A) :
    φ.toMultiplicative x = Multiplicative.ofAdd (φ x.toAdd) := (rfl)

/-- The underlying `MonoidHom` of `φ.toMultiplicative` is `(φ : A →+ B).toMultiplicative`. -/
@[simp] theorem ContinuousAddMonoidHom.toMonoidHom_toMultiplicative [AddMonoid A] [AddMonoid B]
    (φ : A →ₜ+ B) :
    (φ.toMultiplicative : Multiplicative A →* Multiplicative B) =
      (φ : A →+ B).toMultiplicative := (rfl)

/-- `ContinuousAddMonoidHom.toMultiplicative` sends the identity homomorphism to the identity. -/
@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_id [AddMonoid A] :
    (ContinuousAddMonoidHom.id A).toMultiplicative =
      ContinuousMonoidHom.id (Multiplicative A) := (rfl)

/-- `ContinuousAddMonoidHom.toMultiplicative` preserves composition. -/
@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_comp {C : Type*} [TopologicalSpace C]
    [AddMonoid A] [AddMonoid B] [AddMonoid C] (ψ : B →ₜ+ C) (φ : A →ₜ+ B) :
    (ψ.comp φ).toMultiplicative = ψ.toMultiplicative.comp φ.toMultiplicative := (rfl)

/-- `ContinuousAddMonoidHom.toMultiplicative` sends the zero homomorphism to the trivial
multiplicative homomorphism. -/
@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_zero [AddMonoid A] [AddMonoid B] :
    (0 : A →ₜ+ B).toMultiplicative = 1 := (rfl)

/-- Reinterpret a continuous multiplicative homomorphism `M →ₜ* N` as a continuous additive
homomorphism `Additive M →ₜ+ Additive N`. -/
def ContinuousMonoidHom.toAdditive [Monoid M] [Monoid N] (φ : M →ₜ* N) :
    Additive M →ₜ+ Additive N where
  toAddMonoidHom := φ.toMonoidHom.toAdditive
  continuous_toFun := continuous_ofMul.comp (φ.continuous.comp continuous_toMul)

/-- Evaluating `φ.toAdditive` unwraps `x`, applies `φ`, and rewraps with `Additive.ofMul`. -/
@[simp] theorem ContinuousMonoidHom.toAdditive_apply [Monoid M] [Monoid N]
    (φ : M →ₜ* N) (x : Additive M) :
    φ.toAdditive x = Additive.ofMul (φ x.toMul) := (rfl)

/-- The underlying `AddMonoidHom` of `φ.toAdditive` is `(φ : M →* N).toAdditive`. -/
@[simp] theorem ContinuousMonoidHom.toAddMonoidHom_toAdditive [Monoid M] [Monoid N]
    (φ : M →ₜ* N) :
    (φ.toAdditive : Additive M →+ Additive N) = (φ : M →* N).toAdditive := (rfl)

/-- `ContinuousMonoidHom.toAdditive` sends the identity homomorphism to the identity. -/
@[simp] theorem ContinuousMonoidHom.toAdditive_id [Monoid M] :
    (ContinuousMonoidHom.id M).toAdditive = ContinuousAddMonoidHom.id (Additive M) := (rfl)

/-- `ContinuousMonoidHom.toAdditive` preserves composition. -/
@[simp] theorem ContinuousMonoidHom.toAdditive_comp {P : Type*} [TopologicalSpace P]
    [Monoid M] [Monoid N] [Monoid P] (ψ : N →ₜ* P) (φ : M →ₜ* N) :
    (ψ.comp φ).toAdditive = ψ.toAdditive.comp φ.toAdditive := (rfl)

/-- `ContinuousMonoidHom.toAdditive` sends the trivial multiplicative homomorphism to the zero
homomorphism. -/
@[simp] theorem ContinuousMonoidHom.toAdditive_one [Monoid M] [Monoid N] :
    (1 : M →ₜ* N).toAdditive = 0 := (rfl)

end Hom
