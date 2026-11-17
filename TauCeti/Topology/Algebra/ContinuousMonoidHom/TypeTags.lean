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
`MonoidHom` to `ContinuousAddMonoidHom.toMultiplicative` and `ContinuousMonoidHom.toAdditive`.
-/

public section

section Hom

variable {A B M N : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [TopologicalSpace M] [TopologicalSpace N]

/-- Reinterpret a continuous additive homomorphism `A →ₜ+ B` as a continuous multiplicative
homomorphism `Multiplicative A →ₜ* Multiplicative B`. -/
@[expose] def ContinuousAddMonoidHom.toMultiplicative [AddMonoid A] [AddMonoid B] (φ : A →ₜ+ B) :
    Multiplicative A →ₜ* Multiplicative B where
  toMonoidHom := φ.toAddMonoidHom.toMultiplicative
  continuous_toFun := continuous_ofAdd.comp (φ.continuous.comp continuous_toAdd)

@[simp] theorem ContinuousAddMonoidHom.toMultiplicative_apply [AddMonoid A] [AddMonoid B]
    (φ : A →ₜ+ B) (x : Multiplicative A) :
    φ.toMultiplicative x = Multiplicative.ofAdd (φ x.toAdd) := (rfl)

/-- Reinterpret a continuous multiplicative homomorphism `M →ₜ* N` as a continuous additive
homomorphism `Additive M →ₜ+ Additive N`. -/
@[expose] def ContinuousMonoidHom.toAdditive [Monoid M] [Monoid N] (φ : M →ₜ* N) :
    Additive M →ₜ+ Additive N where
  toAddMonoidHom := φ.toMonoidHom.toAdditive
  continuous_toFun := continuous_ofMul.comp (φ.continuous.comp continuous_toMul)

@[simp] theorem ContinuousMonoidHom.toAdditive_apply [Monoid M] [Monoid N]
    (φ : M →ₜ* N) (x : Additive M) :
    φ.toAdditive x = Additive.ofMul (φ x.toMul) := (rfl)

end Hom
