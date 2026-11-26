/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Projections of a product of topological monoids

Mathlib defines `ContinuousMonoidHom.fst`, `ContinuousMonoidHom.snd`, and
`ContinuousMonoidHom.prod`, built from `MonoidHom.fst` and `MonoidHom.snd`. This file records
that their underlying homomorphisms are those projections (`ContinuousMonoidHom.coe_fst` and
`ContinuousMonoidHom.coe_snd`) and provides the composition identities recovering the factors from
`f.prod g` (`ContinuousMonoidHom.fst_comp_prod` and `ContinuousMonoidHom.snd_comp_prod`), together
with their additive counterparts.
-/

public section

namespace ContinuousMonoidHom

section Coe

variable (A B : Type*) [Monoid A] [Monoid B] [TopologicalSpace A] [TopologicalSpace B]

/-- The underlying homomorphism of the continuous first projection is `MonoidHom.fst`. -/
@[to_additive (attr := simp) /-- The underlying additive homomorphism of the continuous first
projection is `AddMonoidHom.fst`. -/]
theorem coe_fst : (fst A B : A × B →* A) = MonoidHom.fst A B :=
  rfl

/-- The underlying homomorphism of the continuous second projection is `MonoidHom.snd`. -/
@[to_additive (attr := simp) /-- The underlying additive homomorphism of the continuous second
projection is `AddMonoidHom.snd`. -/]
theorem coe_snd : (snd A B : A × B →* B) = MonoidHom.snd A B :=
  rfl

end Coe

section CompProd

variable {A B C : Type*} [Monoid A] [Monoid B] [Monoid C]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace C]

/-- Composing the first projection with a product of continuous homomorphisms recovers the first
factor. -/
@[to_additive (attr := simp)
  /-- Composing the first projection with a product of continuous additive homomorphisms recovers
  the first factor. -/]
theorem fst_comp_prod (f : A →ₜ* B) (g : A →ₜ* C) :
    (ContinuousMonoidHom.fst B C).comp (f.prod g) = f := by
  ext x
  simp

/-- Composing the second projection with a product of continuous homomorphisms recovers the second
factor. -/
@[to_additive (attr := simp)
  /-- Composing the second projection with a product of continuous additive homomorphisms recovers
  the second factor. -/]
theorem snd_comp_prod (f : A →ₜ* B) (g : A →ₜ* C) :
    (ContinuousMonoidHom.snd B C).comp (f.prod g) = g := by
  ext x
  simp

end CompProd

end ContinuousMonoidHom
