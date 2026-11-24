/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Projections of a product continuous homomorphism

Mathlib defines `ContinuousMonoidHom.fst`, `ContinuousMonoidHom.snd`, and
`ContinuousMonoidHom.prod`, but omits the composition identities recovering the factors from
`f.prod g`. This file provides `ContinuousMonoidHom.fst_comp_prod` and
`ContinuousMonoidHom.snd_comp_prod` together with their additive counterparts.
-/

public section

namespace ContinuousMonoidHom

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

end ContinuousMonoidHom
