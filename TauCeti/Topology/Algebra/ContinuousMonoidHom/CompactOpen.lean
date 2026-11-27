/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.CompactOpen

/-!
# Evaluating precomposition and postcomposition of continuous homomorphisms

Mathlib's `ContinuousMonoidHom.compLeft E f` and `ContinuousMonoidHom.compRight A f` bundle
precomposition `g ↦ g.comp f` and postcomposition `g ↦ f.comp g` as continuous homomorphisms
between spaces of continuous homomorphisms, but carry no evaluation lemmas. This file records
them, together with their additive versions.
-/

public section

namespace ContinuousMonoidHom

variable {A B E : Type*} [Monoid A] [Monoid B] [CommGroup E]
  [TopologicalSpace A] [TopologicalSpace B] [TopologicalSpace E] [IsTopologicalGroup E]

/-- `ContinuousMonoidHom.compLeft E f` sends `g` to `g.comp f`. -/
@[to_additive (attr := simp)
/-- `ContinuousAddMonoidHom.compLeft E f` sends `g` to `g.comp f`. -/]
theorem compLeft_apply (f : A →ₜ* B) (g : B →ₜ* E) : compLeft E f g = g.comp f :=
  rfl

/-- `ContinuousMonoidHom.compRight A f` sends `g` to `f.comp g`. -/
@[to_additive (attr := simp)
/-- `ContinuousAddMonoidHom.compRight A f` sends `g` to `f.comp g`. -/]
theorem compRight_apply {C : Type*} [CommGroup C] [TopologicalSpace C] [IsTopologicalGroup C]
    (f : C →ₜ* E) (g : A →ₜ* C) : compRight A f g = f.comp g :=
  rfl

end ContinuousMonoidHom
