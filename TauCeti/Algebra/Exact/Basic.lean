/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Exact pairs for group homomorphisms

For a monoid homomorphism `f : G →* M` out of a group `G`, the kernel inclusion `f.ker.subtype`
and `f` form an exact pair (`MonoidHom.mulExact_subtype_ker_map`), with additive counterpart
`AddMonoidHom.exact_subtype_ker_map`.
-/

public section

namespace MonoidHom

/-- The kernel inclusion `f.ker.subtype` and `f` form an exact pair. -/
@[to_additive
  /-- The kernel inclusion `f.ker.subtype` and `f` form an exact pair. -/]
theorem mulExact_subtype_ker_map {G M : Type*} [Group G] [MulOneClass M] (f : G →* M) :
    Function.MulExact f.ker.subtype f :=
  fun y ↦ ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.property⟩

end MonoidHom
