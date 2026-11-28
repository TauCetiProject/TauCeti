/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Elementary properties of exact pairs

* `Function.Surjective.mulExact_comp_iff`: precomposing the first map of a
  multiplicative (or additive) exact pair `f : M → N`, `g : N → P` with a surjective map
  `p : M' → M` preserves and reflects exactness.
* `MonoidHom.mulExact_subtype_ker_map`: for a monoid homomorphism `f : G →* M` out of a group `G`,
  the kernel inclusion `f.ker.subtype` and `f` form an exact pair, with additive counterpart
  `AddMonoidHom.exact_subtype_ker_map`.
-/

public section

namespace Function.Surjective

/-- Precomposing the first map of an exact pair with a surjection preserves and reflects
exactness. -/
@[to_additive
  /-- Precomposing the first map of an additive exact pair with a surjection preserves and reflects
  exactness. -/]
theorem mulExact_comp_iff {M' M N P : Type*} [One P]
    {p : M' → M} (hp : Function.Surjective p) {f : M → N} {g : N → P} :
    Function.MulExact (f ∘ p) g ↔ Function.MulExact f g := by
  simp only [Function.MulExact, hp.range_comp]

end Function.Surjective

namespace MonoidHom

/-- The kernel inclusion `f.ker.subtype` and `f` form an exact pair. -/
@[to_additive
  /-- The kernel inclusion `f.ker.subtype` and `f` form an exact pair. -/]
theorem mulExact_subtype_ker_map {G M : Type*} [Group G] [MulOneClass M] (f : G →* M) :
    Function.MulExact f.ker.subtype f :=
  fun y ↦ ⟨fun hy ↦ ⟨⟨y, hy⟩, rfl⟩, fun ⟨x, hx⟩ ↦ hx ▸ x.property⟩

end MonoidHom
