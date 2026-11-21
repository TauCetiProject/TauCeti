/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Exact.Basic

/-!
# Elementary invariance properties of exact pairs

Precomposing the first map of a multiplicative (or additive) exact pair `f : M → N`, `g : N → P`
with a surjective map `p : M' → M` does not change the range of `f` and therefore preserves and
reflects exactness (`Function.MulExact.comp_iff_of_surjective`). No commutativity or homomorphism
structure is needed.
-/

public section

namespace Function.MulExact

/-- Precomposing the first map of an exact pair with a surjection preserves and reflects
exactness. -/
@[to_additive
  /-- Precomposing the first map of an additive exact pair with a surjection preserves and reflects
  exactness. -/]
theorem comp_iff_of_surjective {M' M N P : Type*} [One P]
    {p : M' → M} (hp : Function.Surjective p) {f : M → N} {g : N → P} :
    Function.MulExact (f ∘ p) g ↔ Function.MulExact f g := by
  simp only [Function.MulExact, hp.range_comp]

end Function.MulExact
