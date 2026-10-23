/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit

/-!
# Directed colimits of algebras

Basic API for Mathlib's generic `DirectLimit B f` of a directed system of `A`-algebras `B i`
with `A`-algebra transition maps `f i j`.

## Main declarations

* `TauCeti.DirectLimit.Algebra.of_comp_f`: the canonical maps into a direct limit of algebras are
  compatible with the transition maps. This is the algebra version of
  `Ring.DirectLimit.of_comp_f` in `TauCeti/Algebra/Colimit/Ring.lean`.
-/

public section

namespace TauCeti

namespace DirectLimit.Algebra

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, Semiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι]

open _root_.DirectLimit.Algebra

/-- The canonical maps into a direct limit of algebras are compatible with the transition
maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) : (of B f j).comp (f i j hij) = of B f i :=
  AlgHom.ext fun _ ↦ of_f _ _

end DirectLimit.Algebra

end TauCeti
