/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Ideal.Pointwise

/-!
# Inertia groups of ideals

This file extends the API for Mathlib's `Ideal.inertia`. Membership in an inertia group may be
tested on any set of algebra generators, provided the group action fixes the base algebra.

## Main results

* `Ideal.mem_inertia_iff_of_adjoin_eq_top`: membership in an inertia group is decided on an
  algebra-generating set.
-/

public section

namespace Ideal

variable {A B G : Type*} [CommSemiring A] [CommRing B] [Group G] [MulSemiringAction G B]
  [Algebra A B] [SMulCommClass G A B]

/-- **Membership in an inertia group is decided on an algebra-generating set.** If `B` is
generated as an `A`-algebra by `S`, and `G` fixes the image of `A`, then `σ` belongs to the
inertia group of `I` exactly when it moves every element of `S` by an element of `I`. -/
theorem mem_inertia_iff_of_adjoin_eq_top (I : Ideal B) {S : Set B}
    (hS : Algebra.adjoin A S = ⊤) {σ : G} :
    σ ∈ I.inertia G ↔ ∀ x ∈ S, σ • x - x ∈ I := by
  constructor
  · intro hσ x _
    exact Ideal.mem_inertia.mp hσ x
  · intro hσ
    rw [Ideal.mem_inertia]
    intro x
    induction hS.ge (Algebra.mem_top (x := x)) using Algebra.adjoin_induction with
    | mem y hy => exact hσ y hy
    | algebraMap r => simp
    | add y z _ _ hy hz => simpa [smul_add, add_sub_add_comm] using I.add_mem hy hz
    | mul y z _ _ hy hz => simpa [smul_mul'] using I.mul_sub_mul_mem hy hz

end Ideal
