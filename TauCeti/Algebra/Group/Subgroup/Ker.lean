/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Ranges and equality loci of group homomorphisms

This file supplies the characteristic membership equation for the subgroup equality locus and the
invariance of the range of a group homomorphism under precomposition with a surjection.

## Main results

* `MonoidHom.mem_eqLocus`: membership in the equality locus is pointwise equality.
* `MonoidHom.range_comp_of_surjective`: precomposition with a surjection preserves the range.
-/

public section

namespace MonoidHom

variable {G M : Type*} [Group G] [Monoid M]

/-- Membership in the equality locus of two group homomorphisms is pointwise equality. -/
@[to_additive (attr := simp)]
theorem mem_eqLocus {f g : G →* M} {x : G} : x ∈ f.eqLocus g ↔ f x = g x :=
  Iff.rfl

/-- Precomposition with a surjective group homomorphism does not change the range. -/
@[to_additive /-- Precomposition with a surjective additive group homomorphism does not change the
range. -/]
theorem range_comp_of_surjective {N P : Type*} [Group N] [Group P] (g : N →* P) (f : G →* N)
    (hf : Function.Surjective f) : (g.comp f).range = g.range := by
  rw [range_comp, range_eq_top_of_surjective f hf, ← range_eq_map]

end MonoidHom
