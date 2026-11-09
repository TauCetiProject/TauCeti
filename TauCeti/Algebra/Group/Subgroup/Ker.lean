/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.Ker

/-!
# Ranges and equality loci of group homomorphisms

This file supplies the characteristic membership equation for the subgroup equality locus, the
invariance of the range of a group homomorphism under precomposition with a surjection, and the
range and kernel of the pointwise inverse of a homomorphism into a commutative group.

## Main results

* `MonoidHom.mem_eqLocus`: membership in the equality locus is pointwise equality.
* `MonoidHom.range_comp_of_surjective`: precomposition with a surjection preserves the range.
* `MonoidHom.range_inv`, `MonoidHom.ker_inv`: the pointwise inverse `f⁻¹` has the same range and
  kernel as `f`.
-/

public section

namespace MonoidHom

variable {G M : Type*} [Group G] [Monoid M]

/-- Membership in the equality locus of two monoid homomorphisms out of a group is pointwise
equality. -/
@[to_additive (attr := simp)]
theorem mem_eqLocus {f g : G →* M} {x : G} : x ∈ f.eqLocus g ↔ f x = g x :=
  Iff.rfl

/-- Precomposition with a surjective group homomorphism does not change the range. -/
@[to_additive /-- Precomposition with a surjective additive group homomorphism does not change the
range. -/]
theorem range_comp_of_surjective {N P : Type*} [Group N] [Group P] (g : N →* P) (f : G →* N)
    (hf : Function.Surjective f) : (g.comp f).range = g.range :=
  SetLike.coe_injective <| by simpa only [coe_range, coe_comp] using hf.range_comp g

/-- The pointwise inverse of a homomorphism into a commutative group has the same range. -/
@[to_additive (attr := simp) /-- The pointwise negation of a homomorphism into a commutative
additive group has the same range. -/]
theorem range_inv {H : Type*} [CommGroup H] (f : G →* H) : f⁻¹.range = f.range := by
  ext
  simp only [mem_range]
  exact inv_surjective.exists.trans (by simp)

/-- The pointwise inverse of a homomorphism into a commutative group has the same kernel. -/
@[to_additive (attr := simp) /-- The pointwise negation of a homomorphism into a commutative
additive group has the same kernel. -/]
theorem ker_inv {H : Type*} [CommGroup H] (f : G →* H) : f⁻¹.ker = f.ker := by
  ext x
  simp

end MonoidHom
