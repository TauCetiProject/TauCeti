/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Complement
public import TauCeti.GroupTheory.Amenable.Discrete

/-!
# Subgroups of amenable discrete groups

Every subgroup of an amenable discrete group is amenable. More generally, if `φ : H →* G` is
injective and `G` is an amenable discrete group, then `H` is amenable for every group topology.

Restricting a mean on `G` to the subgroup does not work, since the subgroup can have mass zero.
Instead, choose a right transversal `T` of the image `φ.range`, so that every `x : G` factors
uniquely as `x = φ (r x) * t` with `t ∈ T` (Mathlib's `Subgroup.IsComplement.equiv`). The map
`r : G → H` satisfies `r (φ h * x) = h * r x`, so for a left-invariant mean `m` on `G` the mean
`f ↦ m (f ∘ r)` on `H` (`TauCeti.Mean.mapOfDiscrete`) is left invariant: the pullback along `r`
of the translate `L_h f` is the translate `L_(φ h) (f ∘ r)`.

Subgroups of amenable topological groups need not be amenable, so the discreteness of `G` cannot
be dropped.

## Main results

* `TauCeti.Amenable.of_injective`: a group embedding in an amenable discrete group is amenable.
* `TauCeti.Amenable.subgroup`: every subgroup of an amenable discrete group is amenable.

## References

* A. Garrido, *An introduction to amenable groups*, Proposition 2.2.
-/

public section

namespace TauCeti

variable {G H : Type*} [Group G] [TopologicalSpace G] [DiscreteTopology G]
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- A group `H` which embeds by an injective homomorphism in an amenable discrete group is
amenable, for every group topology on `H`. -/
theorem Amenable.of_injective [Amenable G] (φ : H →* G) (hφ : Function.Injective φ) :
    Amenable H := by
  -- Factor `x = φ (r x) * t` along a right transversal `T` of the image of `φ`.
  obtain ⟨T, hT, -⟩ := φ.range.exists_isComplement_right 1
  let e := MonoidHom.ofInjective hφ
  obtain ⟨m, hm⟩ := Amenable.exists_isLeftInvariant (G := G)
  refine ⟨m.mapOfDiscrete (fun x => e.symm (hT.equiv x).1), hm.mapOfDiscrete φ fun h x => ?_⟩
  rw [hT.equiv_mul_left_of_mem ⟨h, rfl⟩, map_mul,
    e.symm_apply_eq.2 (Subtype.ext (MonoidHom.ofInjective_apply hφ).symm)]

/-- Every subgroup of an amenable discrete group is amenable. -/
instance Amenable.subgroup [Amenable G] (K : Subgroup G) : Amenable K :=
  .of_injective K.subtype K.subtype_injective

end TauCeti
