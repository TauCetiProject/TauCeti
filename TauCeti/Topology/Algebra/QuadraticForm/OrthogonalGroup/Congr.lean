/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.QuadraticForm.OrthogonalGroup.Closed

/-!
# Continuity of isometric transport of orthogonal groups

An isometric equivalence `e : Q₁ ≃ Q₂` of quadratic maps identifies `O(Q₁)` with `O(Q₂)`, and
`SO(Q₁)` with `SO(Q₂)`, by conjugation. Both groups carry the subspace topology from the
forward-and-inverse topology on linear automorphisms, in which conjugation by a linear equivalence
is continuous (`LinearEquiv.continuous_autCongr`). So the transport is continuous, and, its inverse
being transport along `e.symm`, it is a homeomorphism. In particular it carries compact and open
subgroups of one orthogonal group onto compact and open subgroups of the other, which is what lets
compact-open reference subgroups be moved along an isometry of local quadratic spaces.

## Main results

* `QuadraticMap.IsometryEquiv.continuous_orthogonalGroupCongr`: transport of orthogonal groups
  along an isometry is continuous.
* `QuadraticMap.IsometryEquiv.continuous_specialOrthogonalGroupCongr`: the same for special
  orthogonal groups.
-/

public section

namespace QuadraticMap.IsometryEquiv

open TauCeti.QuadraticMap (orthogonalGroup specialOrthogonalGroup)

section Semiring

variable {R M₁ M₂ N : Type*} [CommSemiring R] [TopologicalSpace R]
  [AddCommMonoid M₁] [Module R M₁] [AddCommMonoid M₂] [Module R M₂]
  [AddCommMonoid N] [Module R N]
  {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}

/-- Transport of orthogonal groups along an isometric equivalence is continuous. -/
@[fun_prop]
theorem continuous_orthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) :
    Continuous e.orthogonalGroupCongr := by
  apply continuous_induced_rng.mpr
  refine ((LinearEquiv.continuous_autCongr e.toLinearEquiv).comp continuous_subtype_val).congr
    fun g ↦ ?_
  ext m
  simp

end Semiring

section Ring

variable {R M₁ M₂ N : Type*} [CommRing R] [TopologicalSpace R]
  [AddCommGroup M₁] [Module R M₁] [AddCommGroup M₂] [Module R M₂]
  [AddCommMonoid N] [Module R N]
  {Q₁ : QuadraticMap R M₁ N} {Q₂ : QuadraticMap R M₂ N}

/-- Transport of special orthogonal groups along an isometric equivalence is continuous. -/
@[fun_prop]
theorem continuous_specialOrthogonalGroupCongr (e : Q₁.IsometryEquiv Q₂) :
    Continuous e.specialOrthogonalGroupCongr := by
  apply continuous_induced_rng.mpr
  refine ((LinearEquiv.continuous_autCongr e.toLinearEquiv).comp continuous_subtype_val).congr
    fun g ↦ ?_
  ext m
  simp

end Ring

end QuadraticMap.IsometryEquiv
