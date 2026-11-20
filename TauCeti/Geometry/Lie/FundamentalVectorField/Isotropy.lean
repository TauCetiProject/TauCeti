/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Subrepresentation
public import TauCeti.Geometry.Lie.Adjoint.Representation.Coadjoint.Basic
public import TauCeti.Geometry.Lie.FundamentalVectorField

import TauCeti.RepresentationTheory.Subrepresentation

/-!
# The isotropy algebra as a representation of the stabilizer

Let a Lie group `G` act smoothly on a manifold `M`. The stabilizer `G_x` of a point `x` maps the
isotropy algebra `𝔤_x = {ξ | ξ_M(x) = 0}` into itself under the adjoint action
(`TauCeti.adjointContinuousLinearMap_mem_isotropy_of_mem_stabilizer`). This file records `𝔤_x` as a
subrepresentation of the adjoint representation of any subgroup `H` of `G_x`, which is the form in
which `Ad(H)`-invariant complements of `𝔤_x` are chosen.

## Main definitions

* `TauCeti.isotropySubrepresentation`: the isotropy algebra `𝔤_x`, as a subrepresentation of the
  adjoint representation of a subgroup of the stabilizer `G_x`.

## Main results

* `TauCeti.toSubmodule_isotropySubrepresentation` and
  `TauCeti.mem_isotropySubrepresentation_iff`: its carrier is `𝔤_x`.
-/

public section

noncomputable section

open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {G : Type*} [TopologicalSpace G] [ChartedSpace H G] [Group G] [LieGroup I (minSmoothness ℝ 3) G]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [CompleteSpace E']
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I' ∞ M] [MulAction G M]
  [ContMDiffSMul I I' ∞ G M]

attribute [local instance] lieGroupOne

variable (I I') in
/-- The isotropy algebra `𝔤_x` of the fundamental infinitesimal action, as a subrepresentation of
the adjoint representation of a subgroup `K` of the stabilizer `G_x`. -/
def isotropySubrepresentation (x : M) {K : Subgroup G} (hK : K ≤ MulAction.stabilizer G x) :
    Subrepresentation ((Lie.adjointRepresentation ℝ I G).comp K.subtype) where
  toSubmodule := ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule
  apply_mem_toSubmodule g _ hξ := by
    simpa only [MonoidHom.coe_comp, Function.comp_apply, Subgroup.coe_subtype,
      Lie.adjointRepresentation_apply, LieSubalgebra.mem_toSubmodule] using
      adjointContinuousLinearMap_mem_isotropy_of_mem_stabilizer (hK g.property) hξ

/-- The underlying submodule of `TauCeti.isotropySubrepresentation` is the isotropy algebra. -/
@[simp]
theorem toSubmodule_isotropySubrepresentation (x : M) {K : Subgroup G}
    (hK : K ≤ MulAction.stabilizer G x) :
    (isotropySubrepresentation I I' x hK).toSubmodule =
      ((InfinitesimalAction.fundamental I G I' M).isotropy x).toSubmodule :=
  -- `(rfl)`, not `rfl`: the body of `isotropySubrepresentation` is not `@[expose]`d, so this must
  -- not be inferred `@[defeq]`.
  (rfl)

/-- Membership in `TauCeti.isotropySubrepresentation` is membership in the isotropy algebra. -/
@[simp]
theorem mem_isotropySubrepresentation_iff {x : M} {K : Subgroup G}
    {hK : K ≤ MulAction.stabilizer G x} {ξ : GroupLieAlgebra I G} :
    ξ ∈ isotropySubrepresentation I I' x hK ↔
      ξ ∈ (InfinitesimalAction.fundamental I G I' M).isotropy x := by
  rw [← Subrepresentation.mem_toSubmodule, toSubmodule_isotropySubrepresentation,
    LieSubalgebra.mem_toSubmodule]

end TauCeti
