/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Geometry.Diffeomorphism.Action
public import TauCeti.Topology.Algebra.HomeomorphAction
public import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
# Relative diffeomorphism groups

This file packages subgroups of the diffeomorphism group that fix a subset pointwise, especially
the manifold boundary.  The geometric-topology roadmap's layer on diffeomorphism groups asks for
the relative group `Diff(M, ∂M)`, the diffeomorphisms fixing the boundary pointwise, as soon as
`Diff(M)` itself is available as a group.  The generic group-action primitive already exists in
Mathlib as `fixingSubgroup`; the boundary-facing name below is just the roadmap-facing
specialization.

## Main definitions

* `TauCeti.Diffeomorph.boundaryFixingSubgroup I n`: the subgroup fixing `I.boundary M` pointwise,
  the group-level precursor of `Diff(M, ∂M)`.

## Main results

* `mem_boundaryFixingSubgroup_iff`: the pointwise membership criterion.
* `toHomeomorphHom_mem_fixingSubgroup_boundary_of_mem_boundaryFixingSubgroup`: a boundary-fixing
  diffeomorphism maps to a boundary-fixing homeomorphism under the forgetful homomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (n : ℕ∞ω)

/-- The subgroup of self-diffeomorphisms fixing the manifold boundary pointwise.  This is the
group-level form of the relative diffeomorphism group `Diff(M, ∂M)`. -/
def boundaryFixingSubgroup : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) (I.boundary M)

/-- The boundary-fixing subgroup is Mathlib's pointwise fixing subgroup, specialized to the
manifold boundary and the diffeomorphism action. -/
theorem boundaryFixingSubgroup_def :
    boundaryFixingSubgroup I n =
      _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) (I.boundary M) := by
  ext f
  simp [boundaryFixingSubgroup, _root_.mem_fixingSubgroup_iff, smul_def]

/-- A self-diffeomorphism lies in the boundary-fixing subgroup exactly when it fixes every
boundary point. -/
@[simp]
theorem mem_boundaryFixingSubgroup_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ boundaryFixingSubgroup I n ↔ ∀ x ∈ I.boundary M, f x = x := by
  simp [boundaryFixingSubgroup, _root_.mem_fixingSubgroup_iff, smul_def]

/-- A boundary-fixing diffeomorphism forgets to a boundary-fixing homeomorphism. -/
theorem toHomeomorphHom_mem_fixingSubgroup_boundary_of_mem_boundaryFixingSubgroup
    {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ boundaryFixingSubgroup I n) :
    toHomeomorphHom f ∈ _root_.fixingSubgroup (M ≃ₜ M) (I.boundary M) := by
  rw [_root_.mem_fixingSubgroup_iff]
  intro x hx
  rw [Homeomorph.smul_def]
  simpa [toHomeomorphHom_apply] using (mem_boundaryFixingSubgroup_iff I n).mp hf x hx

end Diffeomorph

end TauCeti
