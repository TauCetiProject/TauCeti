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

* `TauCeti.Diffeomorph.fixingSubgroup I n s`: the subgroup fixing `s` pointwise.
* `TauCeti.Diffeomorph.boundaryFixingSubgroup I n`: the subgroup fixing `I.boundary M` pointwise,
  the group-level precursor of `Diff(M, ∂M)`.

## Main results

* `mem_fixingSubgroup_iff`: the pointwise membership criterion for a fixed subset.
* `mem_boundaryFixingSubgroup_iff`: the pointwise membership criterion.
* `toHomeomorphHom_mem_fixingSubgroup_of_mem_fixingSubgroup`: a subset-fixing diffeomorphism
  maps to a subset-fixing homeomorphism under the forgetful homomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (n : ℕ∞ω)

/-- The subgroup of self-diffeomorphisms fixing a set pointwise. -/
def fixingSubgroup (s : Set M) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s

/-- The definition of `Diffeomorph.fixingSubgroup` as Mathlib's pointwise fixing subgroup. -/
theorem fixingSubgroup_def (s : Set M) :
    fixingSubgroup I n s = _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s := by
  ext f
  simp [fixingSubgroup, _root_.mem_fixingSubgroup_iff, smul_def]

/-- A self-diffeomorphism lies in the subgroup fixing `s` exactly when it fixes every point of
`s`. -/
@[simp]
theorem mem_fixingSubgroup_iff {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixingSubgroup I n s ↔ ∀ x ∈ s, f x = x := by
  simp [fixingSubgroup, _root_.mem_fixingSubgroup_iff, smul_def]

/-- The diffeomorphism subgroup fixing the empty set is the top subgroup. -/
@[simp]
theorem fixingSubgroup_empty :
    fixingSubgroup I n (∅ : Set M) = ⊤ := by
  simp [fixingSubgroup_def,
    (_root_.fixingSubgroup_empty (M := M ≃ₘ^n⟮I, I⟯ M) (α := M))
  ]

/-- Fixing the union of two sets is the intersection of the fixing subgroups. -/
theorem fixingSubgroup_union {s t : Set M} :
    fixingSubgroup I n (s ∪ t) = fixingSubgroup I n s ⊓ fixingSubgroup I n t := by
  simpa [fixingSubgroup_def] using
    (_root_.fixingSubgroup_union (M := M ≃ₘ^n⟮I, I⟯ M) (α := M) (s := s) (t := t))

/-- Fixing an indexed union is the infimum of the fixing subgroups. -/
theorem fixingSubgroup_iUnion {ι : Sort*} {s : ι → Set M} :
    fixingSubgroup I n (⋃ i, s i) = ⨅ i, fixingSubgroup I n (s i) := by
  simpa [fixingSubgroup_def] using
    (_root_.fixingSubgroup_iUnion (M := M ≃ₘ^n⟮I, I⟯ M) (α := M) (s := s))

/-- The diffeomorphism subgroup fixing a set is antitone in the set. -/
theorem fixingSubgroup_antitone :
    Antitone (fixingSubgroup I n : Set M → Subgroup (M ≃ₘ^n⟮I, I⟯ M)) := by
  intro s t hst
  simpa [fixingSubgroup_def] using
    (_root_.fixingSubgroup_antitone (M := M ≃ₘ^n⟮I, I⟯ M) (α := M) hst)

/-- The subgroup of self-diffeomorphisms fixing the manifold boundary pointwise.  This is the
group-level form of the relative diffeomorphism group `Diff(M, ∂M)`. -/
def boundaryFixingSubgroup : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixingSubgroup I n (I.boundary M)

/-- The boundary-fixing subgroup is the specialization of `Diffeomorph.fixingSubgroup` to the
manifold boundary. -/
theorem boundaryFixingSubgroup_def :
    boundaryFixingSubgroup I n = fixingSubgroup I n (I.boundary M) := by
  ext f
  simp [boundaryFixingSubgroup, mem_fixingSubgroup_iff]

/-- A self-diffeomorphism lies in the boundary-fixing subgroup exactly when it fixes every
boundary point. -/
@[simp]
theorem mem_boundaryFixingSubgroup_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ boundaryFixingSubgroup I n ↔ ∀ x ∈ I.boundary M, f x = x := by
  simp [boundaryFixingSubgroup]

/-- A diffeomorphism fixing a subset forgets to a homeomorphism fixing the same subset. -/
theorem toHomeomorphHom_mem_fixingSubgroup_of_mem_fixingSubgroup {s : Set M}
    {f : M ≃ₘ^n⟮I, I⟯ M} (hf : f ∈ fixingSubgroup I n s) :
    toHomeomorphHom f ∈ _root_.fixingSubgroup (M ≃ₜ M) s := by
  rw [_root_.mem_fixingSubgroup_iff]
  intro x hx
  rw [Homeomorph.smul_def]
  simpa [toHomeomorphHom_apply] using (mem_fixingSubgroup_iff I n).mp hf x hx

/-- A boundary-fixing diffeomorphism forgets to a boundary-fixing homeomorphism. -/
theorem toHomeomorphHom_mem_fixingSubgroup_boundary_of_mem_boundaryFixingSubgroup
    {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ boundaryFixingSubgroup I n) :
    toHomeomorphHom f ∈ _root_.fixingSubgroup (M ≃ₜ M) (I.boundary M) := by
  exact toHomeomorphHom_mem_fixingSubgroup_of_mem_fixingSubgroup I n hf

end Diffeomorph

end TauCeti
