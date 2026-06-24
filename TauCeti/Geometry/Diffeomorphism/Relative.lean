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

This file records the pointwise fixing subgroup for the diffeomorphism action, with
boundary-specific specializations.  The geometric-topology roadmap's layer on diffeomorphism
groups asks for the relative group `Diff(M, ∂M)`, the diffeomorphisms fixing the boundary
pointwise, as soon as `Diff(M)` itself is available as a group.  The underlying subgroup is
Mathlib's `fixingSubgroup` applied directly to the relevant set of points.

## Main definitions

* `Diffeomorph.fixedOnSubgroup I n s`: the subgroup fixing `s` pointwise.
* `Diffeomorph.boundaryFixingSubgroup I n`: the subgroup fixing `I.boundary M` pointwise, the
  group-level precursor of `Diff(M, ∂M)`.

## Main results

* `Diffeomorph.mem_fixedOnSubgroup_iff`: membership in `fixedOnSubgroup` means pointwise fixing.
* `Diffeomorph.fixedOnSubgroup_empty`: the subgroup fixing the empty set is the top subgroup.
* `Diffeomorph.fixedOnSubgroup_univ`: the subgroup fixing the whole space is the bottom
  subgroup.
* `Diffeomorph.fixedOnSubgroup_union`: fixing a union is the infimum of the two fixing
  subgroups.
* `Diffeomorph.mem_boundaryFixingSubgroup_iff`: membership in `boundaryFixingSubgroup` means
  pointwise fixing on the boundary.
* `Diffeomorph.toHomeomorphHom_mem_fixingSubgroup_of_mem_fixedOnSubgroup`: a set-fixing
  diffeomorphism maps to a set-fixing homeomorphism under the forgetful homomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] {n : ℕ∞ω}

/-- The subgroup of self-diffeomorphisms fixing a set pointwise. -/
abbrev fixedOnSubgroup (n : ℕ∞ω) (s : Set M) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  _root_.fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s

/-- Membership in `fixedOnSubgroup` is pointwise fixing on the set. -/
theorem mem_fixedOnSubgroup_iff {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixedOnSubgroup I n s ↔ ∀ x ∈ s, f x = x := by
  simp [fixedOnSubgroup, _root_.mem_fixingSubgroup_iff, smul_def]

/-- The subgroup fixing the empty set is the top subgroup. -/
@[simp]
theorem fixedOnSubgroup_empty :
    fixedOnSubgroup I n (∅ : Set M) = ⊤ := by
  exact _root_.fixingSubgroup_empty (M := M ≃ₘ^n⟮I, I⟯ M) (α := M)

/-- The subgroup fixing the whole space is the bottom subgroup. -/
@[simp]
theorem fixedOnSubgroup_univ :
    fixedOnSubgroup I n (Set.univ : Set M) = ⊥ := by
  ext f
  rw [mem_fixedOnSubgroup_iff, Subgroup.mem_bot]
  constructor
  · intro hf
    apply _root_.Diffeomorph.ext
    intro x
    exact hf x (Set.mem_univ x)
  · rintro rfl x -
    rfl

/-- Fixing a union is the infimum of the two fixing subgroups. -/
theorem fixedOnSubgroup_union {s t : Set M} :
    fixedOnSubgroup I n (s ∪ t) = fixedOnSubgroup I n s ⊓ fixedOnSubgroup I n t := by
  simpa [fixedOnSubgroup] using
    (_root_.fixingSubgroup_union (M := M ≃ₘ^n⟮I, I⟯ M) (s := s) (t := t))

/-- Membership in the subgroup fixing a union is membership in both fixing subgroups. -/
theorem mem_fixedOnSubgroup_union_iff {s t : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixedOnSubgroup I n (s ∪ t) ↔
      f ∈ fixedOnSubgroup I n s ∧ f ∈ fixedOnSubgroup I n t := by
  simp [fixedOnSubgroup_union]

/-- `fixedOnSubgroup` is antitone in the set of fixed points. -/
theorem fixedOnSubgroup_antitone :
    Antitone (fixedOnSubgroup I n : Set M → Subgroup (M ≃ₘ^n⟮I, I⟯ M)) := by
  simpa [fixedOnSubgroup] using
    (_root_.fixingSubgroup_antitone (M := M ≃ₘ^n⟮I, I⟯ M) (α := M))

/-- The subgroup of self-diffeomorphisms fixing the model boundary pointwise. -/
abbrev boundaryFixingSubgroup (n : ℕ∞ω) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixedOnSubgroup I n (I.boundary M)

/-- Membership in `boundaryFixingSubgroup` is pointwise fixing on the boundary. -/
@[simp]
theorem mem_boundaryFixingSubgroup_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ boundaryFixingSubgroup I n ↔ ∀ x ∈ I.boundary M, f x = x :=
  mem_fixedOnSubgroup_iff (I := I) (n := n) (s := I.boundary M) (f := f)

/-- A set-fixing diffeomorphism forgets to a set-fixing homeomorphism. -/
theorem toHomeomorphHom_mem_fixingSubgroup_of_mem_fixedOnSubgroup
    {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ fixedOnSubgroup I n s) :
    toHomeomorphHom f ∈ _root_.fixingSubgroup (M ≃ₜ M) s := by
  rw [_root_.mem_fixingSubgroup_iff]
  intro x hx
  rw [Homeomorph.smul_def]
  simpa [smul_def, toHomeomorphHom_apply] using
    ((mem_fixedOnSubgroup_iff (I := I) (n := n)).mp hf x hx)

end Diffeomorph

end TauCeti
