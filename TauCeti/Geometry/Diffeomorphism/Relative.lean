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
* `Diffeomorph.fixedOnSubgroup_empty`, `Diffeomorph.fixedOnSubgroup_univ`,
  `Diffeomorph.fixedOnSubgroup_union`, `Diffeomorph.fixedOnSubgroup_iUnion`, and
  `Diffeomorph.fixedOnSubgroup_antitone`: the standard set-operation API for fixing subgroups
  specialized to diffeomorphisms.
* `Diffeomorph.fixedOnSubgroup_fixedPoints_gc`: the Galois connection between fixed-on
  subgroups and fixed points for the diffeomorphism action.
* `Diffeomorph.mem_boundaryFixingSubgroup_iff`: membership in `boundaryFixingSubgroup` means
  pointwise boundary fixing.
* `Diffeomorph.toHomeomorphHom_mem_fixingSubgroup_of_mem_fixedOnSubgroup`: a set-fixing
  diffeomorphism maps to a set-fixing homeomorphism under the forgetful homomorphism.
* `Diffeomorph.toHomeomorphHom_mem_fixingSubgroup_boundary_of_mem_boundaryFixingSubgroup`: a
  boundary-fixing diffeomorphism maps to a boundary-fixing homeomorphism under the forgetful
  homomorphism.
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
    fixedOnSubgroup I n (∅ : Set M) = ⊤ :=
  _root_.fixingSubgroup_empty (M ≃ₘ^n⟮I, I⟯ M) M

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

/-- The Galois connection between fixed-on subgroups and fixed points of the diffeomorphism
action. -/
theorem fixedOnSubgroup_fixedPoints_gc :
    GaloisConnection (OrderDual.toDual ∘ fixedOnSubgroup I n)
      ((fun P : Subgroup (M ≃ₘ^n⟮I, I⟯ M) => MulAction.fixedPoints P M) ∘
        OrderDual.ofDual) :=
  _root_.fixingSubgroup_fixedPoints_gc (M ≃ₘ^n⟮I, I⟯ M) M

/-- `fixedOnSubgroup` reverses set inclusion. -/
theorem fixedOnSubgroup_antitone :
    Antitone (fixedOnSubgroup I n : Set M → Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :=
  _root_.fixingSubgroup_antitone (M ≃ₘ^n⟮I, I⟯ M) M

/-- The subgroup fixing a union is the infimum of the subgroups fixing each set. -/
theorem fixedOnSubgroup_union {s t : Set M} :
    fixedOnSubgroup I n (s ∪ t) = fixedOnSubgroup I n s ⊓ fixedOnSubgroup I n t :=
  _root_.fixingSubgroup_union (M ≃ₘ^n⟮I, I⟯ M) M

/-- The subgroup fixing an indexed union is the infimum of the subgroups fixing each set. -/
theorem fixedOnSubgroup_iUnion {ι : Sort*} {s : ι → Set M} :
    fixedOnSubgroup I n (⋃ i, s i) = ⨅ i, fixedOnSubgroup I n (s i) :=
  _root_.fixingSubgroup_iUnion (M ≃ₘ^n⟮I, I⟯ M) M

/-- Fixed points of the supremum of diffeomorphism subgroups are the intersection of their
fixed points. -/
theorem fixedPoints_subgroup_sup {P Q : Subgroup (M ≃ₘ^n⟮I, I⟯ M)} :
    MulAction.fixedPoints (↥(P ⊔ Q)) M =
      MulAction.fixedPoints (↥P) M ∩ MulAction.fixedPoints (↥Q) M :=
  _root_.fixedPoints_subgroup_sup (M ≃ₘ^n⟮I, I⟯ M) M

/-- Fixed points of the supremum of an indexed family of diffeomorphism subgroups are the
intersection of their fixed points. -/
theorem fixedPoints_subgroup_iSup {ι : Sort*} {P : ι → Subgroup (M ≃ₘ^n⟮I, I⟯ M)} :
    MulAction.fixedPoints (↥(iSup P)) M = ⋂ i, MulAction.fixedPoints (↥(P i)) M :=
  _root_.fixedPoints_subgroup_iSup (M ≃ₘ^n⟮I, I⟯ M) M

/-- The subgroup of self-diffeomorphisms fixing the model boundary pointwise. -/
abbrev boundaryFixingSubgroup (n : ℕ∞ω) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixedOnSubgroup I n (I.boundary M)

/-- Membership in `boundaryFixingSubgroup` is pointwise fixing on the model boundary. -/
theorem mem_boundaryFixingSubgroup_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ boundaryFixingSubgroup I n ↔ ∀ x ∈ I.boundary M, f x = x :=
  mem_fixedOnSubgroup_iff (I := I) (n := n) (s := I.boundary M)

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

/-- A boundary-fixing diffeomorphism forgets to a boundary-fixing homeomorphism. -/
theorem toHomeomorphHom_mem_fixingSubgroup_boundary_of_mem_boundaryFixingSubgroup
    {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ boundaryFixingSubgroup I n) :
    toHomeomorphHom f ∈ _root_.fixingSubgroup (M ≃ₜ M) (I.boundary M) :=
  toHomeomorphHom_mem_fixingSubgroup_of_mem_fixedOnSubgroup I hf

end Diffeomorph

end TauCeti
