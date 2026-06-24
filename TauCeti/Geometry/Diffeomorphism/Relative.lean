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

This file packages the subgroups of the diffeomorphism group that fix a set pointwise.  The
geometric-topology roadmap's layer on diffeomorphism groups asks for the relative group
`Diff(M, ∂M)`, the diffeomorphisms fixing the boundary pointwise, as soon as `Diff(M)` itself is
available as a group.  The generic group-action primitive already exists in Mathlib as
`fixingSubgroup`; here we specialize it to Tau Ceti's `Diff` group and record the API in the
diffeomorphism namespace.

## Main definitions

* `TauCeti.Diffeomorph.fixedOnSubgroup I n s`: the subgroup of self-diffeomorphisms fixing
  `s : Set M` pointwise.
* `TauCeti.Diffeomorph.boundaryFixingSubgroup I n`: the subgroup fixing `I.boundary M`
  pointwise, the group-level precursor of `Diff(M, ∂M)`.

## Main results

* `mem_fixedOnSubgroup_iff` and `mem_boundaryFixingSubgroup_iff`: pointwise membership
  criteria.
* `fixedOnSubgroup_union`, `fixedOnSubgroup_empty`, `fixedOnSubgroup_univ`, and
  `fixedOnSubgroup_antitone`: the basic lattice behaviour inherited from `fixingSubgroup`.
* `toHomeomorphHom_mem_fixingSubgroup`: a relative diffeomorphism maps to a relative
  homeomorphism under the forgetful homomorphism.
-/

public section

namespace TauCeti

open scoped Manifold ContDiff

namespace Diffeomorph

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners 𝕜 E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] (n : ℕ∞ω)

/-- The subgroup of self-diffeomorphisms fixing the set `s` pointwise. -/
abbrev fixedOnSubgroup (s : Set M) : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixingSubgroup (M ≃ₘ^n⟮I, I⟯ M) s

/-- A self-diffeomorphism lies in `fixedOnSubgroup I n s` exactly when it fixes every point of
`s`. -/
theorem mem_fixedOnSubgroup_iff {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixedOnSubgroup I n s ↔ ∀ x ∈ s, f x = x := by
  simp [fixedOnSubgroup, mem_fixingSubgroup_iff, smul_def]

/-- The empty relative condition gives the whole diffeomorphism group. -/
@[simp]
theorem fixedOnSubgroup_empty :
    fixedOnSubgroup I n (∅ : Set M) = ⊤ :=
  fixingSubgroup_empty (M ≃ₘ^n⟮I, I⟯ M) M

/-- Fixing all points leaves only the identity diffeomorphism. -/
@[simp]
theorem fixedOnSubgroup_univ :
    fixedOnSubgroup I n (Set.univ : Set M) = ⊥ := by
  ext f
  rw [mem_fixedOnSubgroup_iff]
  constructor
  · intro hf
    rw [Subgroup.mem_bot]
    ext x
    simpa using hf x (Set.mem_univ x)
  · intro hf x _hx
    rw [Subgroup.mem_bot] at hf
    simp [hf]

/-- The subgroup fixing a larger set is contained in the subgroup fixing a smaller set. -/
theorem fixedOnSubgroup_antitone :
    Antitone (fixedOnSubgroup I n : Set M → Subgroup (M ≃ₘ^n⟮I, I⟯ M)) :=
  fixingSubgroup_antitone (M ≃ₘ^n⟮I, I⟯ M) M

/-- Fixing a union is the same as fixing both pieces. -/
theorem fixedOnSubgroup_union (s t : Set M) :
    fixedOnSubgroup I n (s ∪ t) = fixedOnSubgroup I n s ⊓ fixedOnSubgroup I n t :=
  fixingSubgroup_union (M ≃ₘ^n⟮I, I⟯ M) M

/-- Membership in the subgroup fixing a union, in pointwise form. -/
theorem mem_fixedOnSubgroup_union_iff {s t : Set M} {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ fixedOnSubgroup I n (s ∪ t) ↔
      f ∈ fixedOnSubgroup I n s ∧ f ∈ fixedOnSubgroup I n t := by
  rw [fixedOnSubgroup_union, Subgroup.mem_inf]

/-- If `s ⊆ t`, a diffeomorphism fixing `t` pointwise also fixes `s` pointwise. -/
theorem fixedOnSubgroup_mono {s t : Set M} (hst : s ⊆ t) :
    fixedOnSubgroup I n t ≤ fixedOnSubgroup I n s :=
  fixedOnSubgroup_antitone I n hst

/-- A relative diffeomorphism forgets to a relative homeomorphism fixing the same set pointwise. -/
theorem toHomeomorphHom_mem_fixingSubgroup {s : Set M} {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ fixedOnSubgroup I n s) :
    toHomeomorphHom f ∈ fixingSubgroup (M ≃ₜ M) s := by
  rw [mem_fixingSubgroup_iff]
  intro x hx
  rw [Homeomorph.smul_def]
  simpa [toHomeomorphHom_apply] using (mem_fixedOnSubgroup_iff I n).mp hf x hx

/-- The subgroup of self-diffeomorphisms fixing the manifold boundary pointwise.  This is the
group-level form of the relative diffeomorphism group `Diff(M, ∂M)`. -/
abbrev boundaryFixingSubgroup : Subgroup (M ≃ₘ^n⟮I, I⟯ M) :=
  fixedOnSubgroup I n (I.boundary M)

/-- A self-diffeomorphism lies in the boundary-fixing subgroup exactly when it fixes every
boundary point. -/
theorem mem_boundaryFixingSubgroup_iff {f : M ≃ₘ^n⟮I, I⟯ M} :
    f ∈ boundaryFixingSubgroup I n ↔ ∀ x ∈ I.boundary M, f x = x :=
  mem_fixedOnSubgroup_iff I n

/-- A boundary-fixing diffeomorphism forgets to a boundary-fixing homeomorphism. -/
theorem toHomeomorphHom_mem_boundaryFixingSubgroup {f : M ≃ₘ^n⟮I, I⟯ M}
    (hf : f ∈ boundaryFixingSubgroup I n) :
    toHomeomorphHom f ∈ fixingSubgroup (M ≃ₜ M) (I.boundary M) :=
  toHomeomorphHom_mem_fixingSubgroup I n hf

end Diffeomorph

end TauCeti
