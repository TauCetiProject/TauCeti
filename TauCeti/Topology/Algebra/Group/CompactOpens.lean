/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.Set.Card
public import Mathlib.GroupTheory.Index
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.Topology.Sets.Compacts
import TauCeti.GroupTheory.Coset.Card
import TauCeti.Topology.Algebra.Group.OpenSubgroup.Compact

/-!
# Translates of compact open sets and compact open subgroups

For a group `G` acting on a topological space `α` by homeomorphisms (`ContinuousConstSMul G α`),
the translate `g • K` of a compact open set `K` is again compact open. This file records the
resulting pointwise action of `G` on `TopologicalSpace.CompactOpens α`, scoped to `Pointwise` like
Mathlib's pointwise actions on sets and subgroups, and the compact open set underlying a compact
open subgroup. Together they describe the left cosets `g • U` of a compact open subgroup `U` as
compact open sets, which is how finitely additive invariant volumes on the compact open subsets of a
locally profinite group are computed.

## Main definitions

* `TopologicalSpace.CompactOpens.pointwiseMulAction`: the action `g • K` of `G` on compact open
  sets, an instance in the `Pointwise` scope.
* `OpenSubgroup.toCompactOpens`: a compact open subgroup as a compact open set.

## Main results

* `TopologicalSpace.CompactOpens.exists_openSubgroup_le_forall_mul_mem`: a compact open set is a
  union of left cosets of an open subgroup contained in a given open subgroup.
* `OpenSubgroup.forall_mul_mem_toCompactOpens`: a compact open subgroup `U` is a union of left
  cosets of each open subgroup `W ≤ U`.
* `OpenSubgroup.ncard_image_mk_toCompactOpens`: a compact open subgroup `U` meets `[U : W]` left
  cosets of an open subgroup `W ≤ U`.
-/

public section

open Set
open scoped Pointwise

namespace TopologicalSpace.CompactOpens

variable {G α : Type*} [Group G] [MulAction G α] [TopologicalSpace α] [ContinuousConstSMul G α]

/-- The pointwise action of a group on the compact open subsets of a space on which it acts by
homeomorphisms: `g • K` is the translate of `K` by `g`. This is available in the `Pointwise`
scope. -/
@[instance_reducible, expose]
protected def pointwiseMulAction : MulAction G (CompactOpens α) where
  smul g K := ⟨⟨g • (K : Set α), K.isCompact.smul g⟩, K.isOpen.smul g⟩
  one_smul K := CompactOpens.ext (one_smul G (K : Set α))
  mul_smul g h K := CompactOpens.ext (mul_smul g h (K : Set α))

scoped[Pointwise] attribute [instance] TopologicalSpace.CompactOpens.pointwiseMulAction

@[simp, norm_cast]
theorem coe_smul (g : G) (K : CompactOpens α) :
    ((g • K : CompactOpens α) : Set α) = g • (K : Set α) :=
  (rfl)

theorem mem_smul_iff_inv_smul_mem {g : G} {K : CompactOpens α} {x : α} : x ∈ g • K ↔ g⁻¹ • x ∈ K :=
  Set.mem_smul_set_iff_inv_smul_mem

/-- In a topological group, every compact open set `K` is a union of left cosets of some open
subgroup contained in a given open subgroup `U₀`, namely of the intersection of `U₀` with the right
translation stabilizer of `K`. -/
theorem exists_openSubgroup_le_forall_mul_mem {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (K : CompactOpens G) (U₀ : OpenSubgroup G) :
    ∃ W : OpenSubgroup G, W ≤ U₀ ∧ ∀ k ∈ K, ∀ w ∈ W, k * w ∈ K := by
  -- The right translation stabilizer of `K` is the left translation stabilizer of `K⁻¹`.
  let S : OpenSubgroup G :=
    ⟨MulAction.stabilizer G (K : Set G)⁻¹, K.isCompact.inv.isOpen_stabilizer K.isOpen.inv⟩
  refine ⟨U₀ ⊓ S, inf_le_left, fun k hk w hw ↦ ?_⟩
  have hw' : w⁻¹ ∈ MulAction.stabilizer G (K : Set G)⁻¹ := inv_mem (Subgroup.mem_inf.1 hw).2
  have : w⁻¹ * k⁻¹ ∈ (K : Set G)⁻¹ := by
    rw [← MulAction.mem_stabilizer_iff.1 hw']
    exact Set.smul_mem_smul_set (by simpa using hk)
  simpa [mul_inv_rev] using this

end TopologicalSpace.CompactOpens

namespace OpenSubgroup

variable {G : Type*} [Group G] [TopologicalSpace G]

/-- A compact open subgroup, as a compact open subset. -/
def toCompactOpens (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    TopologicalSpace.CompactOpens G :=
  ⟨⟨U, hU⟩, U.isOpen⟩

@[simp]
theorem coe_toCompactOpens (U : OpenSubgroup G) (hU : IsCompact (U : Set G)) :
    (U.toCompactOpens hU : Set G) = U :=
  (rfl)

@[simp]
theorem mem_toCompactOpens {U : OpenSubgroup G} {hU : IsCompact (U : Set G)} {g : G} :
    g ∈ U.toCompactOpens hU ↔ g ∈ U :=
  Iff.rfl

/-- A compact open subgroup `U` is a union of left cosets of each open subgroup `W ≤ U`. -/
theorem forall_mul_mem_toCompactOpens {U W : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (h : W ≤ U) : ∀ k ∈ U.toCompactOpens hU, ∀ w ∈ W, k * w ∈ U.toCompactOpens hU :=
  fun _ hk _ hw ↦ mem_toCompactOpens.2 (U.mul_mem (mem_toCompactOpens.1 hk) (h hw))

/-- A compact open subgroup `U` meets exactly `[U : W]` left cosets of an open subgroup `W ≤ U`. -/
theorem ncard_image_mk_toCompactOpens {U W : OpenSubgroup G} (hU : IsCompact (U : Set G))
    (h : W ≤ U) :
    (((↑) : G → G ⧸ (W : Subgroup G)) '' (U.toCompactOpens hU)).ncard =
      (W : Subgroup G).relIndex U :=
  Subgroup.ncard_image_mk_eq_relIndex (U := (U : Subgroup G)) h

end OpenSubgroup
