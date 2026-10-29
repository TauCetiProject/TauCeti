/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.MulAction
public import Mathlib.Topology.FiberBundle.Basic

/-!
# Fiber bundles from group-valued transition functions

A continuous group action on an arbitrary topological fiber turns a continuous group-valued
cocycle on an open cover into native `FiberBundleCore` data. The composition convention is
`c j k b * c i j b = c i k b`: the transition from chart `i` to chart `j` acts on the left.
Normalization and inverse identities follow from this cocycle equation.

`TauCeti.fiberBundleCoreOfGroupCocycle` delegates the bundle topology, local trivializations,
and joint coordinate changes to Mathlib's `FiberBundleCore` construction. Its transition
functions and inverses act jointly continuously on the base and fiber; no topology on the
homeomorphism group of the fiber, and no point in the fiber, is needed. The resulting core's
native `localTriv` and `fiberBundle` provide the actual bundle and its charts.
-/

public section

universe u v w t

open Set

namespace TauCeti

variable {ι : Type u} {B : Type v} {G : Type w} [Group G]
    (U : ι → Set B) (c : ι → ι → B → G)
    (hc : ∀ i j k b, b ∈ U i ∩ U j ∩ U k → c j k b * c i j b = c i k b)

include hc

/-- A group-valued transition cocycle is the identity on each diagonal chart. -/
lemma groupCocycle_self (i : ι) {b : B} (hb : b ∈ U i) : c i i b = 1 :=
  mul_eq_left.mp (hc i i i b ⟨⟨hb, hb⟩, hb⟩)

/-- Reversing an overlap transition inverts the group element. -/
lemma groupCocycle_symm (i j : ι) {b : B} (hb : b ∈ U i ∩ U j) :
    c j i b = (c i j b)⁻¹ := by
  apply eq_inv_iff_mul_eq_one.mpr
  exact (hc i j i b ⟨hb, hb.1⟩).trans (groupCocycle_self U c hc i hb.1)

variable [TopologicalSpace B] [TopologicalSpace G]
    (F : Type t) [TopologicalSpace F] [MulAction G F] [ContinuousSMul G F]
    (hU : ∀ i, IsOpen (U i)) (indexAt : B → ι) (hindex : ∀ b, b ∈ U (indexAt b))
    (hcontinuous : ∀ i j, ContinuousOn (c i j) (U i ∩ U j))

/-- The native fiber bundle core whose transition from chart `i` to chart `j` acts by `c i j`.
The supplied index chooses a cover member at every base point. Only continuity of the action
is required; the fiber may be empty or have no separation properties. -/
def fiberBundleCoreOfGroupCocycle : FiberBundleCore ι B F where
  baseSet := U
  isOpen_baseSet := hU
  indexAt := indexAt
  mem_baseSet_at := hindex
  coordChange i j b v := c i j b • v
  coordChange_self i b hb v := by rw [groupCocycle_self U c hc i hb, one_smul]
  continuousOn_coordChange i j :=
    continuous_smul.comp_continuousOn ((hcontinuous i j).prodMap continuousOn_id)
  coordChange_comp i j k b hb v := by rw [← mul_smul, hc i j k b hb]

/-- Each native local trivialization has the supplied cover member as its base. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_localTriv_baseSet (i : ι) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i).baseSet =
      U i := (rfl)

/-- The bundle core retains the supplied choice of chart. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_indexAt :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).indexAt =
      indexAt := (rfl)

/-- The core's coordinate change is the given group action. -/
@[simp]
lemma fiberBundleCoreOfGroupCocycle_coordChange (i j : ι) (b : B) (v : F) :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).coordChange i j b v =
      c i j b • v := (rfl)

/-- The joint forward coordinate change fixes the base and acts by the overlap cocycle. -/
lemma fiberBundleCoreOfGroupCocycle_trivChange_apply (i j : ι) (p : B × F) :
    (fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).trivChange i j p =
      (p.1, c i j p.1 • p.2) := (rfl)

/-- On an overlap, the inverse joint coordinate change acts by the inverse group element. -/
lemma fiberBundleCoreOfGroupCocycle_trivChange_symm_apply (i j : ι) (p : B × F)
    (hp : p.1 ∈ U i ∩ U j) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).trivChange i j).symm
        p = (p.1, (c i j p.1)⁻¹ • p.2) := by
  exact congrArg (fun g : G ↦ (p.1, g • p.2)) (groupCocycle_symm U c hc i j hp)

/-- The actual native bundle charts have the prescribed group-valued transition function. -/
lemma fiberBundleCoreOfGroupCocycle_localTriv_coordChange (i j : ι) {b : B}
    (hb : b ∈ U i ∩ U j) (v : F) :
    ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv i).coordChange
      ((fiberBundleCoreOfGroupCocycle U c hc F hU indexAt hindex hcontinuous).localTriv j) b v =
        c i j b • v := by
  simp only [Bundle.Trivialization.coordChange, FiberBundleCore.localTriv_symm_apply,
    FiberBundleCore.localTriv_apply, fiberBundleCoreOfGroupCocycle_coordChange,
    fiberBundleCoreOfGroupCocycle_indexAt]
  rw [← mul_smul, hc i (indexAt b) j b ⟨⟨hb.1, hindex b⟩, hb.2⟩]

end TauCeti
