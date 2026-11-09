/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sober

/-!
# Generic points and generizations

In a sober space, the generic points of irreducible components are precisely the points
with no proper generization. Every point of a closed subset is a specialization of such a
generic point of that subset. These facts let one choose component-generic points without
Noetherianity or a dimension argument.
-/

public section

open Set

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] [QuasiSober X] [T0Space X]

/-- In a sober space, the generic points of irreducible components are exactly the points
with no proper generization. -/
theorem mem_genericPoints_iff {x : X} :
    x ∈ genericPoints X ↔ ∀ y : X, y ⤳ x → y = x := by
  constructor
  · intro hx y hy
    have hle : closure ({x} : Set X) ⊆ closure {y} :=
      specializes_iff_closure_subset.mp hy
    exact (hy.antisymm (specializes_iff_closure_subset.mpr
      (hx.2 isIrreducible_singleton.closure hle))).eq
  · intro hx
    refine ⟨isIrreducible_singleton.closure, fun t ht hxt ↦ ?_⟩
    have hgen := ht.isGenericPoint_genericPoint_closure
    have hxmem : x ∈ t := hxt (subset_closure (mem_singleton x))
    have heq : ht.genericPoint = x := hx _ (hgen.specializes (subset_closure hxmem))
    calc
      t ⊆ closure t := subset_closure
      _ = closure {ht.genericPoint} := hgen.def.symm
      _ = closure {x} := by rw [heq]

end TauCeti

/-- Every point of a closed subset of a quasi-sober space is a specialization of a generic
point of an irreducible component of that subset. -/
theorem IsClosed.exists_genericPoint_specializes {X : Type*} [TopologicalSpace X]
    [QuasiSober X] {s : Set X} (hs : IsClosed s) {x : X} (hx : x ∈ s) :
    ∃ z : s, z ∈ genericPoints s ∧ (z : X) ⤳ x := by
  let : QuasiSober s := hs.isClosedEmbedding_subtypeVal.quasiSober
  let C : irreducibleComponents s :=
    ⟨irreducibleComponent (⟨x, hx⟩ : s), irreducibleComponent_mem_irreducibleComponents _⟩
  refine ⟨(genericPoints.ofComponent C).1, (genericPoints.ofComponent C).2, ?_⟩
  exact ((genericPoints.isGenericPoint_ofComponent C).specializes mem_irreducibleComponent).map
    continuous_subtype_val
