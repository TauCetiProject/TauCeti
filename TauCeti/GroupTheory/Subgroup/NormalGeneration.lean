/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.IsPerfect
public import Mathlib.GroupTheory.Subgroup.Centralizer

/-!
# Normal generators of perfect groups

The product of two generators normally generates a perfect group. In the quotient by
its normal closure, the generator images are inverses and hence commute. This makes the
quotient both commutative and perfect, so it is trivial.

This supplies normal-generation hypotheses for the prime-degree action criterion used
in the CFSG basic-properties roadmap.
-/

public section

namespace Subgroup

variable {G : Type*} [Group G] [Group.IsPerfect G]

/-- The product of two generators normally generates a perfect group. -/
theorem normalClosure_mul_eq_top (a b : G) (hgen : closure ({a, b} : Set G) = ⊤) :
    normalClosure ({a * b} : Set G) = ⊤ := by
  let N := normalClosure ({a * b} : Set G)
  let q := QuotientGroup.mk' N
  have hab : q a * q b = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff (a * b)).mpr
      (subset_normalClosure (Set.mem_singleton _))
  have hcomm : Commute (q a) (q b) := by
    change q a * q b = q b * q a
    rw [hab, mul_eq_one_comm.mp hab]
  have hmap := congrArg (Subgroup.map q) hgen
  rw [MonoidHom.map_closure, Set.image_pair, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective q (QuotientGroup.mk'_surjective N)] at hmap
  have hc : IsMulCommutative (closure ({q a, q b} : Set (G ⧸ N))) :=
    isMulCommutative_closure (Set.pairwise_pair.mpr (fun _ ↦ ⟨hcomm, hcomm.symm⟩))
  have hsurj : Function.Surjective (closure ({q a, q b} : Set (G ⧸ N))).subtype := by
    intro x
    exact ⟨⟨x, by rw [hmap]; trivial⟩, rfl⟩
  have : IsMulCommutative (G ⧸ N) := hsurj.isMulCommutative hc
  apply top_unique
  intro g _
  exact (QuotientGroup.eq_one_iff g).mp (Subsingleton.elim _ _)

end Subgroup
