/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.RibbonGraph.Basic
public import TauCeti.GroupTheory.Perm.Partition

/-!
# Cycle data of a bipartite ribbon graph

Using `blackDegree`, `whiteDegree`, and `faceDegree` from `TauCeti.Combinatorics.RibbonGraph.Basic`,
this file packages the black-vertex, white-vertex, and face degree multisets into
`BipartiteRibbonGraph.cycleData`, identifies them with `fullCycleType` of `rotB`, `rotW`, and
`facePerm`, and proves isomorphism invariance.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 and §1.5.
-/

open Equiv Equiv.Perm

public section

namespace TauCeti

universe u v

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-! ### Full cycle types of rotations and the face permutation -/

/-- The full cycle type of the black rotation is the multiset of black vertex degrees. -/
theorem fullCycleType_rotB :
    fullCycleType Γ.rotB = (Finset.univ : Finset Γ.B).val.map Γ.blackDegree :=
  Γ.rotB.fullCycleType_eq_map_degree Γ.blackEnd Γ.blackEnd_surjective
    (fun _ _ => Γ.blackEnd_eq_blackEnd_iff.symm) Γ.blackDegree Γ.blackDegree_def

/-- The full cycle type of the white rotation is the multiset of white vertex degrees. -/
theorem fullCycleType_rotW :
    fullCycleType Γ.rotW = (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree :=
  Γ.rotW.fullCycleType_eq_map_degree Γ.whiteEnd Γ.whiteEnd_surjective
    (fun _ _ => Γ.whiteEnd_eq_whiteEnd_iff.symm) Γ.whiteDegree Γ.whiteDegree_def

/-- The full cycle type of the face permutation is the multiset of face degrees. -/
theorem fullCycleType_facePerm :
    fullCycleType Γ.facePerm = (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree :=
  Γ.facePerm.fullCycleType_eq_map_degree (fun e => (Quotient.mk'' e : Γ.Face))
    Quotient.mk''_surjective (fun _ _ => (Quotient.eq'' (s₁ := SameCycle.setoid Γ.facePerm)).symm)
    Γ.faceDegree Γ.faceDegree_def

/-! ### Cycle data of a bipartite ribbon graph -/

/-- The ordered triple of black-vertex, white-vertex, and face degree partitions of `Γ`. -/
def cycleData : Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
    (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
    (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree)

/-- The defining formula for the cycle data of a bipartite ribbon graph. -/
theorem cycleData_def : Γ.cycleData = ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
    (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
    (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree) := (rfl)

/-- The degree partitions of `Γ` are the full cycle types of `rotB`, `rotW`, and `facePerm`. -/
theorem cycleData_eq_fullCycleType :
    Γ.cycleData = (fullCycleType Γ.rotB, fullCycleType Γ.rotW, fullCycleType Γ.facePerm) := by
  rw [cycleData_def, fullCycleType_rotB, fullCycleType_rotW, fullCycleType_facePerm]

/-- Each of the three degree partitions of `Γ` sums to the number of edges. -/
theorem sum_cycleData : (Γ.cycleData.1.sum, Γ.cycleData.2.1.sum, Γ.cycleData.2.2.sum) =
    (Fintype.card Γ.E, Fintype.card Γ.E, Fintype.card Γ.E) := by
  simp [cycleData_def, Γ.sum_blackDegree, Γ.sum_whiteDegree, Γ.sum_faceDegree]

/-- The numbers of parts of the three degree partitions are `|B|`, `|W|`, and `faceCount`. -/
theorem card_cycleData : (Γ.cycleData.1.card, Γ.cycleData.2.1.card, Γ.cycleData.2.2.card) =
    (Fintype.card Γ.B, Fintype.card Γ.W, Γ.faceCount) := by simp [cycleData_def, faceCount_def]

/-- Isomorphic bipartite ribbon graphs have the same cycle data. -/
theorem Iso.cycleData_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Γ.cycleData = Δ.cycleData := by
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;> simp only [cycleData_def, ← Finset.map_univ_equiv φ.black,
    ← Finset.map_univ_equiv φ.white, ← Finset.map_univ_equiv φ.faceEquiv, Finset.map_val,
    Multiset.map_map, Function.comp_apply, Equiv.coe_toEmbedding, φ.blackDegree_eq,
    φ.whiteDegree_eq, φ.faceDegree_eq]

end BipartiteRibbonGraph

end TauCeti
