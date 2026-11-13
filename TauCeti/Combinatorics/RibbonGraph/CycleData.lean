/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.CycleData
public import TauCeti.Combinatorics.RibbonGraph.Classification

/-!
# Cell degrees and cycle data of a bipartite ribbon graph

Every black vertex `b`, white vertex `w`, and face `f` of a finite bipartite ribbon graph `Γ` is a
single cycle of `rotB`, `rotW`, and `facePerm` on the edge set `Γ.E`. Completing `blackDegree` and
`whiteDegree` from `TauCeti.Combinatorics.RibbonGraph.Basic`, this file defines `faceDegree` as the
number of edges in a face orbit — half the number of black-white boundary steps around the face — so
that the face degrees also sum to `|E|`.

Packaging the multisets of black vertex degrees, white vertex degrees, and face degrees gives the
computable degree-partition triple `TauCeti.BipartiteRibbonGraph.cycleData`. Its three entries are
the full cycle types of `rotB`, `rotW`, and `facePerm`, so numbering the edges identifies
`Γ.cycleData` with the ordered cycle data `(λ₀, λ₁, λ∞)` of `Γ.toPermutationTriple ν`, independently
of the numbering, and graph isomorphisms preserve `cycleData`.

## Main definitions

* `TauCeti.BipartiteRibbonGraph.faceDegree`: the number of edges in a face orbit of `Γ`.
* `TauCeti.BipartiteRibbonGraph.cycleData`: the ordered triple of multisets of black vertex
  degrees, white vertex degrees, and face degrees.

## Main results

* `TauCeti.BipartiteRibbonGraph.fullCycleType_rotB`,
  `TauCeti.BipartiteRibbonGraph.fullCycleType_rotW`,
  `TauCeti.BipartiteRibbonGraph.fullCycleType_facePerm`: the full cycle types of the three
  permutations are the multisets of black vertex degrees, white vertex degrees, and face degrees.
* `TauCeti.BipartiteRibbonGraph.cycleData_toPermutationTriple`,
  `TauCeti.PermutationTriple.cycleData_ribbonGraph`: passing between ribbon graphs and permutation
  triples preserves `cycleData`.
* `TauCeti.BipartiteRibbonGraph.Iso.cycleData_eq`: isomorphic ribbon graphs have the same cycle
  data.
-/

open Equiv Equiv.Perm

public section

namespace TauCeti

universe u v

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-! ### Face degrees -/

/-- Equality of faces of a finite bipartite ribbon graph is decidable, since lying in the same cycle
of `facePerm` is decidable. -/
instance instDecidableEqFace : DecidableEq Γ.Face :=
  @Quotient.decidableEq _ _ (inferInstanceAs (DecidableRel (SameCycle Γ.facePerm)))

/-- The degree of a face of a bipartite ribbon graph: the number of edges in that orbit of
`facePerm`. Since each edge contributes one black-to-white step and one white-to-black step to the
boundary walk of its face, the boundary walk has length `2 * faceDegree f`, and the face degrees sum
to `|E|` (`TauCeti.BipartiteRibbonGraph.sum_faceDegree`). -/
def faceDegree (f : Γ.Face) : ℕ :=
  Fintype.card {e : Γ.E // (Quotient.mk'' e : Γ.Face) = f}

/-- The degree of a face is the number of edges belonging to that face orbit. -/
theorem faceDegree_def (f : Γ.Face) :
    Γ.faceDegree f = Fintype.card {e : Γ.E // (Quotient.mk'' e : Γ.Face) = f} :=
  (rfl)

/-- Every face orbit is nonempty, so every face has positive degree. -/
theorem faceDegree_pos (f : Γ.Face) : 0 < Γ.faceDegree f := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep f
  exact Fintype.card_pos_iff.mpr ⟨⟨e, rfl⟩⟩

/-- Every edge belongs to a unique face orbit, so the face degrees sum to the number of edges. -/
theorem sum_faceDegree : ∑ f, Γ.faceDegree f = Fintype.card Γ.E := by
  simp only [faceDegree]
  rw [← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv fun e : Γ.E => (Quotient.mk'' e : Γ.Face))

/-- An isomorphism of bipartite ribbon graphs preserves the degree of each face. -/
@[simp]
theorem Iso.faceDegree_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) (f : Γ.Face) :
    Δ.faceDegree (φ.faceEquiv f) = Γ.faceDegree f := by
  symm
  exact Fintype.card_congr <| φ.edge.subtypeEquiv fun e => by
    rw [← φ.faceEquiv_mk, φ.faceEquiv.injective.eq_iff]

/-! ### Full cycle types of rotations and the face permutation -/

/-- The full cycle type of the black rotation is the multiset of black vertex degrees. -/
theorem fullCycleType_rotB :
    fullCycleType Γ.rotB = (Finset.univ : Finset Γ.B).val.map Γ.blackDegree := by
  rw [fullCycleType_eq_map_card_filter Γ.rotB Γ.blackEnd fun _ _ => Γ.blackEnd_eq_blackEnd_iff.symm]
  refine Multiset.map_congr
    (congrArg Finset.val (by convert Finset.image_univ_of_surjective Γ.blackEnd_surjective))
    fun b _ => ?_
  rw [blackDegree_def, Fintype.card_subtype]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- The full cycle type of the white rotation is the multiset of white vertex degrees. -/
theorem fullCycleType_rotW :
    fullCycleType Γ.rotW = (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree := by
  rw [fullCycleType_eq_map_card_filter Γ.rotW Γ.whiteEnd fun _ _ => Γ.whiteEnd_eq_whiteEnd_iff.symm]
  refine Multiset.map_congr
    (congrArg Finset.val (by convert Finset.image_univ_of_surjective Γ.whiteEnd_surjective))
    fun w _ => ?_
  rw [whiteDegree_def, Fintype.card_subtype]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-- The full cycle type of the face permutation is the multiset of face degrees. -/
theorem fullCycleType_facePerm :
    fullCycleType Γ.facePerm = (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree := by
  have hm : ∀ x y : Γ.E, Γ.facePerm.SameCycle x y ↔
      (Quotient.mk'' x : Γ.Face) = Quotient.mk'' y :=
    fun _ _ => (Quotient.eq'' (s₁ := SameCycle.setoid Γ.facePerm)).symm
  rw [fullCycleType_eq_map_card_filter Γ.facePerm (fun e => (Quotient.mk'' e : Γ.Face)) hm]
  refine Multiset.map_congr
    (congrArg Finset.val (by convert Finset.image_univ_of_surjective Quotient.mk''_surjective))
    fun f _ => ?_
  rw [faceDegree_def, Fintype.card_subtype]
  congr 1
  exact Finset.filter_congr_decidable _ _ _

/-! ### Cycle data of a bipartite ribbon graph -/

/-- The ordered triple of degree partitions of a bipartite ribbon graph: the multiset of black
vertex degrees, the multiset of white vertex degrees, and the multiset of face degrees. -/
@[expose] def cycleData : Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
    (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
    (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree)

/-- The defining formula for the cycle data of a bipartite ribbon graph. -/
theorem cycleData_def :
    Γ.cycleData =
      ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
        (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
        (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree) :=
  (rfl)

/-- The three degree partitions of `Γ` are the full cycle types of `rotB`, `rotW`, and `facePerm`.
-/
theorem cycleData_eq_fullCycleType :
    Γ.cycleData = (fullCycleType Γ.rotB, fullCycleType Γ.rotW, fullCycleType Γ.facePerm) := by
  rw [cycleData_def, fullCycleType_rotB, fullCycleType_rotW, fullCycleType_facePerm]

/-- Each of the three degree partitions of `Γ` sums to the number of edges. -/
theorem sum_cycleData :
    (Γ.cycleData.1.sum, Γ.cycleData.2.1.sum, Γ.cycleData.2.2.sum) =
      (Fintype.card Γ.E, Fintype.card Γ.E, Fintype.card Γ.E) := by
  rw [cycleData_def, ← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum,
    ← Finset.sum_eq_multiset_sum, Γ.sum_blackDegree, Γ.sum_whiteDegree, Γ.sum_faceDegree]

/-- The numbers of parts of the three degree partitions are `|B|`, `|W|`, and the face count. -/
theorem card_cycleData :
    (Γ.cycleData.1.card, Γ.cycleData.2.1.card, Γ.cycleData.2.2.card) =
      (Fintype.card Γ.B, Fintype.card Γ.W, Γ.faceCount) := by
  simp [cycleData_def, faceCount_def]

/-- Numbering the edges of a bipartite ribbon graph gives a permutation triple whose cycle data is
the degree-partition triple of the graph. -/
@[simp]
theorem cycleData_toPermutationTriple {n : ℕ} (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).cycleData = Γ.cycleData := by
  apply Prod.ext
  · rw [PermutationTriple.cycleData_σ0, ← fullCycleType_def, toPermutationTriple_σ0,
      fullCycleType_permCongr, fullCycleType_rotB, cycleData_def]
  · apply Prod.ext
    · rw [PermutationTriple.cycleData_σ1, ← fullCycleType_def, toPermutationTriple_σ1,
        fullCycleType_permCongr, fullCycleType_rotW, cycleData_def]
    · rw [PermutationTriple.cycleData_σinf, ← fullCycleType_def, toPermutationTriple_σinf,
        fullCycleType_permCongr, fullCycleType_facePerm, cycleData_def]

/-- Isomorphic bipartite ribbon graphs have the same cycle data. -/
theorem Iso.cycleData_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Γ.cycleData = Δ.cycleData := by
  let ν := Fintype.equivFin Γ.E
  let μ := φ.edge.symm.trans ν
  rw [← Γ.cycleData_toPermutationTriple ν, ← Δ.cycleData_toPermutationTriple μ]
  exact PermutationTriple.cycleData_eq_of_equivalent (equivalent_toPermutationTriple_of_iso φ ν μ)

end BipartiteRibbonGraph

namespace PermutationTriple

/-- Passing from a permutation triple to its bipartite ribbon graph preserves the cycle data. -/
@[simp]
theorem cycleData_ribbonGraph {n : ℕ} (t : PermutationTriple n) :
    t.ribbonGraph.cycleData = t.cycleData := by
  rw [← t.ribbonGraph.cycleData_toPermutationTriple (Equiv.refl (Fin n)),
    t.toPermutationTriple_ribbonGraph]

end PermutationTriple

end TauCeti
