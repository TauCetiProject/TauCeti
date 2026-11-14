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

Completing `blackDegree` and `whiteDegree` from `TauCeti.Combinatorics.RibbonGraph.Basic`, this
file defines `faceDegree` as the number of edges in a face orbit of `facePerm` and packages the
black-vertex, white-vertex, and face degree multisets into `BipartiteRibbonGraph.cycleData`. Its
entries equal `fullCycleType` of `rotB`, `rotW`, and `facePerm`, so edge numberings identify
`Γ.cycleData` with `(Γ.toPermutationTriple ν).cycleData` and graph isomorphisms preserve it.

## Main definitions and results

* `TauCeti.BipartiteRibbonGraph.faceDegree`, `TauCeti.BipartiteRibbonGraph.cycleData`.
* `TauCeti.BipartiteRibbonGraph.fullCycleType_rotB`, `fullCycleType_rotW`, `fullCycleType_facePerm`.
* `TauCeti.BipartiteRibbonGraph.cycleData_toPermutationTriple`,
  `PermutationTriple.cycleData_ribbonGraph`, `BipartiteRibbonGraph.Iso.cycleData_eq`.
-/

open Equiv Equiv.Perm

public section

namespace TauCeti

universe u v

namespace BipartiteRibbonGraph

variable (Γ : BipartiteRibbonGraph.{u})

/-! ### Face degrees -/

/-- Equality of faces of a finite bipartite ribbon graph is decidable. -/
instance instDecidableEqFace : DecidableEq Γ.Face :=
  @Quotient.decidableEq _ _ (inferInstanceAs (DecidableRel (SameCycle Γ.facePerm)))

/-- The degree of a face of `Γ`: the number of edges in that orbit of `facePerm`. -/
def faceDegree (f : Γ.Face) : ℕ := Fintype.card {e : Γ.E // (Quotient.mk'' e : Γ.Face) = f}

/-- The degree of a face is the number of edges belonging to that face orbit. -/
theorem faceDegree_def (f : Γ.Face) :
    Γ.faceDegree f = Fintype.card {e : Γ.E // (Quotient.mk'' e : Γ.Face) = f} := (rfl)

/-- Every face orbit is nonempty, so every face has positive degree. -/
theorem faceDegree_pos (f : Γ.Face) : 0 < Γ.faceDegree f := by
  obtain ⟨e, rfl⟩ := Quotient.exists_rep f; exact Fintype.card_pos_iff.mpr ⟨⟨e, rfl⟩⟩

/-- Every edge belongs to a unique face orbit, so the face degrees sum to `|E|`. -/
theorem sum_faceDegree : ∑ f, Γ.faceDegree f = Fintype.card Γ.E := by
  simp only [faceDegree, ← Fintype.card_sigma]
  exact Fintype.card_congr (Equiv.sigmaFiberEquiv fun e : Γ.E => (Quotient.mk'' e : Γ.Face))

/-- An isomorphism of bipartite ribbon graphs preserves the degree of each face. -/
@[simp] theorem Iso.faceDegree_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) (f : Γ.Face) : Δ.faceDegree (φ.faceEquiv f) = Γ.faceDegree f :=
  (Fintype.card_congr <| φ.edge.subtypeEquiv fun e => by
    rw [← φ.faceEquiv_mk, φ.faceEquiv.injective.eq_iff]).symm

/-! ### Full cycle types of rotations and the face permutation -/

private theorem fullCycleType_eq_map_degree {α : Type*} [Fintype α] [DecidableEq α]
    (σ : Perm Γ.E) (q : Γ.E → α) (hq : Function.Surjective q)
    (hm : ∀ x y, σ.SameCycle x y ↔ q x = q y) (d : α → ℕ)
    (hd : ∀ a, d a = Fintype.card {e : Γ.E // q e = a}) :
    fullCycleType σ = (Finset.univ : Finset α).val.map d := by
  rw [fullCycleType_eq_map_card_filter σ q hm]
  refine Multiset.map_congr (congrArg Finset.val (by convert Finset.image_univ_of_surjective hq))
    fun a _ => ?_
  rw [hd a, Fintype.card_subtype]
  exact congrArg Finset.card (Finset.filter_congr_decidable _ _ _)

/-- The full cycle type of the black rotation is the multiset of black vertex degrees. -/
theorem fullCycleType_rotB :
    fullCycleType Γ.rotB = (Finset.univ : Finset Γ.B).val.map Γ.blackDegree :=
  Γ.fullCycleType_eq_map_degree Γ.rotB Γ.blackEnd Γ.blackEnd_surjective
    (fun _ _ => Γ.blackEnd_eq_blackEnd_iff.symm) Γ.blackDegree Γ.blackDegree_def

/-- The full cycle type of the white rotation is the multiset of white vertex degrees. -/
theorem fullCycleType_rotW :
    fullCycleType Γ.rotW = (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree :=
  Γ.fullCycleType_eq_map_degree Γ.rotW Γ.whiteEnd Γ.whiteEnd_surjective
    (fun _ _ => Γ.whiteEnd_eq_whiteEnd_iff.symm) Γ.whiteDegree Γ.whiteDegree_def

/-- The full cycle type of the face permutation is the multiset of face degrees. -/
theorem fullCycleType_facePerm :
    fullCycleType Γ.facePerm = (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree :=
  Γ.fullCycleType_eq_map_degree Γ.facePerm (fun e => (Quotient.mk'' e : Γ.Face))
    Quotient.mk''_surjective (fun _ _ => (Quotient.eq'' (s₁ := SameCycle.setoid Γ.facePerm)).symm)
    Γ.faceDegree Γ.faceDegree_def

/-! ### Cycle data of a bipartite ribbon graph -/

/-- The ordered triple of black-vertex, white-vertex, and face degree partitions of `Γ`. -/
@[expose] def cycleData : Multiset ℕ × Multiset ℕ × Multiset ℕ :=
  ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
    (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
    (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree)

/-- The defining formula for the cycle data of a bipartite ribbon graph. -/
theorem cycleData_def :
    Γ.cycleData = ((Finset.univ : Finset Γ.B).val.map Γ.blackDegree,
      (Finset.univ : Finset Γ.W).val.map Γ.whiteDegree,
      (Finset.univ : Finset Γ.Face).val.map Γ.faceDegree) := (rfl)

/-- The degree partitions of `Γ` are the full cycle types of `rotB`, `rotW`, and `facePerm`. -/
theorem cycleData_eq_fullCycleType :
    Γ.cycleData = (fullCycleType Γ.rotB, fullCycleType Γ.rotW, fullCycleType Γ.facePerm) := by
  rw [cycleData_def, fullCycleType_rotB, fullCycleType_rotW, fullCycleType_facePerm]

/-- Each of the three degree partitions of `Γ` sums to the number of edges. -/
theorem sum_cycleData :
    (Γ.cycleData.1.sum, Γ.cycleData.2.1.sum, Γ.cycleData.2.2.sum) =
      (Fintype.card Γ.E, Fintype.card Γ.E, Fintype.card Γ.E) := by
  rw [cycleData_def, ← Finset.sum_eq_multiset_sum, ← Finset.sum_eq_multiset_sum,
    ← Finset.sum_eq_multiset_sum, Γ.sum_blackDegree, Γ.sum_whiteDegree, Γ.sum_faceDegree]

/-- The numbers of parts of the three degree partitions are `|B|`, `|W|`, and `faceCount`. -/
theorem card_cycleData :
    (Γ.cycleData.1.card, Γ.cycleData.2.1.card, Γ.cycleData.2.2.card) =
      (Fintype.card Γ.B, Fintype.card Γ.W, Γ.faceCount) := by simp [cycleData_def, faceCount_def]

/-- Numbering the edges of `Γ` gives a permutation triple with cycle data `Γ.cycleData`. -/
@[simp] theorem cycleData_toPermutationTriple {n : ℕ} (ν : Γ.E ≃ Fin n) :
    (Γ.toPermutationTriple ν).cycleData = Γ.cycleData :=
  Prod.ext (by rw [PermutationTriple.cycleData_σ0, ← fullCycleType_def, toPermutationTriple_σ0,
      fullCycleType_permCongr, fullCycleType_rotB, cycleData_def]) <|
  Prod.ext (by rw [PermutationTriple.cycleData_σ1, ← fullCycleType_def, toPermutationTriple_σ1,
      fullCycleType_permCongr, fullCycleType_rotW, cycleData_def])
    (by rw [PermutationTriple.cycleData_σinf, ← fullCycleType_def, toPermutationTriple_σinf,
      fullCycleType_permCongr, fullCycleType_facePerm, cycleData_def])

/-- Isomorphic bipartite ribbon graphs have the same cycle data. -/
theorem Iso.cycleData_eq {Γ : BipartiteRibbonGraph.{u}} {Δ : BipartiteRibbonGraph.{v}}
    (φ : Γ.Iso Δ) : Γ.cycleData = Δ.cycleData := by
  let ν := Fintype.equivFin Γ.E
  rw [← Γ.cycleData_toPermutationTriple ν, ← Δ.cycleData_toPermutationTriple (φ.edge.symm.trans ν)]
  exact PermutationTriple.cycleData_eq_of_equivalent (equivalent_toPermutationTriple_of_iso φ ν _)

end BipartiteRibbonGraph

namespace PermutationTriple

/-- Passing from a permutation triple to its bipartite ribbon graph preserves the cycle data. -/
@[simp] theorem cycleData_ribbonGraph {n : ℕ} (t : PermutationTriple n) :
    t.ribbonGraph.cycleData = t.cycleData := by
  rw [← t.ribbonGraph.cycleData_toPermutationTriple (Equiv.refl (Fin n)),
    t.toPermutationTriple_ribbonGraph]

end PermutationTriple

end TauCeti
