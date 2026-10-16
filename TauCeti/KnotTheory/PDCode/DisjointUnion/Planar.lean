/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.DisjointUnion.Basic
public import TauCeti.KnotTheory.PDCode.Planar

/-!
# Planarity of disjoint unions of PD-codes

Placing diagrams in disjoint discs preserves planarity, and a disjoint union is planar only
if both summands are planar. This lets a planar local replacement on isolated components be
used inside an arbitrary planar surrounding diagram.

The crossing rotation and face traversal act separately on the two blocks of half-edges.
The graph components correspond to the disjoint union of the summands' graph components;
this is proved on monodromy orbits, without identifying the monodromy group with a product
(it may be a proper subdirect product). Face counts are additive, and the Euler bound for
each summand gives the converse of planarity preservation. Crossing-free circles contribute
neither graph components nor faces, so the results include diagrams without crossings.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.3 (rotation systems) and §1.5.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n m : ℕ} (D : PDCode n) (E : PDCode m)

/-- The crossing rotation acts independently on the two summands. -/
@[simp]
theorem crossingRotation_disjointUnion :
    (D.disjointUnion E).crossingRotation =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr D.crossingRotation E.crossingRotation) := by
  ext x
  obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
  rcases x with x | x
  · obtain ⟨x, rfl⟩ := D.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv n).surjective x
    rw [← D.crossing_apply, ← crossing_disjointUnion_castAdd, crossing_apply,
      crossingRotation_crossing]
    simp [crossing_apply]
  · obtain ⟨x, rfl⟩ := E.halfEdge.surjective x
    obtain ⟨⟨i, slot⟩, rfl⟩ := (crossingSlotEquiv m).surjective x
    rw [← E.crossing_apply, ← crossing_disjointUnion_natAdd, crossing_apply,
      crossingRotation_crossing]
    simp [crossing_apply]

/-- Face traversal stays within each summand and follows its original face traversal. -/
@[simp]
theorem facePerm_disjointUnion :
    (D.disjointUnion E).facePerm =
      (disjointUnionHalfEdgeEquiv n m).permCongr
        (Perm.sumCongr D.facePerm E.facePerm) := by
  simp only [facePerm_def, crossingRotation_disjointUnion, disjointUnion_edgePair_val,
    ← permCongr_mul, Perm.sumCongr_mul]

/-- The faces of disjoint diagrams are counted independently. -/
@[simp]
theorem faceCount_disjointUnion :
    (D.disjointUnion E).faceCount = D.faceCount + E.faceCount := by
  simp only [faceCount_def, facePerm_disjointUnion, orbitCount_permCongr, orbitCount_sumCongr]

private abbrev splitGraphOrbit : Fin (4 * (n + m)) →
    D.toPermutationTriple.MonodromyOrbit ⊕ E.toPermutationTriple.MonodromyOrbit :=
  Sum.map (Quotient.mk _) (Quotient.mk _) ∘ (disjointUnionHalfEdgeEquiv n m).symm

private theorem splitGraphOrbit_rotation (x : Fin (4 * (n + m))) :
    splitGraphOrbit D E ((D.disjointUnion E).crossingRotation x) = splitGraphOrbit D E x := by
  obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
  rw [crossingRotation_disjointUnion]
  rcases x with x | x <;>
    simp only [splitGraphOrbit, Function.comp_apply, permCongr_apply, symm_apply_apply,
      Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  · rw [← toPermutationTriple_σ0]
    exact congrArg Sum.inl (D.toPermutationTriple.mk_σ0_apply x)
  · rw [← toPermutationTriple_σ0]
    exact congrArg Sum.inr (E.toPermutationTriple.mk_σ0_apply x)

private theorem splitGraphOrbit_edgePair (x : Fin (4 * (n + m))) :
    splitGraphOrbit D E ((D.disjointUnion E).edgePair.val x) = splitGraphOrbit D E x := by
  obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
  rw [disjointUnion_edgePair_val]
  rcases x with x | x <;>
    simp only [splitGraphOrbit, Function.comp_apply, permCongr_apply, symm_apply_apply,
      Perm.sumCongr_apply, Sum.map_inl, Sum.map_inr]
  · rw [← toPermutationTriple_σ1]
    exact congrArg Sum.inl (D.toPermutationTriple.mk_σ1_apply x)
  · rw [← toPermutationTriple_σ1]
    exact congrArg Sum.inr (E.toPermutationTriple.mk_σ1_apply x)

private abbrev unionGraphOrbit (x : Fin (4 * n) ⊕ Fin (4 * m)) :
    (D.disjointUnion E).toPermutationTriple.MonodromyOrbit :=
  Quotient.mk _ (disjointUnionHalfEdgeEquiv n m x)

private theorem unionGraphOrbit_rotation (x : Fin (4 * n) ⊕ Fin (4 * m)) :
    unionGraphOrbit D E (Perm.sumCongr D.crossingRotation E.crossingRotation x) =
      unionGraphOrbit D E x := by
  have h := (D.disjointUnion E).toPermutationTriple.mk_σ0_apply
    (disjointUnionHalfEdgeEquiv n m x)
  simpa only [unionGraphOrbit, toPermutationTriple_σ0, crossingRotation_disjointUnion,
    permCongr_apply, symm_apply_apply] using h

private theorem unionGraphOrbit_edgePair (x : Fin (4 * n) ⊕ Fin (4 * m)) :
    unionGraphOrbit D E (Perm.sumCongr D.edgePair.val E.edgePair.val x) =
      unionGraphOrbit D E x := by
  have h := (D.disjointUnion E).toPermutationTriple.mk_σ1_apply
    (disjointUnionHalfEdgeEquiv n m x)
  simpa only [unionGraphOrbit, toPermutationTriple_σ1, disjointUnion_edgePair_val,
    permCongr_apply, symm_apply_apply] using h

private theorem splitGraphOrbit_congr {x y : Fin (4 * (n + m))}
    (h : MulAction.orbitRel (D.disjointUnion E).toPermutationTriple.monodromyGroup
      (Fin (4 * (n + m))) x y) : splitGraphOrbit D E x = splitGraphOrbit D E y := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := h
  exact (D.disjointUnion E).toPermutationTriple.apply_eq_of_mem_monodromyGroup
    (fun z => by simpa only [toPermutationTriple_σ0] using splitGraphOrbit_rotation D E z)
    (fun z => by simpa only [toPermutationTriple_σ1] using splitGraphOrbit_edgePair D E z) hσ y

private theorem unionGraphOrbit_inl_congr {x y : Fin (4 * n)}
    (h : MulAction.orbitRel D.toPermutationTriple.monodromyGroup (Fin (4 * n)) x y) :
    unionGraphOrbit D E (.inl x) = unionGraphOrbit D E (.inl y) := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := h
  apply D.toPermutationTriple.apply_eq_of_mem_monodromyGroup
    (f := fun x => unionGraphOrbit D E (.inl x)) _ _ hσ y
  · intro z
    simpa only [toPermutationTriple_σ0, Perm.sumCongr_apply, Sum.map_inl] using
      unionGraphOrbit_rotation D E (.inl z)
  · intro z
    simpa only [toPermutationTriple_σ1, Perm.sumCongr_apply, Sum.map_inl] using
      unionGraphOrbit_edgePair D E (.inl z)

private theorem unionGraphOrbit_inr_congr {x y : Fin (4 * m)}
    (h : MulAction.orbitRel E.toPermutationTriple.monodromyGroup (Fin (4 * m)) x y) :
    unionGraphOrbit D E (.inr x) = unionGraphOrbit D E (.inr y) := by
  obtain ⟨⟨σ, hσ⟩, rfl⟩ := h
  apply E.toPermutationTriple.apply_eq_of_mem_monodromyGroup
    (f := fun x => unionGraphOrbit D E (.inr x)) _ _ hσ y
  · intro z
    simpa only [toPermutationTriple_σ0, Perm.sumCongr_apply, Sum.map_inr] using
      unionGraphOrbit_rotation D E (.inr z)
  · intro z
    simpa only [toPermutationTriple_σ1, Perm.sumCongr_apply, Sum.map_inr] using
      unionGraphOrbit_edgePair D E (.inr z)

/-- The graph components of a disjoint union are exactly the components of its two summands.
This correspondence includes empty blocks of half-edges. -/
def disjointUnionMonodromyOrbitEquiv :
    (D.disjointUnion E).toPermutationTriple.MonodromyOrbit ≃
      D.toPermutationTriple.MonodromyOrbit ⊕ E.toPermutationTriple.MonodromyOrbit where
  toFun := Quotient.lift (splitGraphOrbit D E) (fun _ _ => splitGraphOrbit_congr D E)
  invFun := Sum.elim
    (Quotient.lift (fun x => unionGraphOrbit D E (.inl x))
      (fun _ _ => unionGraphOrbit_inl_congr D E))
    (Quotient.lift (fun x => unionGraphOrbit D E (.inr x))
      (fun _ _ => unionGraphOrbit_inr_congr D E))
  left_inv := Quotient.ind (fun x => by
    obtain ⟨x, rfl⟩ := (disjointUnionHalfEdgeEquiv n m).surjective x
    rcases x with x | x <;> simp [splitGraphOrbit, unionGraphOrbit])
  right_inv := by
    rintro (q | q) <;> induction q using Quotient.inductionOn <;>
      simp [splitGraphOrbit, unionGraphOrbit]

/-- A representative in the first block maps to its original graph component. -/
@[simp]
theorem disjointUnionMonodromyOrbitEquiv_inl (x : Fin (4 * n)) :
    disjointUnionMonodromyOrbitEquiv D E
        (Quotient.mk _ (disjointUnionHalfEdgeEquiv n m (.inl x))) =
      .inl (Quotient.mk _ x) := by
  simp [disjointUnionMonodromyOrbitEquiv]

/-- A representative in the second block maps to its original graph component. -/
@[simp]
theorem disjointUnionMonodromyOrbitEquiv_inr (x : Fin (4 * m)) :
    disjointUnionMonodromyOrbitEquiv D E
        (Quotient.mk _ (disjointUnionHalfEdgeEquiv n m (.inr x))) =
      .inr (Quotient.mk _ x) := by
  simp [disjointUnionMonodromyOrbitEquiv]

/-- The inverse component correspondence includes the first block's representative. -/
@[simp]
theorem disjointUnionMonodromyOrbitEquiv_symm_inl (x : Fin (4 * n)) :
    (disjointUnionMonodromyOrbitEquiv D E).symm (.inl (Quotient.mk _ x)) =
      Quotient.mk _ (disjointUnionHalfEdgeEquiv n m (.inl x)) :=
  (disjointUnionMonodromyOrbitEquiv D E).symm_apply_eq.mpr
    (disjointUnionMonodromyOrbitEquiv_inl D E x).symm

/-- The inverse component correspondence includes the second block's representative. -/
@[simp]
theorem disjointUnionMonodromyOrbitEquiv_symm_inr (x : Fin (4 * m)) :
    (disjointUnionMonodromyOrbitEquiv D E).symm (.inr (Quotient.mk _ x)) =
      Quotient.mk _ (disjointUnionHalfEdgeEquiv n m (.inr x)) :=
  (disjointUnionMonodromyOrbitEquiv D E).symm_apply_eq.mpr
    (disjointUnionMonodromyOrbitEquiv_inr D E x).symm

/-- The number of graph components is additive under disjoint union. -/
@[simp]
theorem card_monodromyOrbit_disjointUnion :
    Nat.card (D.disjointUnion E).toPermutationTriple.MonodromyOrbit =
      Nat.card D.toPermutationTriple.MonodromyOrbit +
        Nat.card E.toPermutationTriple.MonodromyOrbit := by
  rw [Nat.card_congr (disjointUnionMonodromyOrbitEquiv D E), Nat.card_sum]

/-- A disjoint union is planar exactly when both summands are planar. The converse uses
the Euler bound separately on each summand, so a deficit of faces cannot cancel. -/
@[simp]
theorem isPlanar_disjointUnion :
    (D.disjointUnion E).IsPlanar ↔ D.IsPlanar ∧ E.IsPlanar := by
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq,
    faceCount_disjointUnion, card_monodromyOrbit_disjointUnion]
  have hD := D.faceCount_le
  have hE := E.faceCount_le
  omega

end TauCeti.PDCode
