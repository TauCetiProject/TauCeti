/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Three.Basic
public import TauCeti.KnotTheory.PDCode.Planar
import TauCeti.KnotTheory.PDCode.Reidemeister.Three.Local
import TauCeti.Data.Fin.Basic

/-!
# Planarity under the third Reidemeister move

Replacing the three-crossing triangle preserves its boundary face traversal and the connected
components of the underlying graph. Consequently the third Reidemeister move preserves the
number of faces and planarity, for any surrounding PD-code. Faces and planarity require the
three triangle arcs; preserving graph components requires only the two arcs connecting the
first crossing to the second and the second to the third. The strand heights play no role.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
* S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer (2004), §1.5.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm ReidemeisterThree

variable {n : ℕ} (D : PDCode n) (c : Fin 3 ↪ Fin n)
  (h : D.HasReidemeisterThreeTriangleArcs c)

private def localRotation : Perm (Fin 3 × Fin 4) :=
  Equiv.prodCongrRight fun _ ↦ finRotate 4

private def faceSkeleton : Perm (Fin 3 × Fin 4) :=
  swap (0, 0) (0, 3) * swap (0, 0) (1, 3) * swap (0, 0) (1, 2) *
    swap (0, 0) (2, 2) * swap (0, 0) (2, 1)

private def faceFactors (side : Bool) : List ((Fin 3 × Fin 4) × (Fin 3 × Fin 4)) :=
  if side then
    [((0, 1), (2, 3)), ((0, 1), (1, 0)), ((1, 3), (2, 0)),
      ((2, 2), (0, 2)), ((0, 0), (1, 1))]
  else
    [((0, 2), (2, 0)), ((0, 2), (1, 1)), ((1, 2), (2, 3)),
      ((0, 3), (1, 0)), ((2, 1), (0, 1))]

private def faceFactor (side : Bool) : Perm (Fin 3 × Fin 4) :=
  (if side then reidemeisterThreeSlots⁻¹ * localRotation * reidemeisterThreeSlots
    else localRotation) * localInternalMatching

private theorem faceFactor_eq (side : Bool) :
    faceFactor side = ((faceFactors side).map (Function.uncurry Equiv.swap)).prod *
      faceSkeleton := by
  have hf (p : Fin 3 × Fin 4) := reidemeisterThreeSlots_apply p.1 p.2
  have hi (p : Fin 3 × Fin 4) : reidemeisterThreeSlots⁻¹ p =
      ![![(0, 3), (1, 1), (0, 1), (1, 3)],
        ![(0, 0), (2, 1), (0, 2), (2, 3)],
        ![(1, 0), (2, 2), (1, 2), (2, 0)]] p.1 p.2 :=
    reidemeisterThreeSlots_symm_apply p.1 p.2
  cases side <;> apply Equiv.ext <;> intro p <;>
    simp only [faceFactor, localInternalMatching_def, Bool.false_eq_true, ↓reduceIte,
      Perm.mul_apply, hf, hi] <;>
    revert p <;> decide

private theorem faceFactors_isSwapForest (side : Bool) : (faceFactors side).IsSwapForest := by
  cases side <;> simp only [faceFactors, Bool.false_eq_true, ↓reduceIte,
    List.isSwapForest_cons, List.isSwapForest_nil] <;> decide

private theorem faceFactors_internal (side : Bool) :
    ∀ factor ∈ faceFactors side, localInternal factor.2 := by
  cases side <;> norm_num [faceFactors, localInternal_iff]

private theorem faceSkeleton_internal (p : Fin 3 × Fin 4) (hp : localInternal p) :
    faceSkeleton p = p := by
  revert p
  simp only [localInternal_iff]
  decide

private theorem crossingRotation_split :
    D.crossingRotation = localLift D c localRotation * exteriorSlots D c (fun _ ↦ finRotate 4) := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective y
  rw [crossingRotation_crossing, Perm.mul_apply, ← crossing_apply, exteriorSlots_crossing]
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    simp only [Set.mem_range_self, ↓reduceIte, Perm.one_apply]
    simpa only [localRotation, Equiv.prodCongrRight_apply, finRotate_apply,
      triangleEmbedding_apply] using (localLift_apply D c localRotation (j, s)).symm
  · simp only [hi, ↓reduceIte, finRotate_apply]
    rw [localLift_fixed D c _ hi]

private def skeletonTraversal : Perm (Fin (4 * n)) :=
  localLift D c faceSkeleton * exteriorSlots D c (fun _ ↦ finRotate 4) * outsideEdges D c

include h in
private theorem skeletonTraversal_internal (p : Fin 3 × Fin 4) (hp : localInternal p) :
    skeletonTraversal D c (triangleEmbedding D c p) = triangleEmbedding D c p := by
  rw [skeletonTraversal, Perm.mul_apply, Perm.mul_apply, outsideEdges_internal D c h p hp,
    exteriorSlots_local, localLift_apply, faceSkeleton_internal p hp]

include h in
private theorem faceFactor_orbitCount (side : Bool) :
    orbitCount (localLift D c (faceFactor side) * exteriorSlots D c (fun _ ↦ finRotate 4) *
      outsideEdges D c) + 5 =
      orbitCount (skeletonTraversal D c) := by
  have hlen : (faceFactors side).length = 5 := by cases side <;> rfl
  simpa only [skeletonTraversal, mul_assoc, hlen] using
    localLift_swapForest_orbitCount D c (faceFactor side) faceSkeleton (faceFactors side)
      (exteriorSlots D c (fun _ ↦ finRotate 4) * outsideEdges D c)
      (faceFactors_isSwapForest side) (faceFactor_eq side)
      (fun p hp ↦ by
        simpa only [skeletonTraversal, mul_assoc] using
          skeletonTraversal_internal D c h p.2 (faceFactors_internal side p hp))

include h in
/-- The third Reidemeister move preserves the number of faces of the underlying graph. -/
@[simp] theorem faceCount_reidemeisterThree :
    (D.reidemeisterThree c).faceCount = D.faceCount := by
  have hleft := faceFactor_orbitCount D c h false
  have hright := faceFactor_orbitCount D c h true
  rw [faceFactor, localLift_remove_internal D c _ _
    (localLift_commute_exteriorSlots D c localInternalMatching
      (fun _ ↦ finRotate 4))] at hleft hright
  simp only [Bool.false_eq_true, ↓reduceIte, ← crossingRotation_split] at hleft
  simp only [↓reduceIte, map_mul, map_inv, localLift_slots] at hright
  have hr : (D.reidemeisterThree c).crossingRotation = D.crossingRotation := by
    simp only [crossingRotation_def, reidemeisterThree_halfEdge]
  have heq : (D.reidemeisterThreePerm c).symm.permCongr
      (D.crossingRotation * (D.reidemeisterThreePerm c).permCongr D.edgePair.val) =
      (D.reidemeisterThreePerm c)⁻¹ * localLift D c localRotation *
        D.reidemeisterThreePerm c * exteriorSlots D c (fun _ ↦ finRotate 4) * D.edgePair.val := by
    rw [Equiv.permCongr_eq_mul, Equiv.permCongr_eq_mul, crossingRotation_split D c,
      ← Perm.inv_def]
    have hc := (localLift_commute_exteriorSlots D c reidemeisterThreeSlots (fun _ ↦ finRotate 4)).eq
    rw [localLift_slots] at hc
    calc
      _ = (D.reidemeisterThreePerm c)⁻¹ * localLift D c localRotation *
        (exteriorSlots D c (fun _ ↦ finRotate 4) * D.reidemeisterThreePerm c) *
          D.edgePair.val := by group
      _ = _ := by rw [← hc]; group
  rw [← heq, Equiv.orbitCount_permCongr] at hright
  rw [faceCount_def, faceCount_def, facePerm_def, facePerm_def, hr,
    reidemeisterThree_edgePair]
  calc
    _ = orbitCount (D.crossingRotation *
        (D.reidemeisterThreePerm c).permCongr D.edgePair.val) :=
      TauCeti.orbitCount_mul_comm _ _
    _ = orbitCount (D.crossingRotation * D.edgePair.val) := by omega
    _ = _ := TauCeti.orbitCount_mul_comm _ _

/-! ### Connected components of the underlying graph -/

private def graphOrbit (E : PDCode n) (x : Fin (4 * n)) :
    E.toPermutationTriple.MonodromyOrbit := Quotient.mk _ x

private theorem graphOrbit_triangle (E : PDCode n) (u₀ v₁ u₁ v₂ : Fin 4)
    (h₁ : E.edgePair.val (E.crossing (c 0) u₀) = E.crossing (c 1) v₁)
    (h₂ : E.edgePair.val (E.crossing (c 1) u₁) = E.crossing (c 2) v₂)
    (j : Fin 3) (s : Fin 4) :
    graphOrbit E (E.crossing (c j) s) = graphOrbit E (E.crossing (c 0) 0) := by
  have hv (i : Fin n) (t : Fin 4) :
      graphOrbit E (E.crossing i t) = graphOrbit E (E.crossing i 0) := by
    refine apply_eq_apply_zero_of_add_one
      (f := fun t : Fin 4 ↦ graphOrbit E (E.crossing i t)) ?_ t
    intro t
    simpa only [graphOrbit, toPermutationTriple_σ0, crossing_apply,
      crossingRotation_crossing] using E.toPermutationTriple.mk_σ0_apply (E.crossing i t)
  have he : ∀ x, graphOrbit E (E.edgePair.val x) = graphOrbit E x := by
    intro x
    simpa only [graphOrbit, toPermutationTriple_σ1] using E.toPermutationTriple.mk_σ1_apply x
  have hb : graphOrbit E (E.crossing (c 1) 0) = graphOrbit E (E.crossing (c 0) 0) := by
    rw [← hv (c 1) v₁, ← h₁, he, hv]
  have hc : graphOrbit E (E.crossing (c 2) 0) = graphOrbit E (E.crossing (c 0) 0) := by
    rw [← hv (c 2) v₂, ← h₂, he, hv, hb]
  rw [hv]
  fin_cases j
  · rfl
  · exact hb
  · exact hc

private theorem graphOrbit_perm (E : PDCode n)
    (hconn : ∀ j s, graphOrbit E (D.crossing (c j) s) =
      graphOrbit E (D.crossing (c 0) 0)) (x : Fin (4 * n)) :
    graphOrbit E (D.reidemeisterThreePerm c x) = graphOrbit E x := by
  obtain ⟨y, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective y
  rw [← crossing_apply]
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    rw [reidemeisterThreePerm_apply_crossing]
    exact (hconn _ _).trans (hconn j s).symm
  · rw [reidemeisterThreePerm_crossing_of_notMem D c hi]

/-- The third Reidemeister move keeps the connected components of the underlying graph.
Only the two arcs connecting the first crossing to the second and the second to the third
are required; the third triangle arc is unrestricted.
The equivalence sends the component represented by a half-edge to that represented by the
same half-edge after the move. -/
def reidemeisterThreeMonodromyOrbitEquiv
    (h₀₁ : D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0)
    (h₁₂ : D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3) :
    D.toPermutationTriple.MonodromyOrbit ≃
      (D.reidemeisterThree c).toPermutationTriple.MonodromyOrbit := by
  let E := D.reidemeisterThree c
  -- The selected crossings are connected, so the local rewire acts trivially
  -- on its graph-component labels on both sides of the move.
  have hn₀₁ : E.edgePair.val (D.crossing (c 0) 1) = D.crossing (c 1) 3 := by
    have ht := reidemeisterThree_edgePair_transport D c (D.crossing (c 1) 1)
    rw [h₁₂] at ht
    simpa only [E, reidemeisterThreePerm_apply_crossing, reidemeisterThreeSlots_apply,
      Matrix.cons_val, Prod.fst, Prod.snd]
      using ht
  have hn₁₂ : E.edgePair.val (D.crossing (c 1) 2) = D.crossing (c 2) 0 := by
    have ht := reidemeisterThree_edgePair_transport D c (D.crossing (c 0) 2)
    rw [h₀₁] at ht
    simpa only [E, reidemeisterThreePerm_apply_crossing, reidemeisterThreeSlots_apply,
      Matrix.cons_val, Prod.fst, Prod.snd]
      using ht
  have hρOld : ∀ x, graphOrbit D (D.reidemeisterThreePerm c x) = graphOrbit D x :=
    graphOrbit_perm D c D (graphOrbit_triangle c D 2 0 1 3 h₀₁ h₁₂)
  have hρNew : ∀ x, graphOrbit E (D.reidemeisterThreePerm c x) = graphOrbit E x := by
    apply graphOrbit_perm D c E
    intro j s
    simpa only [E, reidemeisterThree_crossing] using
      graphOrbit_triangle c E 1 3 2 0
        (by simpa only [E, reidemeisterThree_crossing] using hn₀₁)
        (by simpa only [E, reidemeisterThree_crossing] using hn₁₂) j s
  have heOld : ∀ x, graphOrbit D (D.edgePair.val x) = graphOrbit D x := by
    intro x
    simpa only [graphOrbit, toPermutationTriple_σ1] using D.toPermutationTriple.mk_σ1_apply x
  have heNew : ∀ x, graphOrbit E (E.edgePair.val x) = graphOrbit E x := by
    intro x
    simpa only [graphOrbit, toPermutationTriple_σ1] using E.toPermutationTriple.mk_σ1_apply x
  have heOldNew : ∀ x, graphOrbit E (D.edgePair.val x) = graphOrbit E x := by
    intro x
    have hx := heNew (D.reidemeisterThreePerm c x)
    rw [reidemeisterThree_edgePair_transport D c, hρNew, hρNew] at hx
    exact hx
  have heNewOld : ∀ x, graphOrbit D (E.edgePair.val x) = graphOrbit D x := by
    intro x
    obtain ⟨y, rfl⟩ := (D.reidemeisterThreePerm c).surjective x
    rw [reidemeisterThree_edgePair_transport D c, hρOld, hρOld, heOld]
  have hr : E.crossingRotation = D.crossingRotation := by
    simp only [E, crossingRotation_def, reidemeisterThree_halfEdge]
  -- The labels are invariant under both rotation and edge generators. Identity on
  -- half-edges therefore descends to mutually inverse maps of the component quotients.
  refine
    { toFun := Quotient.lift (graphOrbit E) ?_
      invFun := Quotient.lift (graphOrbit D) ?_
      left_inv := Quotient.ind (fun x ↦ rfl)
      right_inv := Quotient.ind (fun x ↦ rfl) }
  · rintro _ x ⟨⟨σ, hσ⟩, rfl⟩
    refine D.toPermutationTriple.apply_eq_of_mem_monodromyGroup (f := graphOrbit E)
      (fun x ↦ ?_) (fun x ↦ ?_) hσ x
    · rw [toPermutationTriple_σ0, ← hr]
      simpa only [graphOrbit, toPermutationTriple_σ0] using E.toPermutationTriple.mk_σ0_apply x
    · simpa only [toPermutationTriple_σ1] using heOldNew x
  · rintro _ x ⟨⟨σ, hσ⟩, rfl⟩
    refine E.toPermutationTriple.apply_eq_of_mem_monodromyGroup (f := graphOrbit D)
      (fun x ↦ ?_) (fun x ↦ ?_) hσ x
    · rw [toPermutationTriple_σ0, hr]
      simpa only [graphOrbit, toPermutationTriple_σ0] using D.toPermutationTriple.mk_σ0_apply x
    · simpa only [toPermutationTriple_σ1] using heNewOld x

variable
  (h₀₁ : D.edgePair.val (D.crossing (c 0) 2) = D.crossing (c 1) 0)
  (h₁₂ : D.edgePair.val (D.crossing (c 1) 1) = D.crossing (c 2) 3)

/-- The graph-component equivalence preserves the half-edge representing a component. -/
@[simp] theorem reidemeisterThreeMonodromyOrbitEquiv_apply (x : Fin (4 * n)) :
    reidemeisterThreeMonodromyOrbitEquiv D c h₀₁ h₁₂ (Quotient.mk _ x) =
      Quotient.mk _ x := (rfl)

/-- The inverse graph-component equivalence also preserves its half-edge representative. -/
@[simp] theorem reidemeisterThreeMonodromyOrbitEquiv_symm_apply (x : Fin (4 * n)) :
    (reidemeisterThreeMonodromyOrbitEquiv D c h₀₁ h₁₂).symm (Quotient.mk _ x) =
      Quotient.mk _ x := (rfl)

/-- The move preserves the number of connected components of the underlying graph when
the first two triangle arcs are present. -/
@[simp] theorem card_monodromyOrbit_reidemeisterThree
    (h₀₁ : D.edgePair.val (D.halfEdge (crossingSlotEquiv n (c 0, 2))) =
      D.halfEdge (crossingSlotEquiv n (c 1, 0)))
    (h₁₂ : D.edgePair.val (D.halfEdge (crossingSlotEquiv n (c 1, 1))) =
      D.halfEdge (crossingSlotEquiv n (c 2, 3))) :
    Nat.card (D.reidemeisterThree c).toPermutationTriple.MonodromyOrbit =
      Nat.card D.toPermutationTriple.MonodromyOrbit :=
  Nat.card_congr (reidemeisterThreeMonodromyOrbitEquiv D c
    (by simpa only [crossing_apply] using h₀₁)
    (by simpa only [crossing_apply] using h₁₂)).symm

include h in
/-- A PD-code is planar exactly when its third Reidemeister replacement is planar. -/
@[simp] theorem isPlanar_reidemeisterThree_iff :
    (D.reidemeisterThree c).IsPlanar ↔ D.IsPlanar := by
  have ht := (hasReidemeisterThreeTriangleArcs_iff D c).mp h
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq,
    faceCount_reidemeisterThree D c h,
    card_monodromyOrbit_reidemeisterThree D c
      (by simpa only [crossing_apply] using ht.1)
      (by simpa only [crossing_apply] using ht.2.1)]

end TauCeti.PDCode
