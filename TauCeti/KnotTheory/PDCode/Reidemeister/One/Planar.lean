/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.One.Basic
public import TauCeti.KnotTheory.PDCode.Planar
import TauCeti.Data.Fin.Basic

/-!
# Planarity of arc kink insertion

Inserting a Reidemeister-I kink into an arc adds one vertex, two edges and one face to the
crossing graph, without changing its connected components. Thus it preserves the Euler
criterion for planarity in both directions. The component comparison here concerns the
crossing graph, not the link components: every new half-edge belongs to the old graph
component containing the cut arc.

The face calculation explicitly splices three new darts into the old face traversals and
leaves the fourth as a new singleton face. The component comparison retains the old dart
representatives and assigns all four new darts to the component of the cut arc.

Reference: W. B. R. Lickorish, *An Introduction to Knot Theory*, Chapter 1 (Reidemeister
moves); S. K. Lando and A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, §1.3
(rotation systems and faces). The quotient argument uses the same generator-invariance
method as `TauCeti.KnotTheory.PDCode.ClaspInsertion.Basic`.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm

variable {n : ℕ} (D : PDCode n) (h : Fin (4 * n)) (b : Bool)

/-- Kink insertion retains each old vertex rotation and adds the cyclic rotation of its
new crossing. -/
@[simp]
theorem crossingRotation_reidemeisterOne :
    (D.reidemeisterOne h b).crossingRotation = (halfEdgeSuccEquiv n).permCongr
      (Perm.sumCongr D.crossingRotation (finRotate 4)) := by
  apply eq_permCongr_sumCongr_of_halfEdge_eq (D.reidemeisterOne_halfEdge h b)
    (fun _ ↦ finRotate 4)
  · intro i k
    rw [crossingRotation_crossing, finRotate_apply]
  · intro i k
    rw [crossingRotation_crossing, finRotate_apply]

private theorem rotation_apply (z : Fin (4 * n) ⊕ Fin 4) :
    (D.reidemeisterOne h b).crossingRotation (halfEdgeSuccEquiv n z) =
      halfEdgeSuccEquiv n (Perm.sumCongr D.crossingRotation (finRotate 4) z) := by
  simp [crossingRotation_reidemeisterOne]

private theorem faceTraversal_splice :
    (D.reidemeisterOne h b).crossingRotation * (D.reidemeisterOne h b).edgePair.val =
      (halfEdgeSuccEquiv n).permCongr
        (Perm.sumCongr (D.crossingRotation * D.edgePair.val) (1 : Perm (Fin 4)) *
          swap (.inl h) (.inr 1) * swap (.inl (D.edgePair.val h)) (.inr 0) *
            swap (.inl (D.edgePair.val h)) (.inr 2)) := by
  ext x
  obtain ⟨x, rfl⟩ := (halfEdgeSuccEquiv n).surjective x
  rcases x with x | k
  · by_cases hx : x = h
    · subst x
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne,
        Ne.symm (D.edgePair.apply_ne h), finRotate_apply]
    by_cases hx' : x = D.edgePair.val h
    · subst x
      simp [Perm.mul_apply, swap_apply_of_ne_of_ne, finRotate_apply]
    simp [Perm.mul_apply, D.reidemeisterOne_edgePair_inl_of_ne h b hx hx',
      swap_apply_of_ne_of_ne, hx, hx']
  · fin_cases k <;> simp [Perm.mul_apply, swap_apply_of_ne_of_ne,
      D.edgePair.apply_apply, D.edgePair.apply_ne, finRotate_apply]

/-- Inserting a kink into an arc adds exactly one face: the small monogon of the kink. -/
@[simp]
theorem faceCount_reidemeisterOne :
    (D.reidemeisterOne h b).faceCount = D.faceCount + 1 := by
  rw [faceCount_eq_orbitCount_crossingRotation_mul_edgePair, faceTraversal_splice,
    orbitCount_permCongr]
  let σ := Perm.sumCongr (D.crossingRotation * D.edgePair.val) (1 : Perm (Fin 4))
  have h₀ : orbitCount σ = D.faceCount + 4 := by
    simp [σ, Perm.orbitCount_sumCongr, D.faceCount_eq_orbitCount_crossingRotation_mul_edgePair]
  have h₁ := orbitCount_mul_swap_add_one (τ := σ) (p := .inr 1) (a := .inl h)
    (by simp [σ]) (by simp)
  have h₂ := orbitCount_mul_swap_add_one (τ := σ * swap (.inl h) (.inr 1))
    (p := .inr 0) (a := .inl (D.edgePair.val h))
    (by simp [σ, swap_apply_of_ne_of_ne]) (by simp)
  have h₃ := orbitCount_mul_swap_add_one
    (τ := σ * swap (.inl h) (.inr 1) * swap (.inl (D.edgePair.val h)) (.inr 0))
    (p := .inr 2) (a := .inl (D.edgePair.val h))
    (by simp [σ, swap_apply_of_ne_of_ne]) (by simp)
  dsimp [σ] at h₀ h₁ h₂ h₃
  omega

/-! ### Crossing-graph components -/

private def newOrbit (z : Fin (4 * n) ⊕ Fin 4) :
    (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit :=
  Quotient.mk _ (halfEdgeSuccEquiv n z)

private theorem newOrbit_rotation (z : Fin (4 * n) ⊕ Fin 4) :
    newOrbit D h b (Perm.sumCongr D.crossingRotation (finRotate 4) z) = newOrbit D h b z := by
  unfold newOrbit
  rw [← rotation_apply, ← toPermutationTriple_σ0]
  exact PermutationTriple.mk_σ0_apply _ _

private theorem newOrbit_edge (z : Fin (4 * n) ⊕ Fin 4) :
    (Quotient.mk _ ((D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n z)) :
      (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit) = newOrbit D h b z := by
  simpa only [toPermutationTriple_σ1, newOrbit] using
    (D.reidemeisterOne h b).toPermutationTriple.mk_σ1_apply (halfEdgeSuccEquiv n z)

private theorem newOrbit_inr (k : Fin 4) :
    newOrbit D h b (.inr k) = newOrbit D h b (.inl h) := by
  have hr (i : Fin 4) : newOrbit D h b (.inr (i + 1)) = newOrbit D h b (.inr i) := by
    simpa [finRotate_apply] using newOrbit_rotation D h b (.inr i)
  have hz : newOrbit D h b (.inr 0) = newOrbit D h b (.inl h) := by
    simpa [newOrbit] using newOrbit_edge D h b (.inl h)
  exact (apply_eq_apply_zero_of_add_one (f := fun i ↦ newOrbit D h b (.inr i)) hr k).trans hz

private theorem newOrbit_old_edge (x : Fin (4 * n)) :
    newOrbit D h b (.inl (D.edgePair.val x)) = newOrbit D h b (.inl x) := by
  by_cases hx : x = h
  · subst x
    have he := newOrbit_edge D h b (.inr 1)
    rw [D.reidemeisterOne_edgePair_inr_one] at he
    exact he.trans (newOrbit_inr D h b 1)
  by_cases hx' : x = D.edgePair.val h
  · subst x
    simp only [D.edgePair.apply_apply]
    have he := newOrbit_edge D h b (.inr 1)
    rw [D.reidemeisterOne_edgePair_inr_one] at he
    exact (he.trans (newOrbit_inr D h b 1)).symm
  have he := newOrbit_edge D h b (.inl x)
  rwa [D.reidemeisterOne_edgePair_inl_of_ne h b hx hx'] at he

private def componentMap : D.toPermutationTriple.MonodromyOrbit →
    (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit :=
  Quotient.lift (fun x ↦ newOrbit D h b (.inl x)) (by
    rintro _ x ⟨⟨g, hg⟩, rfl⟩
    exact D.toPermutationTriple.apply_eq_of_mem_monodromyGroup
      (f := fun x ↦ newOrbit D h b (.inl x))
      (fun x ↦ by simpa using newOrbit_rotation D h b (.inl x))
      (fun x ↦ by simpa only [toPermutationTriple_σ1] using newOrbit_old_edge D h b x) hg x)

private def oldOrbit (z : Fin (4 * n) ⊕ Fin 4) : D.toPermutationTriple.MonodromyOrbit :=
  Sum.elim (Quotient.mk _) (fun _ ↦ Quotient.mk _ h) z

private theorem oldOrbit_rotation (z : Fin (4 * n) ⊕ Fin 4) :
    oldOrbit D h (Perm.sumCongr D.crossingRotation (finRotate 4) z) = oldOrbit D h z := by
  rcases z with x | k
  · simpa only [oldOrbit, Perm.sumCongr_apply, Sum.elim_inl, Sum.map_inl,
      toPermutationTriple_σ0] using D.toPermutationTriple.mk_σ0_apply x
  · rfl

private theorem oldOrbit_edge (z : Fin (4 * n) ⊕ Fin 4) :
    oldOrbit D h ((halfEdgeSuccEquiv n).symm
      ((D.reidemeisterOne h b).edgePair.val (halfEdgeSuccEquiv n z))) = oldOrbit D h z := by
  have he (x : Fin (4 * n)) :
      (Quotient.mk _ (D.edgePair.val x) : D.toPermutationTriple.MonodromyOrbit) =
        Quotient.mk _ x := by
    simpa only [toPermutationTriple_σ1] using D.toPermutationTriple.mk_σ1_apply x
  rcases z with x | k
  · by_cases hx : x = h
    · subst x
      simp [oldOrbit]
    by_cases hx' : x = D.edgePair.val h
    · subst x
      simpa [oldOrbit] using (he h).symm
    simpa [D.reidemeisterOne_edgePair_inl_of_ne h b hx hx', oldOrbit] using he x
  · fin_cases k <;> simp [oldOrbit, he h]

private def componentInv : (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit →
    D.toPermutationTriple.MonodromyOrbit :=
  Quotient.lift (fun y ↦ oldOrbit D h ((halfEdgeSuccEquiv n).symm y)) (by
    rintro _ y ⟨⟨g, hg⟩, rfl⟩
    refine (D.reidemeisterOne h b).toPermutationTriple.apply_eq_of_mem_monodromyGroup
      (f := fun y ↦ oldOrbit D h ((halfEdgeSuccEquiv n).symm y))
      (fun y ↦ ?_) (fun y ↦ ?_) hg y
    · obtain ⟨z, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
      rw [toPermutationTriple_σ0, rotation_apply, symm_apply_apply, symm_apply_apply,
        oldOrbit_rotation]
    · obtain ⟨z, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
      simpa only [toPermutationTriple_σ1, symm_apply_apply] using oldOrbit_edge D h b z)

/-- Kink insertion preserves the actual crossing-graph components. Old half-edges keep their
components, and the new crossing lies in the component of the cut arc. -/
def reidemeisterOneMonodromyOrbitEquiv : D.toPermutationTriple.MonodromyOrbit ≃
    (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit where
  toFun := componentMap D h b
  invFun := componentInv D h b
  left_inv := by
    intro c
    induction c using Quotient.ind
    simp [componentMap, componentInv, newOrbit, oldOrbit]
  right_inv := by
    intro c
    obtain ⟨y, rfl⟩ := Quotient.exists_rep c
    obtain ⟨z, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
    rcases z with x | k
    · simp [componentMap, componentInv, newOrbit, oldOrbit]
    · simpa only [componentMap, componentInv, Quotient.lift_mk, symm_apply_apply,
        oldOrbit, Sum.elim_inr, newOrbit] using (newOrbit_inr D h b k).symm

/-- An old half-edge represents the corresponding graph component after kink insertion. -/
@[simp]
theorem reidemeisterOneMonodromyOrbitEquiv_mk (x : Fin (4 * n)) :
    D.reidemeisterOneMonodromyOrbitEquiv h b (Quotient.mk _ x) =
      Quotient.mk _ (halfEdgeSuccEquiv n (.inl x)) := (rfl)

/-- The inverse component comparison retains old representatives and sends every new slot
to the component of the cut arc. -/
@[simp]
theorem reidemeisterOneMonodromyOrbitEquiv_symm_mk (z : Fin (4 * n) ⊕ Fin 4) :
    (D.reidemeisterOneMonodromyOrbitEquiv h b).symm
      (Quotient.mk _ (halfEdgeSuccEquiv n z)) =
        Sum.elim (Quotient.mk _) (fun _ ↦ Quotient.mk _ h) z := by
  apply (D.reidemeisterOneMonodromyOrbitEquiv h b).injective
  rw [Equiv.apply_symm_apply]
  rcases z with x | k
  · simp
  · simpa only [Sum.elim_inr, reidemeisterOneMonodromyOrbitEquiv_mk, newOrbit] using
      newOrbit_inr D h b k

/-- Arc kink insertion does not change the number of crossing-graph components. -/
@[simp]
theorem card_monodromyOrbit_reidemeisterOne :
    Nat.card (D.reidemeisterOne h b).toPermutationTriple.MonodromyOrbit =
      Nat.card D.toPermutationTriple.MonodromyOrbit :=
  (Nat.card_congr (D.reidemeisterOneMonodromyOrbitEquiv h b)).symm

/-- Inserting a Reidemeister-I kink into an arc preserves planarity in both directions. -/
@[simp]
theorem isPlanar_reidemeisterOne : (D.reidemeisterOne h b).IsPlanar ↔ D.IsPlanar := by
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq, faceCount_reidemeisterOne,
    card_monodromyOrbit_reidemeisterOne]
  omega

end TauCeti.PDCode
