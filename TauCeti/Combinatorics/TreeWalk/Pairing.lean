/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.DyckWord
public import TauCeti.Combinatorics.TreeWalk.Basic
import TauCeti.Data.Fin.Basic

/-!
# Edge pairings of closed tree walks

Closed tree walks of length `2 * k` represent, up to first-visit vertex relabeling, the
double-traversal closed walks that dominate expected trace expansions of Wigner matrices, while
noncrossing pair partitions of `Fin (2 * k)` govern the moments of Wigner's semicircle law. In any
closed tree walk `w` of length `2 * k`, every unordered edge `s(w i, w (i + 1))` is traversed
twice, once in each direction; pairing each step `i : Fin (2 * k)` with the unique other step
`j ≠ i` traversing the same unordered edge gives a canonical bijection between these two families.

Under this edge pairing `σ`, an arc `{i, σ i}` opens at `i` (`i < σ i`) if and only if step `i`
discovers a new vertex (`w (i + 1) = i + 1`). Consequently `PlanarMatching.toDyckWord` sends the
edge pairing to the discovery-step Dyck word of `closedTreeWalkEquiv`, yielding explicit
equivalences between `ClosedTreeWalk k`, `PlanarMatching (2 * k)`, and noncrossing pair partitions
of `Fin (2 * k)`.

## Main definitions

* `TauCeti.TreeWalk.closedTreeWalkPlanarMatchingEquiv`: the equivalence
  `ClosedTreeWalk k ≃ PlanarMatching (2 * k)` pairing the two steps along each tree edge.
* `TauCeti.TreeWalk.closedTreeWalkNoncrossingPairingEquiv`: the induced equivalence with
  noncrossing pair partitions of `Fin (2 * k)`.

## Main results

* `TauCeti.TreeWalk.closedTreeWalkPlanarMatchingEquiv_apply_eq_iff`: `j` is the matched partner of
  `i` if and only if `j ≠ i` and steps `i` and `j` traverse the same unordered edge.
* `TauCeti.TreeWalk.toDyckWord_closedTreeWalkPlanarMatchingEquiv`: the planar matching's Dyck word
  agrees with the tree walk's discovery-step Dyck word.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset Equiv

namespace TauCeti.TreeWalk

section EdgeMatching

variable {k : ℕ}

private theorem existsUnique_partnerStep (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    ∃! j : Fin (2 * k), j ∈ univ ∧ (j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1))) := by
  obtain ⟨j, hjne, -, -, hfib, -⟩ := w.2.1.exists_partner_step i
  exact ⟨j, ⟨mem_univ j, hjne, (hfib j).mpr (.inr rfl)⟩,
    fun y ⟨_, hyne, hye⟩ ↦ (hfib y).mp hye |>.resolve_left hyne⟩

/-- The partner step traversing the same edge as step `i` in `w : ClosedTreeWalk k`. -/
private def partnerStep (w : ClosedTreeWalk k) (i : Fin (2 * k)) : Fin (2 * k) :=
  univ.choose (fun j ↦ j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)))
    (existsUnique_partnerStep w i)

private theorem partnerStep_eq_iff (w : ClosedTreeWalk k) (i j : Fin (2 * k)) :
    partnerStep w i = j ↔ j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)) := by
  simpa [partnerStep] using univ.choose_eq_iff _ (existsUnique_partnerStep w i) (a := j)

private theorem partnerStep_spec (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    partnerStep w i ≠ i ∧ w.1 (partnerStep w i) = w.1 (i + 1) ∧
      w.1 ((partnerStep w i : ℕ) + 1) = w.1 i ∧
      (∀ t : Fin (2 * k), s(w.1 t, w.1 (t + 1)) = s(w.1 i, w.1 (i + 1)) ↔
        t = i ∨ t = partnerStep w i) ∧
      (i < partnerStep w i ↔ w.1 (i + 1) = i + 1) := by
  obtain ⟨j, hjne, hj1, hj2, hfib, hlt⟩ := w.2.1.exists_partner_step i
  rw [(partnerStep_eq_iff w i j).mpr ⟨hjne, (hfib j).mpr (.inr rfl)⟩]
  exact ⟨hjne, hj1, hj2, hfib, hlt⟩

private theorem partnerStep_involutive (w : ClosedTreeWalk k) :
    Function.Involutive (partnerStep w) := fun i ↦ by
  obtain ⟨hneq, -, -, hfib, -⟩ := partnerStep_spec w i
  exact (partnerStep_eq_iff w (partnerStep w i) i).mpr ⟨hneq.symm, ((hfib _).mpr (.inr rfl)).symm⟩

/-- The perfect matching of `Fin (2 * k)` pairing the two steps along each edge of `w`. -/
private def edgePerfectMatching (w : ClosedTreeWalk k) : PerfectMatching (Fin (2 * k)) :=
  PerfectMatching.ofInvolutive (partnerStep_involutive w) fun i ↦ (partnerStep_spec w i).1

private theorem val_finRotate_eq_succ (w : ClosedTreeWalk k) (j : Fin (2 * k)) :
    w.1 (finRotate (2 * k) j) = w.1 (j + 1) := by
  rw [Fin.coe_finRotate_eq_ite]; split_ifs with hj
  · rw [hj, w.2.1.root, w.2.1.closed]
  · rfl

private theorem card_image_fin_eq (w : ClosedTreeWalk k) [NeZero k] :
    #(univ.image fun i : Fin (2 * k) ↦ w.1 i) = k + 1 := by
  rw [← w.2.1.card_vertices]; congr 1; ext x
  simp only [mem_image, mem_univ, true_and, mem_filter, mem_range]
  refine ⟨fun ⟨i, hi⟩ ↦ hi ▸ ⟨(w.2.1.le_self i i.isLt.le).trans_lt (by omega),
    w.2.1.idem i.isLt.le⟩, fun ⟨hx, hfix⟩ ↦ ?_⟩
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hx) with rfl | hlt
  · exact ⟨⟨0, by have := NeZero.ne k; omega⟩, by simpa [w.2.1.root, w.2.1.closed] using hfix⟩
  · exact ⟨⟨x, hlt⟩, hfix⟩

private theorem isNoncrossingMatching_edgePerfectMatching (w : ClosedTreeWalk k) :
    (edgePerfectMatching w).val.IsNoncrossingMatching := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact Perm.isNoncrossingMatching_iff.mpr fun a ↦ Fin.elim0 a
  have : NeZero k := ⟨hk⟩
  let τ : Perm (Fin (2 * k)) := finRotate (2 * k) * (edgePerfectMatching w).val
  have hinv_step (i : Fin (2 * k)) : w.1 (τ i) = w.1 i := by
    simp only [τ, Perm.mul_apply, edgePerfectMatching, PerfectMatching.ofInvolutive_apply]
    rw [val_finRotate_eq_succ w (partnerStep w i), (partnerStep_spec w i).2.2.1]
  let g : Quotient (Perm.SameCycle.setoid τ) → ↥(univ.image fun i : Fin (2 * k) ↦ w.1 i) :=
    Quotient.lift (fun i ↦ ⟨w.1 i, mem_image_of_mem _ (mem_univ i)⟩) fun i _ hij ↦
      Subtype.ext <| Perm.sameCycle_one.mp <|
        hij.map_of_forall_sameCycle_apply (π := 1) fun j ↦ Perm.sameCycle_one.mpr (hinv_step j).symm
  have hsurj : Function.Surjective g := fun ⟨_, hy⟩ ↦
    let ⟨i, _, hi⟩ := mem_image.mp hy; ⟨⟦i⟧, Subtype.ext hi⟩
  have hge : k + 1 ≤ orbitCount τ := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, card_image_fin_eq w, ← orbitCount_def]
      using Nat.card_le_card_of_surjective g hsurj
  exact (edgePerfectMatching w).2.orbitCount_finRotate_mul_eq_iff.mp
    (le_antisymm (edgePerfectMatching w).2.orbitCount_finRotate_mul_le hge)

/-- The planar matching pairing the two traversals of every edge of `w`. -/
private def edgePlanarMatching (w : ClosedTreeWalk k) : PlanarMatching (2 * k) :=
  ⟨edgePerfectMatching w, isNoncrossingMatching_edgePerfectMatching w⟩

private theorem toDyckWord_edgePlanarMatching (w : ClosedTreeWalk k) :
    (edgePlanarMatching w).toDyckWord = (closedTreeWalkEquiv k w).1 := by
  ext1; rw [PlanarMatching.toList_toDyckWord, closedTreeWalkEquiv_apply_coe]
  refine List.ofFn_inj.mpr (funext fun i ↦ ?_)
  have hU : (edgePlanarMatching w).dyckStep i = DyckStep.U ↔ upSteps k w.1 i = true := by
    rw [PlanarMatching.dyckStep_eq_U_iff, upSteps_eq_true_iff]
    simp [edgePlanarMatching, edgePerfectMatching, (partnerStep_spec w i).2.2.2.2, i.isLt]
  cases hstep : (edgePlanarMatching w).dyckStep i <;>
    cases hup : upSteps k w.1 i <;> simp_all

/-- **Equivalence between closed tree walks and planar matchings.** Pairing each step of a closed
tree walk of length `2 * k` with the unique other step traversing the same unordered edge gives an
equivalence with `PlanarMatching (2 * k)`. -/
def closedTreeWalkPlanarMatchingEquiv (k : ℕ) : ClosedTreeWalk k ≃ PlanarMatching (2 * k) where
  toFun := edgePlanarMatching
  invFun x := (closedTreeWalkEquiv k).symm (PlanarMatching.dyckWordEquiv k x)
  left_inv w := (closedTreeWalkEquiv k).injective <| by
    rw [Equiv.apply_symm_apply]; exact Subtype.ext (by simp [toDyckWord_edgePlanarMatching])
  right_inv x := (PlanarMatching.dyckWordEquiv k).injective <| Subtype.ext <| by
    simp [PlanarMatching.coe_dyckWordEquiv_apply, toDyckWord_edgePlanarMatching]

/-- Inverse of `closedTreeWalkPlanarMatchingEquiv` via `PlanarMatching.dyckWordEquiv` and
`closedTreeWalkEquiv`. -/
theorem closedTreeWalkPlanarMatchingEquiv_symm_apply (x : PlanarMatching (2 * k)) :
    (closedTreeWalkPlanarMatchingEquiv k).symm x =
      (closedTreeWalkEquiv k).symm (PlanarMatching.dyckWordEquiv k x) := (rfl)

/-- Two steps are paired by `closedTreeWalkPlanarMatchingEquiv` if and only if they are distinct
and traverse the same unordered edge of the walk. -/
theorem closedTreeWalkPlanarMatchingEquiv_apply_eq_iff (w : ClosedTreeWalk k)
    (i j : Fin (2 * k)) :
    (closedTreeWalkPlanarMatchingEquiv k w).1.val i = j ↔
      j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)) := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    partnerStep_eq_iff w i j

/-- The partner of step `i` starts at the endpoint `w (i + 1)` of step `i`. -/
@[simp]
theorem val_closedTreeWalkPlanarMatchingEquiv_apply (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    w.1 ((closedTreeWalkPlanarMatchingEquiv k w).1.val i) = w.1 (i + 1) := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    (partnerStep_spec w i).2.1

/-- The partner of step `i` ends at the start `w i` of step `i`. -/
@[simp]
theorem val_closedTreeWalkPlanarMatchingEquiv_apply_succ (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    w.1 (((closedTreeWalkPlanarMatchingEquiv k w).1.val i : ℕ) + 1) = w.1 i := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    (partnerStep_spec w i).2.2.1

/-- An arc of `closedTreeWalkPlanarMatchingEquiv k w` opens at step `i` if and only if step `i`
discovers a new vertex. -/
@[simp]
theorem lt_closedTreeWalkPlanarMatchingEquiv_apply_iff (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    i < (closedTreeWalkPlanarMatchingEquiv k w).1.val i ↔ w.1 (i + 1) = i + 1 := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    (partnerStep_spec w i).2.2.2.2

/-- `PlanarMatching.toDyckWord` intertwines `closedTreeWalkPlanarMatchingEquiv` with
`closedTreeWalkEquiv`. -/
@[simp]
theorem toDyckWord_closedTreeWalkPlanarMatchingEquiv (w : ClosedTreeWalk k) :
    (closedTreeWalkPlanarMatchingEquiv k w).toDyckWord = (closedTreeWalkEquiv k w).1 :=
  toDyckWord_edgePlanarMatching w

/-- **Equivalence between closed tree walks and noncrossing pair partitions.** Each two-element
block consists of the forward and backward traversals of one edge of the tree walk. -/
def closedTreeWalkNoncrossingPairingEquiv (k : ℕ) :
    ClosedTreeWalk k ≃
      {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing} :=
  (closedTreeWalkPlanarMatchingEquiv k).trans PerfectMatching.noncrossingPairingEquiv

/-- `closedTreeWalkNoncrossingPairingEquiv` is the composition of
`closedTreeWalkPlanarMatchingEquiv` and `PerfectMatching.noncrossingPairingEquiv`. -/
theorem closedTreeWalkNoncrossingPairingEquiv_def (k : ℕ) :
    closedTreeWalkNoncrossingPairingEquiv k =
      (closedTreeWalkPlanarMatchingEquiv k).trans PerfectMatching.noncrossingPairingEquiv := (rfl)

/-- Underlying `Finpartition` of `closedTreeWalkNoncrossingPairingEquiv k w`. -/
@[simp]
theorem closedTreeWalkNoncrossingPairingEquiv_apply_coe (w : ClosedTreeWalk k) :
    (closedTreeWalkNoncrossingPairingEquiv k w).val.val =
      (closedTreeWalkPlanarMatchingEquiv k w).val.toFinpartition := by
  simp [closedTreeWalkNoncrossingPairingEquiv]

/-- Inverse of `closedTreeWalkNoncrossingPairingEquiv` in terms of
`closedTreeWalkPlanarMatchingEquiv` and `PerfectMatching.noncrossingPairingEquiv`. -/
theorem closedTreeWalkNoncrossingPairingEquiv_symm_apply
    (P : {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing}) :
    (closedTreeWalkNoncrossingPairingEquiv k).symm P =
      (closedTreeWalkPlanarMatchingEquiv k).symm
        (PerfectMatching.noncrossingPairingEquiv.symm P) := (rfl)

end EdgeMatching

end TauCeti.TreeWalk
