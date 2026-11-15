/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.DyckWord
public import TauCeti.Combinatorics.TreeWalk.Basic

/-!
# Edge pairings of closed tree walks

In a closed tree walk `w` of length `2 * k`, every unordered edge `s(w i, w (i + 1))` is traversed
twice, once in each direction. Pairing each step `i : Fin (2 * k)` with the unique other step
`j ≠ i` traversing the same unordered edge defines a fixed-point-free involution `σ` of
`Fin (2 * k)`.

Because the return step reverses orientation (`w (σ i) = w (i + 1)` and `w (σ i + 1) = w i`) and
the walk is closed (`w (2 * k) = w 0`), the vertex visited at the start of a step is invariant
under the ribbon-boundary permutation `finRotate (2 * k) * σ`. For `k ≠ 0`, as `w` visits `k + 1`
distinct vertices, `finRotate (2 * k) * σ` has at least `k + 1` orbits, which attains the Euler
bound of `TauCeti.IsPerfectMatching.orbitCount_finRotate_mul_eq_iff` and proves that `σ` is a
noncrossing perfect matching (`PlanarMatching (2 * k)`, with `k = 0` vacuous on `Fin 0`).

Moreover, an arc `{i, σ i}` opens at `i` (`i < σ i`) if and only if step `i` discovers a new
vertex (`w (i + 1) = i + 1`). Hence `PlanarMatching.toDyckWord` sends this edge matching to the
Dyck word of `closedTreeWalkEquiv`, showing that edge pairing gives explicit equivalences between
`ClosedTreeWalk k`, `PlanarMatching (2 * k)`, and noncrossing pair partitions of `Fin (2 * k)`.

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
  obtain ⟨j, hjne, -, -, hfib, -⟩ := w.2.1.exists_other_step i
  exact ⟨j, ⟨mem_univ j, hjne, (hfib j).mpr (.inr rfl)⟩,
    fun y ⟨_, hyne, hye⟩ ↦ (hfib y).mp hye |>.resolve_left hyne⟩

/-- The partner step traversing the same edge as step `i` in `w : ClosedTreeWalk k`. -/
private def partnerStep (w : ClosedTreeWalk k) (i : Fin (2 * k)) : Fin (2 * k) :=
  univ.choose (fun j ↦ j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)))
    (existsUnique_partnerStep w i)

private theorem partnerStep_eq_iff (w : ClosedTreeWalk k) (i j : Fin (2 * k)) :
    partnerStep w i = j ↔ j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)) := by
  simpa only [partnerStep, mem_univ, true_and] using
    univ.choose_eq_iff _ (existsUnique_partnerStep w i) (a := j)

private theorem partnerStep_spec (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    partnerStep w i ≠ i ∧ w.1 (partnerStep w i) = w.1 (i + 1) ∧
      w.1 ((partnerStep w i : ℕ) + 1) = w.1 i ∧
      (∀ t : Fin (2 * k), s(w.1 t, w.1 (t + 1)) = s(w.1 i, w.1 (i + 1)) ↔
        t = i ∨ t = partnerStep w i) ∧
      (i < partnerStep w i ↔ w.1 (i + 1) = i + 1) := by
  obtain ⟨j, hjne, hj1, hj2, hfib, hlt⟩ := w.2.1.exists_other_step i
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
  rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  by_cases hj : (j : ℕ) + 1 < 2 * k
  · rw [Nat.mod_eq_of_lt hj]
  · rw [show (j : ℕ) + 1 = 2 * k by omega, Nat.mod_self, w.2.1.root, w.2.1.closed]

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
  have hzpow (n : ℤ) : ∀ i, w.1 ((τ ^ n) i) = w.1 i := Int.induction_on n (by simp)
    (fun n ih i ↦ by rw [zpow_add_one, Perm.mul_apply, ih, hinv_step])
    (fun n ih i ↦ by
      rw [sub_eq_add_neg, zpow_add, zpow_neg_one, Perm.mul_apply, ih, ← hinv_step (τ⁻¹ i)]; simp)
  let g : Quotient (Perm.SameCycle.setoid τ) → ↥(univ.image fun i : Fin (2 * k) ↦ w.1 i) :=
    Quotient.lift (fun i ↦ ⟨w.1 i, mem_image_of_mem _ (mem_univ i)⟩) fun i _ ⟨n, hn⟩ ↦
      Subtype.ext (hn ▸ (hzpow n i).symm)
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

/-- **Leading-term bridge between closed tree walks and planar matchings.** Pairing each step of a
closed tree walk of length `2 * k` with the unique other step traversing the same unordered edge
gives an equivalence with `PlanarMatching (2 * k)`. -/
def closedTreeWalkPlanarMatchingEquiv (k : ℕ) : ClosedTreeWalk k ≃ PlanarMatching (2 * k) where
  toFun := edgePlanarMatching
  invFun x := (closedTreeWalkEquiv k).symm (PlanarMatching.dyckWordEquiv k x)
  left_inv w := (closedTreeWalkEquiv k).injective <| by
    rw [Equiv.apply_symm_apply]; exact Subtype.ext (by simp [toDyckWord_edgePlanarMatching])
  right_inv x := (PlanarMatching.dyckWordEquiv k).injective <| Subtype.ext <| by
    simp [PlanarMatching.coe_dyckWordEquiv_apply, toDyckWord_edgePlanarMatching]

/-- Inverse of `closedTreeWalkPlanarMatchingEquiv` via `PlanarMatching.dyckWordEquiv` and
`closedTreeWalkEquiv`. -/
@[simp]
theorem closedTreeWalkPlanarMatchingEquiv_symm_apply (x : PlanarMatching (2 * k)) :
    (closedTreeWalkPlanarMatchingEquiv k).symm x =
      (closedTreeWalkEquiv k).symm (PlanarMatching.dyckWordEquiv k x) :=
  (rfl)

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
      (closedTreeWalkPlanarMatchingEquiv k).trans PerfectMatching.noncrossingPairingEquiv :=
  (rfl)

/-- Underlying `Finpartition` of `closedTreeWalkNoncrossingPairingEquiv k w`. -/
@[simp]
theorem closedTreeWalkNoncrossingPairingEquiv_apply_coe (w : ClosedTreeWalk k) :
    (closedTreeWalkNoncrossingPairingEquiv k w).val.val =
      (closedTreeWalkPlanarMatchingEquiv k w).val.toFinpartition := by
  simp [closedTreeWalkNoncrossingPairingEquiv]

/-- Inverse of `closedTreeWalkNoncrossingPairingEquiv` in terms of `closedTreeWalkEquiv`,
`PlanarMatching.dyckWordEquiv`, and `PerfectMatching.noncrossingPairingEquiv`. -/
@[simp]
theorem closedTreeWalkNoncrossingPairingEquiv_symm_apply
    (P : {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing}) :
    (closedTreeWalkNoncrossingPairingEquiv k).symm P =
      (closedTreeWalkPlanarMatchingEquiv k).symm (PerfectMatching.noncrossingPairingEquiv.symm P) :=
  (rfl)

end EdgeMatching

end TauCeti.TreeWalk
