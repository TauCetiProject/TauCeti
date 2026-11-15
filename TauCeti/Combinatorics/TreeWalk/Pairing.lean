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
under the ribbon-boundary permutation `finRotate (2 * k) * σ`. As `w` visits `k + 1` distinct
vertices, `finRotate (2 * k) * σ` has at least `k + 1` orbits, which attains the Euler bound of
`TauCeti.IsPerfectMatching.orbitCount_finRotate_mul_eq_iff` and proves that `σ` is a noncrossing
perfect matching (`PlanarMatching (2 * k)`).

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

namespace IsTreeWalk

variable {k : ℕ} {w : ℕ → ℕ}

/-- Every step of a closed tree walk has a unique distinct partner step traversing the same
unordered edge, in the opposite direction, and the discovery step is the earlier of the two. -/
theorem exists_other_step (hw : IsTreeWalk k w) (i : Fin (2 * k)) :
    ∃ j : Fin (2 * k), j ≠ i ∧ w j = w (i + 1) ∧ w (j + 1) = w i ∧
      (∀ t : Fin (2 * k), s(w t, w (t + 1)) = s(w i, w (i + 1)) ↔ t = i ∨ t = j) ∧
      (i < j ↔ w (i + 1) = i + 1) := by
  obtain ⟨u, hu, hup, heu⟩ := hw.exists_up_edge i.isLt
  have heu' : s(w i, w (i + 1)) = s(w u, w (u + 1)) := by simpa only [hup] using heu
  obtain ⟨d, hd, hdu1, hdu2, hpair⟩ := hw.exists_edge_fiber_eq_pair hu hup
  have hle_u : w u ≤ u := hw.le_self u hu.le
  have hle_d : w d ≤ d := hw.le_self d hd.le
  have hud : u < d := by omega
  have hmem : ∀ t : Fin (2 * k), s(w t, w (t + 1)) = s(w u, w (u + 1)) ↔ t.val = u ∨ t.val = d := by
    intro t
    have ht := Finset.ext_iff.mp hpair t.val
    simpa only [mem_filter, mem_range, t.isLt, true_and, mem_insert, mem_singleton] using ht
  rcases (hmem i).mp heu' with hi | hi
  · refine ⟨⟨d, hd⟩, fun h ↦ by have : d = i.val := congrArg Fin.val h; omega, ?_, ?_, ?_, ?_⟩
    · simp only [hi, hdu1, hup]
    · simp only [hi, hdu2]
    · intro t
      rw [heu', hmem t]
      simp only [Fin.ext_iff, hi]
    · change i.val < d ↔ w (i + 1) = i + 1
      rw [hi]
      exact ⟨fun _ ↦ hup, fun _ ↦ hud⟩
  · refine ⟨⟨u, hu⟩, fun h ↦ by have : u = i.val := congrArg Fin.val h; omega, ?_, ?_, ?_, ?_⟩
    · simp only [hi, hdu2]
    · simp only [hi, hup, hdu1]
    · intro t
      rw [heu', hmem t, or_comm]
      simp only [Fin.ext_iff, hi]
    · change i.val < u ↔ w (i + 1) = i + 1
      rw [hi]
      omega

end IsTreeWalk

section EdgeMatching

variable {k : ℕ}

/-- The partner step traversing the same edge as step `i` in `w : ClosedTreeWalk k`. -/
private def partnerStep (w : ClosedTreeWalk k) (i : Fin (2 * k)) : Fin (2 * k) :=
  ((List.finRange (2 * k)).find? fun j ↦
    decide (j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)))).getD i

private theorem partnerStep_spec (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    partnerStep w i ≠ i ∧ w.1 (partnerStep w i) = w.1 (i + 1) ∧
      w.1 ((partnerStep w i : ℕ) + 1) = w.1 i ∧
      (∀ t : Fin (2 * k), s(w.1 t, w.1 (t + 1)) = s(w.1 i, w.1 (i + 1)) ↔
        t = i ∨ t = partnerStep w i) ∧
      (i < partnerStep w i ↔ w.1 (i + 1) = i + 1) := by
  obtain ⟨j, hjne, hj1, hj2, hfib, hlt⟩ := w.2.1.exists_other_step i
  set p : Fin (2 * k) → Bool := fun x ↦
    decide (x ≠ i ∧ s(w.1 x, w.1 (x + 1)) = s(w.1 i, w.1 (i + 1)))
  have hsome : ((List.finRange (2 * k)).find? p).isSome :=
    List.find?_isSome.mpr ⟨j, List.mem_finRange j, decide_eq_true ⟨hjne, (hfib j).mpr (.inr rfl)⟩⟩
  obtain ⟨m, hm_eq⟩ := Option.isSome_iff_exists.mp hsome
  have hm_p : p m = true := List.find?_some hm_eq
  have hm_prop : m ≠ i ∧ s(w.1 m, w.1 (m + 1)) = s(w.1 i, w.1 (i + 1)) := of_decide_eq_true hm_p
  have hp : partnerStep w i = m := by
    change ((List.finRange (2 * k)).find? p).getD i = m
    rw [hm_eq]
    rfl
  have hmj : m = j := ((hfib m).mp hm_prop.2).resolve_left hm_prop.1
  subst hmj
  simpa only [hp] using ⟨hjne, hj1, hj2, hfib, hlt⟩

private theorem partnerStep_eq_iff (w : ClosedTreeWalk k) (i j : Fin (2 * k)) :
    partnerStep w i = j ↔ j ≠ i ∧ s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1)) := by
  obtain ⟨hneq, -, -, hfib, -⟩ := partnerStep_spec w i
  constructor
  · rintro rfl
    exact ⟨hneq, (hfib _).mpr (.inr rfl)⟩
  · rintro ⟨hji, he⟩
    exact (((hfib j).mp he).resolve_left hji).symm

private theorem partnerStep_involutive (w : ClosedTreeWalk k) :
    Function.Involutive (partnerStep w) := by
  intro i
  obtain ⟨hneq, -, -, hfib, -⟩ := partnerStep_spec w i
  exact (partnerStep_eq_iff w (partnerStep w i) i).mpr
    ⟨hneq.symm, ((hfib _).mpr (.inr rfl)).symm⟩

/-- The perfect matching of `Fin (2 * k)` pairing the two steps along each edge of `w`. -/
private def edgePerfectMatching (w : ClosedTreeWalk k) : PerfectMatching (Fin (2 * k)) :=
  PerfectMatching.ofInvolutive (partnerStep_involutive w) fun i ↦ (partnerStep_spec w i).1

private theorem w_finRotate_eq_succ (w : ClosedTreeWalk k) (j : Fin (2 * k)) :
    w.1 (finRotate (2 * k) j) = w.1 (j + 1) := by
  have hval : (finRotate (2 * k) j : ℕ) = ((j : ℕ) + 1) % (2 * k) := by
    rw [finRotate_apply, Fin.val_add, Fin.val_one', Nat.add_mod_mod]
  rw [hval]
  by_cases hj : (j : ℕ) + 1 < 2 * k
  · rw [Nat.mod_eq_of_lt hj]
  · have hj_eq : (j : ℕ) + 1 = 2 * k := by omega
    rw [hj_eq, Nat.mod_self, w.2.1.root, w.2.1.closed]

private theorem card_image_fin_eq (w : ClosedTreeWalk k) [NeZero k] :
    #(univ.image fun i : Fin (2 * k) ↦ w.1 i) = k + 1 := by
  have himg : univ.image (fun i : Fin (2 * k) ↦ w.1 i) =
      {i ∈ range (2 * k + 1) | w.1 i = i} := by
    ext x
    simp only [mem_image, mem_univ, true_and, mem_filter, mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨(w.2.1.le_self i i.isLt.le).trans_lt (by omega), w.2.1.idem i.isLt.le⟩
    · rintro ⟨hx, hfix⟩
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hx) with rfl | hlt
      · refine ⟨⟨0, Nat.mul_pos two_pos (Nat.pos_of_ne_zero (NeZero.ne k))⟩, ?_⟩
        rw [w.2.1.closed] at hfix
        simpa only [w.2.1.root] using hfix
      · exact ⟨⟨x, hlt⟩, hfix⟩
  rw [himg, w.2.1.card_vertices]

private theorem isNoncrossingMatching_edgePerfectMatching (w : ClosedTreeWalk k) :
    (edgePerfectMatching w).val.IsNoncrossingMatching := by
  rcases eq_or_ne k 0 with rfl | hk
  · exact Perm.isNoncrossingMatching_iff.mpr fun a ↦ Fin.elim0 a
  have : NeZero k := ⟨hk⟩
  let τ : Perm (Fin (2 * k)) := finRotate (2 * k) * (edgePerfectMatching w).val
  have hinv_step (i : Fin (2 * k)) : w.1 (τ i) = w.1 i := by
    simp only [τ, Perm.mul_apply, edgePerfectMatching, PerfectMatching.ofInvolutive_apply]
    rw [w_finRotate_eq_succ w (partnerStep w i), (partnerStep_spec w i).2.2.1]
  have hzpow (n : ℤ) : ∀ i : Fin (2 * k), w.1 ((τ ^ n) i) = w.1 i := by
    induction n using Int.induction_on with
    | zero => intro i; simp
    | succ n ih => intro i; rw [zpow_add_one, Perm.mul_apply, ih, hinv_step]
    | pred n ih =>
      intro i
      have hcancel : τ (τ⁻¹ ((τ ^ (-(n : ℤ))) i)) = (τ ^ (-(n : ℤ))) i := by simp
      rw [show -(n : ℤ) - 1 = (-1 : ℤ) + -(n : ℤ) by ring, zpow_add, zpow_neg_one,
        Perm.mul_apply, ← hinv_step, hcancel, ih]
  let g : Quotient (Perm.SameCycle.setoid τ) → ↥(univ.image fun i : Fin (2 * k) ↦ w.1 i) :=
    Quotient.lift (fun i ↦ ⟨w.1 i, mem_image_of_mem _ (mem_univ i)⟩) fun i j hij ↦ by
      obtain ⟨n, rfl⟩ := hij
      exact Subtype.ext (hzpow n i).symm
  have hsurj : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨i, -, rfl⟩ := mem_image.mp hy
    exact ⟨Quotient.mk _ i, rfl⟩
  have hge : k + 1 ≤ orbitCount τ := by
    have hcard := Nat.card_le_card_of_surjective g hsurj
    simpa only [Nat.card_eq_fintype_card, Fintype.card_coe, card_image_fin_eq w, ← orbitCount_def]
      using hcard
  have hle : orbitCount τ ≤ k + 1 := (edgePerfectMatching w).2.orbitCount_finRotate_mul_le
  exact ((edgePerfectMatching w).2.orbitCount_finRotate_mul_eq_iff).mp (le_antisymm hle hge)

/-- The planar matching pairing the two traversals of every edge of `w`. -/
private def edgePlanarMatching (w : ClosedTreeWalk k) : PlanarMatching (2 * k) :=
  ⟨edgePerfectMatching w, isNoncrossingMatching_edgePerfectMatching w⟩

private theorem toDyckWord_edgePlanarMatching (w : ClosedTreeWalk k) :
    (edgePlanarMatching w).toDyckWord = (closedTreeWalkEquiv k w).1 := by
  ext1
  rw [PlanarMatching.toList_toDyckWord, closedTreeWalkEquiv_apply_coe]
  refine List.ofFn_inj.mpr (funext fun i ↦ ?_)
  have hU : (edgePlanarMatching w).dyckStep i = DyckStep.U ↔ upSteps k w.1 i = true := by
    rw [PlanarMatching.dyckStep_eq_U_iff, upSteps_eq_true_iff]
    simp only [edgePlanarMatching, edgePerfectMatching, PerfectMatching.ofInvolutive_apply,
      (partnerStep_spec w i).2.2.2.2, i.isLt, true_and]
  cases hstep : (edgePlanarMatching w).dyckStep i <;>
    cases hup : upSteps k w.1 i <;> simp_all

/-- **Leading-term bridge between closed tree walks and planar matchings.** Pairing each step of a
closed tree walk of length `2 * k` with the unique other step traversing the same unordered edge
gives an equivalence with `PlanarMatching (2 * k)`. -/
def closedTreeWalkPlanarMatchingEquiv (k : ℕ) : ClosedTreeWalk k ≃ PlanarMatching (2 * k) where
  toFun := edgePlanarMatching
  invFun x := (closedTreeWalkEquiv k).symm (PlanarMatching.dyckWordEquiv k x)
  left_inv w := by
    apply (closedTreeWalkEquiv k).injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext (by simp [toDyckWord_edgePlanarMatching])
  right_inv x := by
    apply (PlanarMatching.dyckWordEquiv k).injective
    refine Subtype.ext ?_
    simp only [PlanarMatching.coe_dyckWordEquiv_apply, toDyckWord_edgePlanarMatching,
      Equiv.apply_symm_apply]

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
theorem w_closedTreeWalkPlanarMatchingEquiv_apply (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    w.1 ((closedTreeWalkPlanarMatchingEquiv k w).1.val i) = w.1 (i + 1) := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    (partnerStep_spec w i).2.1

/-- The partner of step `i` ends at the start `w i` of step `i`. -/
@[simp]
theorem w_closedTreeWalkPlanarMatchingEquiv_apply_succ (w : ClosedTreeWalk k) (i : Fin (2 * k)) :
    w.1 (((closedTreeWalkPlanarMatchingEquiv k w).1.val i : ℕ) + 1) = w.1 i := by
  simpa [closedTreeWalkPlanarMatchingEquiv, edgePlanarMatching, edgePerfectMatching] using
    (partnerStep_spec w i).2.2.1

/-- An arc of `closedTreeWalkPlanarMatchingEquiv k w` opens at step `i` if and only if step `i`
discovers a new vertex. -/
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

/-- Underlying `Finpartition` of `closedTreeWalkNoncrossingPairingEquiv k w`. -/
@[simp]
theorem closedTreeWalkNoncrossingPairingEquiv_apply_coe (w : ClosedTreeWalk k) :
    (closedTreeWalkNoncrossingPairingEquiv k w).val.val =
      (closedTreeWalkPlanarMatchingEquiv k w).val.toFinpartition := by
  simp [closedTreeWalkNoncrossingPairingEquiv]

end EdgeMatching

end TauCeti.TreeWalk
