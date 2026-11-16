/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.TreeWalk.Leading
public import TauCeti.Combinatorics.PlanarMatching.DyckWord

/-!
# Noncrossing edge pairings of closed tree walks

In a closed tree walk of length `2 * m` in first-visit labeling, every unordered tree edge is
traversed twice: once by the step that discovers its child vertex and once in the opposite
direction when leaving that subtree. Grouping the `2 * m` steps by their unordered edge therefore
partitions `Fin (2 * m)` into two-element fibers. Because the walk cannot leave a subtree before
finishing every edge discovered inside it, these fibers do not interleave, forming a planar
matching and equivalently a noncrossing pair partition of `Fin (2 * m)`.

Under this correspondence, the opening points of the planar matching are the discovery steps of the
tree walk, so the planar matching's Dyck word agrees with `closedTreeWalkEquiv`.

## Main definitions

* `TauCeti.TreeWalk.ClosedTreeWalk.edgePartition`: the partition of `Fin (2 * m)` into the
  two-element unordered-edge fibers of a closed tree walk.
* `TauCeti.TreeWalk.ClosedTreeWalk.toPlanarMatching`: the planar matching pairing each step of a
  closed tree walk with the other traversal of the same unordered edge.
* `TauCeti.TreeWalk.ClosedTreeWalk.planarMatchingEquiv`: equivalence between `ClosedTreeWalk m`
  and `PlanarMatching (2 * m)`.
* `TauCeti.TreeWalk.ClosedTreeWalk.noncrossingPairingEquiv`: equivalence between
  `ClosedTreeWalk m` and noncrossing pair partitions of `Fin (2 * m)`.

## Main results

* `TauCeti.TreeWalk.ClosedTreeWalk.toDyckWord_toPlanarMatching`: the Dyck word of the edge
  matching agrees with `closedTreeWalkEquiv`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk

namespace ClosedTreeWalk

variable {m : ℕ}

/-- Whether a vertex in a first-visit labeled walk lies in the subtree discovered at step `u`,
whose root is the vertex `u + 1`. -/
private def inSubtree (w : ℕ → ℕ) (u : ℕ) : ℕ → Bool
  | 0 => false
  | v + 1 => decide (v = u) || inSubtree w u (min (w v) v)
decreasing_by exact Nat.lt_succ_of_le (min_le_right _ _)

@[simp]
private theorem inSubtree_zero (w : ℕ → ℕ) (u : ℕ) : inSubtree w u 0 = false := by
  rw [inSubtree]

@[simp]
private theorem inSubtree_succ_self (w : ℕ → ℕ) (u : ℕ) : inSubtree w u (u + 1) = true := by
  rw [inSubtree]
  simp

private theorem inSubtree_succ_of_ne {w : ℕ → ℕ} {u i : ℕ} (hne : i ≠ u) (hle : w i ≤ i) :
    inSubtree w u (i + 1) = inSubtree w u (w i) := by
  rw [inSubtree]
  simp [hne, min_eq_left hle]

/-- Every step traversing an edge other than the one discovered at `u` preserves membership in the
subtree of `u + 1`. -/
private theorem inSubtree_step_eq_of_edge_ne {w : ℕ → ℕ} (hw : IsTreeWalk m w) {u t : ℕ}
    (ht : t < 2 * m) (hup : w (u + 1) = u + 1)
    (hne : s(w t, w (t + 1)) ≠ s(w u, w (u + 1))) :
    inSubtree w u (w (t + 1)) = inSubtree w u (w t) := by
  obtain ⟨i, hi, -, hti⟩ := hw.exists_up_edge ht
  have hiu : i ≠ u := by
    rintro rfl
    exact hne (hti.trans (by rw [hup]))
  have hsub := inSubtree_succ_of_ne hiu (hw.le_self i hi.le)
  rcases Sym2.eq_iff.mp hti with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2, hsub]
  · rw [h1, h2, hsub]

/-- Between the discovery step `u` and its return step `d`, the walk stays inside the subtree of
`u + 1`. -/
private theorem inSubtree_eq_true_of_between {w : ℕ → ℕ} (hw : IsTreeWalk m w) {u d : ℕ}
    (hup : w (u + 1) = u + 1)
    (hfiber : {t ∈ range (2 * m) | s(w t, w (t + 1)) = s(w u, w (u + 1))} = {u, d})
    {t : ℕ} (hut : u + 1 ≤ t) (htd : t ≤ d) (hd : d < 2 * m) :
    inSubtree w u (w t) = true := by
  induction t, hut using Nat.le_induction with
  | base => rw [hup, inSubtree_succ_self]
  | succ s hsu ih =>
    have hs : s < 2 * m := by omega
    have hnot : s ∉ ({u, d} : Finset ℕ) := by simp; omega
    have hne : s(w s, w (s + 1)) ≠ s(w u, w (u + 1)) := by
      intro heq
      apply hnot
      rw [← hfiber]
      exact mem_filter.mpr ⟨mem_range.mpr hs, heq⟩
    rw [inSubtree_step_eq_of_edge_ne hw hs hup hne]
    exact ih (by omega)

/-- Strictly after the return step `d` of the edge discovered at `u`, the walk stays outside the
subtree of `u + 1`. -/
private theorem inSubtree_eq_false_of_after {w : ℕ → ℕ} (hw : IsTreeWalk m w) {u d : ℕ}
    (hu : u < d) (hup : w (u + 1) = u + 1)
    (hfiber : {t ∈ range (2 * m) | s(w t, w (t + 1)) = s(w u, w (u + 1))} = {u, d}) :
    ∀ r ≤ 2 * m - (d + 1), inSubtree w u (w (2 * m - r)) = false := by
  intro r
  induction r with
  | zero =>
    intro _
    simp [hw.closed]
  | succ r ih =>
    intro hr
    have hs : 2 * m - (r + 1) < 2 * m := by omega
    have hstep : 2 * m - (r + 1) + 1 = 2 * m - r := by omega
    have hnot : 2 * m - (r + 1) ∉ ({u, d} : Finset ℕ) := by simp; omega
    have hne : s(w (2 * m - (r + 1)), w (2 * m - (r + 1) + 1)) ≠ s(w u, w (u + 1)) := by
      intro heq
      apply hnot
      rw [← hfiber]
      exact mem_filter.mpr ⟨mem_range.mpr hs, heq⟩
    have hinv := inSubtree_step_eq_of_edge_ne hw hs hup hne
    rw [hstep] at hinv
    exact hinv.symm.trans (ih (by omega))

/-- Equivalence of steps traversing the same unordered edge of a closed tree walk. -/
private def edgeSetoid (w : ClosedTreeWalk m) : Setoid (Fin (2 * m)) :=
  Setoid.ker fun i : Fin (2 * m) ↦ s(w.1 i, w.1 (i + 1))

private instance decidableRel_edgeSetoid (w : ClosedTreeWalk m) :
    DecidableRel (edgeSetoid w) :=
  fun i j ↦ inferInstanceAs (Decidable (s(w.1 i, w.1 (i + 1)) = s(w.1 j, w.1 (j + 1))))

/-- The partition of `Fin (2 * m)` into the two-element unordered-edge fibers of a closed tree
walk. -/
def edgePartition (w : ClosedTreeWalk m) : Finpartition (univ : Finset (Fin (2 * m))) :=
  Finpartition.ofSetoid (edgeSetoid w)

/-- Two steps lie in the same block of `edgePartition` exactly when they traverse the same
unordered edge. -/
@[simp]
theorem mem_part_edgePartition_iff (w : ClosedTreeWalk m) (i j : Fin (2 * m)) :
    j ∈ (edgePartition w).part i ↔ s(w.1 i, w.1 (i + 1)) = s(w.1 j, w.1 (j + 1)) := by
  rw [edgePartition, Finpartition.mem_part_ofSetoid_iff_rel]
  rfl

/-- Each block of `edgePartition` is the fiber of an unordered edge. -/
theorem part_edgePartition_eq_filter (w : ClosedTreeWalk m) (i : Fin (2 * m)) :
    (edgePartition w).part i =
      ({j : Fin (2 * m) | s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1))} : Finset _) := by
  ext j
  simp [eq_comm]

/-- Every block of `edgePartition` has two elements. -/
theorem isPairing_edgePartition (w : ClosedTreeWalk m) : (edgePartition w).IsPairing := by
  rw [Finpartition.isPairing_iff_part]
  intro i _
  rw [part_edgePartition_eq_filter]
  refine Eq.trans ?_ (w.2.1.card_edge i i.isLt)
  refine card_bij (fun j _ ↦ j.val)
    (fun j hj ↦ mem_filter.mpr ⟨mem_range.mpr j.isLt, (mem_filter.mp hj).2⟩)
    (fun _ _ _ _ h ↦ Fin.ext h) ?_
  intro j hj
  obtain ⟨hjr, hje⟩ := mem_filter.mp hj
  exact ⟨⟨j, mem_range.mp hjr⟩, mem_filter.mpr ⟨mem_univ _, hje⟩, rfl⟩

/-- Characterize an oriented arc `a < b` of the edge matching as a discovery step `a` paired with
its return step `b`. -/
private theorem up_and_fiber_of_lt_partner (w : ClosedTreeWalk m) {a b : Fin (2 * m)}
    (hab : a < b) (hpartner : w.isPairing_edgePartition.toPerfectMatching.val a = b) :
    w.1 (a + 1) = a + 1 ∧ w.1 b = a + 1 ∧
      {t ∈ range (2 * m) | s(w.1 t, w.1 (t + 1)) = s(w.1 a, w.1 (a + 1))} = {a.val, b.val} := by
  have hb := ((w.isPairing_edgePartition.toPerfectMatching_apply_eq_iff a b).mp hpartner).1
  rw [mem_part_edgePartition_iff] at hb
  obtain ⟨u, hu, huup, hau⟩ := w.2.1.exists_up_edge a.isLt
  have hau' : s(w.1 a, w.1 (a + 1)) = s(w.1 u, w.1 (u + 1)) := by rwa [huup]
  obtain ⟨d, hd, hwd, -, hfiber⟩ := w.2.1.exists_edge_fiber_eq_pair hu huup
  have hud : u < d := by
    have hle := w.2.1.le_self d hd.le
    omega
  have ha_mem : a.val ∈ ({u, d} : Finset ℕ) := by
    rw [← hfiber]
    exact mem_filter.mpr ⟨mem_range.mpr a.isLt, hau'⟩
  have hb_mem : b.val ∈ ({u, d} : Finset ℕ) := by
    rw [← hfiber]
    exact mem_filter.mpr ⟨mem_range.mpr b.isLt, hb.symm.trans hau'⟩
  simp only [mem_insert, mem_singleton] at ha_mem hb_mem
  have : a.val < b.val := hab
  rcases ha_mem with ha_eq | ha_eq <;> rcases hb_mem with hb_eq | hb_eq
  · omega
  · subst ha_eq hb_eq
    exact ⟨huup, hwd, by rwa [hau']⟩
  · omega
  · omega

/-- The unordered-edge matching of a closed tree walk is noncrossing. -/
theorem isNoncrossingMatching_edgePartition (w : ClosedTreeWalk m) :
    w.isPairing_edgePartition.toPerfectMatching.val.IsNoncrossingMatching := by
  rw [Equiv.Perm.isNoncrossingMatching_iff]
  intro a b hab hba hcross
  set σ := w.isPairing_edgePartition.toPerfectMatching.val
  have hbσb : b < σ b := lt_trans hba hcross
  obtain ⟨haup, -, hafiber⟩ := up_and_fiber_of_lt_partner w (lt_trans hab hba) rfl
  obtain ⟨hbup, hbw, -⟩ := up_and_fiber_of_lt_partner w hbσb rfl
  have hin : inSubtree w.1 a (w.1 (b + 1)) = true :=
    inSubtree_eq_true_of_between w.2.1 haup hafiber (by omega) (by omega) (σ a).isLt
  have hout : inSubtree w.1 a (w.1 (σ b)) = false := by
    have h := inSubtree_eq_false_of_after w.2.1 (lt_trans hab hba) haup hafiber
      (2 * m - (σ b).val) (by omega)
    have hsub : 2 * m - (2 * m - (σ b).val) = (σ b).val := by omega
    rwa [hsub] at h
  rw [hbup] at hin
  rw [hbw] at hout
  exact Bool.false_ne_true (hout.symm.trans hin)

/-- The **planar matching of a closed tree walk**: each step in `Fin (2 * m)` is paired with the
unique other step traversing the same unordered edge. -/
def toPlanarMatching (w : ClosedTreeWalk m) : PlanarMatching (2 * m) :=
  ⟨w.isPairing_edgePartition.toPerfectMatching, w.isNoncrossingMatching_edgePartition⟩

/-- Two steps are partners in `w.toPlanarMatching` precisely when they are distinct and traverse
the same unordered edge. -/
@[simp]
theorem toPlanarMatching_apply_eq_iff (w : ClosedTreeWalk m) (i j : Fin (2 * m)) :
    w.toPlanarMatching.1.val i = j ↔
      s(w.1 i, w.1 (i + 1)) = s(w.1 j, w.1 (j + 1)) ∧ j ≠ i := by
  simpa only [toPlanarMatching, mem_part_edgePartition_iff] using
    w.isPairing_edgePartition.toPerfectMatching_apply_eq_iff i j

/-- An arc of `w.toPlanarMatching` opens at step `i` if and only if step `i` discovers a new
vertex. -/
theorem lt_toPlanarMatching_iff (w : ClosedTreeWalk m) (i : Fin (2 * m)) :
    i < w.toPlanarMatching.1.val i ↔ upSteps m w.1 i = true := by
  rw [upSteps_eq_true_iff]
  constructor
  · intro hi
    exact ⟨i.isLt, (up_and_fiber_of_lt_partner w hi rfl).1⟩
  · rintro ⟨-, hup⟩
    obtain ⟨d, hd, hwd, -, hfiber⟩ := w.2.1.exists_edge_fiber_eq_pair i.isLt hup
    have hid : i.val < d := by
      have hle := w.2.1.le_self d hd.le
      omega
    let d' : Fin (2 * m) := ⟨d, hd⟩
    have hd_mem : d ∈ {t ∈ range (2 * m) | s(w.1 t, w.1 (t + 1)) = s(w.1 i, w.1 (i + 1))} := by
      rw [hfiber]
      simp
    have hpartner : w.toPlanarMatching.1.val i = d' :=
      (w.toPlanarMatching_apply_eq_iff i d').mpr
        ⟨(mem_filter.mp hd_mem).2.symm, Fin.ne_of_gt hid⟩
    rw [hpartner]
    exact hid

/-- The Dyck step of `w.toPlanarMatching` at `i` is `U` on discovery steps and `D` on return
steps. -/
@[simp]
theorem dyckStep_toPlanarMatching (w : ClosedTreeWalk m) (i : Fin (2 * m)) :
    w.toPlanarMatching.dyckStep i = if upSteps m w.1 i then DyckStep.U else DyckStep.D := by
  cases h : upSteps m w.1 i
  · simp only [Bool.false_eq_true, ↓reduceIte, PlanarMatching.dyckStep_eq_D_iff]
    have hnot : ¬ i < w.toPlanarMatching.1.val i := by
      rw [w.lt_toPlanarMatching_iff i, h]
      decide
    exact (not_lt.mp hnot).lt_of_ne (w.toPlanarMatching.1.apply_ne i)
  · simp only [↓reduceIte, PlanarMatching.dyckStep_eq_U_iff]
    exact (w.lt_toPlanarMatching_iff i).mpr h

/-- The Dyck word of the edge matching of a closed tree walk agrees with `closedTreeWalkEquiv`. -/
@[simp]
theorem toDyckWord_toPlanarMatching (w : ClosedTreeWalk m) :
    w.toPlanarMatching.toDyckWord = (closedTreeWalkEquiv m w).1 := by
  ext1
  rw [PlanarMatching.toList_toDyckWord, closedTreeWalkEquiv_apply_coe]
  congr 1
  funext i
  exact dyckStep_toPlanarMatching w i

/-- Equivalence between closed tree walks of length `2 * m` and planar matchings of `2 * m`
points, sending each walk to its unordered-edge pairing. -/
def planarMatchingEquiv (m : ℕ) : ClosedTreeWalk m ≃ PlanarMatching (2 * m) where
  toFun := toPlanarMatching
  invFun x := (closedTreeWalkEquiv m).symm (PlanarMatching.dyckWordEquiv m x)
  left_inv w := by
    apply (closedTreeWalkEquiv m).injective
    apply Subtype.ext
    simp
  right_inv x := by
    apply PlanarMatching.toDyckWord_injective
    rw [toDyckWord_toPlanarMatching, Equiv.apply_symm_apply, PlanarMatching.coe_dyckWordEquiv_apply]

/-- Applying `planarMatchingEquiv` computes `toPlanarMatching`. -/
@[simp]
theorem planarMatchingEquiv_apply (w : ClosedTreeWalk m) :
    planarMatchingEquiv m w = w.toPlanarMatching := (rfl)

/-- **Closed-walk to noncrossing-pairing bridge.** Closed tree walks of length `2 * m` are
equivalent to noncrossing pair partitions of `Fin (2 * m)`, with each two-element block recording
the two traversals of an unordered tree edge. -/
def noncrossingPairingEquiv (m : ℕ) :
    ClosedTreeWalk m ≃
      {P : NoncrossingPartition (univ : Finset (Fin (2 * m))) // P.val.IsPairing} :=
  (planarMatchingEquiv m).trans PerfectMatching.noncrossingPairingEquiv

/-- The underlying partition of `noncrossingPairingEquiv m w` is `w.edgePartition`. -/
@[simp]
theorem noncrossingPairingEquiv_apply_coe (w : ClosedTreeWalk m) :
    (noncrossingPairingEquiv m w).val.val = w.edgePartition := by
  simp [noncrossingPairingEquiv, toPlanarMatching]

/-- Every block of `noncrossingPairingEquiv m w` is the two-element fiber of an unordered edge. -/
theorem part_noncrossingPairingEquiv (w : ClosedTreeWalk m) (i : Fin (2 * m)) :
    (noncrossingPairingEquiv m w).val.val.part i =
      ({j : Fin (2 * m) | s(w.1 j, w.1 (j + 1)) = s(w.1 i, w.1 (i + 1))} : Finset _) := by
  rw [noncrossingPairingEquiv_apply_coe, part_edgePartition_eq_filter]

end ClosedTreeWalk

end TauCeti.TreeWalk
