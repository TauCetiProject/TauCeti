/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PlanarMatching.DyckWord
public import TauCeti.Combinatorics.TreeWalk.Basic
import Mathlib.Data.Fintype.Fin

/-!
# Step pairings of closed tree walks

In a closed tree walk `w` of length `2 * k`, every unordered edge is traversed by exactly two steps,
once as an up step and once in the opposite direction as a down step, and no two equal-edge step
pairs interleave. Grouping the `2 * k` steps `Fin (2 * k)` by their unordered edge
`s(w a, w (a + 1))` therefore defines a noncrossing pair partition of `Fin (2 * k)` and,
equivalently, a planar matching of `2 * k` boundary points.

An arc of this planar matching opens at step `a` (`a < σ a`) precisely when step `a` is an up step
of `w`, so the Dyck word of the planar matching coincides with the Dyck word of `w` under
`closedTreeWalkEquiv`. Composing with the Dyck-word characterization of planar matchings yields
explicit equivalences between `ClosedTreeWalk k`, `PlanarMatching (2 * k)`, and noncrossing
pairings of `Fin (2 * k)`.

## Main definitions

* `TauCeti.TreeWalk.ClosedTreeWalk.toNoncrossingPairing`: the noncrossing pair partition of
  `Fin (2 * k)` into the two-element unordered-edge fibers of a closed tree walk.
* `TauCeti.TreeWalk.ClosedTreeWalk.toPlanarMatching`: the planar matching sending each step of a
  closed tree walk to the unique other step traversing the same unordered edge.
* `TauCeti.TreeWalk.ClosedTreeWalk.planarMatchingEquiv`: equivalence between `ClosedTreeWalk k` and
  `PlanarMatching (2 * k)`.
* `TauCeti.TreeWalk.ClosedTreeWalk.noncrossingPairingEquiv`: equivalence between `ClosedTreeWalk k`
  and `{P : NoncrossingPartition (Finset.univ : Finset (Fin (2 * k))) // P.val.IsPairing}`.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.1.3, Lemma 2.1.6.
-/

public section

open Finset

namespace TauCeti.TreeWalk.ClosedTreeWalk

variable {k : ℕ}

/-- Partition the `2 * k` steps of a closed tree walk into the two-element fibers of the unordered
edge map `a ↦ s(w a, w (a + 1))`. -/
def toNoncrossingPairing (w : ClosedTreeWalk k) :
    {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing} :=
  let r : Setoid (Fin (2 * k)) := Setoid.ker fun a : Fin (2 * k) ↦ s(w.1 a, w.1 ((a : ℕ) + 1))
  letI : DecidableRel r := fun a b ↦ decEq (s(w.1 a, w.1 ((a : ℕ) + 1)))
    (s(w.1 b, w.1 ((b : ℕ) + 1)))
  let P : Finpartition (univ : Finset (Fin (2 * k))) := Finpartition.ofSetoid r
  have hnc : P.IsNoncrossing := by
    rw [Finpartition.isNoncrossing_iff_part]
    intro a _ b _ c hc d hd hab hbc hcd
    rw [Finpartition.mem_part_ofSetoid_iff_rel] at hc hd
    exact (w.2.1.sym2_ne_of_lt_of_lt_of_lt_of_sym2_eq (Fin.lt_def.mp hab) (Fin.lt_def.mp hbc)
      (Fin.lt_def.mp hcd) d.isLt hc hd).elim
  have hpair : P.IsPairing := by
    rw [Finpartition.isPairing_iff_part]
    intro a _
    refine Eq.trans ?_ (w.2.1.card_edge a a.isLt)
    rw [← Finset.image_fin_univ, filter_image, card_image_of_injective _ Fin.val_injective]
    refine congrArg card (ext fun b ↦ ?_)
    simp [P, r, Finpartition.mem_part_ofSetoid_iff_rel, eq_comm]
  ⟨⟨P, hnc⟩, hpair⟩

/-- Two steps belong to the same block of `w.toNoncrossingPairing` precisely when they traverse the
same unordered edge. -/
@[simp]
theorem mem_part_toNoncrossingPairing (w : ClosedTreeWalk k) (a b : Fin (2 * k)) :
    b ∈ w.toNoncrossingPairing.1.1.part a ↔
      s(w.1 b, w.1 ((b : ℕ) + 1)) = s(w.1 a, w.1 ((a : ℕ) + 1)) := by
  simp only [toNoncrossingPairing, Finpartition.mem_part_ofSetoid_iff_rel]
  exact eq_comm

/-- Each block of `w.toNoncrossingPairing` is the unordered-edge fiber of its representative. -/
theorem part_toNoncrossingPairing (w : ClosedTreeWalk k) (a : Fin (2 * k)) :
    w.toNoncrossingPairing.1.1.part a =
      {b : Fin (2 * k) | s(w.1 b, w.1 ((b : ℕ) + 1)) = s(w.1 a, w.1 ((a : ℕ) + 1))} := by
  ext b
  simp

/-- The planar matching of `Fin (2 * k)` sending each step of a closed tree walk to the unique
other step traversing the same unordered edge. -/
def toPlanarMatching (w : ClosedTreeWalk k) : PlanarMatching (2 * k) :=
  PerfectMatching.noncrossingPairingEquiv.symm w.toNoncrossingPairing

/-- The partner of step `a` in `w.toPlanarMatching` is characterized as the unique step `b ≠ a`
traversing the same unordered edge. -/
@[simp]
theorem toPlanarMatching_apply_eq_iff (w : ClosedTreeWalk k) (a b : Fin (2 * k)) :
    w.toPlanarMatching.1.val a = b ↔
      b ≠ a ∧ s(w.1 b, w.1 ((b : ℕ) + 1)) = s(w.1 a, w.1 ((a : ℕ) + 1)) := by
  rw [toPlanarMatching, PerfectMatching.noncrossingPairingEquiv_symm_apply_val,
    Finpartition.IsPairing.toPerfectMatching_apply_eq_iff, mem_part_toNoncrossingPairing, and_comm]

/-- Every step and its partner in `w.toPlanarMatching` traverse the same unordered edge. -/
@[simp]
theorem sym2_toPlanarMatching_apply (w : ClosedTreeWalk k) (a : Fin (2 * k)) :
    s(w.1 (w.toPlanarMatching.1.val a), w.1 ((w.toPlanarMatching.1.val a : ℕ) + 1)) =
      s(w.1 a, w.1 ((a : ℕ) + 1)) :=
  ((w.toPlanarMatching_apply_eq_iff a _).mp rfl).2

/-- The partner step in `w.toPlanarMatching` starts at the endpoint of step `a`. -/
theorem val_toPlanarMatching_apply (w : ClosedTreeWalk k) (a : Fin (2 * k)) :
    w.1 (w.toPlanarMatching.1.val a) = w.1 ((a : ℕ) + 1) := by
  obtain ⟨hne, heq⟩ := (w.toPlanarMatching_apply_eq_iff a _).mp rfl
  exact (w.2.1.eq_and_eq_of_ne_of_sym2_eq (w.toPlanarMatching.1.val a).isLt a.isLt
    (Fin.val_ne_of_ne hne) heq).1

/-- The partner step in `w.toPlanarMatching` ends at the starting vertex of step `a`. -/
theorem val_toPlanarMatching_apply_add_one (w : ClosedTreeWalk k) (a : Fin (2 * k)) :
    w.1 ((w.toPlanarMatching.1.val a : ℕ) + 1) = w.1 a := by
  obtain ⟨hne, heq⟩ := (w.toPlanarMatching_apply_eq_iff a _).mp rfl
  exact (w.2.1.eq_and_eq_of_ne_of_sym2_eq (w.toPlanarMatching.1.val a).isLt a.isLt
    (Fin.val_ne_of_ne hne) heq).2

/-- An arc of `w.toPlanarMatching` opens at step `a` precisely when step `a` is an up step of `w`.
-/
theorem lt_toPlanarMatching_apply_iff (w : ClosedTreeWalk k) (a : Fin (2 * k)) :
    a < w.toPlanarMatching.1.val a ↔ w.1 ((a : ℕ) + 1) = (a : ℕ) + 1 := by
  set b := w.toPlanarMatching.1.val a
  obtain ⟨hne, heq⟩ := (w.toPlanarMatching_apply_eq_iff a b).mp rfl
  constructor
  · intro hab
    exact (w.2.1.up_and_down_of_lt_of_sym2_eq (Fin.lt_def.mp hab) b.isLt heq.symm).1
  · intro hup
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨_, _, ha1⟩ :=
        w.2.1.up_and_down_of_lt_of_sym2_eq (Fin.lt_def.mp hlt) a.isLt heq
      have hle := w.2.1.le_self b b.isLt.le
      have := Fin.lt_def.mp hlt
      omega
    · exact hgt

/-- The Dyck word of `w.toPlanarMatching` agrees with the Dyck word of `w` under
`closedTreeWalkEquiv`. -/
@[simp]
theorem toDyckWord_toPlanarMatching (w : ClosedTreeWalk k) :
    w.toPlanarMatching.toDyckWord = (closedTreeWalkEquiv k w).1 := by
  ext1
  rw [PlanarMatching.toList_toDyckWord, closedTreeWalkEquiv_apply_coe]
  refine congrArg List.ofFn (funext fun a ↦ ?_)
  by_cases h : a < w.toPlanarMatching.1.val a
  · have hup : upSteps k w.1 a = true :=
      upSteps_eq_true_iff.mpr ⟨a.isLt, (w.lt_toPlanarMatching_apply_iff a).mp h⟩
    simpa [hup] using h
  · have hup : upSteps k w.1 a = false :=
      Bool.eq_false_iff.mpr fun ht ↦
        h ((w.lt_toPlanarMatching_apply_iff a).mpr (upSteps_eq_true_iff.mp ht).2)
    simpa [hup] using (not_lt.mp h).lt_of_ne (w.toPlanarMatching.1.apply_ne a)

/-- Closed tree walks of length `2 * k` are in bijection with planar matchings of `2 * k` points:
forward by matching equal-edge steps, backward by taking the tree walk of the matching's Dyck word.
-/
def planarMatchingEquiv (k : ℕ) : ClosedTreeWalk k ≃ PlanarMatching (2 * k) where
  toFun := toPlanarMatching
  invFun x := (closedTreeWalkEquiv k).symm ⟨x.toDyckWord, x.semilength_toDyckWord⟩
  left_inv w := by
    dsimp only
    have h : (⟨w.toPlanarMatching.toDyckWord, w.toPlanarMatching.semilength_toDyckWord⟩ :
        {p : DyckWord // p.semilength = k}) = closedTreeWalkEquiv k w :=
      Subtype.ext w.toDyckWord_toPlanarMatching
    rw [h, Equiv.symm_apply_apply]
  right_inv x := PlanarMatching.toDyckWord_injective <| by
    rw [toDyckWord_toPlanarMatching, Equiv.apply_symm_apply]

/-- The forward map of `planarMatchingEquiv` is `toPlanarMatching`. -/
@[simp]
theorem planarMatchingEquiv_apply (k : ℕ) (w : ClosedTreeWalk k) :
    planarMatchingEquiv k w = w.toPlanarMatching :=
  (rfl)

/-- The inverse of `planarMatchingEquiv` reconstructs the closed tree walk from the Dyck word of
the planar matching. -/
theorem planarMatchingEquiv_symm_apply (k : ℕ) (x : PlanarMatching (2 * k)) :
    (planarMatchingEquiv k).symm x =
      (closedTreeWalkEquiv k).symm ⟨x.toDyckWord, x.semilength_toDyckWord⟩ :=
  (rfl)

/-- The planar matching of the closed tree walk reconstructed from `x` is `x`. -/
@[simp]
theorem toPlanarMatching_planarMatchingEquiv_symm_apply (k : ℕ) (x : PlanarMatching (2 * k)) :
    ((planarMatchingEquiv k).symm x).toPlanarMatching = x :=
  (planarMatchingEquiv k).apply_symm_apply x

/-- Reconstructing a closed tree walk from `w.toPlanarMatching` recovers `w`. -/
@[simp]
theorem planarMatchingEquiv_symm_toPlanarMatching (w : ClosedTreeWalk k) :
    (planarMatchingEquiv k).symm w.toPlanarMatching = w :=
  (planarMatchingEquiv k).symm_apply_apply w

/-- Closed tree walks of length `2 * k` are in bijection with noncrossing pair partitions of
`Fin (2 * k)`, sending each walk to its partition into two-element unordered-edge fibers. -/
def noncrossingPairingEquiv (k : ℕ) :
    ClosedTreeWalk k ≃
      {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing} :=
  (planarMatchingEquiv k).trans PerfectMatching.noncrossingPairingEquiv

/-- The forward map of `noncrossingPairingEquiv` is `toNoncrossingPairing`. -/
@[simp]
theorem noncrossingPairingEquiv_apply (k : ℕ) (w : ClosedTreeWalk k) :
    noncrossingPairingEquiv k w = w.toNoncrossingPairing := by
  simp [noncrossingPairingEquiv, toPlanarMatching]

/-- The inverse of `noncrossingPairingEquiv` maps a noncrossing pairing to the closed tree walk of
its planar matching. -/
theorem noncrossingPairingEquiv_symm_apply (k : ℕ)
    (P : {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing}) :
    (noncrossingPairingEquiv k).symm P =
      (planarMatchingEquiv k).symm (PerfectMatching.noncrossingPairingEquiv.symm P) :=
  (rfl)

/-- The noncrossing pairing of the closed tree walk reconstructed from `P` is `P`. -/
@[simp]
theorem toNoncrossingPairing_noncrossingPairingEquiv_symm_apply (k : ℕ)
    (P : {P : NoncrossingPartition (univ : Finset (Fin (2 * k))) // P.val.IsPairing}) :
    ((noncrossingPairingEquiv k).symm P).toNoncrossingPairing = P := by
  rw [← noncrossingPairingEquiv_apply, Equiv.apply_symm_apply]

/-- Reconstructing a closed tree walk from `w.toNoncrossingPairing` recovers `w`. -/
@[simp]
theorem noncrossingPairingEquiv_symm_toNoncrossingPairing (w : ClosedTreeWalk k) :
    (noncrossingPairingEquiv k).symm w.toNoncrossingPairing = w := by
  rw [← noncrossingPairingEquiv_apply, Equiv.symm_apply_apply]

end TauCeti.TreeWalk.ClosedTreeWalk
