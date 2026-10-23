/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.Cyclic
public import TauCeti.KnotTheory.PDCode.Oriented.Reidemeister.Three
import Mathlib.Tactic.FinCases

/-!
# The braid relation in braid-word closures

The braid relation `σ i σ (i + 1) σ i = σ (i + 1) σ i σ (i + 1)` is the third Reidemeister move:
the three crossings of either side bound a triangle in the closure diagram, and the move slides one
strand across the crossing of the other two. This file proves that replacing the three letters
`σ i ^ ε₁ σ (i + 1) ^ ε₂ σ i ^ ε₃` of a braid word by `σ (i + 1) ^ ε₃ σ i ^ ε₂ σ (i + 1) ^ ε₁`
gives a Reidemeister equivalent closure, provided the signs give the three strands an acyclic height
order (`ε₁ = ε₃` forces `ε₂ = ε₁`). With all three signs equal this is the braid relation itself.

Like cyclic rotation (`TauCeti.BraidWord.reidemeisterEquiv_closure_rotate`) and the exchange of
letters on disjoint strands (`TauCeti.BraidWord.reidemeisterEquiv_closure_append_cons_cons_comm`),
this is the diagram-level form of a relation of the braid group: it is one step towards showing
that braid words representing the same braid have Reidemeister equivalent closures, the
combinatorial half of the comparison between Markov equivalence of braids and Reidemeister
equivalence of their closures.

## Main results

* `TauCeti.BraidWord.reidemeisterEquiv_closure_append_cons_cons_cons_braid`: the closures of two
  braid words related by the braid relation are Reidemeister equivalent.

## Implementation notes

After a cyclic rotation the three letters are at the bottom of the word. In the closure their
crossings `0`, `1`, `2` form the triangular tangle of `TauCeti.PDCode.reidemeisterThree` once each
of them is read from its opposite slot: the closure numbers the slots of a crossing from the
south-east and the move from the north-west. The move at the triangle `2, 1, 0` then produces
exactly the closure of the other word, read in the same way. Its arcs are compared at the slots
where strands leave their crossings (`TauCeti.BraidWord.edgePair_closure_eq_of_outgoingSlot`).
Along the three strand positions of the triangle the crossings of the remaining letters are met in
the same order in both words, and only the arcs entering or leaving the triangle are moved.

## References

* E. Artin, *Theorie der Zöpfe*, Abh. Math. Sem. Univ. Hamburg 4 (1925), 47-72.
* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82 (1974),
  Chapters 1 and 2.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 1.
-/

public section

namespace TauCeti

namespace BraidWord

open BraidGroup PDCode

variable {n m : ℕ}

/-! ### Reading a crossing from its opposite slot -/

/-- Read the crossing `k` from its opposite slot: two quarter turns. -/
private def halfTurn (D : OrientedPDCode m) (k : Fin m) : OrientedPDCode m :=
  (D.rotateCrossing k).rotateCrossing k

private theorem halfTurn_crossing_self (D : OrientedPDCode m) (k : Fin m) (s : Fin 4) :
    (halfTurn D k).crossing k s = D.crossing k (s + 2) := by
  simp [halfTurn, add_assoc]

private theorem halfTurn_crossing_of_ne (D : OrientedPDCode m) {k k' : Fin m} (h : k' ≠ k)
    (s : Fin 4) : (halfTurn D k).crossing k' s = D.crossing k' s := by
  simp [halfTurn, h]

private theorem reidemeisterEquiv_halfTurn (D : OrientedPDCode m) (k : Fin m) :
    OrientedPDCode.ReidemeisterEquiv D (halfTurn D k) :=
  (OrientedPDCode.reidemeisterEquiv_rotateCrossing D k).trans
    (OrientedPDCode.reidemeisterEquiv_rotateCrossing _ k)

private theorem halfTurn_halfEdge_congr {D D' : OrientedPDCode m} (h : D.halfEdge = D'.halfEdge)
    (k : Fin m) : (halfTurn D k).halfEdge = (halfTurn D' k).halfEdge := by
  refine Equiv.ext fun x ↦ ?_
  obtain ⟨⟨k', s⟩, rfl⟩ := (crossingSlotEquiv m).surjective x
  by_cases hk : k' = k
  · subst hk
    have h₁ := halfTurn_crossing_self D k' s
    have h₂ := halfTurn_crossing_self D' k' s
    simp only [crossing_apply] at h₁ h₂
    rw [h₁, h₂, h]
  · have h₁ := halfTurn_crossing_of_ne D hk s
    have h₂ := halfTurn_crossing_of_ne D' hk s
    simp only [crossing_apply] at h₁ h₂
    rw [h₁, h₂, h]

@[simp] private theorem halfTurn_edgePair (D : OrientedPDCode m) (k : Fin m) :
    (halfTurn D k).edgePair = D.edgePair := by
  simp [halfTurn]

@[simp] private theorem halfTurn_overPair (D : OrientedPDCode m) (k : Fin m) :
    (halfTurn D k).overPair = D.overPair := by
  funext k'
  by_cases h : k' = k
  · subst h; simp [halfTurn]
  · simp [halfTurn, h]

@[simp] private theorem halfTurn_orientation (D : OrientedPDCode m) (k : Fin m) :
    (halfTurn D k).orientation = D.orientation := by
  simp [halfTurn]

@[simp] private theorem halfTurn_crossinglessComponents (D : OrientedPDCode m) (k : Fin m) :
    (halfTurn D k).crossinglessComponents = D.crossinglessComponents := by
  simp [halfTurn]

@[simp] private theorem halfTurn_crossinglessComponentCount (D : OrientedPDCode m) (k : Fin m) :
    (halfTurn D k).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [halfTurn]

variable {N : ℕ}

/-! ### The three bottom crossings, read from their opposite slots -/

/-- Read each of the three bottom crossings from its opposite slot. -/
private def readTriple (D : OrientedPDCode (N + 1 + 1 + 1)) : OrientedPDCode (N + 1 + 1 + 1) :=
  halfTurn (halfTurn (halfTurn D 0) 1) 2

private theorem readTriple_halfEdge_congr {D D' : OrientedPDCode (N + 1 + 1 + 1)}
    (h : D.halfEdge = D'.halfEdge) : (readTriple D).halfEdge = (readTriple D').halfEdge :=
  halfTurn_halfEdge_congr (halfTurn_halfEdge_congr (halfTurn_halfEdge_congr h 0) 1) 2

private theorem reidemeisterEquiv_readTriple (D : OrientedPDCode (N + 1 + 1 + 1)) :
    OrientedPDCode.ReidemeisterEquiv D (readTriple D) :=
  ((reidemeisterEquiv_halfTurn D 0).trans (reidemeisterEquiv_halfTurn _ 1)).trans
    (reidemeisterEquiv_halfTurn _ 2)

@[simp] private theorem readTriple_edgePair (D : OrientedPDCode (N + 1 + 1 + 1)) :
    (readTriple D).edgePair = D.edgePair := by
  simp [readTriple]

@[simp] private theorem readTriple_overPair (D : OrientedPDCode (N + 1 + 1 + 1)) :
    (readTriple D).overPair = D.overPair := by
  simp [readTriple]

@[simp] private theorem readTriple_orientation (D : OrientedPDCode (N + 1 + 1 + 1)) :
    (readTriple D).orientation = D.orientation := by
  simp [readTriple]

@[simp] private theorem readTriple_crossinglessComponents (D : OrientedPDCode (N + 1 + 1 + 1)) :
    (readTriple D).crossinglessComponents = D.crossinglessComponents := by
  simp [readTriple]

@[simp] private theorem readTriple_crossinglessComponentCount (D : OrientedPDCode (N + 1 + 1 + 1)) :
    (readTriple D).crossinglessComponentCount = D.crossinglessComponentCount := by
  simp [readTriple]

private abbrev sh (k : Fin N) : Fin (N + 1 + 1 + 1) := k.succ.succ.succ

@[simp high] private theorem val_zero_fin : ((0 : Fin (N + 1 + 1 + 1)) : ℕ) = 0 := by
  simp

@[simp high] private theorem val_one_fin : ((1 : Fin (N + 1 + 1 + 1)) : ℕ) = 1 := by
  simp

@[simp high] private theorem val_two_fin : ((2 : Fin (N + 1 + 1 + 1)) : ℕ) = 2 :=
  Fin.val_two

private theorem sh_ne_zero (k : Fin N) : sh k ≠ 0 := Fin.succ_ne_zero _
private theorem sh_ne_one (k : Fin N) : sh k ≠ 1 := by simp [Fin.ext_iff]
private theorem sh_ne_two (k : Fin N) : sh k ≠ 2 := by simp [Fin.ext_iff]

private theorem readTriple_crossing_triple (D : OrientedPDCode (N + 1 + 1 + 1))
    {k : Fin (N + 1 + 1 + 1)} (hk : k = 0 ∨ k = 1 ∨ k = 2) (s : Fin 4) :
    (readTriple D).crossing k s = D.crossing k (s + 2) := by
  have h01 : (0 : Fin (N + 1 + 1 + 1)) ≠ 1 := by simp
  have h02 : (0 : Fin (N + 1 + 1 + 1)) ≠ 2 := by simp [Fin.ext_iff]
  have h12 : (1 : Fin (N + 1 + 1 + 1)) ≠ 2 := by simp [Fin.ext_iff]
  rcases hk with rfl | rfl | rfl
  · rw [readTriple, halfTurn_crossing_of_ne _ h02, halfTurn_crossing_of_ne _ h01,
      halfTurn_crossing_self]
  · rw [readTriple, halfTurn_crossing_of_ne _ h12, halfTurn_crossing_self,
      halfTurn_crossing_of_ne _ h01.symm]
  · rw [readTriple, halfTurn_crossing_self, halfTurn_crossing_of_ne _ h12.symm,
      halfTurn_crossing_of_ne _ h02.symm]

@[simp] private theorem readTriple_halfEdge_zero (D : OrientedPDCode (N + 1 + 1 + 1)) (s : Fin 4) :
    (readTriple D).halfEdge (crossingSlotEquiv _ (0, s)) =
      D.halfEdge (crossingSlotEquiv _ (0, s + 2)) := by
  simpa using readTriple_crossing_triple D (Or.inl rfl) s

@[simp] private theorem readTriple_halfEdge_one (D : OrientedPDCode (N + 1 + 1 + 1)) (s : Fin 4) :
    (readTriple D).halfEdge (crossingSlotEquiv _ (1, s)) =
      D.halfEdge (crossingSlotEquiv _ (1, s + 2)) := by
  simpa using readTriple_crossing_triple D (Or.inr (Or.inl rfl)) s

@[simp] private theorem readTriple_halfEdge_two (D : OrientedPDCode (N + 1 + 1 + 1)) (s : Fin 4) :
    (readTriple D).halfEdge (crossingSlotEquiv _ (2, s)) =
      D.halfEdge (crossingSlotEquiv _ (2, s + 2)) := by
  simpa using readTriple_crossing_triple D (Or.inr (Or.inr rfl)) s

private theorem readTriple_crossing_sh (D : OrientedPDCode (N + 1 + 1 + 1)) (k : Fin N)
    (s : Fin 4) : (readTriple D).crossing (sh k) s = D.crossing (sh k) s := by
  rw [readTriple, halfTurn_crossing_of_ne _ (sh_ne_two k), halfTurn_crossing_of_ne _ (sh_ne_one k),
    halfTurn_crossing_of_ne _ (sh_ne_zero k)]

/-- The triangle of the third Reidemeister move, from the top crossing down. -/
private def triangle (N : ℕ) : Fin 3 ↪ Fin (N + 1 + 1 + 1) :=
  ⟨![2, 1, 0], by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp_all [Fin.ext_iff]⟩

@[simp] private theorem triangle_zero : triangle N 0 = 2 := (rfl)
@[simp] private theorem triangle_one : triangle N 1 = 1 := (rfl)
@[simp] private theorem triangle_two : triangle N 2 = 0 := (rfl)

private theorem sh_notMem_range_triangle (k : Fin N) :
    sh k ∉ Set.range (triangle N) := by
  rintro ⟨a, ha⟩
  fin_cases a <;> simp [Fin.ext_iff] at ha

private theorem add_two_add_two (r : Fin 4) : r + 2 + 2 = r := by
  fin_cases r <;> rfl

private theorem triangle_mem (a : Fin 3) :
    triangle N a = 0 ∨ triangle N a = 1 ∨ triangle N a = 2 := by
  fin_cases a <;> simp

/-- The rewire of the third move at the triangle of the half-turned code, on the slots of the
original code. -/
private theorem reidemeisterThreePerm_readTriple (D : OrientedPDCode (N + 1 + 1 + 1)) (a : Fin 3)
    (s : Fin 4) :
    (readTriple D).reidemeisterThreePerm (triangle N) (D.crossing (triangle N a) s) =
      D.crossing (triangle N (reidemeisterThreeSlots (a, s + 2)).1)
        ((reidemeisterThreeSlots (a, s + 2)).2 + 2) := by
  have h (b : Fin 3) (r : Fin 4) :
      D.crossing (triangle N b) r = (readTriple D).crossing (triangle N b) (r + 2) := by
    rw [readTriple_crossing_triple D (triangle_mem b), add_two_add_two]
  rw [h, reidemeisterThreePerm_apply_crossing, h, add_two_add_two]

private theorem reidemeisterThreePerm_readTriple_sh (D : OrientedPDCode (N + 1 + 1 + 1))
    (k : Fin N) (s : Fin 4) :
    (readTriple D).reidemeisterThreePerm (triangle N) (D.crossing (sh k) s) =
      D.crossing (sh k) s := by
  rw [← readTriple_crossing_sh]
  exact reidemeisterThreePerm_crossing_of_notMem _ _ (sh_notMem_range_triangle k) s

private theorem reidemeisterThreePerm_readTriple_symm (D : OrientedPDCode (N + 1 + 1 + 1))
    (a : Fin 3) (s : Fin 4) :
    ((readTriple D).reidemeisterThreePerm (triangle N)).symm (D.crossing (triangle N a) s) =
      D.crossing (triangle N (reidemeisterThreeSlots.symm (a, s + 2)).1)
        ((reidemeisterThreeSlots.symm (a, s + 2)).2 + 2) := by
  rw [Equiv.symm_apply_eq, reidemeisterThreePerm_readTriple, add_two_add_two, Prod.mk.eta,
    Equiv.apply_symm_apply, add_two_add_two]

private theorem reidemeisterThreePerm_readTriple_symm_sh (D : OrientedPDCode (N + 1 + 1 + 1))
    (k : Fin N) (s : Fin 4) :
    ((readTriple D).reidemeisterThreePerm (triangle N)).symm (D.crossing (sh k) s) =
      D.crossing (sh k) s := by
  rw [Equiv.symm_apply_eq, reidemeisterThreePerm_readTriple_sh]

private theorem fin_cases_triple (k : Fin (N + 1 + 1 + 1)) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ ∃ k₀, k = sh k₀ := by
  refine Fin.cases (Or.inl rfl) (fun k ↦ ?_) k
  refine Fin.cases (Or.inr (Or.inl Fin.succ_zero_eq_one)) (fun k ↦ ?_) k
  refine Fin.cases (Or.inr (Or.inr (Or.inl Fin.succ_one_eq_two))) (fun k ↦ ?_) k
  exact Or.inr (Or.inr (Or.inr ⟨k, rfl⟩))

private theorem fin_cases_triangle (k : Fin (N + 1 + 1 + 1)) :
    (∃ a, k = triangle N a) ∨ ∃ k₀, k = sh k₀ := by
  rcases fin_cases_triple k with rfl | rfl | rfl | h
  · exact Or.inl ⟨2, rfl⟩
  · exact Or.inl ⟨1, rfl⟩
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inr h

/-! ### Successors along a strand position -/

/-- Along a position whose crossings are `T ++ V`, the successor of a crossing in `V`. -/
private theorem nextCrossing_of_mem_right {w : BraidWord n} {p : Fin n} {T V : List (Fin w.length)}
    (hw : w.crossingsAt p = T ++ V) {x : Fin w.length} (hx : x ∈ V) :
    w.nextCrossing p x =
      if V.formPerm x = V.head (List.ne_nil_of_mem hx) then
        (T ++ V).head (by simp [List.ne_nil_of_mem hx])
      else V.formPerm x := by
  rw [nextCrossing_def, hw]
  exact List.formPerm_append_apply_of_mem_right (hw ▸ (w.sortedLT_crossingsAt p).nodup) hx

/-- Along a position whose crossings are `T ++ V`, the successor of the last crossing of `T`. -/
private theorem nextCrossing_getLast_left {w : BraidWord n} {p : Fin n} {T V : List (Fin w.length)}
    (hw : w.crossingsAt p = T ++ V) (hT : T ≠ []) :
    w.nextCrossing p (T.getLast hT) = (V ++ T).head (by simp [hT]) := by
  rw [nextCrossing_def, hw]
  exact List.formPerm_append_apply_getLast_left (hw ▸ (w.sortedLT_crossingsAt p).nodup) hT

/-- Along a position whose crossings start with `x, y`, the successor of `x` is `y`. -/
private theorem nextCrossing_of_cons_cons {w : BraidWord n} {p : Fin n} {x y : Fin w.length}
    {l : List (Fin w.length)} (hw : w.crossingsAt p = x :: y :: l) : w.nextCrossing p x = y := by
  rw [nextCrossing_def, hw]
  exact List.formPerm_apply_head x y l (hw ▸ (w.sortedLT_crossingsAt p).nodup)

/-- Along a position whose crossings start with `x, y, z`, the successor of `y` is `z`. -/
private theorem nextCrossing_of_cons_cons_cons {w : BraidWord n} {p : Fin n}
    {x y z : Fin w.length} {l : List (Fin w.length)} (hw : w.crossingsAt p = x :: y :: z :: l) :
    w.nextCrossing p y = z := by
  have hnd := (w.sortedLT_crossingsAt p).nodup
  rw [hw] at hnd
  rw [nextCrossing_def, hw, List.formPerm_cons_cons, Equiv.Perm.mul_apply,
    List.formPerm_apply_head y z l hnd.of_cons]
  simp only [List.nodup_cons, List.mem_cons, not_or] at hnd
  exact Equiv.swap_apply_of_ne_of_ne (Ne.symm hnd.1.2.1) (Ne.symm hnd.2.1.1)

/-! ### Entry and exit slots

`TauCeti.BraidWord.incomingSlot_strand` and its siblings, with the strand position given by a
hypothesis, so that `simp` applies them once it has computed the letter of the crossing. -/

private theorem incomingSlot_eq_three {w : BraidWord n} {k : Fin w.length} {p : Fin n}
    (hp : p = strand w[k.1].1) : w.incomingSlot k p = 3 := by
  rw [hp, incomingSlot_strand]

private theorem incomingSlot_eq_zero {w : BraidWord n} {k : Fin w.length} {p : Fin n}
    (hp : p = strandSucc w[k.1].1) : w.incomingSlot k p = 0 := by
  rw [hp, incomingSlot_strandSucc]

private theorem outgoingSlot_eq_two {w : BraidWord n} {k : Fin w.length} {p : Fin n}
    (hp : p = strand w[k.1].1) : w.outgoingSlot k p = 2 := by
  rw [hp, outgoingSlot_strand]

private theorem outgoingSlot_eq_one {w : BraidWord n} {k : Fin w.length} {p : Fin n}
    (hp : p = strandSucc w[k.1].1) : w.outgoingSlot k p = 1 := by
  rw [hp, outgoingSlot_strandSucc]

/-! ### Closures of words with three letters at the bottom

The closure of `x :: y :: z :: v` has `v.length + 1 + 1 + 1` crossings, definitionally but not
syntactically `(x :: y :: z :: v).length`. The following restatements of the closure lemmas use
the former, so that they apply to half-edges named through it. -/

private theorem orientation_closure_cons₃ (x y z : Fin (n - 1) × ℤˣ) (v : BraidWord n)
    (k : Fin (v.length + 1 + 1 + 1)) (s : Fin 4) :
    (closure (x :: y :: z :: v)).orientation (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, s)) =
      decide (s = 1 ∨ s = 2) :=
  orientation_closure (x :: y :: z :: v) k s

private theorem edgePair_closure_cons₃_outgoingSlot {x y z : Fin (n - 1) × ℤˣ} {v : BraidWord n}
    {k : Fin (v.length + 1 + 1 + 1)} {p : Fin n} (hk : k ∈ crossingsAt (x :: y :: z :: v) p) :
    (closure (x :: y :: z :: v)).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, outgoingSlot (x :: y :: z :: v) k p)) =
      crossingSlotEquiv (v.length + 1 + 1 + 1) (nextCrossing (x :: y :: z :: v) p k,
        incomingSlot (x :: y :: z :: v) (nextCrossing (x :: y :: z :: v) p k) p) := by
  have h := edgePair_closure_outgoingSlot (x :: y :: z :: v) hk
  simp only [crossing_closure] at h
  exact h

private theorem edgePair_closure_cons₃_one {x y z : Fin (n - 1) × ℤˣ} {v : BraidWord n}
    (k : Fin (v.length + 1 + 1 + 1)) :
    (closure (x :: y :: z :: v)).edgePair.val (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, 1)) =
      crossingSlotEquiv (v.length + 1 + 1 + 1)
        (nextCrossing (x :: y :: z :: v) (strandSucc (x :: y :: z :: v)[k.1].1) k,
          incomingSlot (x :: y :: z :: v)
            (nextCrossing (x :: y :: z :: v) (strandSucc (x :: y :: z :: v)[k.1].1) k)
            (strandSucc (x :: y :: z :: v)[k.1].1)) :=
  edgePair_closure_crossingSlotEquiv_one (x :: y :: z :: v) k

private theorem edgePair_closure_cons₃_two {x y z : Fin (n - 1) × ℤˣ} {v : BraidWord n}
    (k : Fin (v.length + 1 + 1 + 1)) :
    (closure (x :: y :: z :: v)).edgePair.val (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, 2)) =
      crossingSlotEquiv (v.length + 1 + 1 + 1)
        (nextCrossing (x :: y :: z :: v) (strand (x :: y :: z :: v)[k.1].1) k,
          incomingSlot (x :: y :: z :: v)
            (nextCrossing (x :: y :: z :: v) (strand (x :: y :: z :: v)[k.1].1) k)
            (strand (x :: y :: z :: v)[k.1].1)) :=
  edgePair_closure_crossingSlotEquiv_two (x :: y :: z :: v) k

private theorem edgePair_closure_cons₃_zero {x y z : Fin (n - 1) × ℤˣ} {v : BraidWord n}
    (k : Fin (v.length + 1 + 1 + 1)) :
    (closure (x :: y :: z :: v)).edgePair.val (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, 0)) =
      crossingSlotEquiv (v.length + 1 + 1 + 1)
        ((nextCrossing (x :: y :: z :: v) (strandSucc (x :: y :: z :: v)[k.1].1)).symm k,
          outgoingSlot (x :: y :: z :: v)
            ((nextCrossing (x :: y :: z :: v) (strandSucc (x :: y :: z :: v)[k.1].1)).symm k)
            (strandSucc (x :: y :: z :: v)[k.1].1)) :=
  edgePair_closure_crossingSlotEquiv_zero (x :: y :: z :: v) k

private theorem edgePair_closure_cons₃_three {x y z : Fin (n - 1) × ℤˣ} {v : BraidWord n}
    (k : Fin (v.length + 1 + 1 + 1)) :
    (closure (x :: y :: z :: v)).edgePair.val (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, 3)) =
      crossingSlotEquiv (v.length + 1 + 1 + 1)
        ((nextCrossing (x :: y :: z :: v) (strand (x :: y :: z :: v)[k.1].1)).symm k,
          outgoingSlot (x :: y :: z :: v)
            ((nextCrossing (x :: y :: z :: v) (strand (x :: y :: z :: v)[k.1].1)).symm k)
            (strand (x :: y :: z :: v)[k.1].1)) :=
  edgePair_closure_crossingSlotEquiv_three (x :: y :: z :: v) k

private theorem crossingsAt_cons_cons_cons (x y z : Fin (n - 1) × ℤˣ) (v : BraidWord n)
    (p : Fin n) :
    crossingsAt (x :: y :: z :: v) p =
      (if p = strand x.1 ∨ p = strandSucc x.1 then [0] else []) ++
        (if p = strand y.1 ∨ p = strandSucc y.1 then [1] else []) ++
        (if p = strand z.1 ∨ p = strandSucc z.1 then [2] else []) ++
        (v.crossingsAt p).map sh := by
  rw [crossingsAt_cons, crossingsAt_cons, crossingsAt_cons]
  simp only [List.map_append, List.map_map, List.append_assoc]
  congr 1
  congr 1
  · split_ifs <;> simp
  congr 1
  · split_ifs <;> simp

/-! ### The braid relation -/

section BraidRelation

variable (v : BraidWord n) {i j : Fin (n - 1)} (ε₁ ε₂ ε₃ : ℤˣ)

/-- The word with the three letters `σ i ^ ε₁ σ (i + 1) ^ ε₂ σ i ^ ε₃` at the bottom. -/
local notation "W₁" => ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v : BraidWord n)
/-- The word with the three letters `σ (i + 1) ^ ε₃ σ i ^ ε₂ σ (i + 1) ^ ε₁` at the bottom. -/
local notation "W₂" => ((j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v : BraidWord n)
/-- The rewire of the third Reidemeister move at the triangle of the closure of `W₁`. -/
local notation "ρ" =>
  PDCode.reidemeisterThreePerm (OrientedPDCode.toPDCode (readTriple (closure W₁)))
    (triangle (List.length v))

private theorem rewire_triangle (a : Fin 3) (s : Fin 4) :
    ρ (crossingSlotEquiv _ (triangle _ a, s)) =
      crossingSlotEquiv _ (triangle _ (reidemeisterThreeSlots (a, s + 2)).1,
        (reidemeisterThreeSlots (a, s + 2)).2 + 2) := by
  have h := reidemeisterThreePerm_readTriple (closure W₁) a s
  simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
  exact h

private theorem rewire_symm_triangle (a : Fin 3) (s : Fin 4) :
    (ρ).symm (crossingSlotEquiv _ (triangle _ a, s)) =
      crossingSlotEquiv _ (triangle _ (reidemeisterThreeSlots.symm (a, s + 2)).1,
        (reidemeisterThreeSlots.symm (a, s + 2)).2 + 2) := by
  have h := reidemeisterThreePerm_readTriple_symm (closure W₁) a s
  simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
  exact h

private theorem rewire_symm_sh (k : Fin v.length) (s : Fin 4) :
    (ρ).symm (crossingSlotEquiv _ (sh k, s)) = crossingSlotEquiv _ (sh k, s) := by
  have h := reidemeisterThreePerm_readTriple_symm_sh (closure W₁) k s
  simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
  exact h

private theorem rewire_port_left :
    ρ (crossingSlotEquiv _ (0, incomingSlot W₁ (0 : Fin (v.length + 1 + 1 + 1)) (strand i))) =
      crossingSlotEquiv _ (1, incomingSlot W₂ (1 : Fin (v.length + 1 + 1 + 1)) (strand i)) := by
  have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 2 3
  simp only [reidemeisterThreeSlots_apply] at h
  rw [incomingSlot_eq_three, incomingSlot_eq_three]
  · simpa using h
  all_goals simp

private theorem rewire_port_right :
    ρ (crossingSlotEquiv _ (1, incomingSlot W₁ (1 : Fin (v.length + 1 + 1 + 1)) (strandSucc j))) =
      crossingSlotEquiv _ (0, incomingSlot W₂ (0 : Fin (v.length + 1 + 1 + 1)) (strandSucc j)) := by
  have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 1 0
  simp only [reidemeisterThreeSlots_apply] at h
  rw [incomingSlot_eq_zero, incomingSlot_eq_zero]
  · simpa using h
  all_goals simp

/-- The rewire fixes the half-edges at the crossings of `v`, which sit at the same slots of the
same letters in both words. -/
private theorem rewire_sh (k : Fin v.length) (p : Fin n) :
    ρ (crossingSlotEquiv _ (sh k, incomingSlot W₁ (sh k) p)) =
      crossingSlotEquiv _ (sh k, incomingSlot W₂ (sh k) p) := by
  have h := reidemeisterThreePerm_readTriple_sh (closure W₁) k (incomingSlot W₁ (sh k) p)
  simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
  rw [h, incomingSlot_congr (w := W₂) (w' := W₁) (j := sh k) (i := sh k) (by simp)]

private theorem rewire_of_mem {p : Fin n} {y : Fin (v.length + 1 + 1 + 1)}
    (hy : y ∈ (v.crossingsAt p).map sh) :
    ρ (crossingSlotEquiv _ (y, incomingSlot W₁ y p)) =
      crossingSlotEquiv _ (y, incomingSlot W₂ y p) := by
  obtain ⟨k, -, rfl⟩ := List.mem_map.1 hy
  exact rewire_sh v ε₁ ε₂ ε₃ k p

/-- Along a position with crossings `T ++ V` in `W₁` and `T' ++ V` in `W₂`, the rewire carries the
arc leaving the last crossing of `V` (or of `T`, if `V` is empty) to the corresponding arc. -/
private theorem rewire_head {p : Fin n} {T T' V : List (Fin (v.length + 1 + 1 + 1))}
    (hV : ∀ y ∈ V, y ∈ (v.crossingsAt p).map sh) (hT : T ≠ []) (hT' : T' ≠ [])
    (hport : ρ (crossingSlotEquiv _ (T.head hT, incomingSlot W₁ (T.head hT) p)) =
      crossingSlotEquiv _ (T'.head hT', incomingSlot W₂ (T'.head hT') p)) :
    ρ (crossingSlotEquiv _ ((V ++ T).head (by simp [hT]),
        incomingSlot W₁ ((V ++ T).head (by simp [hT])) p)) =
      crossingSlotEquiv _ ((V ++ T').head (by simp [hT']),
        incomingSlot W₂ ((V ++ T').head (by simp [hT'])) p) := by
  cases V with
  | nil => simpa using hport
  | cons y ys =>
    simp only [List.cons_append, List.head_cons]
    exact rewire_of_mem v ε₁ ε₂ ε₃ (hV y List.mem_cons_self)

/-- Along a position with crossings `T ++ V` in `W₁` and `T' ++ V` in `W₂`, the rewire carries the
arc leaving a crossing of `V` to the corresponding arc. -/
private theorem rewire_next_of_mem {p : Fin n} {T T' : List (Fin (v.length + 1 + 1 + 1))}
    (hT : T ≠ []) (hT' : T' ≠ [])
    (hw₁ : crossingsAt W₁ p = T ++ (v.crossingsAt p).map sh)
    (hw₂ : crossingsAt W₂ p = T' ++ (v.crossingsAt p).map sh)
    (hport : ρ (crossingSlotEquiv _ (T.head hT, incomingSlot W₁ (T.head hT) p)) =
      crossingSlotEquiv _ (T'.head hT', incomingSlot W₂ (T'.head hT') p))
    {x : Fin (v.length + 1 + 1 + 1)} (hx : x ∈ (v.crossingsAt p).map sh) :
    ρ (crossingSlotEquiv _ (nextCrossing W₁ p x, incomingSlot W₁ (nextCrossing W₁ p x) p)) =
      crossingSlotEquiv _ (nextCrossing W₂ p x, incomingSlot W₂ (nextCrossing W₂ p x) p) := by
  rw [nextCrossing_of_mem_right hw₁ hx, nextCrossing_of_mem_right hw₂ hx]
  split_ifs
  · simpa [List.head_append_of_ne_nil hT, List.head_append_of_ne_nil hT'] using hport
  · exact rewire_of_mem v ε₁ ε₂ ε₃ (List.formPerm_apply_mem_of_mem hx)

variable (hij : (j : ℕ) = i + 1)
include hij

private theorem strand_eq_strandSucc : strand j = strandSucc i := Fin.ext (by simp [hij])
private theorem strand_ne_strandSucc_right : strand i ≠ strandSucc j := by
  simp only [ne_eq, Fin.ext_iff, val_strand, val_strandSucc, hij]
  omega
private theorem strandSucc_ne_strandSucc : strandSucc i ≠ strandSucc j := by
  simp [Fin.ext_iff, hij]

private theorem crossingsAt_triple_left :
    crossingsAt ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strand i) =
      [0, 2] ++ (v.crossingsAt (strand i)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij, strand_ne_strandSucc, strand_ne_strandSucc_right hij]

private theorem crossingsAt_triple_mid :
    crossingsAt ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strandSucc i) =
      [0, 1, 2] ++ (v.crossingsAt (strandSucc i)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij]

private theorem crossingsAt_triple_right :
    crossingsAt ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strandSucc j) =
      [1] ++ (v.crossingsAt (strandSucc j)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [(strand_ne_strandSucc_right hij).symm, (strandSucc_ne_strandSucc hij).symm]

private theorem crossingsAt_triple_other {p : Fin n} (hL : p ≠ strand i) (hM : p ≠ strandSucc i)
    (hR : p ≠ strandSucc j) :
    crossingsAt ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) p = (v.crossingsAt p).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij, hL, hM, hR]

private theorem crossingsAt_triple'_left :
    crossingsAt ((j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v) (strand i) =
      [1] ++ (v.crossingsAt (strand i)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij, strand_ne_strandSucc, strand_ne_strandSucc_right hij]

private theorem crossingsAt_triple'_mid :
    crossingsAt ((j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v) (strandSucc i) =
      [0, 1, 2] ++ (v.crossingsAt (strandSucc i)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij]

private theorem crossingsAt_triple'_right :
    crossingsAt ((j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v) (strandSucc j) =
      [0, 2] ++ (v.crossingsAt (strandSucc j)).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [(strand_ne_strandSucc_right hij).symm, (strandSucc_ne_strandSucc hij).symm]

private theorem crossingsAt_triple'_other {p : Fin n} (hL : p ≠ strand i) (hM : p ≠ strandSucc i)
    (hR : p ≠ strandSucc j) :
    crossingsAt ((j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v) p = (v.crossingsAt p).map sh := by
  rw [crossingsAt_cons_cons_cons]
  simp [strand_eq_strandSucc hij, hL, hM, hR]

private theorem nextCrossing_triple_left_zero :
    nextCrossing ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strand i) 0 = 2 :=
  nextCrossing_of_cons_cons (crossingsAt_triple_left v ε₁ ε₂ ε₃ hij)

private theorem nextCrossing_triple_mid_zero :
    nextCrossing ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strandSucc i) 0 = 1 :=
  nextCrossing_of_cons_cons (crossingsAt_triple_mid v ε₁ ε₂ ε₃ hij)

private theorem nextCrossing_triple_mid_one :
    nextCrossing ((i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v) (strandSucc i) 1 = 2 := by
  exact nextCrossing_of_cons_cons_cons (crossingsAt_triple_mid v ε₁ ε₂ ε₃ hij)

private theorem rewire_port_mid :
    ρ (crossingSlotEquiv _ (0, incomingSlot W₁ (0 : Fin (v.length + 1 + 1 + 1)) (strandSucc i))) =
      crossingSlotEquiv _ (0, incomingSlot W₂ (0 : Fin (v.length + 1 + 1 + 1)) (strandSucc i)) := by
  have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 2 0
  simp only [reidemeisterThreeSlots_apply] at h
  rw [incomingSlot_eq_zero, incomingSlot_eq_three]
  · simpa using h
  all_goals simp [strand_eq_strandSucc hij]

/-- After the half turns, the three bottom crossings of the closure of `W₁` form the triangle of
the third Reidemeister move, and the signs give its strands an acyclic height order. -/
private theorem hasReidemeisterThreeTriangle_readTriple (h : ε₁ = ε₃ → ε₂ = ε₁) :
    (readTriple (closure W₁)).HasReidemeisterThreeTriangle (triangle v.length) := by
  rw [hasReidemeisterThreeTriangle_iff]
  simp only [readTriple_edgePair, readTriple_overPair, crossing_apply, triangle_zero,
    triangle_one, triangle_two, readTriple_halfEdge_zero, readTriple_halfEdge_one,
    readTriple_halfEdge_two, halfEdge_closure, Equiv.Perm.one_apply, Fin.reduceAdd]
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h₁ : (nextCrossing W₁ (strandSucc i)).symm 2 = 1 :=
      Equiv.symm_apply_eq _ |>.2 (nextCrossing_triple_mid_one v ε₁ ε₂ ε₃ hij).symm
    rw [edgePair_closure_cons₃_zero]
    simp [h₁, outgoingSlot_eq_two, strand_eq_strandSucc hij]
  · have h₁ : (nextCrossing W₁ (strandSucc i)).symm 1 = 0 :=
      Equiv.symm_apply_eq _ |>.2 (nextCrossing_triple_mid_zero v ε₁ ε₂ ε₃ hij).symm
    rw [edgePair_closure_cons₃_three]
    simp [h₁, outgoingSlot_eq_one, strand_eq_strandSucc hij]
  · have h₁ : (nextCrossing W₁ (strand i)).symm 2 = 0 :=
      Equiv.symm_apply_eq _ |>.2 (nextCrossing_triple_left_zero v ε₁ ε₂ ε₃ hij).symm
    rw [edgePair_closure_cons₃_three]
    simp [h₁, outgoingSlot_eq_two]
  · simp only [overPair_closure]
    intro he
    have h₃₁ : ε₃ = ε₁ := by
      rcases Int.units_eq_one_or ε₁ with rfl | rfl <;>
        rcases Int.units_eq_one_or ε₃ with rfl | rfl <;> simp_all
    simp [h h₃₁.symm, h₃₁]

private theorem nextCrossing_triple'_right_zero :
    nextCrossing W₂ (strandSucc j) 0 = 2 :=
  nextCrossing_of_cons_cons (crossingsAt_triple'_right v ε₁ ε₂ ε₃ hij)

private theorem nextCrossing_triple'_mid_zero :
    nextCrossing W₂ (strandSucc i) 0 = 1 :=
  nextCrossing_of_cons_cons (crossingsAt_triple'_mid v ε₁ ε₂ ε₃ hij)

private theorem nextCrossing_triple'_mid_one :
    nextCrossing W₂ (strandSucc i) 1 = 2 :=
  nextCrossing_of_cons_cons_cons (crossingsAt_triple'_mid v ε₁ ε₂ ε₃ hij)

private theorem nextCrossing_triple_left_two :
    nextCrossing W₁ (strand i) 2 = ((v.crossingsAt (strand i)).map sh ++ [0, 2]).head (by simp) :=
  nextCrossing_getLast_left (T := [0, 2]) (crossingsAt_triple_left v ε₁ ε₂ ε₃ hij) (by simp)

private theorem nextCrossing_triple_mid_two :
    nextCrossing W₁ (strandSucc i) 2 =
      ((v.crossingsAt (strandSucc i)).map sh ++ [0, 1, 2]).head (by simp) :=
  nextCrossing_getLast_left (T := [0, 1, 2]) (crossingsAt_triple_mid v ε₁ ε₂ ε₃ hij) (by simp)

private theorem nextCrossing_triple_right_one :
    nextCrossing W₁ (strandSucc j) 1 =
      ((v.crossingsAt (strandSucc j)).map sh ++ [1]).head (by simp) :=
  nextCrossing_getLast_left (T := [1]) (crossingsAt_triple_right v ε₁ ε₂ ε₃ hij) (by simp)

private theorem nextCrossing_triple'_left_one :
    nextCrossing W₂ (strand i) 1 = ((v.crossingsAt (strand i)).map sh ++ [1]).head (by simp) :=
  nextCrossing_getLast_left (T := [1]) (crossingsAt_triple'_left v ε₁ ε₂ ε₃ hij) (by simp)

private theorem nextCrossing_triple'_mid_two :
    nextCrossing W₂ (strandSucc i) 2 =
      ((v.crossingsAt (strandSucc i)).map sh ++ [0, 1, 2]).head (by simp) :=
  nextCrossing_getLast_left (T := [0, 1, 2]) (crossingsAt_triple'_mid v ε₁ ε₂ ε₃ hij) (by simp)

private theorem nextCrossing_triple'_right_two :
    nextCrossing W₂ (strandSucc j) 2 =
      ((v.crossingsAt (strandSucc j)).map sh ++ [0, 2]).head (by simp) :=
  nextCrossing_getLast_left (T := [0, 2]) (crossingsAt_triple'_right v ε₁ ε₂ ε₃ hij) (by simp)

private theorem crossingsAt_eq_nil_iff_triple (p : Fin n) :
    crossingsAt W₁ p = [] ↔ crossingsAt W₂ p = [] := by
  by_cases hL : p = strand i
  · subst hL
    simp [crossingsAt_triple_left v ε₁ ε₂ ε₃ hij, crossingsAt_triple'_left v ε₁ ε₂ ε₃ hij]
  by_cases hM : p = strandSucc i
  · subst hM
    simp [crossingsAt_triple_mid v ε₁ ε₂ ε₃ hij, crossingsAt_triple'_mid v ε₁ ε₂ ε₃ hij]
  by_cases hR : p = strandSucc j
  · subst hR
    simp [crossingsAt_triple_right v ε₁ ε₂ ε₃ hij, crossingsAt_triple'_right v ε₁ ε₂ ε₃ hij]
  rw [crossingsAt_triple_other v ε₁ ε₂ ε₃ hij hL hM hR,
    crossingsAt_triple'_other v ε₁ ε₂ ε₃ hij hL hM hR]

/-! The arcs of the closure of `W₂` at the slots where strands leave their crossings, compared
with the arcs of the closure of `W₁` moved by the rewire: first at the three crossings of the
triangle, from the top down, then at the crossings of `v`. -/

private theorem edgePair_closure_triple'_two {p : Fin n}
    (hp : p = strandSucc i ∨ p = strandSucc j) :
    (closure W₂).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (2, outgoingSlot W₂ 2 p)) =
      ρ ((closure W₁).edgePair.val
        ((ρ).symm (crossingSlotEquiv (v.length + 1 + 1 + 1) (2, outgoingSlot W₂ 2 p)))) := by
  rw [← triangle_zero, rewire_symm_triangle, triangle_zero]
  rcases hp with rfl | rfl
  · -- The middle strand leaves the triangle upwards.
    simp only [List.length_cons, val_two_fin, List.getElem_cons_succ, List.getElem_cons_zero,
      strand_eq_strandSucc hij, outgoingSlot_eq_two, Fin.isValue, Fin.reduceAdd,
      reidemeisterThreeSlots_symm_apply, Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val',
      Matrix.cons_val_zero, Matrix.cons_val_fin_one, triangle_zero]
    rw [edgePair_closure_cons₃_two, edgePair_closure_cons₃_one]
    simp only [val_two_fin, List.getElem_cons_succ, List.getElem_cons_zero,
      strand_eq_strandSucc hij]
    rw [nextCrossing_triple'_mid_two v ε₁ ε₂ ε₃ hij, nextCrossing_triple_mid_two v ε₁ ε₂ ε₃ hij]
    exact (rewire_head v ε₁ ε₂ ε₃ (fun _ h ↦ h) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (rewire_port_mid v ε₁ ε₂ ε₃ hij)).symm
  · -- The right strand leaves the triangle upwards.
    simp only [List.length_cons, val_two_fin, List.getElem_cons_succ, List.getElem_cons_zero,
      outgoingSlot_eq_one, Fin.isValue, Fin.reduceAdd, reidemeisterThreeSlots_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.cons_val_zero, triangle_one]
    rw [edgePair_closure_cons₃_one, edgePair_closure_cons₃_one]
    simp only [val_two_fin, val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [nextCrossing_triple'_right_two v ε₁ ε₂ ε₃ hij,
      nextCrossing_triple_right_one v ε₁ ε₂ ε₃ hij]
    exact (rewire_head v ε₁ ε₂ ε₃ (fun _ h ↦ h) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (rewire_port_right v ε₁ ε₂ ε₃)).symm

private theorem edgePair_closure_triple'_one {p : Fin n}
    (hp : p = strand i ∨ p = strandSucc i) :
    (closure W₂).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (1, outgoingSlot W₂ 1 p)) =
      ρ ((closure W₁).edgePair.val
        ((ρ).symm (crossingSlotEquiv (v.length + 1 + 1 + 1) (1, outgoingSlot W₂ 1 p)))) := by
  rw [← triangle_one, rewire_symm_triangle, triangle_one]
  rcases hp with rfl | rfl
  · -- The left strand leaves the triangle upwards.
    simp only [List.length_cons, val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero,
      outgoingSlot_eq_two, Fin.isValue, Fin.reduceAdd, reidemeisterThreeSlots_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, triangle_zero, zero_add]
    rw [edgePair_closure_cons₃_two, edgePair_closure_cons₃_two]
    simp only [val_two_fin, val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [nextCrossing_triple'_left_one v ε₁ ε₂ ε₃ hij, nextCrossing_triple_left_two v ε₁ ε₂ ε₃ hij]
    exact (rewire_head v ε₁ ε₂ ε₃ (fun _ h ↦ h) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (rewire_port_left v ε₁ ε₂ ε₃)).symm
  · -- An arc inside the triangle.
    simp only [List.length_cons, val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero,
      outgoingSlot_eq_one, Fin.isValue, Fin.reduceAdd, reidemeisterThreeSlots_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val', Matrix.cons_val,
      Matrix.cons_val_fin_one, Matrix.cons_val_one, Matrix.cons_val_zero, triangle_two]
    rw [edgePair_closure_cons₃_one, edgePair_closure_cons₃_one]
    simp only [val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero, Fin.val_zero]
    rw [nextCrossing_triple'_mid_one v ε₁ ε₂ ε₃ hij, nextCrossing_triple_mid_zero v ε₁ ε₂ ε₃ hij]
    have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 1 3
    simp [reidemeisterThreeSlots_apply] at h
    simp [incomingSlot_eq_three, strand_eq_strandSucc hij, h]

private theorem edgePair_closure_triple'_zero {p : Fin n}
    (hp : p = strandSucc i ∨ p = strandSucc j) :
    (closure W₂).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (0, outgoingSlot W₂ 0 p)) =
      ρ ((closure W₁).edgePair.val
        ((ρ).symm (crossingSlotEquiv (v.length + 1 + 1 + 1) (0, outgoingSlot W₂ 0 p)))) := by
  rw [← triangle_two, rewire_symm_triangle, triangle_two]
  rcases hp with rfl | rfl
  · -- An arc inside the triangle.
    simp only [List.length_cons, val_zero_fin, List.getElem_cons_zero, strand_eq_strandSucc hij,
      outgoingSlot_eq_two, Fin.isValue, Fin.reduceAdd, reidemeisterThreeSlots_symm_apply,
      Nat.succ_eq_add_one, Nat.reduceAdd, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_fin_one, Matrix.cons_val, Matrix.cons_val_one, triangle_one, zero_add]
    rw [edgePair_closure_cons₃_two, edgePair_closure_cons₃_two]
    simp only [val_one_fin, List.getElem_cons_succ, List.getElem_cons_zero, Fin.val_zero,
      strand_eq_strandSucc hij]
    rw [nextCrossing_triple'_mid_zero v ε₁ ε₂ ε₃ hij, nextCrossing_triple_mid_one v ε₁ ε₂ ε₃ hij]
    have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 0 0
    simp [reidemeisterThreeSlots_apply] at h
    simp [incomingSlot_eq_zero, h]
  · -- An arc inside the triangle.
    simp only [List.length_cons, val_zero_fin, List.getElem_cons_zero, outgoingSlot_eq_one,
      Fin.isValue, Fin.reduceAdd, reidemeisterThreeSlots_symm_apply, Nat.succ_eq_add_one,
      Nat.reduceAdd, Matrix.cons_val', Matrix.cons_val, Matrix.cons_val_fin_one,
      Matrix.cons_val_one, triangle_two, zero_add]
    rw [edgePair_closure_cons₃_one, edgePair_closure_cons₃_two]
    simp only [List.getElem_cons_zero, Fin.val_zero]
    rw [nextCrossing_triple'_right_zero v ε₁ ε₂ ε₃ hij,
      nextCrossing_triple_left_zero v ε₁ ε₂ ε₃ hij]
    have h := rewire_triangle v (i := i) (j := j) ε₁ ε₂ ε₃ 0 3
    simp [reidemeisterThreeSlots_apply] at h
    simp [incomingSlot_eq_three, incomingSlot_eq_zero, h]

/-- At a crossing of `v` the same letter sits at the same place in both words, so the arc leaving
it ends at the same crossing of `v`, or else enters the triangle through corresponding ports. -/
private theorem edgePair_closure_triple'_sh (k : Fin v.length) {p : Fin n}
    (hk : p = strand v[k.1].1 ∨ p = strandSucc v[k.1].1) :
    (closure W₂).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (sh k, outgoingSlot W₂ (sh k) p)) =
      ρ ((closure W₁).edgePair.val
        ((ρ).symm
          (crossingSlotEquiv (v.length + 1 + 1 + 1) (sh k, outgoingSlot W₂ (sh k) p)))) := by
  have hk₂ : sh k ∈ crossingsAt W₂ p := by
    rw [mem_crossingsAt (w := W₂) (j := sh k)]
    simpa using hk
  have hk₁ : sh k ∈ crossingsAt W₁ p := by
    rw [mem_crossingsAt (w := W₁) (j := sh k)]
    simpa using hk
  have hx : sh k ∈ (v.crossingsAt p).map sh := List.mem_map_of_mem (by simpa using hk)
  rw [rewire_symm_sh, edgePair_closure_cons₃_outgoingSlot hk₂,
    outgoingSlot_congr (w := W₁) (w' := W₂) (j := sh k) (i := sh k) (by simp),
    edgePair_closure_cons₃_outgoingSlot hk₁]
  by_cases hL : p = strand i
  · subst hL
    exact (rewire_next_of_mem v ε₁ ε₂ ε₃ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (crossingsAt_triple_left v ε₁ ε₂ ε₃ hij) (crossingsAt_triple'_left v ε₁ ε₂ ε₃ hij)
      (rewire_port_left v ε₁ ε₂ ε₃) hx).symm
  by_cases hM : p = strandSucc i
  · subst hM
    exact (rewire_next_of_mem v ε₁ ε₂ ε₃ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (crossingsAt_triple_mid v ε₁ ε₂ ε₃ hij) (crossingsAt_triple'_mid v ε₁ ε₂ ε₃ hij)
      (rewire_port_mid v ε₁ ε₂ ε₃ hij) hx).symm
  by_cases hR : p = strandSucc j
  · subst hR
    exact (rewire_next_of_mem v ε₁ ε₂ ε₃ (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)
      (crossingsAt_triple_right v ε₁ ε₂ ε₃ hij) (crossingsAt_triple'_right v ε₁ ε₂ ε₃ hij)
      (rewire_port_right v ε₁ ε₂ ε₃) hx).symm
  -- A position away from the triangle: both words meet the same crossings along it.
  have h₁ := crossingsAt_triple_other v ε₁ ε₂ ε₃ hij hL hM hR
  have h₂ := crossingsAt_triple'_other v ε₁ ε₂ ε₃ hij hL hM hR
  have hnext : nextCrossing W₂ p = nextCrossing W₁ p := by
    rw [nextCrossing_def, nextCrossing_def, h₁, h₂]
  have hmem : nextCrossing W₁ p (sh k) ∈ (v.crossingsAt p).map sh := by
    rw [nextCrossing_def, h₁]
    exact List.formPerm_apply_mem_of_mem hx
  rw [hnext]
  exact (rewire_of_mem v ε₁ ε₂ ε₃ hmem).symm

/-- The arcs of the closure of `W₂`, at the slots where strands leave their crossings, are the
arcs of the closure of `W₁` moved by the rewire. -/
private theorem edgePair_closure_triple' (k : Fin (v.length + 1 + 1 + 1)) (p : Fin n)
    (hk : k ∈ crossingsAt W₂ p) :
    (closure W₂).edgePair.val
        (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, outgoingSlot W₂ k p)) =
      ρ ((closure W₁).edgePair.val
        ((ρ).symm (crossingSlotEquiv (v.length + 1 + 1 + 1) (k, outgoingSlot W₂ k p)))) := by
  rw [mem_crossingsAt (w := W₂) (j := k)] at hk
  rcases fin_cases_triple k with rfl | rfl | rfl | ⟨k, rfl⟩
  · exact edgePair_closure_triple'_zero v ε₁ ε₂ ε₃ hij
      (by simpa [strand_eq_strandSucc hij] using hk)
  · exact edgePair_closure_triple'_one v ε₁ ε₂ ε₃ hij (by simpa using hk)
  · exact edgePair_closure_triple'_two v ε₁ ε₂ ε₃ hij
      (by simpa [strand_eq_strandSucc hij] using hk)
  · exact edgePair_closure_triple'_sh v ε₁ ε₂ ε₃ hij k (by simpa using hk)

private theorem reidemeisterThree_readTriple_closure :
    (readTriple (closure W₁)).reidemeisterThree (triangle v.length) = readTriple (closure W₂) := by
  apply OrientedPDCode.ext
  · apply PDCode.ext
    · simp only [OrientedPDCode.toPDCode_reidemeisterThree, reidemeisterThree_halfEdge]
      exact readTriple_halfEdge_congr (by simp)
    · simp only [OrientedPDCode.toPDCode_reidemeisterThree, readTriple_edgePair]
      refine (edgePair_closure_eq_of_outgoingSlot W₂ fun k p hk ↦ ?_).symm
      rw [reidemeisterThree_edgePair, Equiv.permCongr_apply, readTriple_edgePair]
      exact edgePair_closure_triple' v ε₁ ε₂ ε₃ hij k p hk
    · simp only [OrientedPDCode.toPDCode_reidemeisterThree,
        reidemeisterThree_crossinglessComponentCount,
        readTriple_crossinglessComponentCount, crossinglessComponentCount_closure,
        crossingsAt_eq_nil_iff_triple v ε₁ ε₂ ε₃ hij]
    · funext k
      simp only [OrientedPDCode.toPDCode_reidemeisterThree, reidemeisterThree_overPair,
        readTriple_overPair, overPair_closure, triangle_zero, triangle_two]
      rcases fin_cases_triple k with rfl | rfl | rfl | ⟨k, rfl⟩
      · rw [decide_eq_decide]
        simp
      · rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]) (by simp)]
        simp
      · simp
      · rw [Equiv.swap_apply_of_ne_of_ne (sh_ne_two k) (sh_ne_zero k)]
        simp
  · funext x
    obtain ⟨⟨k, s⟩, rfl⟩ := (crossingSlotEquiv _).surjective x
    simp only [OrientedPDCode.orientation_reidemeisterThree, readTriple_orientation]
    rw [orientation_closure_cons₃]
    rcases fin_cases_triangle k with ⟨a, rfl⟩ | ⟨k, rfl⟩
    · have h := reidemeisterThreePerm_readTriple_symm (closure W₁) a s
      simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
      rw [h, orientation_closure_cons₃]
      fin_cases a <;> fin_cases s <;> simp [reidemeisterThreeSlots_symm_apply]
    · have h := reidemeisterThreePerm_readTriple_symm_sh (closure W₁) k s
      simp only [crossing_apply, halfEdge_closure, Equiv.Perm.one_apply] at h
      rw [h, orientation_closure_cons₃]
  · simp only [OrientedPDCode.crossinglessComponents_reidemeisterThree,
      readTriple_crossinglessComponents, crossinglessComponents_closure,
      crossingsAt_eq_nil_iff_triple v ε₁ ε₂ ε₃ hij]

/-- The braid relation at the bottom of a word. -/
private theorem reidemeisterEquiv_closure_cons_braid (h : ε₁ = ε₃ → ε₂ = ε₁) :
    OrientedPDCode.ReidemeisterEquiv (closure W₁) (closure W₂) := by
  have h₃ := OrientedPDCode.reidemeisterEquiv_reidemeisterThree _ _
    (hasReidemeisterThreeTriangle_readTriple v ε₁ ε₂ ε₃ hij h)
  rw [reidemeisterThree_readTriple_closure v ε₁ ε₂ ε₃ hij] at h₃
  exact (reidemeisterEquiv_readTriple _).trans (h₃.trans (reidemeisterEquiv_readTriple _).symm)

end BraidRelation

/-- **The braid relation in braid-word closures.** Replacing three adjacent letters
`σ i ^ ε₁ σ (i + 1) ^ ε₂ σ i ^ ε₃` of a braid word by `σ (i + 1) ^ ε₃ σ i ^ ε₂ σ (i + 1) ^ ε₁`
gives a Reidemeister equivalent closure, as long as `ε₁ = ε₃` forces `ε₂ = ε₁`. With all three
signs equal this is the braid relation `σ i σ (i + 1) σ i = σ (i + 1) σ i σ (i + 1)`. The condition
on the signs says that the three strands crossing in the triangle have an acyclic height order, so
that the move is a third Reidemeister move. -/
theorem reidemeisterEquiv_closure_append_cons_cons_cons_braid (u v : BraidWord n)
    {i j : Fin (n - 1)} (hij : (j : ℕ) = i + 1) {ε₁ ε₂ ε₃ : ℤˣ} (h : ε₁ = ε₃ → ε₂ = ε₁) :
    OrientedPDCode.ReidemeisterEquiv (closure (u ++ (i, ε₁) :: (j, ε₂) :: (i, ε₃) :: v))
      (closure (u ++ (j, ε₃) :: (i, ε₂) :: (j, ε₁) :: v)) := by
  have hrot (t : BraidWord n) :
      OrientedPDCode.ReidemeisterEquiv (closure (u ++ t)) (closure (t ++ u)) := by
    have := reidemeisterEquiv_closure_rotate (u ++ t) u.length
    rwa [List.rotate_append_length_eq] at this
  refine (hrot _).trans (OrientedPDCode.ReidemeisterEquiv.trans ?_ (hrot _).symm)
  simpa only [List.cons_append] using
    reidemeisterEquiv_closure_cons_braid (v ++ u) ε₁ ε₂ ε₃ hij h

end BraidWord

end TauCeti
