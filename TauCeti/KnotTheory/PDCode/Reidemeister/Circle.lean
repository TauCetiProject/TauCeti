/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Circle
public import TauCeti.KnotTheory.PDCode.Planar
import TauCeti.GroupTheory.Perm.SumCongr
import Mathlib.Tactic.LinearCombination
import TauCeti.Data.Fin.Basic

/-!
# A Reidemeister kink on a crossing-free circle

`PDCode.adjoinKink D b` adjoins an isolated one-crossing component to `D`. Its two arcs
join slots `0`–`1` and `2`–`3`, as in `PDCode.kink`, and `b` chooses the over-strand.
It is the result of applying the first Reidemeister move to the new circle in
`PDCode.adjoinCircle D`. This complements arc-based kink insertion, whose half-edge argument
cannot select a crossing-free component.

The state-circle formula includes the empty surrounding diagram. Consequently the bracket
formula compares the kink with `D.adjoinCircle`, with no nonemptiness assumption on `D`.
The kink contributes one graph component and three faces, so adjoining it preserves planarity.
The Kauffman bracket of `D.adjoinKink b` is the bracket of `D.adjoinCircle` multiplied by
`-a³` when `b = true` and by `-a⁻³` when `b = false`.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997),
  Chapters 1 and 3 (Reidemeister moves and the Kauffman bracket).
* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395–407.
* Formalization sources: `PDCode.kauffmanBracket_reidemeisterOne` and
  `PDCode.stateLoopCount_adjoinCircle`.
-/

public section

namespace TauCeti
namespace PDCode

open Equiv Equiv.Perm TemperleyLieb

variable {n : ℕ}

/-- Adjoin an isolated kink with over-pair indicator `b`. Compared with `D.adjoinCircle`,
the new circle has acquired one crossing by a first Reidemeister move. -/
def adjoinKink (D : PDCode n) (b : Bool) : PDCode (n + 1) where
  halfEdge := (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1)
  edgePair := PerfectMatching.congr (halfEdgeSuccEquiv n)
    (PerfectMatching.mk (Perm.sumCongr D.edgePair.val (slotSmoothing true))
      (by
        rintro (x | s)
        · simp
        · simp only [Perm.sumCongr_apply, Sum.map_inr, slotSmoothing_apply_apply])
      (by
        rintro (x | s) h
        · exact D.edgePair.apply_ne x (Sum.inl.inj h)
        · exact slotSmoothing_ne true s (Sum.inr.inj h)))
  crossinglessComponentCount := D.crossinglessComponentCount
  overPair := Fin.snoc D.overPair b

/-- The old crossings and the new crossing occupy separate blocks of half-edges. -/
@[simp] theorem adjoinKink_halfEdge (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).halfEdge = (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.halfEdge 1) :=
  (rfl)

/-- The old arcs and the two arcs of the kink form separate matchings. -/
theorem adjoinKink_edgePair_val (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).edgePair.val =
      (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.edgePair.val (slotSmoothing true)) := by
  simp [adjoinKink, PerfectMatching.congr_val]

/-- Adjoining a kink retains the crossing-free components of the surrounding diagram. -/
@[simp] theorem adjoinKink_crossinglessComponentCount (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).crossinglessComponentCount = D.crossinglessComponentCount := (rfl)

/-- The new crossing has over-pair indicator `b`; the old indicators are unchanged. -/
@[simp] theorem adjoinKink_overPair (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).overPair = Fin.snoc D.overPair b := (rfl)

/-- The old crossings keep their slots. -/
-- Prefer the block formula to the generic `crossing_apply` expansion.
@[simp 1100] theorem adjoinKink_crossing_castSucc (D : PDCode n) (b : Bool) (i : Fin n)
    (s : Fin 4) :
    (D.adjoinKink b).crossing i.castSucc s = halfEdgeSuccEquiv n (.inl (D.crossing i s)) := by
  simp [crossing_apply, Equiv.permCongr_apply]

/-- The slots of the new crossing are the new half-edges. -/
-- Prefer the block formula to the generic `crossing_apply` expansion.
@[simp 1100] theorem adjoinKink_crossing_last (D : PDCode n) (b : Bool) (s : Fin 4) :
    (D.adjoinKink b).crossing (Fin.last n) s = halfEdgeSuccEquiv n (.inr s) := by
  simp [crossing_apply, Equiv.permCongr_apply]

/-- The old arcs are unchanged by adjoining a kink. -/
@[simp] theorem adjoinKink_edgePair_inl (D : PDCode n) (b : Bool) (x : Fin (4 * n)) :
    (D.adjoinKink b).edgePair.val (halfEdgeSuccEquiv n (.inl x)) =
      halfEdgeSuccEquiv n (.inl (D.edgePair.val x)) := by
  simp [adjoinKink_edgePair_val, Equiv.permCongr_apply]

/-- The new arcs pair slots `0`–`1` and `2`–`3`, independently of the old diagram. -/
@[simp] theorem adjoinKink_edgePair_inr (D : PDCode n) (b : Bool) (s : Fin 4) :
    (D.adjoinKink b).edgePair.val (halfEdgeSuccEquiv n (.inr s)) =
      halfEdgeSuccEquiv n (.inr (slotSmoothing true s)) := by
  simp [adjoinKink_edgePair_val, Equiv.permCongr_apply]

private theorem orbitCount_opposite_mul_smoothing :
    orbitCount (oppositeCrossingSlot * slotSmoothing true) = 2 := by
  have h : IsPerfectMatching (oppositeCrossingSlot * slotSmoothing true) := by
    rw [isPerfectMatching_iff]
    simp only [oppositeCrossingSlot_apply, slotSmoothing_true,
      Perm.mul_apply]
    decide
  have hcount := h.two_mul_orbitCount
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcount
  omega

private theorem orbitCount_smoothing_mul_smoothing (b : Bool) :
    orbitCount (slotSmoothing b * slotSmoothing true) = if b then 4 else 2 := by
  cases b
  · have h : IsPerfectMatching (slotSmoothing false * slotSmoothing true) := by
      rw [isPerfectMatching_iff]
      simp only [slotSmoothing_false, slotSmoothing_true, Perm.mul_apply]
      decide
    have hcount := h.two_mul_orbitCount
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcount
    simp only [Bool.false_eq_true, ↓reduceIte]
    omega
  · have h : slotSmoothing true * slotSmoothing true = 1 :=
      Equiv.ext (slotSmoothing_apply_apply true)
    rw [h, orbitCount_one]
    simp

private theorem orbitCount_mul_adjoinKink_edgePair (D : PDCode n) (b : Bool)
    (σ : Perm (Fin (4 * n))) (τ : Perm (Fin 4)) :
    orbitCount ((halfEdgeSuccEquiv n).permCongr (Perm.sumCongr σ τ) *
      (D.adjoinKink b).edgePair.val) =
      orbitCount (σ * D.edgePair.val) + orbitCount (τ * slotSmoothing true) := by
  rw [adjoinKink_edgePair_val, ← Equiv.permCongr_mul, Perm.sumCongr_mul,
    orbitCount_permCongr, orbitCount_sumCongr]

/-- Adjoining an isolated kink adds one crossing-bearing component. -/
@[simp] theorem crossingComponentCount_adjoinKink (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).crossingComponentCount = D.crossingComponentCount + 1 := by
  rw [crossingComponentCount_def, crossingComponentCount_def, componentPerm_def,
    componentPerm_def, crossingTurn_eq_permCongr_sumCongr (adjoinKink_halfEdge D b),
    orbitCount_mul_adjoinKink_edgePair, orbitCount_opposite_mul_smoothing]
  omega

/-- A kink and a crossing-free circle contribute the same number of components. -/
@[simp] theorem componentCount_adjoinKink (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).componentCount = D.adjoinCircle.componentCount := by
  simp [Nat.add_assoc, Nat.add_comm]

/-- A state of the isolated kink contributes two circles when it separates its arcs,
and one circle otherwise. -/
@[simp] theorem stateLoopCount_adjoinKink (D : PDCode n) (b : Bool)
    (s : Fin (n + 1) → Bool) :
    (D.adjoinKink b).stateLoopCount s =
      D.stateLoopCount (Fin.init s) + 1 + if s (Fin.last n) = b then 1 else 0 := by
  rw [stateLoopCount_def, stateLoopCount_def, statePerm_def, statePerm_def,
    smoothingTurn_eq_permCongr_sumCongr (adjoinKink_halfEdge D b),
    init_smoothingChoice_of_overPair_eq (adjoinKink_overPair D b),
    smoothingChoice_last_of_overPair_eq (adjoinKink_overPair D b),
    orbitCount_mul_adjoinKink_edgePair, orbitCount_smoothing_mul_smoothing,
    adjoinKink_crossinglessComponentCount]
  by_cases h : s (Fin.last n) = b <;> simp [h] <;> omega

/-- The first Reidemeister factor for a kink on a crossing-free circle. The surrounding
diagram may be empty. -/
@[simp] theorem kauffmanBracket_adjoinKink {R : Type*} [CommRing R] (D : PDCode n)
    (b : Bool) (a : Rˣ) :
    (D.adjoinKink b).kauffmanBracket a =
      -(((bif b then a else a⁻¹ : Rˣ) : R) ^ 3) * D.adjoinCircle.kauffmanBracket a := by
  rw [kauffmanBracket_def, kauffmanBracket_def, ← (Fin.snocEquiv fun _ => Bool).sum_comp,
    Fintype.sum_prod_type, Fintype.sum_bool, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [Fin.snocEquiv, Equiv.coe_fn_mk, stateLoopCount_adjoinKink,
    Fin.init_snoc, Fin.snoc_last, stateWeight_snoc, stateLoopCount_adjoinCircle]
  cases b <;> simp only [Bool.cond_true, Bool.cond_false, Bool.true_eq_false, Bool.false_eq_true,
    ↓reduceIte, add_zero, Nat.add_sub_cancel, pow_succ, jonesDelta_def, Units.val_mul]
  · linear_combination (-((stateWeight s a : R) * (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^
      D.stateLoopCount s * (a : R))) * a.inv_mul
  · linear_combination (-((stateWeight s a : R) * (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2)) ^
      D.stateLoopCount s * ((a⁻¹ : Rˣ) : R))) * a.mul_inv

/-- Reflection switches the over-strand of the new kink. -/
@[simp] theorem mirror_adjoinKink (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).mirror = D.mirror.adjoinKink (!b) := by
  apply PDCode.ext
  · simp
  · apply Subtype.ext
    simp [adjoinKink_edgePair_val]
  · simp
  · funext i
    induction i using Fin.lastCases <;> simp

private theorem crossingRotation_adjoinKink (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).crossingRotation =
      (halfEdgeSuccEquiv n).permCongr (Perm.sumCongr D.crossingRotation (finRotate 4)) := by
  apply eq_permCongr_sumCongr_of_halfEdge_eq (adjoinKink_halfEdge D b)
    (fun _ => finRotate 4)
  · intro i s
    rw [crossingRotation_crossing, finRotate_apply]
  · intro i s
    rw [crossingRotation_crossing, finRotate_apply]

private def kinkOrbit (D : PDCode n) (b : Bool) (z : Fin (4 * n) ⊕ Fin 4) :
    (D.adjoinKink b).toPermutationTriple.MonodromyOrbit :=
  Quotient.mk _ (halfEdgeSuccEquiv n z)

private theorem kinkOrbit_rotation (D : PDCode n) (b : Bool) (z : Fin (4 * n) ⊕ Fin 4) :
    kinkOrbit D b (Perm.sumCongr D.crossingRotation (finRotate 4) z) = kinkOrbit D b z := by
  have h := (D.adjoinKink b).toPermutationTriple.mk_σ0_apply (halfEdgeSuccEquiv n z)
  simpa [toPermutationTriple_σ0, crossingRotation_adjoinKink, Equiv.permCongr_apply,
    kinkOrbit] using h

private theorem kinkOrbit_pair (D : PDCode n) (b : Bool) (z : Fin (4 * n) ⊕ Fin 4) :
    kinkOrbit D b (Perm.sumCongr D.edgePair.val (slotSmoothing true) z) = kinkOrbit D b z := by
  have h := (D.adjoinKink b).toPermutationTriple.mk_σ1_apply (halfEdgeSuccEquiv n z)
  simpa [toPermutationTriple_σ1, adjoinKink_edgePair_val, Equiv.permCongr_apply,
    kinkOrbit] using h

private theorem kinkOrbit_inr (D : PDCode n) (b : Bool) (s : Fin 4) :
    kinkOrbit D b (.inr s) = kinkOrbit D b (.inr 0) := by
  apply apply_eq_apply_zero_of_add_one (f := fun s => kinkOrbit D b (.inr s))
  intro t
  simpa [finRotate_apply] using kinkOrbit_rotation D b (.inr t)

/-- The new kink is one connected component of the underlying graph, separate from all
components of the surrounding diagram. -/
@[simp] theorem card_monodromyOrbit_adjoinKink (D : PDCode n) (b : Bool) :
    Nat.card (D.adjoinKink b).toPermutationTriple.MonodromyOrbit =
      Nat.card D.toPermutationTriple.MonodromyOrbit + 1 := by
  -- On old half-edges remember their old component; collapse all new slots to one point.
  let f : Fin (4 * n) ⊕ Fin 4 → D.toPermutationTriple.MonodromyOrbit ⊕ Unit :=
    Sum.elim (fun x => .inl (Quotient.mk _ x)) (fun _ => .inr ())
  have hf0 (z : Fin (4 * n) ⊕ Fin 4) :
      f (Perm.sumCongr D.crossingRotation (finRotate 4) z) = f z := by
    rcases z with x | s
    · simp [f, ← toPermutationTriple_σ0]
    · rfl
  have hf1 (z : Fin (4 * n) ⊕ Fin 4) :
      f (Perm.sumCongr D.edgePair.val (slotSmoothing true) z) = f z := by
    rcases z with x | s
    · simp [f, ← toPermutationTriple_σ1]
    · rfl
  have he : (D.adjoinKink b).toPermutationTriple.MonodromyOrbit ≃
      D.toPermutationTriple.MonodromyOrbit ⊕ Unit :=
    { toFun := Quotient.lift (fun y => f ((halfEdgeSuccEquiv n).symm y)) (by
        rintro _ y ⟨⟨g, hg⟩, rfl⟩
        refine PermutationTriple.apply_eq_of_mem_monodromyGroup _
          (f := fun y => f ((halfEdgeSuccEquiv n).symm y)) ?_ ?_ hg y
        · intro y
          obtain ⟨z, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
          simpa [toPermutationTriple_σ0, crossingRotation_adjoinKink,
            Equiv.permCongr_apply] using hf0 z
        · intro y
          obtain ⟨z, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
          simpa [toPermutationTriple_σ1, adjoinKink_edgePair_val,
            Equiv.permCongr_apply] using hf1 z)
      invFun := Sum.elim (Quotient.lift (fun x => kinkOrbit D b (.inl x)) (by
        rintro _ x ⟨⟨g, hg⟩, rfl⟩
        refine PermutationTriple.apply_eq_of_mem_monodromyGroup _
          (f := fun x => kinkOrbit D b (.inl x)) ?_ ?_ hg x
        · intro x
          simpa [toPermutationTriple_σ0] using kinkOrbit_rotation D b (.inl x)
        · intro x
          simpa [toPermutationTriple_σ1] using kinkOrbit_pair D b (.inl x)))
        (fun _ => kinkOrbit D b (.inr 0))
      left_inv := Quotient.ind (fun y => by
        obtain ⟨x | s, rfl⟩ := (halfEdgeSuccEquiv n).surjective y
        · simp [f, kinkOrbit]
          rfl
        · simpa [f, kinkOrbit] using (kinkOrbit_inr D b s).symm)
      right_inv := by
        rintro (x | u)
        · induction x using Quotient.ind
          rename_i x
          exact congrArg f ((halfEdgeSuccEquiv n).symm_apply_apply (.inl x))
        · simp [f, kinkOrbit] }
  simpa using Nat.card_congr he

/-- The isolated kink adds its three faces to the surrounding diagram. -/
@[simp] theorem faceCount_adjoinKink (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).faceCount = D.faceCount + 3 := by
  have hperm : finRotate 4 * slotSmoothing true = Equiv.swap 0 2 := by
    ext s
    simp only [Perm.mul_apply, finRotate_apply, slotSmoothing_true]
    fin_cases s <;> decide
  have hc := orbitCount_mul_swap_add_one (τ := (1 : Perm (Fin 4))) (p := 2) (a := 0)
    rfl (by decide)
  simp only [one_mul, orbitCount_one, Nat.card_fin] at hc
  rw [faceCount_eq_orbitCount_crossingRotation_mul_edgePair,
    crossingRotation_adjoinKink, orbitCount_mul_adjoinKink_edgePair, hperm,
    ← faceCount_eq_orbitCount_crossingRotation_mul_edgePair]
  omega

/-- The first Reidemeister move on a crossing-free circle preserves planarity. -/
@[simp] theorem isPlanar_adjoinKink_iff (D : PDCode n) (b : Bool) :
    (D.adjoinKink b).IsPlanar ↔ D.IsPlanar := by
  rw [isPlanar_iff_faceCount_eq, isPlanar_iff_faceCount_eq,
    faceCount_adjoinKink, card_monodromyOrbit_adjoinKink]
  omega

end PDCode
end TauCeti
