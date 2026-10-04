/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.Reidemeister.Three.Basic
public import TauCeti.KnotTheory.PDCode.Kauffman
import TauCeti.KnotTheory.PDCode.Reidemeister.Three.Local
import Mathlib.Tactic.LinearCombination

/-!
# Invariance of the Kauffman bracket under the third Reidemeister move

The eight local smoothings are reduced to the five matchings of the six boundary ports.
The reduction inserts six internal vertices into the traversal, except for the middle
smoothing, which leaves an additional circle. The surrounding diagram is arbitrary.
The crossing weights cancel for each of the six acyclic height orders;
`kauffmanBracket_reidemeisterThree` states the resulting invariance.

## References

* L. H. Kauffman, *State models and the Jones polynomial*, Topology 26 (1987), 395-407.
* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 3.
-/

public section

namespace TauCeti.PDCode

open Equiv Equiv.Perm TauCeti.TemperleyLieb ReidemeisterThree

variable {n : ℕ} (D : PDCode n) (c : Fin 3 ↪ Fin n)
  (h : D.HasReidemeisterThreeTriangle c)

/-! ### The eight local smoothings -/

private def localVertex (i : Fin 12) : Fin 3 × Fin 4 :=
  (crossingSlotEquiv 3).symm i

private theorem localVertex_eq (i : Fin 12) :
    localVertex i = ![(0, 0), (0, 1), (0, 2), (0, 3), (1, 0), (1, 1),
      (1, 2), (1, 3), (2, 0), (2, 1), (2, 2), (2, 3)] i := by
  apply (crossingSlotEquiv 3).injective
  rw [localVertex, Equiv.apply_symm_apply]
  have hf (p : Fin 3 × Fin 4) : (crossingSlotEquiv 3 p).val = p.2.val + 4 * p.1.val :=
    crossingSlotEquiv_apply_val 3 p.1 p.2
  fin_cases i <;> apply Fin.ext <;> simp [hf]

private def localSmoothing (q : Fin 3 → Bool) : Perm (Fin 3 × Fin 4) :=
  Equiv.prodCongrRight fun i ↦ slotSmoothing (q i)

private theorem localSmoothing_apply (q : Fin 3 → Bool) (i : Fin 3) (s : Fin 4) :
    localSmoothing q (i, s) = (i, slotSmoothing (q i) s) := (rfl)

private theorem localSmoothing_eq (q : Fin 3 → Bool) :
    localSmoothing q = Equiv.prodCongrRight (fun i ↦
      if q i then swap 0 1 * swap 2 3 else swap 0 3 * swap 1 2) := by
  rw [localSmoothing]
  congr 1
  funext i
  cases q i <;> simp

private def localPairing (k : Fin 5) : Perm (Fin 3 × Fin 4) :=
  ![swap (0, 0) (0, 3) * swap (1, 3) (1, 2) * swap (2, 1) (2, 2),
    swap (0, 0) (0, 3) * swap (1, 3) (2, 1) * swap (2, 2) (1, 2),
    swap (0, 0) (1, 2) * swap (0, 3) (1, 3) * swap (2, 1) (2, 2),
    swap (0, 0) (2, 1) * swap (0, 3) (1, 3) * swap (2, 2) (1, 2),
    swap (0, 0) (2, 1) * swap (0, 3) (2, 2) * swap (1, 3) (1, 2)] k

private def leftPairingIndex (q : Fin 3 → Bool) : Fin 5 :=
  match q 0, q 1, q 2 with
  | false, false, false => 0
  | false, false, true => 1
  | false, true, false => 0
  | false, true, true => 0
  | true, false, false => 2
  | true, false, true => 3
  | true, true, false => 0
  | true, true, true => 4

private def pairingIndex (side : Bool) (q : Fin 3 → Bool) : Fin 5 :=
  if side then ![3, 2, 1, 0, 4] (leftPairingIndex q) else leftPairingIndex q

private def localFactor (side : Bool) (q : Fin 3 → Bool) : Perm (Fin 3 × Fin 4) :=
  (if side then reidemeisterThreeSlots⁻¹ * localSmoothing q * reidemeisterThreeSlots
    else localSmoothing q) * localInternalMatching

private def smoothingFactors (side : Bool) (q : Fin 3 → Bool) :
    List ((Fin 3 × Fin 4) × (Fin 3 × Fin 4)) :=
  ((match side, q 0, q 1, q 2 with
    | false, false, false, false => [(8, 5), (2, 8), (7, 2), (1, 4), (11, 1), (6, 11)]
    | false, false, false, true => [(10, 5), (6, 11), (2, 8), (7, 2), (1, 4), (9, 1)]
    | false, false, true, false => [(2, 8), (2, 5), (1, 4), (1, 11)]
    | false, false, true, true => [(4, 11), (1, 4), (9, 1), (2, 8), (5, 2), (10, 5)]
    | false, true, false, false => [(8, 5), (0, 8), (3, 4), (7, 2), (11, 1), (6, 11)]
    | false, true, false, true => [(10, 5), (6, 11), (0, 8), (3, 4), (7, 2), (9, 1)]
    | false, true, true, false => [(5, 2), (8, 5), (0, 8), (11, 1), (4, 11), (3, 4)]
    | false, true, true, true => [(4, 11), (3, 4), (0, 8), (5, 2), (10, 5), (9, 1)]
    | true, false, false, false => [(8, 2), (5, 8), (0, 5), (1, 11), (4, 1), (9, 4)]
    | true, false, false, true => [(5, 8), (0, 5), (9, 4), (10, 2), (1, 11), (6, 1)]
    | true, false, true, false => [(2, 5), (2, 8), (1, 11), (1, 4)]
    | true, false, true, true => [(5, 8), (2, 5), (10, 2), (11, 4), (1, 11), (6, 1)]
    | true, true, false, false => [(8, 2), (7, 8), (4, 1), (9, 4), (0, 5), (3, 11)]
    | true, true, false, true => [(7, 8), (9, 4), (10, 2), (6, 1), (0, 5), (3, 11)]
    | true, true, true, false => [(4, 1), (11, 4), (3, 11), (2, 5), (8, 2), (7, 8)]
    | true, true, true, true => [(7, 8), (11, 4), (3, 11), (6, 1), (2, 5), (10, 2)]
    : List (Fin 12 × Fin 12))).map fun p ↦ (localVertex p.1, localVertex p.2)

private theorem localFactor_eq (side : Bool) (q : Fin 3 → Bool) :
    localFactor side q =
      ((smoothingFactors side q).map (Function.uncurry Equiv.swap)).prod *
        localPairing (pairingIndex side q) := by
  have hq : q = ![q 0, q 1, q 2] := by ext i; fin_cases i <;> simp
  rw [hq]
  generalize q 0 = x, q 1 = y, q 2 = z
  have hf (p : Fin 3 × Fin 4) : reidemeisterThreeSlots p =
      ![![(1, 0), (0, 2), (1, 2), (0, 0)],
        ![(2, 0), (0, 1), (2, 2), (0, 3)],
        ![(2, 3), (1, 1), (2, 1), (1, 3)]] p.1 p.2 :=
    reidemeisterThreeSlots_apply p.1 p.2
  have hi (p : Fin 3 × Fin 4) : reidemeisterThreeSlots⁻¹ p =
      ![![(0, 3), (1, 1), (0, 1), (1, 3)],
        ![(0, 0), (2, 1), (0, 2), (2, 3)],
        ![(1, 0), (2, 2), (1, 2), (2, 0)]] p.1 p.2 :=
    reidemeisterThreeSlots_symm_apply p.1 p.2
  cases side <;> cases x <;> cases y <;> cases z <;>
    apply Equiv.ext <;> intro p <;>
    simp only [localFactor, Bool.false_eq_true, ↓reduceIte, Perm.mul_apply, hf, hi] <;>
    simp only [localInternalMatching_def, localSmoothing_eq, smoothingFactors, localVertex_eq] <;>
    revert p <;> decide

private theorem smoothingFactors_isSwapForest (side : Bool) (q : Fin 3 → Bool) :
    (smoothingFactors side q).IsSwapForest := by
  have hq : q = ![q 0, q 1, q 2] := by ext i; fin_cases i <;> simp
  rw [hq]
  generalize q 0 = x, q 1 = y, q 2 = z
  cases side <;> cases x <;> cases y <;> cases z <;>
    simp only [smoothingFactors, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, List.map_cons, List.map_nil,
      List.isSwapForest_cons,
      List.isSwapForest_nil, localVertex_eq] <;> decide

private theorem smoothingFactors_internal (side : Bool) (q : Fin 3 → Bool) :
    ∀ factor ∈ smoothingFactors side q, localInternal factor.2 := by
  have hq : q = ![q 0, q 1, q 2] := by ext i; fin_cases i <;> simp
  rw [hq]
  generalize q 0 = x, q 1 = y, q 2 = z
  cases side <;> cases x <;> cases y <;> cases z <;>
    norm_num [smoothingFactors, localVertex_eq, localInternal_iff]

private theorem localPairing_internal (k : Fin 5) (p : Fin 3 × Fin 4)
    (hp : localInternal p) : localPairing k p = p := by
  revert k p
  decide


private theorem smoothingTurn_split (u : Fin n → Bool) :
    D.smoothingTurn u = localLift D c (localSmoothing (u ∘ c)) *
      exteriorSlots D c (fun i ↦ slotSmoothing (u i)) := by
  apply Equiv.ext
  intro x
  obtain ⟨y, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, s⟩, rfl⟩ := (crossingSlotEquiv n).surjective y
  rw [smoothingTurn_crossing, Perm.mul_apply, ← crossing_apply, exteriorSlots_crossing]
  by_cases hi : i ∈ Set.range c
  · obtain ⟨j, rfl⟩ := hi
    simp only [Set.mem_range_self, ↓reduceIte, Perm.one_apply]
    simpa only [localSmoothing_apply, Function.comp_apply, triangleEmbedding_apply] using
      (localLift_apply D c (localSmoothing (u ∘ c)) (j, s)).symm
  · simp only [hi, ↓reduceIte]
    rw [localLift_fixed D c _ hi]

private def pairingTraversal (u : Fin n → Bool) (k : Fin 5) : Perm (Fin (4 * n)) :=
  localLift D c (localPairing k) * exteriorSlots D c (fun i ↦ slotSmoothing (u i)) *
    outsideEdges D c

include h in
private theorem pairingTraversal_internal (u : Fin n → Bool) (k : Fin 5)
    (p : Fin 3 × Fin 4) (hp : localInternal p) :
    pairingTraversal D c u k (triangleEmbedding D c p) = triangleEmbedding D c p := by
  rw [pairingTraversal, Perm.mul_apply, Perm.mul_apply, outsideEdges_internal D c h.arcs p hp,
    exteriorSlots_local, localLift_apply, localPairing_internal k p hp]

include h in
private theorem localFactor_orbitCount (side : Bool) (q : Fin 3 → Bool)
    (u : Fin n → Bool) :
    orbitCount (localLift D c (localFactor side q) *
      exteriorSlots D c (fun i ↦ slotSmoothing (u i)) * outsideEdges D c) +
        (smoothingFactors side q).length =
        orbitCount (pairingTraversal D c u (pairingIndex side q)) := by
  simpa only [pairingTraversal, mul_assoc] using
    localLift_swapForest_orbitCount D c (localFactor side q)
      (localPairing (pairingIndex side q)) (smoothingFactors side q)
      (exteriorSlots D c (fun i ↦ slotSmoothing (u i)) * outsideEdges D c)
      (smoothingFactors_isSwapForest side q) (localFactor_eq side q)
      (fun p hp ↦ by
        simpa only [pairingTraversal, mul_assoc] using
          pairingTraversal_internal D c h u _ p.2 (smoothingFactors_internal side q p hp))

include h in
private theorem rawTraversal_orbitCount (side : Bool) (u : Fin n → Bool) :
    orbitCount (if side then
      (D.reidemeisterThree c).smoothingTurn u * (D.reidemeisterThree c).edgePair.val
      else D.smoothingTurn u * D.edgePair.val) + (smoothingFactors side (u ∘ c)).length =
        orbitCount (pairingTraversal D c u (pairingIndex side (u ∘ c))) := by
  have hc := localFactor_orbitCount D c h side (u ∘ c) u
  rw [localFactor, localLift_remove_internal D c _ _
    (localLift_commute_exteriorSlots D c localInternalMatching
      (fun i ↦ slotSmoothing (u i)))] at hc
  cases side with
  | false => simpa only [Bool.false_eq_true, ↓reduceIte, ← smoothingTurn_split] using hc
  | true =>
    simp only [↓reduceIte, map_mul, map_inv] at hc
    have hρ := localLift_slots D c
    have hS : (D.reidemeisterThree c).smoothingTurn u = D.smoothingTurn u := by
      simp only [smoothingTurn_def, reidemeisterThree_halfEdge]
    rw [hρ] at hc
    simp only [↓reduceIte]
    rw [hS, reidemeisterThree_edgePair]
    have heq : (D.reidemeisterThreePerm c).symm.permCongr
        (D.smoothingTurn u * (D.reidemeisterThreePerm c).permCongr D.edgePair.val) =
        (D.reidemeisterThreePerm c)⁻¹ * localLift D c (localSmoothing (u ∘ c)) *
          D.reidemeisterThreePerm c * exteriorSlots D c (fun i ↦ slotSmoothing (u i)) *
            D.edgePair.val := by
      rw [Equiv.permCongr_eq_mul, Equiv.permCongr_eq_mul, smoothingTurn_split D c u, ← Perm.inv_def]
      have hcomm := (localLift_commute_exteriorSlots D c reidemeisterThreeSlots
        (fun i ↦ slotSmoothing (u i))).eq
      rw [hρ] at hcomm
      calc
        _ = (D.reidemeisterThreePerm c)⁻¹ * localLift D c (localSmoothing (u ∘ c)) *
            (exteriorSlots D c (fun i ↦ slotSmoothing (u i)) * D.reidemeisterThreePerm c) *
              D.edgePair.val := by group
        _ = _ := by rw [← hcomm]; group
    rw [← Equiv.orbitCount_permCongr (D.reidemeisterThreePerm c).symm,
      heq]
    exact hc

private noncomputable def localStatesEquiv {n : ℕ} (c : Fin 3 ↪ Fin n) :
    (Fin n → Bool) ≃ (Fin 3 → Bool) × ({i : Fin n // i ∉ Set.range c} → Bool) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i ↦ i ∈ Set.range c) (fun _ ↦ Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr c.toEquivRange.symm (Equiv.refl Bool)) (Equiv.refl _))

private noncomputable def assembleState {n : ℕ} (c : Fin 3 ↪ Fin n) (q : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) : Fin n → Bool :=
  (localStatesEquiv c).symm (q, r)

private theorem assembleState_local {n : ℕ} (c : Fin 3 ↪ Fin n) (q : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) (j : Fin 3) :
    assembleState c q r (c j) = q j := by
  classical
  simp [assembleState, localStatesEquiv, Equiv.arrowCongr]

private theorem assembleState_outside {n : ℕ} (c : Fin 3 ↪ Fin n) (q : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) (i : {i : Fin n // i ∉ Set.range c}) :
    assembleState c q r i = r i := by
  classical
  simp [assembleState, localStatesEquiv, Equiv.arrowCongr, i.property]

private theorem assembleState_prod {n : ℕ} {M : Type*} [CommMonoid M]
    (c : Fin 3 ↪ Fin n) (q : Fin 3 → Bool) (r : {i : Fin n // i ∉ Set.range c} → Bool)
    (f : Fin n → Bool → M) :
    (∏ i, f i (assembleState c q r i)) =
      (∏ j, f (c j) (q j)) * ∏ i : {i : Fin n // i ∉ Set.range c}, f i (r i) := by
  classical
  let : Fintype (Set.range c) := Subtype.fintype (fun i ↦ i ∈ Set.range c)
  rw [← Fintype.prod_subtype_mul_prod_subtype (fun i ↦ i ∈ Set.range c)
    (fun i ↦ f i (assembleState c q r i))]
  congr 1
  · symm
    refine Fintype.prod_equiv c.toEquivRange (fun j ↦ f (c j) (q j))
      (fun i : {i : Fin n // i ∈ Set.range c} ↦ f i (assembleState c q r i)) (fun j ↦ ?_)
    simp [assembleState_local]
  · exact Finset.prod_congr rfl (fun i _ ↦ congrArg (f i) (assembleState_outside c q r i))

private def rawState (D : PDCode n) (u : Fin n → Bool) : Fin n → Bool :=
  fun i ↦ u i == D.overPair i

private theorem rawState_smoothingChoice (D : PDCode n) (u : Fin n → Bool) :
    D.smoothingChoice (rawState D u) = u := by
  funext i
  cases hu : u i <;> cases ho : D.overPair i <;>
    simp [rawState, hu, ho, smoothingChoice_of_true, smoothingChoice_of_false]

private theorem rawState_injective (D : PDCode n) : Function.Injective (rawState D) := by
  intro u v huv
  have := congrArg D.smoothingChoice huv
  simpa only [rawState_smoothingChoice] using this

private theorem rawState_surjective (D : PDCode n) : Function.Surjective (rawState D) := by
  intro s
  refine ⟨D.smoothingChoice s, ?_⟩
  funext i
  cases hs : s i <;> cases ho : D.overPair i <;>
    simp [rawState, hs, ho, smoothingChoice_of_true, smoothingChoice_of_false]

private noncomputable def rawLoopCount (D : PDCode n) (u : Fin n → Bool) : ℕ :=
  orbitCount (D.smoothingTurn u * D.edgePair.val) / 2 + D.crossinglessComponentCount

private theorem rawLoopCount_eq (D : PDCode n) (u : Fin n → Bool) :
    rawLoopCount D u = D.stateLoopCount (rawState D u) := by
  rw [stateLoopCount_def, statePerm_def, rawState_smoothingChoice]
  rfl

include c in
private theorem rawLoopCount_pos (u : Fin n → Bool) : 1 ≤ rawLoopCount D u := by
  rw [rawLoopCount_eq]
  apply D.one_le_stateLoopCount
  have hn := (c 0).isLt
  omega

private theorem exteriorSlots_assemble (q q' : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) :
    exteriorSlots D c (fun i ↦ slotSmoothing (assembleState c q r i)) =
      exteriorSlots D c (fun i ↦ slotSmoothing (assembleState c q' r i)) := by
  apply Equiv.ext
  intro x
  obtain ⟨z, rfl⟩ := D.halfEdge.surjective x
  obtain ⟨⟨i, t⟩, rfl⟩ := (crossingSlotEquiv n).surjective z
  rw [← crossing_apply, exteriorSlots_crossing, exteriorSlots_crossing]
  by_cases hi : i ∈ Set.range c
  · simp only [hi, ↓reduceIte]
  · have hq := assembleState_outside c q r ⟨i, hi⟩
    have hq' := assembleState_outside c q' r ⟨i, hi⟩
    simp only [hi, ↓reduceIte, hq, hq']

private theorem pairingTraversal_assemble (q : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) (k : Fin 5) :
    pairingTraversal D c (assembleState c q r) k =
      pairingTraversal D c (assembleState c (fun _ ↦ false) r) k := by
  rw [pairingTraversal, pairingTraversal, exteriorSlots_assemble D c q (fun _ ↦ false) r]

private def extraCircle (q : Fin 3 → Bool) : ℕ :=
  if q 0 = false ∧ q 1 = true ∧ q 2 = false then 1 else 0

private theorem smoothingFactors_length (side : Bool) (q : Fin 3 → Bool) :
    (smoothingFactors side q).length + 2 * extraCircle q = 6 := by
  have hq : q = ![q 0, q 1, q 2] := by ext i; fin_cases i <;> simp
  rw [hq]
  generalize q 0 = x, q 1 = y, q 2 = z
  cases side <;> cases x <;> cases y <;> cases z <;>
    simp only [smoothingFactors, List.length_map] <;> decide

private def pairingRepresentative (k : Fin 5) : Fin 3 → Bool :=
  ![![false, false, false], ![false, false, true], ![true, false, false],
    ![true, false, true], ![true, true, true]] k

private theorem pairingRepresentative_spec (k : Fin 5) :
    pairingIndex false (pairingRepresentative k) = k ∧
      (smoothingFactors false (pairingRepresentative k)).length = 6 := by
  revert k
  decide

private noncomputable def pairingExponent
    (r : {i : Fin n // i ∉ Set.range c} → Bool) (k : Fin 5) : ℕ :=
  orbitCount (pairingTraversal D c (assembleState c (fun _ ↦ false) r) k) / 2 +
    D.crossinglessComponentCount - 4

include h in
private theorem pairingTraversal_loops_lower
    (r : {i : Fin n // i ∉ Set.range c} → Bool) (k : Fin 5) :
    4 ≤ orbitCount (pairingTraversal D c (assembleState c (fun _ ↦ false) r) k) / 2 +
      D.crossinglessComponentCount := by
  have hc := rawTraversal_orbitCount D c h false (assembleState c (pairingRepresentative k) r)
  have hq : assembleState c (pairingRepresentative k) r ∘ c = pairingRepresentative k := by
    funext j
    exact assembleState_local c _ r j
  rw [hq, (pairingRepresentative_spec k).1, (pairingRepresentative_spec k).2,
    pairingTraversal_assemble] at hc
  simp only [Bool.false_eq_true, ↓reduceIte] at hc
  have hp := rawLoopCount_pos D c (assembleState c (pairingRepresentative k) r)
  simp only [rawLoopCount] at hp
  omega

include h in
private theorem rawLoopCount_assemble (side : Bool) (q : Fin 3 → Bool)
    (r : {i : Fin n // i ∉ Set.range c} → Bool) :
    rawLoopCount (if side then D.reidemeisterThree c else D) (assembleState c q r) - 1 =
      pairingExponent D c r (pairingIndex side q) + extraCircle q := by
  have hc := rawTraversal_orbitCount D c h side (assembleState c q r)
  have hq : assembleState c q r ∘ c = q := by
    funext j
    exact assembleState_local c q r j
  rw [hq, pairingTraversal_assemble] at hc
  have hl := smoothingFactors_length side q
  have hp := pairingTraversal_loops_lower D c h r (pairingIndex side q)
  simp only [pairingExponent]
  cases side <;> simp only [Bool.false_eq_true, ↓reduceIte, rawLoopCount,
    reidemeisterThree_crossinglessComponentCount] at * <;> omega

private def overWeight {R : Type*} [CommRing R] (a : Rˣ) (b : Bool) : R :=
  if b then ((a⁻¹ : Rˣ) : R) else (a : R)

-- The coefficients of the two nonmatching boundary pairings agree at the Jones loop value.
private theorem localCoefficient {R : Type*} [CommRing R] (a : Rˣ) (ba bb bc : Bool)
    (height : ba = bc → bb = ba) :
    overWeight a ba * overWeight a bb * overWeight a bc +
      overWeight a ba * overWeight a (!bb) * overWeight a bc * jonesDelta a +
      overWeight a ba * overWeight a (!bb) * overWeight a (!bc) +
      overWeight a (!ba) * overWeight a (!bb) * overWeight a bc =
      overWeight a (!ba) * overWeight a bb * overWeight a (!bc) := by
  cases ba <;> cases bb <;> cases bc
  all_goals simp only [overWeight, Bool.not_false, Bool.not_true, Bool.false_eq_true,
    ↓reduceIte, jonesDelta_def]
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * (a : R)) * a.mul_inv
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * ((a⁻¹ : Rˣ) : R)) * a.mul_inv
  · have := height rfl
    contradiction
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * (a : R)) * a.mul_inv
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * ((a⁻¹ : Rˣ) : R)) * a.mul_inv
  · have := height rfl
    contradiction
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * (a : R)) * a.mul_inv
  · linear_combination (-((a : R) ^ 2 + ((a⁻¹ : Rˣ) : R) ^ 2) * ((a⁻¹ : Rˣ) : R)) * a.mul_inv

private def pairingValue {R : Type*} [CommRing R] (δ P Q Rv S I : R)
    (u v w : Bool) : R :=
  if u then
    if v then if w then I else P else if w then S else Rv
  else
    if v then if w then P else δ * P else if w then Q else P

private def smoothingWeight {R : Type*} [CommRing R] (a : Rˣ) (over raw : Bool) : R :=
  overWeight a (if raw then !over else over)

private theorem localSum {R : Type*} [CommRing R] (a : Rˣ) (ba bb bc : Bool)
    (height : ba = bc → bb = ba) (P Q Rv S I : R) :
    (∑ u : Bool, ∑ v : Bool, ∑ t : Bool,
      smoothingWeight a ba u * smoothingWeight a bb v * smoothingWeight a bc t *
        pairingValue (jonesDelta a) P Q Rv S I u v t) =
    (∑ u : Bool, ∑ v : Bool, ∑ t : Bool,
      smoothingWeight a bc u * smoothingWeight a bb v * smoothingWeight a ba t *
        pairingValue (jonesDelta a) S Rv Q P I u v t) := by
  simp only [Fintype.sum_bool, smoothingWeight, pairingValue, Bool.false_eq_true, ↓reduceIte]
  linear_combination (P - S) * (localCoefficient a ba bb bc height)

private theorem sumCube {R : Type*} [AddCommMonoid R] (f : (Fin 3 → Bool) → R) :
    (∑ q : Fin 3 → Bool, f q) = ∑ u : Bool, ∑ v : Bool, ∑ t : Bool, f ![u, v, t] := by
  let e : Bool × Bool × Bool ≃ (Fin 3 → Bool) :=
    (Equiv.prodCongr (Equiv.refl Bool) (piFinTwoEquiv (fun _ ↦ Bool)).symm).trans
      (Fin.consEquiv (fun _ ↦ Bool))
  rw [← e.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

-- Equality for each fixed exterior state, before summing over the surrounding diagram.
private theorem localSumFin3 {R : Type*} [CommRing R] (a : Rˣ) (ba bb bc : Bool)
    (height : ba = bc → bb = ba) (P Q Rv S I : R) :
    (∑ q : Fin 3 → Bool,
      (∏ i, smoothingWeight a (![ba, bb, bc] i) (q i)) *
        pairingValue (jonesDelta a) P Q Rv S I (q 0) (q 1) (q 2)) =
    (∑ q : Fin 3 → Bool,
      (∏ i, smoothingWeight a (![bc, bb, ba] i) (q i)) *
        pairingValue (jonesDelta a) S Rv Q P I (q 0) (q 1) (q 2)) := by
  rw [sumCube, sumCube]
  simp only [Fin.prod_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two]
  exact localSum a ba bb bc height P Q Rv S I

private theorem rawState_weight {R : Type*} [CommRing R] (D : PDCode n)
    (a : Rˣ) (u : Fin n → Bool) :
    (stateWeight (rawState D u) a : R) = ∏ i, smoothingWeight a (D.overPair i) (u i) := by
  rw [stateWeight_def, Units.coe_prod]
  apply Finset.prod_congr rfl
  intro i hi
  cases hu : u i <;> cases ho : D.overPair i <;>
    simp [rawState, smoothingWeight, overWeight, hu, ho]

private theorem kauffmanBracket_raw {R : Type*} [CommRing R] (D : PDCode n) (a : Rˣ) :
    D.kauffmanBracket a = ∑ u : Fin n → Bool,
      (∏ i, smoothingWeight a (D.overPair i) (u i)) * jonesDelta a ^ (rawLoopCount D u - 1) := by
  rw [kauffmanBracket_def]
  symm
  refine Fintype.sum_bijective (rawState D)
    ⟨rawState_injective D, rawState_surjective D⟩ _ _ fun u ↦ ?_
  rw [rawState_weight, ← rawLoopCount_eq]

private theorem localLoopValue {R : Type*} [CommRing R] (δ : R) (K : Fin 5 → ℕ)
    (side : Bool) (q : Fin 3 → Bool) :
    δ ^ (K (pairingIndex side q) + extraCircle q) =
      if side then pairingValue δ (δ ^ K 3) (δ ^ K 2) (δ ^ K 1) (δ ^ K 0) (δ ^ K 4)
        (q 0) (q 1) (q 2)
      else pairingValue δ (δ ^ K 0) (δ ^ K 1) (δ ^ K 2) (δ ^ K 3) (δ ^ K 4)
        (q 0) (q 1) (q 2) := by
  have hq : q = ![q 0, q 1, q 2] := by ext i; fin_cases i <;> simp
  rw [hq]
  generalize q 0 = x, q 1 = y, q 2 = z
  cases side <;> cases x <;> cases y <;> cases z <;>
    simp [pairingIndex, leftPairingIndex, extraCircle, pairingValue, pow_succ, mul_comm]

private theorem overPair_outside (side : Bool) (i : {i : Fin n // i ∉ Set.range c}) :
    (if side then D.reidemeisterThree c else D).overPair i = D.overPair i := by
  have h0 : (i : Fin n) ≠ c 0 := fun he ↦ i.property ⟨0, he.symm⟩
  have h2 : (i : Fin n) ≠ c 2 := fun he ↦ i.property ⟨2, he.symm⟩
  cases side <;> simp [Equiv.swap_apply_of_ne_of_ne h0 h2]

include h in
private theorem kauffmanBracket_split {R : Type*} [CommRing R] (a : Rˣ) (side : Bool) :
    (if side then D.reidemeisterThree c else D).kauffmanBracket a =
      ∑ r : {i : Fin n // i ∉ Set.range c} → Bool,
        (∏ i : {i : Fin n // i ∉ Set.range c}, smoothingWeight a (D.overPair i) (r i)) *
        ∑ q : Fin 3 → Bool,
          (∏ j, smoothingWeight a ((if side then D.reidemeisterThree c else D).overPair (c j))
            (q j)) *
          (if side then pairingValue (jonesDelta a)
            (jonesDelta a ^ pairingExponent D c r 3) (jonesDelta a ^ pairingExponent D c r 2)
            (jonesDelta a ^ pairingExponent D c r 1) (jonesDelta a ^ pairingExponent D c r 0)
            (jonesDelta a ^ pairingExponent D c r 4) (q 0) (q 1) (q 2)
          else pairingValue (jonesDelta a)
            (jonesDelta a ^ pairingExponent D c r 0) (jonesDelta a ^ pairingExponent D c r 1)
            (jonesDelta a ^ pairingExponent D c r 2) (jonesDelta a ^ pairingExponent D c r 3)
            (jonesDelta a ^ pairingExponent D c r 4) (q 0) (q 1) (q 2)) := by
  classical
  rw [kauffmanBracket_raw, ← (localStatesEquiv c).symm.sum_comp]
  simp only [Fintype.sum_prod_type, ← assembleState.eq_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assembleState_prod, rawLoopCount_assemble D c h side q r, localLoopValue]
  simp only [overPair_outside D c]
  ring

include h in
/-- The third Reidemeister move preserves the Kauffman bracket, for every surrounding
PD-code and all six acyclic strand height orders. -/
@[simp] theorem kauffmanBracket_reidemeisterThree {R : Type*} [CommRing R] (a : Rˣ) :
    (D.reidemeisterThree c).kauffmanBracket a = D.kauffmanBracket a := by
  classical
  have hs0 := kauffmanBracket_split D c h a false
  have hs1 := kauffmanBracket_split D c h a true
  simp only [Bool.false_eq_true, ↓reduceIte] at hs0 hs1
  rw [hs0, hs1]
  apply Finset.sum_congr rfl
  intro r hr
  congr 1
  have ho : (fun j ↦ (D.reidemeisterThree c).overPair (c j)) =
      ![D.overPair (c 2), D.overPair (c 1), D.overPair (c 0)] := by
    funext j
    have h01 : c 0 ≠ c 1 := c.injective.ne (by decide)
    have h12 : c 1 ≠ c 2 := c.injective.ne (by decide)
    fin_cases j <;> simp [Equiv.swap_apply_def, h12, Ne.symm h01]
  have ho' : (fun j ↦ D.overPair (c j)) =
      ![D.overPair (c 0), D.overPair (c 1), D.overPair (c 2)] := by
    funext j
    fin_cases j <;> rfl
  have hl := localSumFin3 a (D.overPair (c 0)) (D.overPair (c 1)) (D.overPair (c 2))
    ((hasReidemeisterThreeTriangle_iff D c).mp h).2.2.2
    (jonesDelta a ^ pairingExponent D c r 0) (jonesDelta a ^ pairingExponent D c r 1)
    (jonesDelta a ^ pairingExponent D c r 2) (jonesDelta a ^ pairingExponent D c r 3)
    (jonesDelta a ^ pairingExponent D c r 4)
  simpa only [← ho, ← ho'] using hl.symm

end TauCeti.PDCode
