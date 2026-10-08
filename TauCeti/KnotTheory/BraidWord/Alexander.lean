/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.BraidWord.PDCode
public import TauCeti.KnotTheory.Burau.Basic
public import TauCeti.KnotTheory.PDCode.Alexander.Basic
import TauCeti.Data.List.Rotate

/-!
# The Alexander module of a closed braid

The Alexander module of the closure of a braid word `w` on `n` strands, read off its PD-code
through the Wirtinger presentation, is the cokernel of `burau β - 1` acting on column vectors,
where `burau β` is the unreduced Burau matrix at `t = T` of the braid `β` that `w` represents:

`w.closure.AlexanderModule ≃ (Fin n → ℤ[T;T⁻¹]) ⧸ range (burau β - 1)`.

Hence the elementary ideal `E_k` of the closure is the ideal of `(n - k)`-minors of `burau β - 1`
(`TauCeti.BraidWord.elementaryIdeal_closure`). This is the presentation-changing step joining the
diagram algorithm for the Alexander invariants to the Burau algorithm.

The isomorphism is the classical elimination of the Wirtinger generators of a closed braid.
Cutting the braid at height `k`, just below its `k`-th letter, the generators met there are
determined by those at the bottom: the Burau matrix of a crossing is exactly the matrix of its
crossing relations, written in the basis `T ^ (-p) • e p` of the strand positions `p`. So the
generator on position `p` at height `k` is sent to `T ^ (-p)` times the class of the `p`-th column
of the Burau matrix of the first `k` letters. Closing the braid identifies the top with the
bottom, which is the relation `burau β - 1`. Strand positions crossed by no letter close up to
crossing-free circles, whose generators are free; the Burau matrix fixes their basis vectors.

## Main definitions

* `TauCeti.BraidWord.closureAlexanderModuleEquiv`: the Alexander module of the closure is the
  cokernel of the Burau matrix minus the identity.

## Main results

* `TauCeti.BraidWord.closureAlexanderModuleEquiv_incomingSlot`,
  `TauCeti.BraidWord.closureAlexanderModuleEquiv_outgoingSlot` and
  `TauCeti.BraidWord.closureAlexanderModuleEquiv_crossinglessGenerator`: its values on the
  generators.
* `TauCeti.BraidWord.elementaryIdeal_closure`: the elementary ideals of the closure are the
  ideals of minors of the Burau matrix minus the identity.

## References

* J. Birman, *Braids, Links, and Mapping Class Groups*, Annals of Mathematics Studies 82,
  Princeton University Press (1974), Chapter 3 (the Burau matrix of a braid presents the
  Alexander module of its closure).
* R. H. Crowell, R. H. Fox, *Introduction to Knot Theory*, Graduate Texts in Mathematics 57,
  Springer (1977), Chapters VI–VII (the Wirtinger presentation and the Alexander matrix).
-/

public section

noncomputable section

open LaurentPolynomial Matrix

namespace TauCeti

namespace BraidWord

open BraidGroup KnotTheory PDCode

variable {n : ℕ} (w : BraidWord n)

/-! ### The Burau matrices of the letters and of the prefixes -/

/-- The Laurent variable `T` as a unit. -/
private abbrev tUnit : ℤ[T;T⁻¹]ˣ := (isUnit_T 1).unit

/-- The Burau matrix of the braid of the first `k` letters. -/
private def prefixMatrix (k : ℕ) : Matrix (Fin n) (Fin n) ℤ[T;T⁻¹] :=
  burau n tUnit (toBraid (w.take k))

/-- The Burau matrix of a single letter. -/
private def letterMatrix (x : Fin (n - 1) × ℤˣ) : Matrix (Fin n) (Fin n) ℤ[T;T⁻¹] :=
  burau n tUnit (sigma x.1 ^ (x.2 : ℤ))

private theorem prefixMatrix_zero : w.prefixMatrix 0 = 1 := by
  simp [prefixMatrix]

private theorem prefixMatrix_length :
    w.prefixMatrix w.length = burau n tUnit w.toBraid := by
  simp [prefixMatrix]

private theorem prefixMatrix_succ (j : Fin w.length) :
    w.prefixMatrix (j + 1) = w.prefixMatrix j * letterMatrix w[j.1] := by
  rw [prefixMatrix, prefixMatrix, letterMatrix, List.take_add_one,
    List.getElem?_eq_getElem j.2, Option.toList_some, toBraid_append, map_mul, Units.val_mul,
    toBraid_cons, toBraid_nil, mul_one]

/-- The basis vector `T ^ (-p) • e p` of a strand position, in which the Burau matrix of a letter
is the matrix of the Wirtinger relations of its crossing. -/
private def twist (p : Fin n) : Fin n → ℤ[T;T⁻¹] :=
  Pi.single p (T (-(p : ℤ)))

private theorem single_one_eq_smul_twist (q : Fin n) :
    (Pi.single q 1 : Fin n → ℤ[T;T⁻¹]) = (T (q : ℤ) : ℤ[T;T⁻¹]) • twist q := by
  rw [twist, ← Pi.single_smul', smul_eq_mul, ← T_add]
  simp

/-- The coefficient of the rank-one part of the Burau matrix of a letter: `1` for a positive
letter and `T⁻¹` for a negative one. -/
private def letterCoeff (ε : ℤˣ) : ℤ[T;T⁻¹] :=
  if ε = 1 then 1 else T (-1)

private theorem letterMatrix_eq (x : Fin (n - 1) × ℤˣ) :
    letterMatrix x = 1 - letterCoeff x.2 •
      vecMulVec (burauCol (T 1 : ℤ[T;T⁻¹]) x.1) (burauRow ℤ[T;T⁻¹] x.1) := by
  rcases Int.units_eq_one_or x.2 with h | h
  · simp [letterMatrix, letterCoeff, h, burauMatrix_def]
  · have hu : tUnit * (isUnit_T (R := ℤ) (-1)).unit = 1 :=
      Units.ext (by rw [Units.val_mul, IsUnit.unit_spec, IsUnit.unit_spec, ← T_add]; simp)
    have hinv : ((tUnit⁻¹ : ℤ[T;T⁻¹]ˣ) : ℤ[T;T⁻¹]) = T (-1) := by
      rw [inv_eq_of_mul_eq_one_right hu, IsUnit.unit_spec]
    have := inv_burauMatrix (R := ℤ[T;T⁻¹]) tUnit x.1
    simp only [IsUnit.unit_spec, hinv] at this
    simp [letterMatrix, letterCoeff, h, this]

private theorem letterMatrix_mulVec (x : Fin (n - 1) × ℤˣ) (v : Fin n → ℤ[T;T⁻¹]) :
    letterMatrix x *ᵥ v =
      v - (letterCoeff x.2 * (burauRow ℤ[T;T⁻¹] x.1 ⬝ᵥ v)) • burauCol (T 1 : ℤ[T;T⁻¹]) x.1 := by
  rw [letterMatrix_eq, sub_mulVec, one_mulVec, smul_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    smul_smul]

private theorem letterMatrix_mulVec_twist_of_ne (x : Fin (n - 1) × ℤˣ) {p : Fin n}
    (h₀ : p ≠ strand x.1) (h₁ : p ≠ strandSucc x.1) :
    letterMatrix x *ᵥ twist p = twist p := by
  rw [letterMatrix_mulVec, burauRow_dotProduct]
  simp [twist, h₀.symm, h₁.symm]

/-- The crossing relation expressing the generator leaving on the lower position. -/
private theorem letterMatrix_mulVec_twist_strand (x : Fin (n - 1) × ℤˣ) :
    letterMatrix x *ᵥ twist (strand x.1) =
      (letterCoeff x.2 * T 1) • twist (strandSucc x.1) +
        (1 - letterCoeff x.2 * T 1) • twist (strand x.1) := by
  have hne := strand_ne_strandSucc x.1
  rw [letterMatrix_mulVec, burauRow_dotProduct]
  funext q
  by_cases hq₀ : q = strand x.1
  · subst hq₀
    simp only [twist, Pi.sub_apply, Pi.smul_apply, Pi.add_apply, smul_eq_mul,
      Pi.single_eq_same, Pi.single_eq_of_ne hne.symm, Pi.single_eq_of_ne hne, burauCol_apply,
      ite_true, hne, ite_false, sub_zero, mul_zero]
    ring
  by_cases hq₁ : q = strandSucc x.1
  · subst hq₁
    simp [twist, burauCol_apply, hne.symm]
  simp [twist, burauCol_apply, hq₀, hq₁, Pi.single_apply]

/-- The crossing relation expressing the generator leaving on the upper position. -/
private theorem letterMatrix_mulVec_twist_strandSucc (x : Fin (n - 1) × ℤˣ) :
    letterMatrix x *ᵥ twist (strandSucc x.1) =
      letterCoeff x.2 • twist (strand x.1) + (1 - letterCoeff x.2) • twist (strandSucc x.1) := by
  have hne := strand_ne_strandSucc x.1
  rw [letterMatrix_mulVec, burauRow_dotProduct]
  funext q
  by_cases hq₀ : q = strand x.1
  · subst hq₀
    simp [twist, burauCol_apply, hne]
  by_cases hq₁ : q = strandSucc x.1
  · subst hq₁
    simp [twist, burauCol_apply, hne.symm]
    ring
  simp [twist, burauCol_apply, hq₀, hq₁, Pi.single_apply]

/-! ### The first crossing above a height -/

/-- The first crossing involving the strand position `p` at or above the height `m`, that is,
among the letters numbered `m` or more. -/
private def firstAbove (p : Fin n) (m : ℕ) : Option (Fin w.length) :=
  (w.crossingsAt p).find? fun k ↦ m ≤ (k : ℕ)

private theorem mem_crossingsAt_of_firstAbove_eq_some {p : Fin n} {m : ℕ} {j : Fin w.length}
    (h : w.firstAbove p m = some j) : j ∈ w.crossingsAt p :=
  List.mem_of_find?_eq_some h

private theorem firstAbove_length (p : Fin n) : w.firstAbove p w.length = none := by
  simp [firstAbove, List.find?_eq_none, Fin.is_lt]

private theorem firstAbove_zero_eq_none_iff {p : Fin n} :
    w.firstAbove p 0 = none ↔ w.crossingsAt p = [] := by
  simp [firstAbove, List.find?_eq_none, List.eq_nil_iff_forall_not_mem]

private theorem firstAbove_succ_of_not_mem {p : Fin n} {j : Fin w.length}
    (hj : j ∉ w.crossingsAt p) : w.firstAbove p (j + 1) = w.firstAbove p j := by
  refine List.find?_congr fun k hk ↦ ?_
  have : k ≠ j := fun h ↦ hj (h ▸ hk)
  have : (k : ℕ) ≠ j := fun h ↦ this (Fin.ext h)
  simp only [decide_eq_decide]
  omega

/-- Splitting the crossings along a position at one of them: those before it lie below it, and
those after it lie above it. -/
private theorem exists_crossingsAt_eq_append {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    ∃ l₁ l₂, w.crossingsAt p = l₁ ++ j :: l₂ ∧ (∀ k ∈ l₁, k < j) ∧ ∀ k ∈ l₂, j < k := by
  obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hj
  have hs := List.sortedLT_iff_pairwise.1 (w.sortedLT_crossingsAt p)
  rw [hl, List.pairwise_append, List.pairwise_cons] at hs
  exact ⟨l₁, l₂, hl, fun k hk ↦ hs.2.2 k hk j List.mem_cons_self, hs.2.1.1⟩

private theorem firstAbove_of_mem {p : Fin n} {j : Fin w.length} (hj : j ∈ w.crossingsAt p) :
    w.firstAbove p j = some j := by
  obtain ⟨l₁, l₂, hl, h₁, -⟩ := w.exists_crossingsAt_eq_append hj
  have h₁' : l₁.find? (fun k : Fin w.length ↦ decide ((j : ℕ) ≤ k)) = none :=
    List.find?_eq_none.2 fun k hk ↦ by
      have := Fin.lt_def.1 (h₁ k hk)
      simp only [decide_eq_true_eq]
      omega
  rw [firstAbove, hl, List.find?_append, h₁', Option.none_or,
    List.find?_cons_of_pos (by simp)]

/-- Above a crossing along a position, the first crossing is the next one along it, unless the
crossing is the topmost one; then the next crossing is the lowest one. -/
private theorem firstAbove_succ_of_mem {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.firstAbove p (j + 1) = some (w.nextCrossing p j) ∨
      (w.firstAbove p (j + 1) = none ∧ w.firstAbove p 0 = some (w.nextCrossing p j)) := by
  obtain ⟨l₁, l₂, hl, h₁, h₂⟩ := w.exists_crossingsAt_eq_append hj
  have hnd : (l₁ ++ [j] ++ l₂).Nodup := by
    simpa [hl] using (w.sortedLT_crossingsAt p).nodup
  have hnext : w.nextCrossing p j = (l₂ ++ (l₁ ++ [j])).head (by simp) := by
    have := List.formPerm_append_apply_getLast_left hnd (T := l₁ ++ [j]) (by simp)
    simpa [nextCrossing_def, hl] using this
  have hl₁ : l₁.find? (fun k : Fin w.length ↦ decide ((j : ℕ) + 1 ≤ k)) = none :=
    List.find?_eq_none.2 fun k hk ↦ by
      have := Fin.lt_def.1 (h₁ k hk)
      simp only [decide_eq_true_eq]
      omega
  have hl₂ : l₂.find? (fun k : Fin w.length ↦ decide ((j : ℕ) + 1 ≤ k)) = l₂.head? := by
    cases l₂ with
    | nil => rfl
    | cons a l₂ =>
      have := Fin.lt_def.1 (h₂ a List.mem_cons_self)
      rw [List.find?_cons_of_pos (by simp only [decide_eq_true_eq]; omega), List.head?_cons]
  have hfind : w.firstAbove p (j + 1) = l₂.head? := by
    rw [firstAbove, hl, List.find?_append, hl₁, Option.none_or,
      List.find?_cons_of_neg (by simp), hl₂]
  have hzero : w.firstAbove p 0 = (l₁ ++ j :: l₂).head? := by
    rw [firstAbove, hl]
    cases l₁ <;> simp
  cases l₂ with
  | nil =>
    right
    refine ⟨hfind, ?_⟩
    rw [hzero, hnext, List.head?_eq_some_head (by simp)]
    cases l₁ <;> simp
  | cons a l₂ =>
    left
    rw [hfind, hnext]
    simp

/-! ### The forward map, to the Burau cokernel -/

/-- The relations of the Burau cokernel: the columns of `burau β - 1`. -/
private abbrev burauRelations : Submodule ℤ[T;T⁻¹] (Fin n → ℤ[T;T⁻¹]) :=
  LinearMap.range ((burau n tUnit w.toBraid : Matrix (Fin n) (Fin n) ℤ[T;T⁻¹]) - 1).mulVecLin

/-- The class in the Burau cokernel of the twisted `p`-th column of the Burau matrix of the
first `m` letters: the image of the generator on position `p` at height `m`. -/
private def cokerValue (m : ℕ) (p : Fin n) :
    (Fin n → ℤ[T;T⁻¹]) ⧸ w.burauRelations :=
  w.burauRelations.mkQ (w.prefixMatrix m *ᵥ twist p)

private theorem prefixMatrix_succ_mulVec_twist_of_not_mem {p : Fin n} {j : Fin w.length}
    (hj : j ∉ w.crossingsAt p) :
    w.prefixMatrix (j + 1) *ᵥ twist p = w.prefixMatrix j *ᵥ twist p := by
  rw [mem_crossingsAt, not_or] at hj
  rw [prefixMatrix_succ, ← mulVec_mulVec, letterMatrix_mulVec_twist_of_ne _ hj.1 hj.2]

/-- The height of the first crossing along `p` at or above the height `m`, or the top height if
there is none. -/
private def aboveHeight (p : Fin n) (m : ℕ) : ℕ :=
  ((w.firstAbove p m).map Fin.val).getD w.length

/-- The twisted `p`-th column of the prefix Burau matrices is constant between consecutive
crossings along `p`. -/
private theorem prefixMatrix_mulVec_twist_aboveHeight (p : Fin n) {m : ℕ}
    (hm : m ≤ w.length) :
    w.prefixMatrix m *ᵥ twist p = w.prefixMatrix (w.aboveHeight p m) *ᵥ twist p := by
  induction hm using Nat.decreasingInduction with
  | self => simp [aboveHeight, firstAbove_length]
  | of_succ k hk ih =>
    by_cases hj : (⟨k, hk⟩ : Fin w.length) ∈ w.crossingsAt p
    · simp [aboveHeight, w.firstAbove_of_mem hj]
    · have h := w.firstAbove_succ_of_not_mem hj
      have h' := w.prefixMatrix_succ_mulVec_twist_of_not_mem hj
      simp only at h h'
      rw [← h', ih, aboveHeight, aboveHeight, h]

/-- Closing the braid identifies its top with its bottom. -/
private theorem cokerValue_length (p : Fin n) : w.cokerValue w.length p = w.cokerValue 0 p := by
  rw [cokerValue, cokerValue, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, prefixMatrix_length, prefixMatrix_zero, one_mulVec]
  exact ⟨twist p, by rw [mulVecLin_apply, sub_mulVec, one_mulVec]⟩

private theorem cokerValue_aboveHeight (p : Fin n) {m : ℕ} (hm : m ≤ w.length) :
    w.cokerValue m p = w.cokerValue (w.aboveHeight p m) p := by
  rw [cokerValue, cokerValue, w.prefixMatrix_mulVec_twist_aboveHeight p hm]

/-- The arc leaving a crossing upwards along `p` carries the same value as at the next crossing
along `p`. -/
private theorem cokerValue_succ_eq_nextCrossing {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.cokerValue (j + 1) p = w.cokerValue (w.nextCrossing p j) p := by
  rw [w.cokerValue_aboveHeight p (Nat.succ_le_of_lt j.2), aboveHeight]
  rcases w.firstAbove_succ_of_mem hj with h | ⟨h, h₀⟩
  · rw [h, Option.map_some, Option.getD_some]
  · rw [h, Option.map_none, Option.getD_none, cokerValue_length,
      w.cokerValue_aboveHeight p (Nat.zero_le _), aboveHeight, h₀, Option.map_some,
      Option.getD_some]

/-- The value of a crossing slot: the generator on its strand position, at the height below its
crossing for an incoming slot and above it for an outgoing slot. -/
private def slotValue (x : Fin w.length × Fin 4) : (Fin n → ℤ[T;T⁻¹]) ⧸ w.burauRelations :=
  w.cokerValue (if x.2 = 1 ∨ x.2 = 2 then x.1 + 1 else x.1)
    (if x.2 = 0 ∨ x.2 = 1 then strandSucc w[x.1.1].1 else strand w[x.1.1].1)

private theorem slotValue_incomingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) : w.slotValue (j, w.incomingSlot j p) = w.cokerValue j p := by
  rw [mem_crossingsAt] at hj
  rcases hj with rfl | rfl
  · simp [slotValue, incomingSlot_strand]
  · simp [slotValue, incomingSlot_strandSucc]

private theorem slotValue_outgoingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.slotValue (j, w.outgoingSlot j p) = w.cokerValue (j + 1) p := by
  rw [mem_crossingsAt] at hj
  rcases hj with rfl | rfl
  · simp [slotValue, outgoingSlot_strand]
  · simp [slotValue, outgoingSlot_strandSucc]

/-- The weight of the incoming slot of a crossing on the upper position of its letter. -/
private theorem alexanderWeight_closure_zero (j : Fin w.length) :
    w.closure.alexanderWeight j 0 = letterCoeff w[j.1].2 * T 1 := by
  rw [OrientedPDCode.alexanderWeight_def]
  rcases Int.units_eq_one_or w[j.1].2 with h | h
  · simp [h, letterCoeff]
  · have hT : (T (-1) : ℤ[T;T⁻¹]) * T 1 = 1 := by rw [← T_add]; simp
    simp [h, letterCoeff, hT]

/-- The weight of the incoming slot of a crossing on the lower position of its letter. -/
private theorem alexanderWeight_closure_three (j : Fin w.length) :
    w.closure.alexanderWeight j 3 = letterCoeff w[j.1].2 := by
  rw [OrientedPDCode.alexanderWeight_def]
  rcases Int.units_eq_one_or w[j.1].2 with h | h <;> simp [h, letterCoeff]

/-- The values of the generators of the Alexander module of the closure in the Burau cokernel. -/
private def cokerGen :
    Fin (4 * w.length) ⊕ Fin w.closure.crossinglessComponentCount →
      (Fin n → ℤ[T;T⁻¹]) ⧸ w.burauRelations
  | .inl h => w.slotValue ((crossingSlotEquiv w.length).symm h)
  | .inr c => w.cokerValue 0 (w.crossinglessPosition c)

private theorem cokerGen_inl (x : Fin w.length × Fin 4) :
    w.cokerGen (.inl (crossingSlotEquiv w.length x)) = w.slotValue x := by
  rw [cokerGen, Equiv.symm_apply_apply]

/-- The two ends of an arc of the closure have the same value. -/
private theorem cokerGen_edgePair (h : Fin (4 * w.length)) :
    w.cokerGen (.inl (w.closure.edgePair.val h)) = w.cokerGen (.inl h) := by
  obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv w.length).surjective h
  have hs := w.mem_crossingsAt_strand j
  have hS := w.mem_crossingsAt_strandSucc j
  obtain rfl | rfl | rfl | rfl : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
    fin_cases slot <;> simp
  · rw [edgePair_closure_crossingSlotEquiv_zero, cokerGen_inl, cokerGen_inl,
      w.slotValue_outgoingSlot (w.nextCrossing_symm_mem_crossingsAt_iff.2 hS),
      w.cokerValue_succ_eq_nextCrossing (w.nextCrossing_symm_mem_crossingsAt_iff.2 hS),
      Equiv.apply_symm_apply, ← w.slotValue_incomingSlot hS, incomingSlot_strandSucc]
  · rw [edgePair_closure_crossingSlotEquiv_one, cokerGen_inl, cokerGen_inl,
      w.slotValue_incomingSlot (w.nextCrossing_mem_crossingsAt_iff.2 hS),
      ← w.cokerValue_succ_eq_nextCrossing hS, ← w.slotValue_outgoingSlot hS,
      outgoingSlot_strandSucc]
  · rw [edgePair_closure_crossingSlotEquiv_two, cokerGen_inl, cokerGen_inl,
      w.slotValue_incomingSlot (w.nextCrossing_mem_crossingsAt_iff.2 hs),
      ← w.cokerValue_succ_eq_nextCrossing hs, ← w.slotValue_outgoingSlot hs,
      outgoingSlot_strand]
  · rw [edgePair_closure_crossingSlotEquiv_three, cokerGen_inl, cokerGen_inl,
      w.slotValue_outgoingSlot (w.nextCrossing_symm_mem_crossingsAt_iff.2 hs),
      w.cokerValue_succ_eq_nextCrossing (w.nextCrossing_symm_mem_crossingsAt_iff.2 hs),
      Equiv.apply_symm_apply, ← w.slotValue_incomingSlot hs, incomingSlot_strand]

/-- The crossing relations of the closure hold in the Burau cokernel: the Burau matrix of a
letter is the matrix of the Wirtinger relations of its crossing. -/
private theorem cokerGen_crossing (j : Fin w.length) (slot : Fin 4) :
    w.cokerGen (.inl (w.closure.crossing j (slot + 2))) =
      w.closure.alexanderWeight j slot • w.cokerGen (.inl (w.closure.crossing j slot)) +
        (1 - w.closure.alexanderWeight j slot) •
          w.cokerGen (.inl (w.closure.crossing j (slot + 1))) := by
  refine w.closure.apply_crossing_add_two_of_two_of_one (fun h ↦ w.cokerGen (.inl h)) j ?_ ?_ slot
  · simp only [crossing_closure, cokerGen_inl, alexanderWeight_closure_zero, slotValue,
      cokerValue]
    simp only [Fin.isValue, Fin.reduceEq, or_self, ↓reduceIte, or_false, or_true,
      prefixMatrix_succ, ← mulVec_mulVec, letterMatrix_mulVec_twist_strand, mulVec_add,
      mulVec_smul, map_add, map_smul]
  · simp only [crossing_closure, cokerGen_inl, alexanderWeight_closure_three, slotValue,
      cokerValue]
    simp only [Fin.isValue, Fin.reduceEq, or_self, ↓reduceIte, or_false, or_true,
      prefixMatrix_succ, ← mulVec_mulVec, letterMatrix_mulVec_twist_strandSucc, mulVec_add,
      mulVec_smul, map_add, map_smul]

/-- The forward map: the Wirtinger relations of the closure hold in the Burau cokernel. -/
private def toCoker :
    w.closure.AlexanderModule →ₗ[ℤ[T;T⁻¹]] (Fin n → ℤ[T;T⁻¹]) ⧸ w.burauRelations :=
  w.closure.alexanderLift w.cokerGen w.cokerGen_edgePair w.cokerGen_crossing

private theorem toCoker_inl (x : Fin w.length × Fin 4) :
    w.toCoker (w.closure.alexanderGenerator (.inl (crossingSlotEquiv w.length x))) =
      w.slotValue x := by
  rw [toCoker, OrientedPDCode.alexanderLift_alexanderGenerator, cokerGen_inl]

private theorem toCoker_inr (c : Fin w.closure.crossinglessComponentCount) :
    w.toCoker (w.closure.alexanderGenerator (.inr c)) =
      w.cokerValue 0 (w.crossinglessPosition c) := by
  rw [toCoker, OrientedPDCode.alexanderLift_alexanderGenerator, cokerGen]

/-! ### The inverse map, from the Burau cokernel -/

/-- The generator of the incoming slot of a crossing along `p`. -/
private def inGen (j : Fin w.length) (p : Fin n) : w.closure.AlexanderModule :=
  w.closure.alexanderGenerator (.inl (w.closure.crossing j (w.incomingSlot j p)))

/-- The generator of the outgoing slot of a crossing along `p`. -/
private def outGen (j : Fin w.length) (p : Fin n) : w.closure.AlexanderModule :=
  w.closure.alexanderGenerator (.inl (w.closure.crossing j (w.outgoingSlot j p)))

private theorem outGen_eq_inGen_nextCrossing {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) : w.outGen j p = w.inGen (w.nextCrossing p j) p := by
  rw [outGen, inGen, ← w.edgePair_closure_outgoingSlot hj,
    OrientedPDCode.alexanderGenerator_edgePair]

/-- The generator of the crossing-free circle on a position crossed by no letter. -/
private def crossinglessGen (p : Fin n) : w.closure.AlexanderModule :=
  if h : w.crossingsAt p = [] then w.closure.alexanderGenerator (.inr (w.crossinglessIndex h))
  else 0

/-- The generator on `p` at the bottom of the braid. -/
private def bottomGen (p : Fin n) : w.closure.AlexanderModule :=
  (w.firstAbove p 0).elim (w.crossinglessGen p) fun j ↦ w.inGen j p

/-- The generator on `p` at the height `m`: that of the first crossing along `p` at or above `m`,
or of the bottom of the braid if there is none. -/
private def levelGen (m : ℕ) (p : Fin n) : w.closure.AlexanderModule :=
  (w.firstAbove p m).elim (w.bottomGen p) fun j ↦ w.inGen j p

private theorem levelGen_length (p : Fin n) : w.levelGen w.length p = w.levelGen 0 p := by
  rw [levelGen, firstAbove_length, levelGen, bottomGen]
  cases w.firstAbove p 0 <;> rfl

private theorem levelGen_of_mem {p : Fin n} {j : Fin w.length} (hj : j ∈ w.crossingsAt p) :
    w.levelGen j p = w.inGen j p := by
  rw [levelGen, w.firstAbove_of_mem hj, Option.elim_some]

private theorem levelGen_succ_of_mem {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) : w.levelGen (j + 1) p = w.outGen j p := by
  rw [w.outGen_eq_inGen_nextCrossing hj, levelGen]
  rcases w.firstAbove_succ_of_mem hj with h | ⟨h, h₀⟩
  · rw [h, Option.elim_some]
  · rw [h, Option.elim_none, bottomGen, h₀, Option.elim_some]

private theorem levelGen_succ_of_not_mem {p : Fin n} {j : Fin w.length}
    (hj : j ∉ w.crossingsAt p) : w.levelGen (j + 1) p = w.levelGen j p := by
  rw [levelGen, levelGen, w.firstAbove_succ_of_not_mem hj]

private theorem levelGen_crossing_strand (j : Fin w.length) :
    (letterCoeff w[j.1].2 * T 1) • w.levelGen j (strandSucc w[j.1].1) +
        (1 - letterCoeff w[j.1].2 * T 1) • w.levelGen j (strand w[j.1].1) =
      w.outGen j (strand w[j.1].1) := by
  rw [w.levelGen_of_mem (w.mem_crossingsAt_strandSucc j),
    w.levelGen_of_mem (w.mem_crossingsAt_strand j), ← alexanderWeight_closure_zero, outGen, inGen,
    inGen, outgoingSlot_strand, incomingSlot_strand, incomingSlot_strandSucc]
  exact (w.closure.alexanderGenerator_crossing_two j).symm

private theorem levelGen_crossing_strandSucc (j : Fin w.length) :
    letterCoeff w[j.1].2 • w.levelGen j (strand w[j.1].1) +
        (1 - letterCoeff w[j.1].2) • w.levelGen j (strandSucc w[j.1].1) =
      w.outGen j (strandSucc w[j.1].1) := by
  rw [w.levelGen_of_mem (w.mem_crossingsAt_strand j),
    w.levelGen_of_mem (w.mem_crossingsAt_strandSucc j), ← alexanderWeight_closure_three, outGen,
    inGen, inGen, outgoingSlot_strandSucc, incomingSlot_strand, incomingSlot_strandSucc]
  simpa using (w.closure.alexanderGenerator_crossing_add_two j 3).symm

/-- The inverse map on the free module: the basis vector of `q` goes to `T ^ q` times the
generator on `q` at the bottom of the braid. -/
private def ofFree : (Fin n → ℤ[T;T⁻¹]) →ₗ[ℤ[T;T⁻¹]] w.closure.AlexanderModule :=
  Fintype.linearCombination ℤ[T;T⁻¹] fun q ↦ (T (q : ℤ) : ℤ[T;T⁻¹]) • w.levelGen 0 q

private theorem ofFree_twist (p : Fin n) : w.ofFree (twist p) = w.levelGen 0 p := by
  rw [ofFree, twist, Fintype.linearCombination_apply_single, smul_smul, ← T_add]
  simp

/-- The generator on `p` at the height `m` is the image of the twisted `p`-th column of the
Burau matrix of the first `m` letters. -/
private theorem ofFree_prefixMatrix_mulVec_twist (p : Fin n) {m : ℕ} (hm : m ≤ w.length) :
    w.ofFree (w.prefixMatrix m *ᵥ twist p) = w.levelGen m p := by
  induction m generalizing p with
  | zero => rw [prefixMatrix_zero, one_mulVec, ofFree_twist]
  | succ m ih =>
    have hmL : m < w.length := hm
    let j : Fin w.length := ⟨m, hmL⟩
    have hj : (j : ℕ) = m := rfl
    rw [← hj, prefixMatrix_succ, ← mulVec_mulVec]
    by_cases hp : j ∈ w.crossingsAt p
    · rw [w.levelGen_succ_of_mem hp]
      rcases w.mem_crossingsAt.1 hp with rfl | rfl
      · rw [letterMatrix_mulVec_twist_strand]
        simp only [mulVec_add, mulVec_smul, map_add, map_smul]
        rw [ih _ hmL.le, ih _ hmL.le, ← hj]
        exact w.levelGen_crossing_strand j
      · rw [letterMatrix_mulVec_twist_strandSucc]
        simp only [mulVec_add, mulVec_smul, map_add, map_smul]
        rw [ih _ hmL.le, ih _ hmL.le, ← hj]
        exact w.levelGen_crossing_strandSucc j
    · rw [mem_crossingsAt, not_or] at hp
      rw [letterMatrix_mulVec_twist_of_ne _ hp.1 hp.2, ih _ hmL.le, hj,
        ← w.levelGen_succ_of_not_mem (j := j) (by simpa [not_or] using hp)]

/-- The inverse map: the closing relations `burau β - 1` hold among the bottom generators. -/
private def ofCoker :
    (Fin n → ℤ[T;T⁻¹]) ⧸ w.burauRelations →ₗ[ℤ[T;T⁻¹]] w.closure.AlexanderModule :=
  w.burauRelations.liftQ w.ofFree <| LinearMap.range_le_ker_iff.2 <| by
    ext p
    have h := w.ofFree_prefixMatrix_mulVec_twist p le_rfl
    rw [prefixMatrix_length, levelGen_length, ← w.ofFree_twist p, ← sub_eq_zero, ← map_sub] at h
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_single, mulVecLin_apply,
      LinearMap.zero_comp, LinearMap.zero_apply]
    rw [single_one_eq_smul_twist, mulVec_smul, map_smul, sub_mulVec, one_mulVec, h, smul_zero]

private theorem ofCoker_mk (v : Fin n → ℤ[T;T⁻¹]) :
    w.ofCoker (w.burauRelations.mkQ v) = w.ofFree v :=
  Submodule.liftQ_apply _ _ _

private theorem ofCoker_cokerValue (p : Fin n) {m : ℕ} (hm : m ≤ w.length) :
    w.ofCoker (w.cokerValue m p) = w.levelGen m p := by
  rw [cokerValue, ofCoker_mk, w.ofFree_prefixMatrix_mulVec_twist p hm]

private theorem ofCoker_slotValue_incomingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.ofCoker (w.slotValue (j, w.incomingSlot j p)) =
      w.closure.alexanderGenerator (.inl (crossingSlotEquiv w.length (j, w.incomingSlot j p))) := by
  rw [w.slotValue_incomingSlot hj, w.ofCoker_cokerValue p j.2.le, w.levelGen_of_mem hj, inGen,
    crossing_closure]

private theorem ofCoker_slotValue_outgoingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.ofCoker (w.slotValue (j, w.outgoingSlot j p)) =
      w.closure.alexanderGenerator (.inl (crossingSlotEquiv w.length (j, w.outgoingSlot j p))) := by
  rw [w.slotValue_outgoingSlot hj, w.ofCoker_cokerValue p j.2, w.levelGen_succ_of_mem hj, outGen,
    crossing_closure]

/-- The bottom generator on `q` is sent to the class of `T ^ (-q) • e q`. -/
private theorem toCoker_levelGen_zero (q : Fin n) :
    w.toCoker (w.levelGen 0 q) = w.burauRelations.mkQ (twist q) := by
  rw [levelGen]
  cases h : w.firstAbove q 0 with
  | none =>
    have hq := w.firstAbove_zero_eq_none_iff.1 h
    rw [Option.elim_none, bottomGen, h, Option.elim_none, crossinglessGen,
      dite_eq_left_of_eq_true (eq_true hq), toCoker_inr,
      crossinglessPosition_crossinglessIndex, cokerValue, prefixMatrix_zero, one_mulVec]
  | some j =>
    have hj := w.mem_crossingsAt_of_firstAbove_eq_some h
    have h₀ := w.prefixMatrix_mulVec_twist_aboveHeight q (Nat.zero_le _)
    rw [aboveHeight, h, Option.map_some, Option.getD_some, prefixMatrix_zero, one_mulVec] at h₀
    rw [Option.elim_some, inGen, crossing_closure, toCoker_inl, w.slotValue_incomingSlot hj,
      cokerValue, ← h₀]

/-! ### The isomorphism -/

/-- **The Alexander module of a closed braid is the Burau cokernel.** For a braid word `w` on
`n` strands representing the braid `β`, the Alexander module of the closure of `w` is isomorphic
to the cokernel of `burau β - 1`, the unreduced Burau matrix at `t = T` minus the identity,
acting on column vectors. -/
def closureAlexanderModuleEquiv :
    w.closure.AlexanderModule ≃ₗ[ℤ[T;T⁻¹]] (Fin n → ℤ[T;T⁻¹]) ⧸
      LinearMap.range ((burau n (isUnit_T (R := ℤ) 1).unit w.toBraid :
        Matrix (Fin n) (Fin n) ℤ[T;T⁻¹]) - 1).mulVecLin :=
  LinearEquiv.ofLinearMap w.toCoker w.ofCoker
    (by
      refine Submodule.linearMap_qext _ (LinearMap.pi_ext' fun q ↦ LinearMap.ext_ring ?_)
      simp only [LinearMap.comp_apply, LinearMap.id_apply, LinearMap.coe_single]
      rw [w.ofCoker_mk, single_one_eq_smul_twist, map_smul, ofFree_twist, map_smul,
        toCoker_levelGen_zero, map_smul])
    (by
      refine OrientedPDCode.AlexanderModule.hom_ext _ fun g ↦ ?_
      rw [LinearMap.comp_apply, LinearMap.id_apply]
      rcases g with h | c
      · obtain ⟨⟨j, slot⟩, rfl⟩ := (crossingSlotEquiv w.length).surjective h
        have hs := w.mem_crossingsAt_strand j
        have hS := w.mem_crossingsAt_strandSucc j
        rw [toCoker_inl]
        obtain rfl | rfl | rfl | rfl : slot = 0 ∨ slot = 1 ∨ slot = 2 ∨ slot = 3 := by
          fin_cases slot <;> simp
        · simpa only [incomingSlot_strandSucc] using w.ofCoker_slotValue_incomingSlot hS
        · simpa only [outgoingSlot_strandSucc] using w.ofCoker_slotValue_outgoingSlot hS
        · simpa only [outgoingSlot_strand] using w.ofCoker_slotValue_outgoingSlot hs
        · simpa only [incomingSlot_strand] using w.ofCoker_slotValue_incomingSlot hs
      · have hc := w.crossingsAt_crossinglessPosition c
        rw [toCoker_inr, w.ofCoker_cokerValue _ (Nat.zero_le _), levelGen,
          w.firstAbove_zero_eq_none_iff.2 hc, Option.elim_none, bottomGen,
          w.firstAbove_zero_eq_none_iff.2 hc, Option.elim_none, crossinglessGen,
          dite_eq_left_of_eq_true (eq_true hc)]
        congr 2
        exact w.crossinglessPosition_strictMono.injective
          (w.crossinglessPosition_crossinglessIndex hc))

/-- The generator of the slot at which a strand enters a crossing from below along `p` is sent to
`T ^ (-p)` times the class of the `p`-th column of the Burau matrix of the letters below the
crossing. -/
theorem closureAlexanderModuleEquiv_incomingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.closureAlexanderModuleEquiv
        (w.closure.alexanderGenerator (.inl (w.closure.crossing j (w.incomingSlot j p)))) =
      Submodule.Quotient.mk ((burau n (isUnit_T (R := ℤ) 1).unit (toBraid (w.take j)) :
        Matrix (Fin n) (Fin n) ℤ[T;T⁻¹]) *ᵥ Pi.single p (T (-(p : ℤ)))) := by
  rw [closureAlexanderModuleEquiv, LinearEquiv.coe_ofLinearMap, crossing_closure, toCoker_inl,
    w.slotValue_incomingSlot hj, cokerValue, prefixMatrix, twist, Submodule.mkQ_apply]

/-- The generator of the slot at which a strand leaves a crossing upwards along `p` is sent to
`T ^ (-p)` times the class of the `p`-th column of the Burau matrix of the letters up to and
including the crossing. -/
theorem closureAlexanderModuleEquiv_outgoingSlot {p : Fin n} {j : Fin w.length}
    (hj : j ∈ w.crossingsAt p) :
    w.closureAlexanderModuleEquiv
        (w.closure.alexanderGenerator (.inl (w.closure.crossing j (w.outgoingSlot j p)))) =
      Submodule.Quotient.mk ((burau n (isUnit_T (R := ℤ) 1).unit (toBraid (w.take (j + 1))) :
        Matrix (Fin n) (Fin n) ℤ[T;T⁻¹]) *ᵥ Pi.single p (T (-(p : ℤ)))) := by
  rw [closureAlexanderModuleEquiv, LinearEquiv.coe_ofLinearMap, crossing_closure, toCoker_inl,
    w.slotValue_outgoingSlot hj, cokerValue, prefixMatrix, twist, Submodule.mkQ_apply]

/-- The generator of a crossing-free circle is sent to `T ^ (-p)` times the class of the basis
vector of its strand position `p`. -/
@[simp]
theorem closureAlexanderModuleEquiv_crossinglessGenerator
    (c : Fin w.closure.crossinglessComponentCount) :
    w.closureAlexanderModuleEquiv (w.closure.alexanderGenerator (.inr c)) =
      Submodule.Quotient.mk
        (Pi.single (w.crossinglessPosition c) (T (-(w.crossinglessPosition c : ℤ)))) := by
  rw [closureAlexanderModuleEquiv, LinearEquiv.coe_ofLinearMap, toCoker_inr, cokerValue,
    prefixMatrix_zero, one_mulVec, twist, Submodule.mkQ_apply]

/-- **The elementary ideals of a closed braid are Burau minors.** The `k`-th elementary ideal of
the closure of a braid word on `n` strands is generated by the `(n - k)`-minors of `burau β - 1`,
the unreduced Burau matrix at `t = T` of the represented braid minus the identity. -/
theorem elementaryIdeal_closure (k : ℕ) :
    w.closure.elementaryIdeal k =
      (LinearMap.range ((burau n (isUnit_T (R := ℤ) 1).unit w.toBraid :
        Matrix (Fin n) (Fin n) ℤ[T;T⁻¹]) - 1).mulVecLin).minorsIdeal (n - k) := by
  rw [OrientedPDCode.elementaryIdeal_def, fittingIdeal_congr w.closureAlexanderModuleEquiv,
    fittingIdeal_eq_minorsIdeal_ker (Submodule.mkQ_surjective _), Submodule.ker_mkQ,
    Module.finrank_fin_fun]

end BraidWord

end TauCeti
