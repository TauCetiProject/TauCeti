/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Serialization
public import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.Primrec.FiniteSet

/-!
# Removing pauses from serialized enumerations

The cardinality clock of a finite-stage enumeration sends `n` to the first stage containing
at least `n` elements, if there is one. For increasing stages the clock is total precisely
when the limit is infinite. When the source starts empty and has at most one entry per
transition, reading it at the cardinality clock removes pauses without dropping any stage
contents or changing the order of entry.

The partial cardinality search is computable in any oracles that compute the binary stage
codes. Every infinite c.e. set has a computable presentation with exactly one new element
per transition (`exists_unpaused_stages`).

For an empty-start serialized enumeration, `entryAt` returns each element at its unique
discovery position and diverges at positions beyond the entries of a finite limit.
A primitive-recursive compiler turns an ordinary c.e. index into a program for this search.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1.
-/

public section

namespace TauCeti.Enumeration

variable {α : Type*}

/-- The first stage with at least `n` elements, undefined if no stage reaches that size. -/
def stageAtCard (A : ℕ → Finset α) (n : ℕ) : Part ℕ :=
  Nat.rfind fun s => Part.some (decide (n ≤ (A s).card))

/-- The cardinality search succeeds exactly at the least qualifying stage. -/
@[simp]
theorem mem_stageAtCard {A : ℕ → Finset α} {n s : ℕ} :
    s ∈ stageAtCard A n ↔ n ≤ (A s).card ∧ ∀ t < s, (A t).card < n := by
  simpa only [stageAtCard, Part.mem_some_iff, eq_comm (a := true), eq_comm (a := false),
    decide_eq_true_eq, decide_eq_false_iff_not, not_le]
    using (@Nat.mem_rfind (fun t => Part.some (decide (n ≤ (A t).card))) s)

/-- A cardinality bound is reached exactly when the corresponding search halts. -/
@[simp]
theorem stageAtCard_dom {A : ℕ → Finset α} {n : ℕ} :
    (stageAtCard A n).Dom ↔ ∃ s, n ≤ (A s).card := by
  simpa only [stageAtCard, Part.mem_some_iff, decide_eq_true_eq, Part.some_dom, implies_true,
    and_true, eq_comm (a := true)]
    using (@Nat.rfind_dom (fun s => Part.some (decide (n ≤ (A s).card))))

/-- An increasing enumeration with infinite limit has a total cardinality clock. -/
def cardClock (A : ℕ → Finset α) (hA : Monotone A) (hInf : (stageLimit A).Infinite)
    (n : ℕ) : ℕ :=
  Nat.find ((stageLimit_infinite_iff hA).mp hInf n)

/-- The total cardinality clock gives the result of the partial search. -/
theorem cardClock_mem_stageAtCard {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) (n : ℕ) : cardClock A hA hInf n ∈ stageAtCard A n := by
  rw [mem_stageAtCard, cardClock]
  let H := (stageLimit_infinite_iff hA).mp hInf n
  exact ⟨Nat.find_spec H, fun _ ht => Nat.lt_of_not_ge (Nat.find_min H ht)⟩

/-- By stage `s` the cardinality clock for `n` has rung exactly when the source has at least
`n` elements. -/
theorem cardClock_le_iff {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) {n s : ℕ} :
    cardClock A hA hInf n ≤ s ↔ n ≤ (A s).card := by
  have h := mem_stageAtCard.mp (cardClock_mem_stageAtCard hA hInf n)
  exact ⟨fun hs => h.1.trans (Finset.card_le_card (hA hs)),
    fun hs => Nat.le_of_not_gt fun ht => (Nat.not_lt_of_ge hs) (h.2 s ht)⟩

/-- The search for zero elements stops at the first stage. -/
@[simp]
theorem cardClock_zero {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) : cardClock A hA hInf 0 = 0 :=
  Nat.le_zero.mp ((cardClock_le_iff hA hInf).mpr (Nat.zero_le _))

/-- The cardinality clock is nondecreasing in the requested size. -/
theorem monotone_cardClock {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) : Monotone (cardClock A hA hInf) :=
  fun _ n h => (cardClock_le_iff hA hInf).mpr
    (h.trans (mem_stageAtCard.mp (cardClock_mem_stageAtCard hA hInf n)).1)

/-- The first stage at or above a requested size has exactly that size when the
enumeration starts empty and adds at most one element per transition. -/
theorem card_stage_eq_of_mem_stageAtCard [DecidableEq α] {A : ℕ → Finset α}
    (hzero : A 0 = ∅) (hstep : ∀ s, (fresh A s).card ≤ 1)
    {n s : ℕ} (hs : s ∈ stageAtCard A n) : (A s).card = n := by
  obtain ⟨hcard, hmin⟩ := mem_stageAtCard.mp hs
  cases s with
  | zero =>
    simp [hzero] at hcard
    simp [hzero, hcard]
  | succ s =>
    have h := Finset.card_le_card_sdiff_add_card (s := A (s + 1)) (t := A s)
    rw [← fresh_eq_sdiff] at h
    have hle := hstep s
    have hlt := hmin s (Nat.lt_succ_self s)
    omega

/-- Read an increasing enumeration at the first stage reaching each cardinality. For an
empty-start serialized source with infinite limit, this removes exactly the pauses. -/
def unpausedStage (A : ℕ → Finset α) (hA : Monotone A) (hInf : (stageLimit A).Infinite)
    (n : ℕ) : Finset α :=
  A (cardClock A hA hInf n)

/-- The unpaused stage is the source at its cardinality clock. -/
theorem unpausedStage_def {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) (n : ℕ) :
    unpausedStage A hA hInf n = A (cardClock A hA hInf n) :=
  (rfl)

/-- Removing pauses preserves the initial stage. -/
@[simp]
theorem unpausedStage_zero {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) : unpausedStage A hA hInf 0 = A 0 := by
  rw [unpausedStage_def, cardClock_zero]

/-- Removing pauses preserves monotonicity. -/
theorem monotone_unpausedStage {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) : Monotone (unpausedStage A hA hInf) :=
  hA.comp (monotone_cardClock hA hInf)

/-- At unpaused stage `n` exactly `n` elements have entered. -/
theorem card_unpausedStage [DecidableEq α] {A : ℕ → Finset α} (hA : Monotone A)
    (hzero : A 0 = ∅) (hstep : ∀ s, (fresh A s).card ≤ 1)
    (hInf : (stageLimit A).Infinite) (n : ℕ) : (unpausedStage A hA hInf n).card = n :=
  card_stage_eq_of_mem_stageAtCard hzero hstep (cardClock_mem_stageAtCard hA hInf n)

/-- The unpaused enumeration adds exactly one element at each transition. -/
theorem card_fresh_unpausedStage [DecidableEq α] {A : ℕ → Finset α} (hA : Monotone A)
    (hzero : A 0 = ∅) (hstep : ∀ s, (fresh A s).card ≤ 1)
    (hInf : (stageLimit A).Infinite) (n : ℕ) : (fresh (unpausedStage A hA hInf) n).card = 1 := by
  have h := card_fresh_add_card (monotone_unpausedStage hA hInf (Nat.le_succ n))
  rw [card_unpausedStage hA hzero hstep, card_unpausedStage hA hzero hstep] at h
  omega

/-- The cardinality of a source stage gives the stage with identical contents in the
unpaused enumeration. This comparison does not require a single-entry source. -/
theorem unpausedStage_card {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) (s : ℕ) :
    unpausedStage A hA hInf (A s).card = A s := by
  rw [unpausedStage_def]
  apply Finset.eq_of_subset_of_card_le (hA ((cardClock_le_iff hA hInf).mpr le_rfl))
  exact (mem_stageAtCard.mp (cardClock_mem_stageAtCard hA hInf _)).1

/-- A cardinality clock retains every source stage's contents, and thus its limit. -/
@[simp]
theorem stageLimit_unpausedStage {A : ℕ → Finset α} (hA : Monotone A)
    (hInf : (stageLimit A).Infinite) : stageLimit (unpausedStage A hA hInf) = stageLimit A := by
  ext x
  simp only [mem_stageLimit]
  exact ⟨fun ⟨n, hn⟩ => ⟨cardClock A hA hInf n, hn⟩,
    fun ⟨s, hs⟩ => ⟨(A s).card, by rwa [unpausedStage_card]⟩⟩

/-- The binary code of the fresh entries is computable in any oracles that compute the stage
codes. -/
theorem computableIn_equivBitIndices_symm_fresh {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s)) :
    ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (fresh (A i) s) := by
  have hnext := hA.comp (ComputableIn.fst.pair (ComputableIn.succ.comp ComputableIn.snd))
  refine (Primrec.nat_ldiff.computableIn.comp (hnext.pair hA)).of_eq fun ⟨i, s⟩ => ?_
  simp only [Part.some_inj, Nat.succ_eq_add_one]
  apply Finset.equivBitIndices.injective
  -- The primitive-recursive operation and the decoder lemma use the same bitwise difference.
  exact (Finset.equivBitIndices_ldiff _ _).trans (by simp [fresh_eq_sdiff])

/-- A family of cardinality tests is computable relative to the stage codes. -/
private theorem computableIn_cardTest {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s)) :
    ComputableIn₂ O fun (p : ι × ℕ) s => decide (p.2 ≤ (A p.1 s).card) := by
  have hcard : ComputableIn O fun q : (ι × ℕ) × ℕ =>
      (Finset.equivBitIndices (Finset.equivBitIndices.symm (A q.1.1 q.2))).card :=
    Primrec.card_equivBitIndices.computableIn.comp
      (hA.comp ((ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd))
  exact (Primrec.nat_le.decide.computableIn.comp
    ((ComputableIn.snd.comp ComputableIn.fst).pair hcard)).of_eq fun _ => by simp

/-- The partial cardinality search is uniform in the source parameter and the size being
searched for. The search needs neither monotonicity nor infinitude. -/
theorem recursiveIn_stageAtCard {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s)) :
    RecursiveIn₂ O fun i n => stageAtCard (A i) n :=
  RecursiveIn.rfind (computableIn_cardTest hA).recursiveIn₂

/-- The total cardinality clock is uniformly computable relative to the source stages,
provided each of their limits is infinite. -/
theorem computableIn_cardClock {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s))
    (hm : ∀ i, Monotone (A i)) (hi : ∀ i, (stageLimit (A i)).Infinite) :
    ComputableIn₂ O fun i n => cardClock (A i) (hm i) (hi i) n :=
  ComputableIn.find (computableIn_cardTest hA)
    fun p => (stageLimit_infinite_iff (hm p.1)).mp (hi p.1) p.2

/-- Reading effective stages at their cardinality clocks is uniformly computable in the
same oracles. -/
theorem computableIn_unpausedStage {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s))
    (hm : ∀ i, Monotone (A i)) (hi : ∀ i, (stageLimit (A i)).Infinite) :
    ComputableIn₂ O fun i n => Finset.equivBitIndices.symm (unpausedStage (A i) (hm i) (hi i) n) :=
  hA.comp (ComputableIn.fst.pair (computableIn_cardClock hA hm hi))

/-- The entry at position `n` (counted from zero) of an empty-start serialized enumeration.
Wait for an entry at a transition with exactly `n` elements already present. -/
def entryAt (A : ℕ → Finset ℕ) (n : ℕ) : Part ℕ :=
  Nat.rfindOpt fun s =>
    if (A s).card = n then
      Nat.leastBitIndex (Finset.equivBitIndices.symm (fresh A s))
    else none

/-- At a transition containing at most one new element, the least new element is exactly
the element that enters, if any. -/
private theorem leastBitIndex_fresh_eq_some {A : ℕ → Finset ℕ} {s x : ℕ}
    (hstep : (fresh A s).card ≤ 1) :
    Nat.leastBitIndex (Finset.equivBitIndices.symm (fresh A s)) = some x ↔ x ∈ fresh A s := by
  rw [Nat.leastBitIndex_eq_some_iff, Equiv.apply_symm_apply]
  exact ⟨And.left, fun hx => ⟨hx, fun _ hy => (Finset.card_le_one_iff.mp hstep hx hy).le⟩⟩

/-- An entry is the `n`th discovery exactly when it enters with `n` elements already
present. A transition can have an empty fresh set, in which case the search continues. -/
theorem mem_entryAt {A : ℕ → Finset ℕ} (hA : Monotone A)
    (hstep : ∀ s, (fresh A s).card ≤ 1) {n x : ℕ} :
    x ∈ entryAt A n ↔ ∃ s, (A s).card = n ∧ x ∈ fresh A s := by
  let candidate (s : ℕ) :=
    if (A s).card = n then Nat.leastBitIndex (Finset.equivBitIndices.symm (fresh A s)) else none
  have hc (s y : ℕ) : y ∈ candidate s ↔ (A s).card = n ∧ y ∈ fresh A s := by
    by_cases h : (A s).card = n
    · simp only [candidate, h, ite_eq_left, Option.mem_def, leastBitIndex_fresh_eq_some (hstep s),
        true_and]
    · simp [candidate, h]
  constructor
  · intro hx
    obtain ⟨s, hs⟩ := Nat.rfindOpt_spec hx
    exact ⟨s, (hc s x).mp hs⟩
  · rintro ⟨s, hs, hx⟩
    obtain ⟨y, hy⟩ := Part.dom_iff_mem.mp
      (Nat.rfindOpt_dom.mpr ⟨s, x, (hc s x).mpr ⟨hs, hx⟩⟩)
    obtain ⟨t, ht⟩ := Nat.rfindOpt_spec hy
    obtain ⟨ht, hyt⟩ := (hc t y).mp ht
    have card_lt_of_earlier_entry {i j z : ℕ} (hij : i < j) (hz : z ∈ fresh A i) :
        (A i).card < (A j).card := by
      obtain ⟨hnew, hold⟩ := mem_fresh.mp hz
      exact Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr
        ⟨hA hij.le, fun he => hold (he ▸ hA hij hnew)⟩)
    have sameStage : s = t := by
      rcases lt_trichotomy s t with h | h | h
      · exact (Nat.ne_of_lt (card_lt_of_earlier_entry h hx) (hs.trans ht.symm)).elim
      · exact h
      · exact (Nat.ne_of_lt (card_lt_of_earlier_entry h hyt) (ht.trans hs.symm)).elim
    subst t
    have hyx := Option.some.inj
      (((leastBitIndex_fresh_eq_some (hstep s)).mpr hyt).symm.trans
        ((leastBitIndex_fresh_eq_some (hstep s)).mpr hx))
    exact hyx ▸ hy

/-- The search for entry `n` halts exactly when the source reaches a size greater than
`n`. In particular, there is no result at or above the size of a finite limit. -/
theorem entryAt_dom {A : ℕ → Finset ℕ} (hA : Monotone A) (hzero : A 0 = ∅)
    (hstep : ∀ s, (fresh A s).card ≤ 1) (n : ℕ) :
    (entryAt A n).Dom ↔ ∃ s, n < (A s).card := by
  constructor
  · intro h
    obtain ⟨x, hx⟩ := Part.dom_iff_mem.mp h
    obtain ⟨s, hcard, hs⟩ := (mem_entryAt hA hstep).mp hx
    have hadd := card_fresh_add_card (hA (Nat.le_succ s))
    have hpos := Finset.card_pos.mpr ⟨x, hs⟩
    exact ⟨s + 1, by omega⟩
  · intro h
    obtain ⟨t, ht⟩ := Part.dom_iff_mem.mp (stageAtCard_dom.mpr h)
    cases t with
    | zero =>
      have hcard := (mem_stageAtCard.mp ht).1
      simp [hzero] at hcard
    | succ s =>
      have hnew := card_stage_eq_of_mem_stageAtCard hzero hstep ht
      have hold := (mem_stageAtCard.mp ht).2 s (Nat.lt_succ_self s)
      have hadd := card_fresh_add_card (hA (Nat.le_succ s))
      have hle := hstep s
      have hpos : 0 < (fresh A s).card := by omega
      obtain ⟨x, hx⟩ := Finset.card_pos.mp hpos
      exact ((mem_entryAt hA hstep).mpr ⟨s, by omega, hx⟩).fst

/-- Each member of the limit is returned by the entry search at its unique position. -/
theorem existsUnique_mem_entryAt_iff {A : ℕ → Finset ℕ} (hA : Monotone A) (hzero : A 0 = ∅)
    (hstep : ∀ s, (fresh A s).card ≤ 1) {x : ℕ} :
    (∃! n, x ∈ entryAt A n) ↔ x ∈ stageLimit A := by
  constructor
  · rintro ⟨n, hn, _⟩
    obtain ⟨s, _, hs⟩ := (mem_entryAt hA hstep).mp hn
    exact mem_stageLimit_of_mem_fresh hs
  · intro hx
    obtain ⟨s, hs⟩ := exists_mem_fresh_of_mem_stageLimit hx (by simp [hzero])
    refine ⟨(A s).card, (mem_entryAt hA hstep).mpr ⟨s, rfl, hs⟩, ?_⟩
    intro n hn
    obtain ⟨t, ht, hxt⟩ := (mem_entryAt hA hstep).mp hn
    rw [unique_entry_stage hA hxt hs] at ht
    exact ht.symm

/-- Searching for the `n`th entry is relatively computable, uniformly in the cardinality
and the source parameter. Termination is governed by `entryAt_dom`. -/
theorem recursiveIn_entryAt {ι : Type*} [Primcodable ι] {O : Set (ℕ →. ℕ)}
    {A : ι → ℕ → Finset ℕ}
    (hA : ComputableIn₂ O fun i s => Finset.equivBitIndices.symm (A i s)) :
    RecursiveIn₂ O fun i n => entryAt (A i) n := by
  have hargs : ComputableIn O fun q : (ι × ℕ) × ℕ => (q.1.1, q.2) :=
    (ComputableIn.fst.comp ComputableIn.fst).pair ComputableIn.snd
  have hcard : ComputableIn O fun q : (ι × ℕ) × ℕ => (A q.1.1 q.2).card :=
    (Primrec.card_equivBitIndices.computableIn.comp (hA.comp hargs)).of_eq fun _ => by simp
  have hmin := Primrec.nat_leastBitIndex.computableIn.comp
    ((computableIn_equivBitIndices_symm_fresh hA).comp hargs)
  have hselect :=
    (Primrec.cond Primrec.fst Primrec.snd (Primrec.const (none : Option ℕ))).computableIn (O := O)
  exact RecursiveIn.rfindOpt ((hselect.comp
    ((Primrec.eq.decide.computableIn.comp
      (hcard.pair (ComputableIn.snd.comp ComputableIn.fst))).pair hmin)).of_eq fun _ => by
        simp [Bool.cond_eq_ite])

/-- A successful entry search identifies the one new element at the corresponding
unpaused transition. -/
theorem fresh_unpausedStage_eq_singleton {A : ℕ → Finset ℕ} (hA : Monotone A)
    (hstep : ∀ s, (fresh A s).card ≤ 1) (hInf : (stageLimit A).Infinite)
    {n x : ℕ} (hx : x ∈ entryAt A n) : fresh (unpausedStage A hA hInf) n = {x} := by
  obtain ⟨s, hs, hx⟩ := (mem_entryAt hA hstep).mp hx
  have hfresh : fresh A s = {x} :=
    Finset.eq_singleton_iff_unique_mem.mpr
      ⟨hx, fun _ hy => Finset.card_le_one_iff.mp (hstep s) hy hx⟩
  have hnext := card_fresh_add_card (hA (Nat.le_succ s))
  rw [hfresh, Finset.card_singleton, hs, Nat.add_comm] at hnext
  have hnow : unpausedStage A hA hInf n = A s := hs ▸ unpausedStage_card hA hInf s
  have hlater : unpausedStage A hA hInf (n + 1) = A (s + 1) :=
    hnext ▸ unpausedStage_card hA hInf (s + 1)
  rw [fresh_eq_sdiff, hnow, hlater, ← fresh_eq_sdiff, hfresh]

/-- Every infinite c.e. subset of the naturals has computable increasing stages starting
empty with exactly one entry at each transition. -/
theorem exists_unpaused_stages {S : Set ℕ} (hS : REPred (· ∈ S)) (hinf : S.Infinite) :
    ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧ (∀ s, (fresh A s).card = 1) ∧
      Computable (fun s => Finset.equivBitIndices.symm (A s)) ∧ stageLimit A = S := by
  obtain ⟨A, hmono, hzero, hstep, hcomp, hlim⟩ := rePred_iff_exists_serialized_stages.mp hS
  have hInf : (stageLimit A).Infinite := hlim ▸ hinf
  have hcomp₂ : Computable₂ (fun (_ : Unit) s => Finset.equivBitIndices.symm (A s)) :=
    hcomp.comp₂ Computable.snd
  have heff := computableIn₂_empty_iff.mp
    (computableIn_unpausedStage (A := fun _ : Unit => A) hcomp₂.computableIn
      (fun _ => hmono) (fun _ => hInf))
  exact ⟨unpausedStage A hmono hInf, monotone_unpausedStage hmono hInf,
    (unpausedStage_zero hmono hInf).trans hzero, card_fresh_unpausedStage hmono hzero hstep hInf,
    heff.comp (Computable.const ()) Computable.id, (stageLimit_unpausedStage hmono hInf).trans hlim⟩

/-- An ordinary c.e. index can be compiled into a program that returns the entries of
its serialized domain in discovery order, diverging beyond the last entry if finite.
The index transformation is primitive recursive. -/
theorem exists_primrec_eval_entryAt_serializedStage :
    ∃ compile : Nat.Partrec.Code → Nat.Partrec.Code, Primrec compile ∧
      ∀ c n, (compile c).eval n = entryAt (serializedStage c.domStage) n := by
  have hrec := TauCeti.recursiveIn₂_empty_iff.mp
    (recursiveIn_entryAt (A := fun c : Nat.Partrec.Code => serializedStage c.domStage)
      computable_serializedStage_domStage.computableIn)
  have hnat : Nat.Partrec fun m =>
      entryAt (serializedStage (Denumerable.ofNat Nat.Partrec.Code m.unpair.1).domStage)
        m.unpair.2 :=
    Partrec.nat_iff.mp (hrec.comp ((Primrec.ofNat Nat.Partrec.Code).to_comp.comp
      (Computable.fst.comp Computable.unpair)) (Computable.snd.comp Computable.unpair))
  obtain ⟨u, hu⟩ := Nat.Partrec.Code.exists_code.mp hnat
  refine ⟨fun c => u.curry (Encodable.encode c),
    Nat.Partrec.Code.primrec₂_curry.comp (Primrec.const u) Primrec.encode, fun c n => ?_⟩
  rw [Nat.Partrec.Code.eval_curry, hu]
  simp

end TauCeti.Enumeration
