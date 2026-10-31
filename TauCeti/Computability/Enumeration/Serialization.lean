/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Code
import TauCeti.Computability.Enumeration.Domain
import TauCeti.Computability.Primrec.FiniteSet

/-!
# Serializing finite-stage enumerations

`TauCeti.Enumeration.serializedStage A` enumerates the union of arbitrary finite stages `A`,
starting empty and adding at most one number per stage. At transition `s → s + 1`, unpair `s`
as `(x, t)` and enumerate `x` if it belongs to `A t`. Repeated discoveries cause pauses.
No decision about whether the limiting set is finite is needed.

The construction preserves the limiting set, with explicit stage comparisons when the original
stages increase. Its binary finite-set codes are computable uniformly in any parameters of the
original enumeration. In particular, applying it to the canonical domain stages gives a uniform
serialized presentation of every c.e. set. Numbers can also encode pairs or tagged entries:
serialization does not change their codes or identify distinct entries.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1–2
  (effective enumerations), and Chapter VII.3 (single-entry enumerations with pauses).
-/

public section

namespace TauCeti.Enumeration

/-- Serialize finite stages by inspecting one pair `(number, original stage)` per transition.
The stages start empty, and repeated discoveries do not add a new entry. -/
def serializedStage (A : ℕ → Finset ℕ) : ℕ → Finset ℕ
  | 0 => ∅
  | s + 1 =>
    if s.unpair.1 ∈ A s.unpair.2 then insert s.unpair.1 (serializedStage A s)
    else serializedStage A s

/-- A serialized enumeration starts empty, including when its source starts nonempty. -/
@[simp]
theorem serializedStage_zero (A : ℕ → Finset ℕ) : serializedStage A 0 = ∅ :=
  (rfl)

/-- The transition tests precisely the pair coded by the preceding stage. -/
theorem serializedStage_succ (A : ℕ → Finset ℕ) (s : ℕ) :
    serializedStage A (s + 1) =
      if s.unpair.1 ∈ A s.unpair.2 then insert s.unpair.1 (serializedStage A s)
      else serializedStage A s :=
  (rfl)

/-- A number has appeared by serialized stage `s` exactly when one of its discovery pairs
has a code smaller than `s`. -/
@[simp]
theorem mem_serializedStage {A : ℕ → Finset ℕ} {s x : ℕ} :
    x ∈ serializedStage A s ↔ ∃ t, Nat.pair x t < s ∧ x ∈ A t := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [serializedStage_succ]
    have hp := Nat.pair_unpair s
    constructor
    · split_ifs with h
      · intro hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨s.unpair.2, by omega, h⟩
        · obtain ⟨t, ht, hx⟩ := ih.mp hx
          exact ⟨t, by omega, hx⟩
      · intro hx
        obtain ⟨t, ht, hx⟩ := ih.mp hx
        exact ⟨t, by omega, hx⟩
    · rintro ⟨t, ht, hx⟩
      by_cases hlt : Nat.pair x t < s
      · have hx' := ih.mpr ⟨t, hlt, hx⟩
        split_ifs <;> simp [hx']
      · have heq : Nat.pair x t = s := by omega
        have hu := congrArg Nat.unpair heq
        simp only [Nat.unpair_pair] at hu
        have hleft := congrArg Prod.fst hu
        have hright := congrArg Prod.snd hu
        simp [← hleft, ← hright, hx]

/-- Serialized stages increase even when the original stages do not. -/
theorem monotone_serializedStage (A : ℕ → Finset ℕ) : Monotone (serializedStage A) := by
  intro s t hst x hx
  obtain ⟨u, hu, hx⟩ := mem_serializedStage.mp hx
  exact mem_serializedStage.mpr ⟨u, hu.trans_le hst, hx⟩

/-- The only possible fresh number at transition `s → s + 1` is the first coordinate of `s`. -/
theorem fresh_serializedStage_subset (A : ℕ → Finset ℕ) (s : ℕ) :
    fresh (serializedStage A) s ⊆ {s.unpair.1} := by
  intro x hx
  obtain ⟨hnew, hold⟩ := mem_fresh.mp hx
  rw [serializedStage_succ] at hnew
  split_ifs at hnew
  · exact Finset.mem_singleton.mpr ((Finset.mem_insert.mp hnew).resolve_right hold)
  · exact (hold hnew).elim

/-- Serialization permits zero or one new entry at each stage. -/
theorem card_fresh_serializedStage_le_one (A : ℕ → Finset ℕ) (s : ℕ) :
    (fresh (serializedStage A) s).card ≤ 1 :=
  (Finset.card_le_card (fresh_serializedStage_subset A s)).trans (by simp)

/-- Every original discovery is present by the stage following the code of its pair. -/
theorem mem_serializedStage_pair_succ {A : ℕ → Finset ℕ} {t x : ℕ} (hx : x ∈ A t) :
    x ∈ serializedStage A (Nat.pair x t + 1) :=
  mem_serializedStage.mpr ⟨t, Nat.lt_succ_self _, hx⟩

/-- Serialization preserves the limiting set, without monotonicity or effectivity assumptions. -/
@[simp]
theorem stageLimit_serializedStage (A : ℕ → Finset ℕ) :
    stageLimit (serializedStage A) = stageLimit A := by
  ext x
  simp only [mem_stageLimit, mem_serializedStage]
  exact ⟨fun ⟨_, t, _, hx⟩ => ⟨t, hx⟩,
    fun ⟨t, hx⟩ => ⟨Nat.pair x t + 1, t, Nat.lt_succ_self _, hx⟩⟩

/-- For increasing source stages, serialization never enumerates a number before it is
present in the source at that stage. -/
theorem serializedStage_subset {A : ℕ → Finset ℕ} (hA : Monotone A) (s : ℕ) :
    serializedStage A s ⊆ A s := by
  intro x hx
  obtain ⟨t, ht, hx⟩ := mem_serializedStage.mp hx
  exact hA ((Nat.right_le_pair x t).trans ht.le) hx

/-- An explicit clock bounding the delay of every entry in a source stage. The clock depends
only on the stage and its binary finite-set code, so it is computable from effective stages. -/
theorem subset_serializedStage (A : ℕ → Finset ℕ) (t : ℕ) :
    A t ⊆ serializedStage A (Nat.pair (Finset.equivBitIndices.symm (A t)) t) := by
  intro x hx
  have hbit : x ∈ (Finset.equivBitIndices.symm (A t)).bitIndices := by
    simpa [Nat.testBit_sum_two_pow] using hx
  have hlt := x.lt_two_pow_self.trans_le (Nat.two_pow_le_of_mem_bitIndices hbit)
  exact mem_serializedStage.mpr ⟨t, Nat.pair_lt_pair_left t hlt, hx⟩

/-- Binary codes of serialized stages are computable, uniformly in all parameters of the
source stages. No monotonicity of the source or infinitude of its limit is required. -/
theorem computable_serializedStage {α : Type*} [Primcodable α]
    {A : α → ℕ → Finset ℕ}
    (hA : Computable fun p : α × ℕ => Finset.equivBitIndices.symm (A p.1 p.2)) :
    Computable fun p : α × ℕ => Finset.equivBitIndices.symm (serializedStage (A p.1) p.2) := by
  have hunpair : Computable fun p : (α × ℕ) × (ℕ × ℕ) => p.2.1.unpair :=
    Primrec.unpair.to_comp.comp (Computable.fst.comp Computable.snd)
  have hcode : Computable fun p : (α × ℕ) × (ℕ × ℕ) =>
      Finset.equivBitIndices.symm (A p.1.1 p.2.1.unpair.2) :=
    hA.comp ((Computable.fst.comp Computable.fst).pair (Computable.snd.comp hunpair))
  have hmem : ComputablePred fun p : (α × ℕ) × (ℕ × ℕ) =>
      p.2.1.unpair.1 ∈ A p.1.1 p.2.1.unpair.2 :=
    (Primrec.mem_equivBitIndices.decide.to_comp.comp
      hcode (Computable.fst.comp hunpair)).computablePred.of_eq fun p => by simp
  have hstep : Computable fun p : (α × ℕ) × (ℕ × ℕ) =>
      if p.2.1.unpair.1 ∈ A p.1.1 p.2.1.unpair.2 then
        p.2.2 ||| 2 ^ p.2.1.unpair.1 else p.2.2 :=
    (Computable.cond hmem.decide
      (Primrec.nat_lor.to_comp.comp (Computable.snd.comp Computable.snd)
        (Primrec.nat_pow.to_comp.comp (Computable.const 2) (Computable.fst.comp hunpair)))
      (Computable.snd.comp Computable.snd)).of_eq fun p => by simp
  refine (Computable.nat_rec Computable.snd (Computable.const 0) hstep.to₂).of_eq ?_
  rintro ⟨a, s⟩
  induction s with
  | zero => simp
  | succ s ih =>
    simp only [ih, serializedStage_succ]
    split_ifs with h
    · apply Finset.equivBitIndices.injective
      rw [Finset.equivBitIndices_lor, Equiv.apply_symm_apply]
      simp [Finset.equivBitIndices_apply, Finset.union_singleton]
    · rfl

/-- The canonical c.e. domain enumeration has uniformly computable serialized stages. -/
theorem computable_serializedStage_domStage :
    Computable fun p : Nat.Partrec.Code × ℕ =>
      Finset.equivBitIndices.symm (serializedStage p.1.domStage p.2) :=
  computable_serializedStage Nat.Partrec.Code.primrec_domStage.to_comp

/-- Every c.e. predicate has an effective increasing finite-stage presentation starting empty
with at most one new entry per stage, and every such presentation has a c.e. limit. -/
theorem rePred_iff_exists_serialized_stages {p : ℕ → Prop} :
    REPred p ↔ ∃ A : ℕ → Finset ℕ, Monotone A ∧ A 0 = ∅ ∧
      (∀ s, (fresh A s).card ≤ 1) ∧
      Computable (fun s => Finset.equivBitIndices.symm (A s)) ∧ stageLimit A = {x | p x} := by
  constructor
  · intro hp
    obtain ⟨c, hc⟩ := rePred_iff_exists_code.mp hp
    refine ⟨serializedStage c.domStage, monotone_serializedStage _, serializedStage_zero _,
      card_fresh_serializedStage_le_one _,
      computable_serializedStage_domStage.comp ((Computable.const c).pair Computable.id), ?_⟩
    rw [stageLimit_serializedStage, Nat.Partrec.Code.stageLimit_domStage]
    ext x
    exact (hc x).symm
  · rintro ⟨A, hmono, hzero, _, hcomp, hlim⟩
    exact rePred_iff_exists_stages.mpr ⟨A, hmono, hzero, hcomp, hlim⟩

end TauCeti.Enumeration
