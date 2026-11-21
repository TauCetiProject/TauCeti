/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.FiniteSet
public import TauCeti.Computability.Primrec.List
public import TauCeti.Computability.Priority.Injury.Basic

/-!
# The finite routing transition for Sacks splitting

Requirements are ordered by `2 * e + i`, where the parity `i` is the side they protect.
A finite list records the current numerical restraints; every unrecorded restraint is zero.
Route each fresh number to the side opposite the least requirement it threatens, using the
inclusive test `x ≤ r`. If nothing is threatened, route to side zero.

The search includes the first unrecorded requirement. This is necessary for zero: even an
unrecorded restraint protects zero. Positive numbers threaten only recorded requirements.
The transition handles a whole finite batch against the same current restraints, rather than
recalculating restraints after routing each element. It preserves disjointness and covers exactly
the old union together with the batch. The injury attribution theorem identifies a strictly
higher-priority requirement on the opposite side for each entry that breaches a live restraint.

Binary finite-set codes make the routing and the whole transition primitive recursive. These
are the finite algorithms used to split a c.e. enumeration; no decidability of its limit is used.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987,
  Theorem VII.3.2, the routing rule on p. 125.
-/

public section

namespace TauCeti.SacksSplitting

/-- The least threatened priority, searching also the first implicit zero restraint. -/
def leastThreat (r : List ℕ) (x : ℕ) : Option ℕ :=
  (List.range (r.length + 1)).find? fun k => x ≤ r[k]?.getD 0

/-- The finite search returns exactly the least threatened priority in its search interval. -/
@[simp] theorem leastThreat_eq_some_iff {r : List ℕ} {x k : ℕ} :
    leastThreat r x = some k ↔
      x ≤ r[k]?.getD 0 ∧ k ≤ r.length ∧ ∀ j < k, r[j]?.getD 0 < x := by
  simp [leastThreat, List.find?_range_eq_some]

/-- A threatening priority is in the search interval, unless the input is zero. -/
private theorem threat_in_search {r : List ℕ} {x k : ℕ} (h : x ≤ r[k]?.getD 0) :
    ∃ j ≤ r.length, j ≤ k ∧ x ≤ r[j]?.getD 0 := by
  by_cases hk : k ≤ r.length
  · exact ⟨k, hk, le_rfl, h⟩
  · have hk' : r.length ≤ k := by omega
    have hz : x = 0 := by simpa [List.getElem?_eq_none hk'] using h
    exact ⟨0, Nat.zero_le _, Nat.zero_le _, by simp [hz]⟩

/-- Failure means that no priority, including the implicit zero restraints, is threatened. -/
@[simp] theorem leastThreat_eq_none_iff {r : List ℕ} {x : ℕ} :
    leastThreat r x = none ↔ ∀ k : ℕ, r[k]?.getD 0 < x := by
  simp only [leastThreat, List.find?_eq_none, List.mem_range, decide_eq_true_eq,
    not_le]
  constructor
  · intro h k
    by_contra hk
    obtain ⟨j, hj, -, hxj⟩ := threat_in_search (Nat.le_of_not_gt hk)
    exact (h j (by omega)).not_ge hxj
  · intro h k _; exact h k

/-- The least threatened priority is at most any threatened priority, recorded or not. -/
theorem exists_leastThreat_le {r : List ℕ} {x k : ℕ} (h : x ≤ r[k]?.getD 0) :
    ∃ j ≤ k, leastThreat r x = some j := by
  cases hj : leastThreat r x with
  | none => exact False.elim ((leastThreat_eq_none_iff.1 hj k).not_ge h)
  | some j =>
    refine ⟨j, ?_, rfl⟩
    by_contra hle
    exact (leastThreat_eq_some_iff.1 hj).2.2 k (by omega) |>.not_ge h

/-- The destination side: opposite the least threatened priority, or side zero if none. -/
def route (r : List ℕ) (x : ℕ) : Bool :=
  ((leastThreat r x).map fun k => !k.bodd).getD false

/-- No threatened requirement means that the entry goes to side zero. -/
theorem route_of_leastThreat_eq_none {r : List ℕ} {x : ℕ} (h : leastThreat r x = none) :
    route r x = false := by simp [route, h]

/-- A threatened requirement sends the entry to its opposite side. -/
theorem route_of_leastThreat_eq_some {r : List ℕ} {x k : ℕ}
    (h : leastThreat r x = some k) : route r x = !k.bodd := by simp [route, h]

/-- Every threatened requirement injured by the destination has a strictly higher-priority
threatened requirement on the other side. This includes the boundary `x = r[k]`. -/
theorem exists_higher_priority_of_route_eq {r : List ℕ} {x k : ℕ}
    (hx : x ≤ r[k]?.getD 0) (hside : route r x = k.bodd) :
    ∃ j < k, x ≤ r[j]?.getD 0 ∧ j.bodd = !k.bodd := by
  obtain ⟨j, hjk, hj⟩ := exists_leastThreat_le hx
  have hs := (route_of_leastThreat_eq_some hj).symm.trans hside
  have hne : j ≠ k := by intro h; subst j; cases k.bodd <;> simp_all
  refine ⟨j, lt_of_le_of_ne hjk hne, (leastThreat_eq_some_iff.1 hj).1, ?_⟩
  cases hjb : j.bodd <;> cases hkb : k.bodd <;> simp_all

/-- The part of a batch routed to side `b`, using the pre-transition restraints. -/
def routedBatch (r : List ℕ) (D : Finset ℕ) (b : Bool) : Finset ℕ :=
  D.filter fun x => route r x = b

/-- Membership in a routed batch. -/
@[simp] theorem mem_routedBatch {r : List ℕ} {D : Finset ℕ} {b : Bool} {x : ℕ} :
    x ∈ routedBatch r D b ↔ x ∈ D ∧ route r x = b := by simp [routedBatch]

/-- The two routed batches are disjoint. -/
theorem disjoint_routedBatch (r : List ℕ) (D : Finset ℕ) :
    Disjoint (routedBatch r D false) (routedBatch r D true) := by
  simp only [Finset.disjoint_left, mem_routedBatch]
  grind

/-- Every element of the batch goes to exactly one side. -/
@[simp] theorem routedBatch_union (r : List ℕ) (D : Finset ℕ) :
    routedBatch r D false ∪ routedBatch r D true = D := by
  ext x
  cases h : route r x <;> simp [h]

/-- One batched transition. Already assigned numbers are ignored, so old assignments never
change, even if the supplied batch contains repetitions from earlier stages. -/
def step (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) : Finset ℕ × Finset ℕ :=
  let fresh := D \ (A.1 ∪ A.2)
  (A.1 ∪ routedBatch r fresh false, A.2 ∪ routedBatch r fresh true)

/-- The equations specifying both output halves of a transition. -/
theorem step_def (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    step r A D = (A.1 ∪ routedBatch r (D \ (A.1 ∪ A.2)) false,
      A.2 ∪ routedBatch r (D \ (A.1 ∪ A.2)) true) := (rfl)

/-- The first output half retains its old entries and adds the fresh entries routed to it. -/
@[simp] theorem step_fst (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    (step r A D).1 = A.1 ∪ routedBatch r (D \ (A.1 ∪ A.2)) false := by
  rw [step_def]

/-- The second output half retains its old entries and adds the fresh entries routed to it. -/
@[simp] theorem step_snd (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    (step r A D).2 = A.2 ∪ routedBatch r (D \ (A.1 ∪ A.2)) true := by
  rw [step_def]

/-- An entry in the first output half is old or fresh and routed to side zero. -/
theorem mem_step_fst_iff {r : List ℕ} {A : Finset ℕ × Finset ℕ} {D : Finset ℕ} {x : ℕ} :
    x ∈ (step r A D).1 ↔ x ∈ A.1 ∨
      (x ∈ D ∧ x ∉ A.1 ∪ A.2 ∧ route r x = false) := by
  simp only [step_fst, Finset.mem_union, mem_routedBatch, Finset.mem_sdiff]
  tauto

/-- An entry in the second output half is old or fresh and routed to side one. -/
theorem mem_step_snd_iff {r : List ℕ} {A : Finset ℕ × Finset ℕ} {D : Finset ℕ} {x : ℕ} :
    x ∈ (step r A D).2 ↔ x ∈ A.2 ∨
      (x ∈ D ∧ x ∉ A.1 ∪ A.2 ∧ route r x = true) := by
  simp only [step_snd, Finset.mem_union, mem_routedBatch, Finset.mem_sdiff]
  tauto

/-- The first half never loses an entry. -/
theorem subset_step_fst (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    A.1 ⊆ (step r A D).1 := by
  rw [step_def]
  exact Finset.subset_union_left

/-- The second half never loses an entry. -/
theorem subset_step_snd (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    A.2 ⊆ (step r A D).2 := by
  rw [step_def]
  exact Finset.subset_union_left

/-- A transition preserves disjointness without any single-entry assumption on the batch. -/
theorem disjoint_step {r : List ℕ} {A : Finset ℕ × Finset ℕ} {D : Finset ℕ}
    (h : Disjoint A.1 A.2) : Disjoint (step r A D).1 (step r A D).2 := by
  rw [step_def]
  simp only [Finset.disjoint_left, mem_routedBatch, Finset.mem_union, Finset.mem_sdiff] at h ⊢
  aesop

/-- The union after a transition is exactly the old union together with the supplied batch. -/
-- Simplify the combined union before the projection lemmas expand its halves.
@[simp↓] theorem step_union (r : List ℕ) (A : Finset ℕ × Finset ℕ) (D : Finset ℕ) :
    (step r A D).1 ∪ (step r A D).2 = A.1 ∪ A.2 ∪ D := by
  rw [step_def]
  ext x
  cases hx : route r x <;> simp [hx] <;> tauto

/-! ### Injury attribution and finite injury -/

open Priority Enumeration

/-- For stages related by a routing transition, each actual injury on side `k.bodd` is caused
by a threatened priority strictly below `k` on the opposite side. -/
theorem exists_higher_priority_of_mem_injuriesAt
    {A : Bool → ℕ → Finset ℕ} {r : ℕ → List ℕ} {D : ℕ → Finset ℕ} {s k x : ℕ}
    (hstep : step (r s) (A false s, A true s) (D s) =
      (A false (s + 1), A true (s + 1)))
    (hx : x ∈ injuriesAt (A k.bodd) (fun j t => some ((r t)[j]?.getD 0)) k s) :
    ∃ j < k, x ≤ (r s)[j]?.getD 0 ∧ j.bodd = !k.bodd := by
  obtain ⟨hx₁, hx₀, b, hb, hxb⟩ := mem_injuriesAt.1 hx
  have hb' : (r s)[k]?.getD 0 = b := Option.some.inj hb
  apply exists_higher_priority_of_route_eq (hxb.trans_eq hb'.symm)
  have hfirst := congrArg Prod.fst hstep
  have hsecond := congrArg Prod.snd hstep
  simp only at hfirst hsecond
  cases hk : k.bodd
  · rw [hk] at hx₀
    rw [hk, ← hfirst, mem_step_fst_iff] at hx₁
    exact (hx₁.resolve_left hx₀).2.2
  · rw [hk] at hx₀
    rw [hk, ← hsecond, mem_step_snd_iff] at hx₁
    exact (hx₁.resolve_left hx₀).2.2

/-- If every higher-priority restraint is eventually bounded, a routed monotone enumeration
injures `k` only finitely often. Neither a bound on the number of injuries nor stabilization of
`k`'s own restraint is assumed. This is the combinatorial step of priority induction for
Sacks splitting. -/
theorem finite_injurySet_of_bounded_higher_priority
    {A : Bool → ℕ → Finset ℕ} {r : ℕ → List ℕ} {D : ℕ → Finset ℕ} {k s₀ R : ℕ}
    (hstep : ∀ s, step (r s) (A false s, A true s) (D s) =
      (A false (s + 1), A true (s + 1)))
    (hbound : ∀ s ≥ s₀, ∀ j < k, (r s)[j]?.getD 0 ≤ R) :
    (injurySet (A k.bodd) (fun j t => some ((r t)[j]?.getD 0)) k).Finite := by
  have hA : Monotone (A k.bodd) := monotone_nat_of_le_succ fun s => by
    cases k.bodd
    · exact (subset_step_fst ..).trans_eq (congrArg Prod.fst (hstep s))
    · exact (subset_step_snd ..).trans_eq (congrArg Prod.snd (hstep s))
  obtain ⟨t, ht⟩ := finite_prefix_stabilizes hA (R + 1)
  apply (finite_injurySet_iff_eventually_eq_empty hA).2
  refine ⟨max s₀ t, fun s hs => Finset.eq_empty_of_forall_notMem fun x hx => ?_⟩
  obtain ⟨j, hj, hxj, -⟩ := exists_higher_priority_of_mem_injuriesAt (hstep s) hx
  have hxR : x ≤ R := hxj.trans (hbound s (by omega) j hj)
  obtain ⟨hx₁, hx₀, -⟩ := mem_injuriesAt.1 hx
  exact hx₀ ((ht s (by omega) x (by omega)).2 (subset_stageLimit _ (s + 1) hx₁))

/-! ### Effectivity on binary codes -/

open Primrec

/-- The finite search is primitive recursive in the restraint list and the entry. -/
theorem primrec₂_leastThreat : Primrec₂ leastThreat := by
  have hp : Primrec₂ fun (p : List ℕ × ℕ) k => decide (p.2 ≤ p.1[k]?.getD 0) :=
    (nat_le.comp (snd.comp fst)
      (option_getD.comp (list_getElem?.comp (fst.comp fst) snd) (const 0))).decide.to₂
  exact (list_find? (list_range.comp (succ.comp (list_length.comp fst))) hp).to₂

/-- The destination is primitive recursive in the restraint list and the entry. -/
theorem primrec₂_route : Primrec₂ route :=
  (option_getD.comp (option_map primrec₂_leastThreat
    (Primrec.not.comp (nat_bodd.comp snd)).to₂) (const false)).to₂

/-- Binary coding of a routed batch is primitive recursive uniformly in all inputs. -/
theorem primrec_routedBatch : Primrec fun p : List ℕ × ℕ × Bool =>
    Finset.equivBitIndices.symm (routedBatch p.1 (Finset.equivBitIndices p.2.1) p.2.2) := by
  have hp : PrimrecRel fun (p : List ℕ × ℕ × Bool) x => route p.1 x = p.2.2 :=
    Primrec.eq.comp (primrec₂_route.comp (fst.comp fst) snd) (snd.comp (snd.comp fst))
  exact (equivBitIndices_symm_toFinset.comp
    (hp.swap.listFilter.comp (nat_bitIndices.comp (fst.comp snd)) Primrec.id)).of_eq fun p => by
      simp [routedBatch, List.toFinset_filter, Finset.equivBitIndices_apply]

/-- The entire batched transition is primitive recursive on the two old binary codes and the
batch code, uniformly in the current restraint list. -/
theorem primrec_step : Primrec fun p : List ℕ × (ℕ × ℕ) × ℕ =>
    let A := step p.1 (Finset.equivBitIndices p.2.1.1, Finset.equivBitIndices p.2.1.2)
      (Finset.equivBitIndices p.2.2)
    (Finset.equivBitIndices.symm A.1, Finset.equivBitIndices.symm A.2) := by
  have ha : Primrec fun p : List ℕ × (ℕ × ℕ) × ℕ => p.2.1.1 := fst.comp (fst.comp snd)
  have hb : Primrec fun p : List ℕ × (ℕ × ℕ) × ℕ => p.2.1.2 := snd.comp (fst.comp snd)
  have hd : Primrec fun p : List ℕ × (ℕ × ℕ) × ℕ => p.2.2 := snd.comp snd
  have hf := nat_ldiff.comp hd (nat_lor.comp ha hb)
  have hout (b : Bool) := primrec_routedBatch.comp (fst.pair (hf.pair (const b)))
  refine ((nat_lor.comp ha (hout false)).pair (nat_lor.comp hb (hout true))).of_eq fun p => ?_
  dsimp only
  apply Prod.ext <;> apply Finset.equivBitIndices.injective <;>
    simp only [Nat.lor_eq, Finset.equivBitIndices_lor, Finset.equivBitIndices_ldiff,
      Equiv.apply_symm_apply, step]

/-! ### Boundary checks -/

-- An unrecorded zero restraint really protects zero.
example : leastThreat [] 0 = some 0 := by decide

-- A positive number threatens no implicit zero restraint.
example : route [] 1 = false := by decide

-- Route a whole batch, including entries exactly at both recorded restraints.
example : step [3, 5] (∅, ∅) {0, 3, 4, 5, 6} = ({4, 5, 6}, {0, 3}) := by decide

end TauCeti.SacksSplitting
