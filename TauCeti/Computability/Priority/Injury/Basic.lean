/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Enumeration.Stage
public import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Lattice
import Mathlib.Order.Interval.Finset.Nat

/-!
# Injury bookkeeping for finite-stage enumerations

A finite-injury construction enumerates a set in finite stages `A s`, and a requirement `e`
protects, at each stage `s`, either nothing (`r e s = none`) or the numbers up to a restraint
`b` (`r e s = some b`, an inclusive bound). A number **injures** `e` in the transition to stage
`s + 1` when it enters at that transition and lies at or below the active restraint.

* `injuriesAt A r e s`: the finite batch of numbers injuring `e` in that transition.
* `injuryEvents A r e`: the pairs `(s, x)` with `x ∈ injuriesAt A r e s`.
* `injurySet A r e`: the numbers that ever injure `e`, Soare's `I_e`.
* `injuryStages A r e`: the stages `s + 1` at which some number injures `e`.

Finitely many injury stages are the same as an eventually injury-free tail, and give finitely many
injuring numbers. When the stages are monotone, a number enters at most once
(`TauCeti.Enumeration.unique_entry_stage`), so it injures `e` at most once. Then finitely many
injuring numbers are equivalent to both, and there are at most as many injury stages as injuring
numbers. Several numbers
may injure `e` at one stage, so the inequality can be strict. Without monotonicity a single number
can leave and re-enter, injuring `e` at infinitely many stages.

A restraint protecting fewer numbers at every stage has fewer injuries, and inclusions of the
batches pass to the events, numbers and stages. Control of the restraint itself gives finite
injury: a restraint that is eventually bounded admits only finitely many injuring numbers, with no
monotonicity of the stages and no bound on its earlier values. Under monotone stages this yields
an injury-free tail.

Injury concerns entries into a protected interval only. Resetting the records of lower-priority
requirements, effectiveness of the injury sets, preservation of computations and satisfaction of
requirements are separate matters, not treated here.

## Main results

* `TauCeti.Priority.mem_injuriesAt`, `TauCeti.Priority.injuriesAt_eq_empty_of_eq_none`: membership
  in an injury batch; no restraint, no injury.
* `TauCeti.Priority.injurySet_eq_image`, `TauCeti.Priority.injuryStages_eq_image`: numbers and
  stages are the projections of the events.
* `TauCeti.Priority.injuriesAt_mono`, `TauCeti.Priority.injuryEvents_mono`,
  `TauCeti.Priority.injurySet_mono`, `TauCeti.Priority.injuryStages_mono`: a smaller restraint
  has fewer injuries.
* `TauCeti.Priority.injOn_snd_injuryEvents`: under monotone stages a number injures at most once.
* `TauCeti.Priority.finite_injuryStages_iff_eventually_eq_empty`: finitely many injury stages are
  an eventually injury-free tail, with no monotonicity.
* `TauCeti.Priority.finite_injurySet_iff_finite_injuryStages`,
  `TauCeti.Priority.finite_injurySet_iff_eventually_eq_empty`: under monotone stages, finitely
  many injuring numbers are equivalent to both.
* `TauCeti.Priority.ncard_injuryStages_le`: finitely many injuring numbers bound the number of
  injury stages.
* `TauCeti.Priority.finite_injurySet_of_eventually_bounded`: an eventually bounded restraint admits
  only finitely many injuring numbers.
* `TauCeti.Priority.exists_forall_injuriesAt_eq_empty_of_eventually_bounded`: under monotone
  stages, an eventually bounded restraint gives an injury-free tail.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

open Set TauCeti.Enumeration

namespace TauCeti

namespace Priority

variable (A : ℕ → Finset ℕ) (r : ℕ → ℕ → Option ℕ) (e : ℕ)

/-- The numbers injuring requirement `e` in the transition to stage `s + 1`: the fresh entries at
or below the active restraint. -/
def injuriesAt (s : ℕ) : Finset ℕ :=
  (fresh A s).filter fun x => ∃ b, r e s = some b ∧ x ≤ b

/-- The injury events of requirement `e`: the pairs `(s, x)` with `x` injuring `e` in the
transition to stage `s + 1`. -/
def injuryEvents : Set (ℕ × ℕ) :=
  {p | p.2 ∈ injuriesAt A r e p.1}

/-- The numbers that ever injure requirement `e`, Soare's `I_e`. -/
def injurySet : Set ℕ :=
  {x | ∃ s, x ∈ injuriesAt A r e s}

/-- The stages `s + 1` at which some number injures requirement `e`. -/
def injuryStages : Set ℕ :=
  {t | ∃ s, t = s + 1 ∧ (injuriesAt A r e s).Nonempty}

variable {A r e}

/-- Membership in an injury batch: a fresh entry at or below the active restraint. -/
@[simp]
theorem mem_injuriesAt {s x : ℕ} :
    x ∈ injuriesAt A r e s ↔ x ∈ A (s + 1) ∧ x ∉ A s ∧ ∃ b, r e s = some b ∧ x ≤ b := by
  simp [injuriesAt, and_assoc]

/-- Every injury is a fresh entry. -/
theorem injuriesAt_subset_fresh {s : ℕ} : injuriesAt A r e s ⊆ fresh A s :=
  Finset.filter_subset _ _

/-- With no active restraint there is no injury. -/
theorem injuriesAt_eq_empty_of_eq_none {s : ℕ} (h : r e s = none) : injuriesAt A r e s = ∅ := by
  ext x
  simp [h]

/-- Membership in the injury events. -/
@[simp]
theorem mem_injuryEvents {p : ℕ × ℕ} : p ∈ injuryEvents A r e ↔ p.2 ∈ injuriesAt A r e p.1 :=
  Iff.rfl

/-- Membership in the injury set. -/
@[simp]
theorem mem_injurySet {x : ℕ} : x ∈ injurySet A r e ↔ ∃ s, x ∈ injuriesAt A r e s :=
  Iff.rfl

/-- Membership in the injury stages. -/
theorem mem_injuryStages {t : ℕ} :
    t ∈ injuryStages A r e ↔ ∃ s, t = s + 1 ∧ (injuriesAt A r e s).Nonempty :=
  Iff.rfl

/-- `s + 1` is an injury stage exactly when the batch of the transition to it is nonempty. -/
@[simp]
theorem succ_mem_injuryStages {s : ℕ} :
    s + 1 ∈ injuryStages A r e ↔ (injuriesAt A r e s).Nonempty := by
  simp [mem_injuryStages]

/-- Stage `0` is never an injury stage. -/
@[simp]
theorem zero_notMem_injuryStages : 0 ∉ injuryStages A r e := by
  simp [mem_injuryStages]

/-- The injury set is the projection of the events to their numbers. -/
theorem injurySet_eq_image : injurySet A r e = Prod.snd '' injuryEvents A r e := by
  ext x
  simp

/-- The injury stages are the projection of the events to their stages. -/
theorem injuryStages_eq_image :
    injuryStages A r e = (fun p : ℕ × ℕ => p.1 + 1) '' injuryEvents A r e := by
  ext t
  simp only [mem_injuryStages, mem_image, mem_injuryEvents, Prod.exists]
  constructor
  · rintro ⟨s, rfl, x, hx⟩
    exact ⟨s, x, hx, rfl⟩
  · rintro ⟨s, x, hx, rfl⟩
    exact ⟨s, rfl, x, hx⟩

/-! ### Comparing restraints -/

/-- **A smaller restraint has fewer injuries**: if every active restraint `c` of `r'` at stage `s`
is matched by an active restraint of `r` at least `c`, every injury for `r'` is one for `r`. -/
theorem injuriesAt_mono {r' : ℕ → ℕ → Option ℕ} {s : ℕ}
    (h : ∀ c, r' e s = some c → ∃ b, r e s = some b ∧ c ≤ b) :
    injuriesAt A r' e s ⊆ injuriesAt A r e s := by
  intro x hx
  obtain ⟨hx₁, hx₂, c, hc, hxc⟩ := mem_injuriesAt.1 hx
  obtain ⟨b, hb, hcb⟩ := h c hc
  exact mem_injuriesAt.2 ⟨hx₁, hx₂, b, hb, hxc.trans hcb⟩

/-- Stagewise inclusions of injury batches give an inclusion of injury events. -/
theorem injuryEvents_mono {r' : ℕ → ℕ → Option ℕ}
    (h : ∀ s, injuriesAt A r' e s ⊆ injuriesAt A r e s) :
    injuryEvents A r' e ⊆ injuryEvents A r e :=
  fun p hp => h p.1 hp

/-- Stagewise inclusions of injury batches give an inclusion of injury sets. -/
theorem injurySet_mono {r' : ℕ → ℕ → Option ℕ}
    (h : ∀ s, injuriesAt A r' e s ⊆ injuriesAt A r e s) :
    injurySet A r' e ⊆ injurySet A r e :=
  fun _ ⟨s, hs⟩ => ⟨s, h s hs⟩

/-- Stagewise inclusions of injury batches give an inclusion of injury stages. -/
theorem injuryStages_mono {r' : ℕ → ℕ → Option ℕ}
    (h : ∀ s, injuriesAt A r' e s ⊆ injuriesAt A r e s) :
    injuryStages A r' e ⊆ injuryStages A r e :=
  fun _ ⟨s, hst, hs⟩ => ⟨s, hst, hs.mono (h s)⟩

/-! ### Finiteness and monotone stages -/

/-- **Under monotone stages a number injures at most once**: it enters the enumeration at most
once. -/
theorem injOn_snd_injuryEvents (hA : Monotone A) : InjOn Prod.snd (injuryEvents A r e) := by
  rintro ⟨s, x⟩ hsx ⟨t, y⟩ hty (rfl : x = y)
  simp only [mem_injuryEvents] at hsx hty
  rw [unique_entry_stage hA (injuriesAt_subset_fresh hsx) (injuriesAt_subset_fresh hty)]

/-- Finitely many injury stages give finitely many injuring numbers, with no monotonicity. -/
theorem finite_injurySet_of_finite_injuryStages (h : (injuryStages A r e).Finite) :
    (injurySet A r e).Finite := by
  refine ((h.image Nat.pred).biUnion fun s _ => (injuriesAt A r e s).finite_toSet).subset ?_
  intro x hx
  obtain ⟨s, hs⟩ := mem_injurySet.1 hx
  exact mem_biUnion ⟨s + 1, succ_mem_injuryStages.2 ⟨x, hs⟩, rfl⟩ hs

/-- **Finite injury numbers and finite injury stages agree** under monotone stages. -/
theorem finite_injurySet_iff_finite_injuryStages (hA : Monotone A) :
    (injurySet A r e).Finite ↔ (injuryStages A r e).Finite := by
  refine ⟨fun h => ?_, finite_injurySet_of_finite_injuryStages⟩
  rw [injurySet_eq_image] at h
  rw [injuryStages_eq_image]
  exact (Finite.of_finite_image h (injOn_snd_injuryEvents hA)).image _

/-- **Finitely many injury stages are an eventually injury-free tail**, with no monotonicity. -/
theorem finite_injuryStages_iff_eventually_eq_empty :
    (injuryStages A r e).Finite ↔ ∃ s₀, ∀ s, s₀ ≤ s → injuriesAt A r e s = ∅ := by
  constructor
  · rintro h
    obtain ⟨B, hB⟩ := h.bddAbove
    refine ⟨B, fun s hs => Finset.eq_empty_of_forall_notMem fun x hx => ?_⟩
    have := hB (succ_mem_injuryStages.2 ⟨x, hx⟩)
    omega
  · rintro ⟨s₀, hs₀⟩
    refine (finite_Iic s₀).subset fun t ht => ?_
    obtain ⟨s, rfl, x, hx⟩ := mem_injuryStages.1 ht
    by_contra hlt
    rw [hs₀ s (by simp at hlt; omega)] at hx
    simp at hx

/-- **Finitely many injuring numbers are an eventually injury-free tail**, under monotone
stages. -/
theorem finite_injurySet_iff_eventually_eq_empty (hA : Monotone A) :
    (injurySet A r e).Finite ↔ ∃ s₀, ∀ s, s₀ ≤ s → injuriesAt A r e s = ∅ := by
  rw [finite_injurySet_iff_finite_injuryStages hA, finite_injuryStages_iff_eventually_eq_empty]

/-- **An eventually bounded restraint gives finite injury.** If from stage `s₀` on every active
restraint of `e` is at most `R`, only finitely many numbers ever injure `e`. Neither monotone
stages nor a bound on the restraint before `s₀` is needed. -/
theorem finite_injurySet_of_eventually_bounded {s₀ R : ℕ}
    (h : ∀ s, s₀ ≤ s → ∀ b, r e s = some b → b ≤ R) : (injurySet A r e).Finite := by
  refine (((finite_Iio s₀).biUnion fun s _ => (injuriesAt A r e s).finite_toSet).union
    (finite_Iic R)).subset ?_
  intro x hx
  obtain ⟨s, hs⟩ := mem_injurySet.1 hx
  rcases Nat.lt_or_ge s s₀ with hlt | hle
  · exact Or.inl (mem_biUnion hlt hs)
  · obtain ⟨-, -, b, hb, hxb⟩ := mem_injuriesAt.1 hs
    exact Or.inr (hxb.trans (h s hle b hb))

/-- **Injury-free tail.** Under monotone stages, an eventually bounded restraint is eventually
never injured. -/
theorem exists_forall_injuriesAt_eq_empty_of_eventually_bounded (hA : Monotone A) {s₀ R : ℕ}
    (h : ∀ s, s₀ ≤ s → ∀ b, r e s = some b → b ≤ R) :
    ∃ s₁, ∀ s, s₁ ≤ s → injuriesAt A r e s = ∅ :=
  (finite_injurySet_iff_eventually_eq_empty hA).1 (finite_injurySet_of_eventually_bounded h)

/-- **At most as many injury stages as injuring numbers**, when there are finitely many injuring
numbers and the stages are monotone. Several numbers may injure at one stage, so the inequality can
be strict. -/
theorem ncard_injuryStages_le (hA : Monotone A) (h : (injurySet A r e).Finite) :
    (injuryStages A r e).ncard ≤ (injurySet A r e).ncard := by
  have hinj := injOn_snd_injuryEvents (r := r) (e := e) hA
  have hev : (injuryEvents A r e).Finite := by
    rw [injurySet_eq_image] at h
    exact Finite.of_finite_image h hinj
  rw [injuryStages_eq_image, injurySet_eq_image, hinj.ncard_image]
  exact ncard_image_le hev

end Priority

end TauCeti
