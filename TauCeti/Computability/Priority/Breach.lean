/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Priority.Injury.Basic
public import Mathlib.Data.Nat.PSub

/-!
# Use-prefix breaches and boundary injuries

A successful oracle computation with use `u` reads only the oracle below `u`, while a restraint
`some b` protects the numbers up to `b` inclusive. A restraint equal to the use thus protects one
more number than the computation reads. This file separates the two conditions.

The **use-prefix restraint** `usePrefixRestraint r` protects exactly the numbers strictly below the
active restraint of `r`: it is `some c` where `r` is `some (c + 1)`, and inactive where `r` is
inactive or `some 0`. The **use-prefix breaches** of requirement `e` are the injuries for this
restraint, so the use-prefix breach batch, events, number set and stages are

* `injuriesAt A (usePrefixRestraint r) e s`, the fresh entries strictly below the active
  restraint (`mem_injuriesAt_usePrefixRestraint`),
* `injuryEvents A (usePrefixRestraint r) e`,
* `injurySet A (usePrefixRestraint r) e`,
* `injuryStages A (usePrefixRestraint r) e`,

and every result about injury objects, such as their projections and the finiteness criteria under
monotone stages, applies to them verbatim. The **boundary injuries** `boundaryInjuriesAt A r e s`
are the fresh entries equal to the active restraint. An injury batch is the disjoint union of its
use-prefix breaches and its boundary injuries.

Finitely many injuring numbers give finitely many use-prefix breaching numbers. The converse fails:
with stages `[0, s)` and restraint `some s` at stage `s`, every number is a boundary injury while
nothing breaches the use prefix. Control of the restraint itself does give finite injury
(`TauCeti.Priority.finite_injurySet_of_eventually_bounded`).

## Main definitions

* `TauCeti.Priority.usePrefixRestraint`: the restraint protecting the numbers strictly below the
  active restraint.
* `TauCeti.Priority.boundaryInjuriesAt`: the fresh entries equal to the active restraint.

## Main results

* `TauCeti.Priority.injuriesAt_usePrefixRestraint_union_boundaryInjuriesAt`,
  `TauCeti.Priority.disjoint_injuriesAt_usePrefixRestraint_boundaryInjuriesAt`: an injury batch is
  the disjoint union of its use-prefix breaches and its boundary injuries.
* `TauCeti.Priority.finite_injurySet_usePrefixRestraint_of_finite_injurySet`: finitely many
  injuring numbers give finitely many use-prefix breaching numbers.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters III.1 and VII.
-/

public section

open Set TauCeti.Enumeration

namespace TauCeti

namespace Priority

/-! ### The use-prefix restraint -/

/-- The restraint protecting exactly the numbers strictly below the active restraint of `r`:
`some c` where `r e s = some (c + 1)`, and inactive where `r e s` is `none` or `some 0`. -/
def usePrefixRestraint (r : ℕ → ℕ → Option ℕ) (e s : ℕ) : Option ℕ :=
  (r e s).bind Nat.ppred

variable {A : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {e s : ℕ}

/-- The use-prefix restraint is `some c` exactly where the restraint is `some (c + 1)`. -/
@[simp]
theorem usePrefixRestraint_eq_some_iff {c : ℕ} :
    usePrefixRestraint r e s = some c ↔ r e s = some (c + 1) := by
  rcases h : r e s with - | b <;> simp [usePrefixRestraint, h, eq_comm]

/-- The use-prefix restraint is inactive exactly where the restraint is inactive or `some 0`. -/
@[simp]
theorem usePrefixRestraint_eq_none_iff :
    usePrefixRestraint r e s = none ↔ r e s = none ∨ r e s = some 0 := by
  rcases h : r e s with - | (- | b) <;> simp [usePrefixRestraint, h]

/-- Membership in a use-prefix breach batch: a fresh entry strictly below the active
restraint. -/
@[simp high]
theorem mem_injuriesAt_usePrefixRestraint {x : ℕ} :
    x ∈ injuriesAt A (usePrefixRestraint r) e s ↔
      x ∈ A (s + 1) ∧ x ∉ A s ∧ ∃ b, r e s = some b ∧ x < b := by
  simp only [mem_injuriesAt, usePrefixRestraint_eq_some_iff]
  refine and_congr_right fun _ => and_congr_right fun _ => ⟨?_, ?_⟩
  · rintro ⟨c, hc, hxc⟩
    exact ⟨c + 1, hc, Nat.lt_succ_of_le hxc⟩
  · rintro ⟨b, hb, hxb⟩
    obtain ⟨c, rfl⟩ := Nat.exists_eq_add_one_of_ne_zero (Nat.ne_zero_of_lt hxb)
    exact ⟨c, hb, Nat.le_of_lt_succ hxb⟩

/-- Every use-prefix breach is an injury. -/
theorem injuriesAt_usePrefixRestraint_subset :
    injuriesAt A (usePrefixRestraint r) e s ⊆ injuriesAt A r e s :=
  injuriesAt_mono fun c hc => ⟨c + 1, usePrefixRestraint_eq_some_iff.1 hc, c.le_succ⟩

/-- Every use-prefix breach event is an injury event. -/
theorem injuryEvents_usePrefixRestraint_subset :
    injuryEvents A (usePrefixRestraint r) e ⊆ injuryEvents A r e :=
  injuryEvents_mono fun _ => injuriesAt_usePrefixRestraint_subset

/-- Every use-prefix breaching number is an injuring number. -/
theorem injurySet_usePrefixRestraint_subset :
    injurySet A (usePrefixRestraint r) e ⊆ injurySet A r e :=
  injurySet_mono fun _ => injuriesAt_usePrefixRestraint_subset

/-- Every use-prefix breach stage is an injury stage. -/
theorem injuryStages_usePrefixRestraint_subset :
    injuryStages A (usePrefixRestraint r) e ⊆ injuryStages A r e :=
  injuryStages_mono fun _ => injuriesAt_usePrefixRestraint_subset

/-- **Finite injury bounds the use-prefix breaches**: finitely many injuring numbers give finitely
many use-prefix breaching numbers. The converse fails without control of the restraint. -/
theorem finite_injurySet_usePrefixRestraint_of_finite_injurySet (h : (injurySet A r e).Finite) :
    (injurySet A (usePrefixRestraint r) e).Finite :=
  h.subset injurySet_usePrefixRestraint_subset

/-! ### Boundary injuries -/

variable (A r e s) in
/-- The boundary injuries of requirement `e` in the transition to stage `s + 1`: the fresh entries
equal to the active restraint. Such an entry injures `e` but lies outside the use prefix. -/
def boundaryInjuriesAt : Finset ℕ :=
  (fresh A s).filter fun x => r e s = some x

/-- Membership in a boundary injury batch: a fresh entry equal to the active restraint. -/
@[simp]
theorem mem_boundaryInjuriesAt {x : ℕ} :
    x ∈ boundaryInjuriesAt A r e s ↔ x ∈ A (s + 1) ∧ x ∉ A s ∧ r e s = some x := by
  simp [boundaryInjuriesAt, and_assoc]

/-- Every boundary injury is an injury. -/
theorem boundaryInjuriesAt_subset_injuriesAt :
    boundaryInjuriesAt A r e s ⊆ injuriesAt A r e s := by
  intro x hx
  rw [mem_boundaryInjuriesAt] at hx
  exact mem_injuriesAt.2 ⟨hx.1, hx.2.1, x, hx.2.2, le_rfl⟩

/-- **An injury batch splits** into its use-prefix breaches and its boundary injuries. -/
theorem injuriesAt_usePrefixRestraint_union_boundaryInjuriesAt :
    injuriesAt A (usePrefixRestraint r) e s ∪ boundaryInjuriesAt A r e s =
      injuriesAt A r e s := by
  ext x
  rw [Finset.mem_union, mem_injuriesAt_usePrefixRestraint, mem_boundaryInjuriesAt, mem_injuriesAt]
  constructor
  · rintro (⟨hx₁, hx₂, b, hb, hxb⟩ | ⟨hx₁, hx₂, hb⟩)
    · exact ⟨hx₁, hx₂, b, hb, hxb.le⟩
    · exact ⟨hx₁, hx₂, x, hb, le_rfl⟩
  · rintro ⟨hx₁, hx₂, b, hb, hxb⟩
    rcases hxb.lt_or_eq with hxb | rfl
    · exact Or.inl ⟨hx₁, hx₂, b, hb, hxb⟩
    · exact Or.inr ⟨hx₁, hx₂, hb⟩

/-- Use-prefix breaches and boundary injuries are disjoint. -/
theorem disjoint_injuriesAt_usePrefixRestraint_boundaryInjuriesAt :
    Disjoint (injuriesAt A (usePrefixRestraint r) e s) (boundaryInjuriesAt A r e s) := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  rw [mem_injuriesAt_usePrefixRestraint] at hx
  rw [mem_boundaryInjuriesAt] at hx'
  obtain ⟨-, -, b, hb, hxb⟩ := hx
  rw [hx'.2.2, Option.some.injEq] at hb
  exact hxb.ne hb

end Priority

end TauCeti
