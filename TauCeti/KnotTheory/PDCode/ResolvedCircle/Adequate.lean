/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.PDCode.ResolvedCircle.Adjacent

/-!
# Adequate diagrams

A diagram is *A-adequate* if, in its all-A smoothing, the two arcs left at each crossing lie on
two different circles; it is *B-adequate* if the same holds in its all-B smoothing. In the native
convention the all-A state is the constant state `true` and the all-B state the constant state
`false`. Changing the smoothing of one crossing `c` either merges the circles through `c` or
splits the circle through `c`, so adequacy says that every edge of the cube of resolutions leaving
the all-A vertex is a merge, and every edge arriving at the all-B vertex is a split
(`TauCeti.PDCode.isAAdequate_iff`, `TauCeti.PDCode.isBAdequate_iff`).

These are the conditions under which the extreme states of the Khovanov complex survive in
homology: they control the extreme quantum degrees, and hence the cochain support used in the
crossing-number bound for adequate diagrams.

## Main definitions

* `TauCeti.PDCode.IsAAdequate`: two circles of the all-A smoothing pass through every crossing.
* `TauCeti.PDCode.IsBAdequate`: two circles of the all-B smoothing pass through every crossing.

## Main results

* `TauCeti.PDCode.isAAdequate_def`, `TauCeti.PDCode.isBAdequate_def`: the defining
  circle-incidence conditions.
* `TauCeti.PDCode.isAAdequate_iff`, `TauCeti.PDCode.isBAdequate_iff`: adequacy says that changing
  any single crossing of the extreme smoothing lowers the number of circles by one.
* `TauCeti.PDCode.IsAAdequate.stateLoopCount_add_one`,
  `TauCeti.PDCode.IsBAdequate.stateLoopCount_add_one`: the circle count of every state adjacent to
  the extreme state.

## References

* W. B. R. Lickorish, *An Introduction to Knot Theory*, Springer GTM 175 (1997), Chapter 5.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §7.
-/

public section

namespace TauCeti

open Finset

namespace PDCode

variable {n : ℕ} (D : PDCode n)

/-- A PD code is **A-adequate** if two different circles of its all-A smoothing pass through every
crossing: changing any single crossing of the all-A smoothing to its B-smoothing merges two
circles. -/
def IsAAdequate : Prop :=
  ∀ c, #(D.circlesAt (fun _ ↦ true) c) = 2

/-- A PD code is **B-adequate** if two different circles of its all-B smoothing pass through every
crossing: changing any single crossing of the all-B smoothing to its A-smoothing merges two
circles. -/
def IsBAdequate : Prop :=
  ∀ c, #(D.circlesAt (fun _ ↦ false) c) = 2

/-- A PD code is A-adequate exactly when two circles of its all-A smoothing pass through every
crossing. -/
theorem isAAdequate_def : D.IsAAdequate ↔ ∀ c, #(D.circlesAt (fun _ ↦ true) c) = 2 :=
  Iff.rfl

/-- A PD code is B-adequate exactly when two circles of its all-B smoothing pass through every
crossing. -/
theorem isBAdequate_def : D.IsBAdequate ↔ ∀ c, #(D.circlesAt (fun _ ↦ false) c) = 2 :=
  Iff.rfl

/-- A-adequacy says that changing any single crossing of the all-A smoothing lowers the number of
circles by one. -/
theorem isAAdequate_iff :
    D.IsAAdequate ↔ ∀ c,
      D.stateLoopCount (Function.update (fun _ ↦ true) c false) + 1 =
        D.stateLoopCount fun _ ↦ true :=
  forall_congr' fun c ↦ D.card_circlesAt_eq_two_iff_stateLoopCount_add_one
    (fun j hj ↦ by simp [Function.update_of_ne hj]) (by simp)

/-- B-adequacy says that changing any single crossing of the all-B smoothing lowers the number of
circles by one. -/
theorem isBAdequate_iff :
    D.IsBAdequate ↔ ∀ c,
      D.stateLoopCount (Function.update (fun _ ↦ false) c true) + 1 =
        D.stateLoopCount fun _ ↦ false :=
  forall_congr' fun c ↦ D.card_circlesAt_eq_two_iff_stateLoopCount_add_one
    (fun j hj ↦ by simp [Function.update_of_ne hj]) (by simp)

variable {D}

/-- In an A-adequate diagram, a state selecting the B-smoothing at exactly one crossing has one
circle fewer than the all-A state. -/
theorem IsAAdequate.stateLoopCount_add_one (hA : D.IsAAdequate) {t : Fin n → Bool} {c : Fin n}
    (ht : ∀ j, j ≠ c → t j = true) (hc : t c = false) :
    D.stateLoopCount t + 1 = D.stateLoopCount fun _ ↦ true :=
  (D.card_circlesAt_eq_two_iff_stateLoopCount_add_one (fun j hj ↦ (ht j hj).symm)
    (by simp [hc])).1 (hA c)

/-- In a B-adequate diagram, a state selecting the A-smoothing at exactly one crossing has one
circle fewer than the all-B state. -/
theorem IsBAdequate.stateLoopCount_add_one (hB : D.IsBAdequate) {t : Fin n → Bool} {c : Fin n}
    (ht : ∀ j, j ≠ c → t j = false) (hc : t c = true) :
    D.stateLoopCount t + 1 = D.stateLoopCount fun _ ↦ false :=
  (D.card_circlesAt_eq_two_iff_stateLoopCount_add_one (fun j hj ↦ (ht j hj).symm)
    (by simp [hc])).1 (hB c)

end PDCode

end TauCeti
