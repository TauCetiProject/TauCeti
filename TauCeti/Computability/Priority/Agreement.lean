/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Agreement
public import TauCeti.Computability.Priority.Injury.Basic

/-!
# Preservation of agreement along a stage enumeration

In Sacks's constructions a set is enumerated in finite stages `A s`, and the requirement
`C ≠ Φ_e^A` holds as its restraint the agreement restraint of `Φ_e` against the answers of `A s`
(`TauCeti.Oracle.Single.Code.setAnswers`) with fuel `s` and the target `C s`, Soare's `r(e, s)`.
This file specializes the preservation theorems of
`TauCeti.Computability.SingleOracle.Agreement` to that setting: a transition that does not injure
the requirement keeps the answers at and below the restraint, hence the computations up to and
including the length of agreement, and the agreements where the target bit does not change.

## Main results

* `TauCeti.Oracle.Single.Code.eqOn_setAnswers_of_injuriesAt_eq_empty`: without injury, the answers
  of `A s` and `A (s + 1)` agree at and below the restraint.
* `TauCeti.Oracle.Single.Code.evaln_succ_eq_some_of_injuriesAt_eq_empty`: **one-step preservation
  of computations**, with no hypothesis on the target.
* `TauCeti.Oracle.Single.Code.agreesAt_succ_of_injuriesAt_eq_empty`: **one-step preservation of
  agreement** where the target bit does not change.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.3, in
  particular the Remark on p. 122.
-/

public section

open Set TauCeti.Priority

namespace TauCeti.Oracle.Single.Code

variable {A C : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {e s b x : ℕ} {c : Code} {d : Halt}

/-- If nothing injures requirement `e`, with active restraint `b`, in the transition to stage
`s + 1`, and `A s ⊆ A (s + 1)`, then the oracle answers of `A s` and `A (s + 1)` agree at and
below `b`. -/
theorem eqOn_setAnswers_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1)) (hr : r e s = some b)
    (hI : injuriesAt A r e s = ∅) :
    EqOn (setAnswers (A s)) (setAnswers (A (s + 1))) (Iic b) :=
  eqOn_setAnswers_iff.2 fun _ hz => mem_iff_mem_succ_of_injuriesAt_eq_empty hA hr hI hz

/-- **One-step preservation of computations.** Let requirement `e` hold, at stage `s`, the
agreement restraint of `c` against the answers of `A s` with fuel `s` and the target `C s`. If no
number injures `e` in the transition to stage `s + 1`, and `A s ⊆ A (s + 1)`, then every successful
stage-`s` run at an argument up to and including the length of agreement is a successful
stage-`s + 1` run, with the same output and use. The target `C` may change. -/
theorem evaln_succ_eq_some_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1))
    (hr : r e s = some (agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1)))
    (hI : injuriesAt A r e s = ∅)
    (hx : x ≤ agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1))
    (hd : evaln (setAnswers (A s)) s c x = some d) :
    evaln (setAnswers (A (s + 1))) (s + 1) c x = some d :=
  evaln_eq_some_of_eqOn_agreementRestraint s.le_succ
    (eqOn_setAnswers_of_injuriesAt_eq_empty hA hr hI) hx hd

/-- **One-step preservation of agreement.** Under the hypotheses of
`evaln_succ_eq_some_of_injuriesAt_eq_empty`, agreement at an argument below the length of agreement
persists to stage `s + 1` when membership of that argument in `C` does not change. -/
theorem agreesAt_succ_of_injuriesAt_eq_empty (hA : A s ⊆ A (s + 1))
    (hr : r e s = some (agreementRestraint (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1)))
    (hI : injuriesAt A r e s = ∅)
    (hx : x < agreementLength (setAnswers (A s)) s c ((C s : Set ℕ).indicator 1))
    (hC : x ∈ C (s + 1) ↔ x ∈ C s) :
    AgreesAt (setAnswers (A (s + 1))) (s + 1) c ((C (s + 1) : Set ℕ).indicator 1) x :=
  agreesAt_of_eqOn_agreementRestraint s.le_succ (eqOn_setAnswers_of_injuriesAt_eq_empty hA hr hI)
    hx (by simp [indicator_apply, hC])

end TauCeti.Oracle.Single.Code
