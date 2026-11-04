/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Breach

/-!
# Regression examples: use-prefix breaches and boundary injuries

These examples exercise the use-prefix breach and boundary injury objects from a downstream module,
through public statements only:

* an entry exactly at the restraint is a boundary injury and not a use-prefix breach;
* under the restraint `some 0` an entry `0` injures, but breaches no use prefix;
* with stages `[0, s)` and the growing restraint `some s`, every number injures as a boundary
  injury while nothing breaches the use prefix: finitely many use-prefix breaches do not give
  finite injury without control of the restraint.
-/

open TauCeti.Priority

-- An entry exactly at the restraint is a boundary injury, and not a use-prefix breach.
example :
    5 ∈ boundaryInjuriesAt (fun s => if s = 0 then ∅ else {5}) (fun _ _ => some 5) 0 0 ∧
      5 ∉ injuriesAt (fun s => if s = 0 then ∅ else {5}) (usePrefixRestraint fun _ _ => some 5)
        0 0 := by
  simp

-- Under the restraint `some 0` the entry `0` injures, but the use-prefix restraint is inactive.
example :
    0 ∈ injuriesAt (fun s => if s = 0 then ∅ else {0}) (fun _ _ => some 0) 0 0 ∧
      usePrefixRestraint (fun _ _ => some 0) 0 0 = none := by
  simp

-- Stages `[0, s)` with restraint `some s`: every number is a boundary injury ...
example (s : ℕ) : boundaryInjuriesAt Finset.range (fun _ s => some s) 0 s = {s} := by
  ext x
  simp only [mem_boundaryInjuriesAt, Finset.mem_range, Option.some.injEq, Finset.mem_singleton]
  omega

-- ... so every number injures, while nothing breaches the use prefix.
example :
    injurySet Finset.range (fun _ s => some s) 0 = Set.univ ∧
      injurySet Finset.range (usePrefixRestraint fun _ s => some s) 0 = ∅ := by
  constructor
  · refine Set.eq_univ_of_forall fun x => mem_injurySet.2 ⟨x, ?_⟩
    simp
  · refine Set.eq_empty_of_forall_notMem fun x hx => ?_
    obtain ⟨s, hs⟩ := mem_injurySet.1 hx
    simp only [mem_injuriesAt_usePrefixRestraint, Finset.mem_range, Option.some.injEq] at hs
    omega
