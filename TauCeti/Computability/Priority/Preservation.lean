/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Limit
public import TauCeti.Computability.Priority.Breach

/-!
# Preservation of protected stage computations

In a priority construction, a stage computation `Φ_{e,s}^{A_s}(x)` persists in the limit when
nothing enters the enumeration below its use after stage `s`
(`TauCeti.Oracle.Single.Code.evaln_indicator_stageLimit_eq_some_of_forall_notMem_fresh`). This is
the case when the requirement protecting the computation is not injured after that stage, provided
its restraint covers the use at every later stage. The covering premise is needed because
restraints can drop: once the protected interval no longer contains the use, an entry below the use
is not an injury but still changes the computation. An address below the use is covered by an
inclusive restraint `some b` when it is at most `b`; for use-prefix breaches, which only count
entries strictly below the restraint, it must be less than `b`. A restraint equal to the use covers
it in both senses.

## Main results

In the namespace `TauCeti.Oracle.Single.Code`:

* `evaln_indicator_stageLimit_eq_some_of_injuriesAt_eq_empty`,
  `evaln_indicator_stageLimit_eq_some_of_injuriesAt_usePrefixRestraint_eq_empty`: preservation
  of a stage computation whose use stays covered by a restraint that is not injured,
  respectively whose use prefix is not breached.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter VII.1.
-/

public section

open TauCeti.Enumeration TauCeti.Priority

namespace TauCeti

namespace Oracle.Single.Code

variable {A : ℕ → Finset ℕ} {r : ℕ → ℕ → Option ℕ} {k n s e : ℕ} {c : Code} {d : Halt}

/-- **Preservation under a covering restraint without injury.** Under monotone stages, let a run
against the set oracle of `A s` succeed. Suppose that at every later stage requirement `e` is not
injured, and every address below the use of the run lies in its protected interval: the restraint
is active, `some b`, with the address at most `b`. Then the run succeeds with the same output and
use against the set oracle of the limit. -/
theorem evaln_indicator_stageLimit_eq_some_of_injuriesAt_eq_empty (hA : Monotone A)
    (h : evaln (fun z => some ((A s : Set ℕ).indicator 1 z)) k c n = some d)
    (hr : ∀ t, s ≤ t → ∀ z, z < d.use → ∃ b, r e t = some b ∧ z ≤ b)
    (hI : ∀ t, s ≤ t → injuriesAt A r e t = ∅) :
    evaln (fun z => some ((stageLimit A).indicator 1 z)) k c n = some d :=
  evaln_indicator_stageLimit_eq_some_of_forall_notMem_fresh hA h fun t ht z hz =>
    have ⟨_, hb, hzb⟩ := hr t ht z hz
    notMem_fresh_of_injuriesAt_eq_empty (hI t ht) hb hzb

/-- **Preservation under a covering restraint without use-prefix breach.** Under monotone stages,
let a run against the set oracle of `A s` succeed. Suppose that at every later stage the use prefix
of requirement `e` is not breached, and every address below the use of the run lies strictly below
its restraint: the restraint is active, `some b`, with the address less than `b`. Then the run
succeeds with the same output and use against the set oracle of the limit. -/
theorem evaln_indicator_stageLimit_eq_some_of_injuriesAt_usePrefixRestraint_eq_empty
    (hA : Monotone A) (h : evaln (fun z => some ((A s : Set ℕ).indicator 1 z)) k c n = some d)
    (hr : ∀ t, s ≤ t → ∀ z, z < d.use → ∃ b, r e t = some b ∧ z < b)
    (hI : ∀ t, s ≤ t → injuriesAt A (usePrefixRestraint r) e t = ∅) :
    evaln (fun z => some ((stageLimit A).indicator 1 z)) k c n = some d :=
  evaln_indicator_stageLimit_eq_some_of_forall_notMem_fresh hA h fun t ht z hz =>
    have ⟨_, hb, hzb⟩ := hr t ht z hz
    notMem_fresh_of_injuriesAt_usePrefixRestraint_eq_empty (hI t ht) hb hzb

end Oracle.Single.Code

end TauCeti
