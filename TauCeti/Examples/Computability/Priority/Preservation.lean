/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Priority.Preservation

/-!
# Regression examples: preservation of protected stage computations

These examples exercise the preservation of stage computations from a downstream module, through
public statements only. They use the program `oracle`, which on input `n` reads only the answer at
address `n`: against a set not containing `n` it halts with output `0` and use `n + 1`.

* **An injury at the use boundary:** when `1` enters under the restraint `some 1`, equal to the
  use, the entry injures the requirement but is not a use-prefix breach, and the computation found
  at stage `0` survives in the limit, by the use-prefix form of preservation.
* **Simultaneous preservation:** two computations with uses `1` and `3` both survive an entry
  above a restraint covering both uses, while an entry between the two uses preserves only the
  computation with the smaller use.
* **A dropped restraint:** when the restraint `some 0` covers address `0` at stage `0` and is
  inactive afterwards, `0` can enter at stage `2` without injuring the requirement, and the
  computation found at stage `0` fails against the limit at every fuel. Absence of injury does not
  preserve a use that the restraint no longer covers.
-/

open TauCeti.Enumeration TauCeti.Priority TauCeti.Oracle.Single.Code

/-! ### An injury at the use boundary -/

-- Against stage `0` the run halts with output `0` and use `1`. When `1` enters in the transition
-- to stage `1`, under the restraint `some 1`, equal to that use, the entry injures ...
example : evaln (setAnswers ∅) 1 oracle 0 = some ⟨0, 1⟩ ∧
    1 ∈ injurySet (fun s => if s = 0 then ∅ else {1}) (fun _ _ => some 1) 0 :=
  ⟨by simp, mem_injurySet.2 ⟨0, by simp⟩⟩

-- ... but breaches no use prefix, at any stage, so the computation found at stage `0` survives in
-- the limit.
example :
    (∀ t, injuriesAt (fun s => if s = 0 then ∅ else {1}) (usePrefixRestraint fun _ _ => some 1)
      0 t = ∅) ∧
    evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {1})) 1 oracle 0 = some ⟨0, 1⟩ := by
  have hI (t : ℕ) : injuriesAt (fun s => if s = 0 then ∅ else {1})
      (usePrefixRestraint fun _ _ => some 1) 0 t = ∅ := by
    ext x
    simp only [mem_injuriesAt_usePrefixRestraint, Nat.add_one_ne_zero, ite_false,
      Finset.mem_singleton, Option.some.injEq, exists_eq_left', Finset.notMem_empty, iff_false,
      not_and]
    omega
  exact ⟨hI, evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_usePrefixRestraint_eq_empty
    (s := 0) (monotone_nat_of_le_succ fun s => by split_ifs <;> simp_all) (by simp)
    (fun _ _ _ hz => ⟨1, rfl, hz⟩) fun t _ => hI t⟩

/-! ### Simultaneous preservation of two computations with different uses -/

-- Against stage `0`, the runs of `oracle` on inputs `0` and `2` have uses `1` and `3`.
example : evaln (setAnswers ∅) 1 oracle 0 = some ⟨0, 1⟩ ∧ evaln (setAnswers ∅) 3 oracle 2 =
    some ⟨0, 3⟩ := by
  simp

-- When `3` enters in the transition to stage `1`, it does not injure the restraint `some 2`,
-- which covers the addresses read by both runs, so both survive in the limit.
example :
    evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {3})) 1 oracle 0 = some ⟨0, 1⟩ ∧
      evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {3})) 3 oracle 2 =
        some ⟨0, 3⟩ := by
  have hA : Monotone fun s : ℕ => if s = 0 then (∅ : Finset ℕ) else {3} :=
    monotone_nat_of_le_succ fun s => by split_ifs <;> simp_all
  have hI (t : ℕ) (_ : 0 ≤ t) :
      injuriesAt (fun s => if s = 0 then ∅ else {3}) (fun _ _ => some 2) 0 t = ∅ := by
    ext x
    simp only [mem_injuriesAt, Nat.add_one_ne_zero, ite_false, Finset.mem_singleton,
      Option.some.injEq, exists_eq_left', Finset.notMem_empty, iff_false, not_and]
    omega
  -- one argument for the common restraint `some 2` preserves both runs
  exact ⟨evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_eq_empty hA (s := 0) (by simp)
      (fun _ _ z hz => ⟨2, rfl, by simp at hz; omega⟩) hI,
    evaln_setAnswers_stageLimit_eq_some_of_injuriesAt_eq_empty hA (s := 0) (by simp)
      (fun _ _ z hz => ⟨2, rfl, by simp at hz; omega⟩) hI⟩

-- When `2` enters instead, between the two uses, the run with use `1` survives in the limit while
-- the run with use `3` changes its output.
example :
    evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {2})) 1 oracle 0 = some ⟨0, 1⟩ ∧
      evaln (setAnswers (stageLimit fun s => if s = 0 then ∅ else {2})) 3 oracle 2 =
        some ⟨1, 3⟩ := by
  have h0 : 0 ∉ stageLimit fun s => if s = 0 then (∅ : Finset ℕ) else {2} := by
    simp only [mem_stageLimit, not_exists]
    intro s
    split_ifs <;> simp
  have h2 : 2 ∈ stageLimit fun s => if s = 0 then (∅ : Finset ℕ) else {2} :=
    mem_stageLimit.2 ⟨1, by simp⟩
  simp [h0, h2]

/-! ### A dropped restraint -/

-- `0` enters in the transition to stage `2`, while the restraint is `some 0` at stage `0` only.
-- At stage `0` this restraint covers the address `0` read by the run of `oracle` on input `0`,
-- which halts with output `0` and use `1`. Nothing ever injures the requirement ...
example :
    injurySet (fun s => if s ≤ 1 then ∅ else {0}) (fun _ s => if s = 0 then some 0 else none) 0 =
      ∅ := by
  ext x
  simp only [mem_injurySet, mem_injuriesAt, Option.ite_none_right_eq_some, Option.some.injEq,
    Set.mem_empty_iff_false, iff_false, not_exists, not_and]
  rintro s hs - b ⟨rfl, rfl⟩ -
  simp at hs

-- ... yet the computation fails against the limit, at every fuel.
example (k : ℕ) :
    evaln (setAnswers (stageLimit fun s => if s ≤ 1 then ∅ else {0})) k oracle 0 ≠
      some ⟨0, 1⟩ := by
  have h0 : 0 ∈ stageLimit fun s => if s ≤ 1 then (∅ : Finset ℕ) else {0} :=
    mem_stageLimit.2 ⟨2, by simp⟩
  rcases k with - | k <;> simp [h0]
