/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.SingleOracle.Race.Family

/-!
# Examples of finite-family races

Three persistent discovery streams illustrate the two levels of priority. The lowest index
discovers later, and the other two discover simultaneously. The smaller of those two indices
wins and is retained when the lowest index becomes available.

A tuple of three query programs illustrates the oracle specialization, including the use
recorded for a negative answer.
-/

open TauCeti.Staged TauCeti.Oracle.Single Code

-- Streams 1 and 2 discover at stage 1, while stream 0 discovers at stage 2.
example (s : ℕ) (hs : 1 ≤ s) :
    raceFamily (fun (i : Fin 3) t => if (if i = 0 then 2 else 1) ≤ t then some i.val else none) s =
      some (1, 1) := by
  refine raceFamily_eq_some_iff.2 ⟨1, hs, by decide, ?_, ?_⟩
  · intro u hu j
    obtain rfl : u = 0 := by omega
    by_cases hj : j = 0 <;> simp [hj]
  · intro j hj
    have : j.val < 1 := hj
    obtain rfl : j = 0 := Fin.ext (by omega)
    decide

-- Stage zero is inspected, and an empty family has no winner at any stage.
example : raceFamily (fun (_ : Fin 3) (_ : ℕ) => some (7 : ℕ)) 0 = some (0, 7) := by
  refine raceFamily_eq_some_iff.2 ⟨0, le_rfl, rfl, by simp, ?_⟩
  intro j hj
  exact (Fin.not_lt_zero j hj).elim

example (s : ℕ) (D : Fin 0 → ℕ → Option ℕ) : raceFamily D s = none := by
  exact raceFamily_eq_none_iff.2 fun _ _ i => i.elim0

-- Three simultaneous query runs retain the least index and the positive use of a negative answer.
example (Z : Set ℕ) (hZ : 0 ∉ Z) (s : ℕ) (hs : Encodable.encode (oracle : Code) < s) :
    raceFamilyStage (setAnswers Z) (fun _ : Fin 3 => oracle) 0 s = some (0, ⟨0, 1⟩) := by
  let t := Encodable.encode (oracle : Code) + 1
  refine raceFamilyStage_eq_some_iff.2 ⟨t, hs, ?_, ?_, ?_⟩
  · apply evalStage_eq_some_of_evaln (k := 1) _ (by omega) (by omega) (by simp [t])
    simp [hZ]
  · intro u hu _
    exact evalStage_eq_none_of_le_encode (by omega)
  · intro j hj
    exact (Fin.not_lt_zero j hj).elim
