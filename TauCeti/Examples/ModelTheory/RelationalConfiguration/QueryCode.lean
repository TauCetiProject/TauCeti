/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.ModelTheory.RelationalConfiguration.QueryCode

/-!
# Examples of the query code

The query code reads a configuration through the decoder of `Encodable.ofCountable`, not through
an enumeration of its own; it pads with `false`, so in the empty language, which has no atoms, it
is constantly `false`. Changing a configuration at one atom changes its query code exactly at the
indices decoding to that atom.
-/

open FirstOrder FirstOrder.Language TauCeti RelationalConfiguration

-- The query code at the code of an atom is the value of the configuration there.
example {L : Language} [∀ n, Countable (L.Relations n)] (c : RelationalConfiguration L ℕ)
    (a : Atom L ℕ) :
    queryCode c (@Encodable.encode _ (Encodable.ofCountable _) a) = c.eval a := by
  simp

-- The empty language has no atoms, so every query code is the padding.
example (c : RelationalConfiguration Language.empty ℕ) : queryCode c = fun _ => false := by
  have : IsEmpty (Atom Language.empty ℕ) := ⟨fun a => isEmptyElim a.2.1⟩
  exact queryCode_of_isEmpty c

-- Two configurations differing only at the atom `a` have query codes differing at the code of `a`,
-- and only at indices decoding to `a`.
example {L : Language} [∀ n, Countable (L.Relations n)] {c d : RelationalConfiguration L ℕ}
    {a : Atom L ℕ} (ha : c.eval a ≠ d.eval a) (hne : ∀ b ≠ a, c.eval b = d.eval b) :
    queryCode c (@Encodable.encode _ (Encodable.ofCountable _) a) ≠
        queryCode d (@Encodable.encode _ (Encodable.ofCountable _) a) ∧
      ∀ n, queryCode c n ≠ queryCode d n →
        @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n = some a := by
  refine ⟨by simpa using ha, fun n hn => ?_⟩
  rcases h : @Encodable.decode (Atom L ℕ) (Encodable.ofCountable _) n with _ | b
  · simp [queryCode_of_decode_eq_none h] at hn
  · rw [queryCode_of_decode_eq_some h, queryCode_of_decode_eq_some h] at hn
    exact congrArg some (not_imp_comm.1 (hne b) hn)
