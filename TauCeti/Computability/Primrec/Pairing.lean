/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Primrec.List
public import TauCeti.Data.Nat.Pairing

/-!
# Primitive-recursive column membership and witness search

Membership in the pairing column `e.pairColumn` and the bounded fresh-witness search
`Nat.leastInPairColumn e b` are primitive recursive uniformly in the column index `e` and lower
bound `b`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapters I.4 and VII.2.
-/

public section

namespace Primrec

/-- Membership in `e.pairColumn` is primitive recursive uniformly in `e` and `n`. -/
theorem mem_pairColumn : PrimrecRel fun (e : ℕ) n => n ∈ e.pairColumn :=
  (Primrec.eq.comp (snd.comp (unpair.comp snd)) fst).primrecRel.of_eq fun _ _ =>
    Nat.mem_pairColumn.symm

/-- Selecting the least member of `e.pairColumn` at or above `b` is primitive recursive in `e`
and `b`. -/
theorem nat_leastInPairColumn : Primrec₂ Nat.leastInPairColumn := by
  have hbound : Primrec fun p : ℕ × ℕ => Nat.pair p.2 p.1 + 1 :=
    succ.comp (Primrec₂.natPair.comp snd fst)
  have hpred : PrimrecRel fun (p : ℕ × ℕ) (x : ℕ) => p.2 ≤ x ∧ x.unpair.2 = p.1 :=
    (nat_le.comp (snd.comp fst) snd).and
      (Primrec.eq.comp (snd.comp (unpair.comp snd)) (fst.comp fst))
  have hfind : Primrec fun p : ℕ × ℕ =>
      (List.range (Nat.pair p.2 p.1 + 1)).find? fun x => decide (p.2 ≤ x ∧ x.unpair.2 = p.1) :=
    list_find? (list_range.comp hbound) hpred.decide
  exact (option_getD.comp hfind (Primrec₂.natPair.comp snd fst)).to₂.of_eq fun e b =>
    (Nat.leastInPairColumn_def e b).symm

end Primrec
