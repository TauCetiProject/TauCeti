/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.RE

/-!
# Closure properties of computable and c.e. predicates

Mathlib's `ComputablePred` and `REPred` come with complementation and Post's theorem. This file
adds the closure properties needed to read off the effectivity of predicates assembled from
computable pieces:

* `ComputablePred.and`: computable predicates are closed under conjunction;
* `ComputablePred.exists_lt`: a bounded existential quantifier over a computable predicate is
  computable, uniformly in the bound;
* `ComputablePred.rePred_exists`: an unbounded existential quantifier over a computable predicate
  is c.e., by unbounded search.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1.
-/

public section

variable {α : Type*} [Primcodable α]

namespace ComputablePred

/-- Computable predicates are closed under conjunction. -/
protected theorem and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∧ q a := by
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  exact Computable.computablePred <| (Primrec.and.to_comp.comp hp hq).of_eq fun a => by simp

/-- A bounded existential quantifier over a computable predicate is computable, uniformly in the
bound. -/
theorem exists_lt {p : α → ℕ → Prop} (hp : ComputablePred fun x : α × ℕ => p x.1 x.2) :
    ComputablePred fun x : α × ℕ => ∃ y < x.2, p x.1 y := by
  classical
  replace hp := hp.decide
  -- scan `0, …, n - 1`, accumulating the disjunction of the tested values
  have h : Computable fun x : α × ℕ =>
      Nat.rec (motive := fun _ => Bool) false (fun y b => b || decide (p x.1 y)) x.2 :=
    Computable.nat_rec Computable.snd (Computable.const false)
      (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
        (hp.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))).to₂
  refine Computable.computablePred (h.of_eq fun x => ?_)
  obtain ⟨a, n⟩ := x
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.lt_succ_iff_lt_or_eq, or_and_right, exists_or]

/-- An unbounded existential quantifier over a computable predicate is c.e.: search for a
witness. -/
theorem rePred_exists {p : α → ℕ → Prop} (hp : ComputablePred fun x : α × ℕ => p x.1 x.2) :
    REPred fun a => ∃ n, p a n := by
  classical
  replace hp := hp.decide
  have h : Partrec fun a => Nat.rfind fun n => Part.some (decide (p a n)) :=
    Partrec.rfind hp.partrec
  refine h.dom_re.of_eq fun a => ⟨fun h => ?_, fun ⟨n, hn⟩ => ?_⟩
  · obtain ⟨n, hn⟩ := Part.dom_iff_mem.1 h
    exact ⟨n, by simpa using Nat.rfind_spec hn⟩
  · obtain ⟨m, hm, -⟩ := Nat.rfind_min' (p := fun n => decide (p a n)) (by simpa using hn)
    exact Part.dom_iff_mem.2 ⟨m, hm⟩

end ComputablePred
