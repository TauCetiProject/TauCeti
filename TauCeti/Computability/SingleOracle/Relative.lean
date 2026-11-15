/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.RecursiveIn

/-!
# Oracle-relative computability of bounded simulation

Bounded simulation against a uniformly oracle-computable family of total oracles is itself
uniformly oracle-computable. The simulator first computes a finite initial segment of the
oracle and then uses the primitive-recursive finite-string evaluator. Only the first `k`
answers are needed for fuel `k`, including to certify failure.

This allows a computable approximation of an oracle to be passed to a bounded simulator,
without assuming that its oracle answers are primitive recursive. In particular it supports
approximations to computations in a Turing jump relative to the original oracle.

-/

public section

namespace TauCeti.Oracle.Single.Code

variable {G : Set (ℕ →. ℕ)} {σ : ℕ → ℕ → ℕ}

/-- Bounded evaluation against a uniformly oracle-computable sequence of total oracles is
oracle-computable, uniformly in the sequence parameter, fuel, program and input. -/
theorem computableIn_evaln (hσ : ComputableIn₂ G σ) :
    ComputableIn G (fun p : ℕ × ℕ × Code × ℕ =>
      evaln (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2) := by
  have hp' : ComputableIn G (fun p : ℕ × ℕ => (List.range p.2).map (σ p.1)) :=
    hσ.list_range_map
  have hargs : ComputableIn G (fun p : ℕ × ℕ × Code × ℕ => (p.1, p.2.1)) :=
    ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd)
  have hp := hp'.comp hargs
  have hsim : ComputableIn G (fun p : List ℕ × ℕ × Code × ℕ =>
      evaln (fun z => p.1[z]?) p.2.1 p.2.2.1 p.2.2.2) :=
    primrec_evaln_list.computableIn
  have hr := hsim.comp (hp.pair ComputableIn.snd)
  exact RecursiveIn.of_eq hr fun p => congrArg Part.some (evaln_range_map _ _ _ _)

end TauCeti.Oracle.Single.Code
