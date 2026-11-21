/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.SingleOracle.Stage
public import TauCeti.Computability.RecursiveIn

/-!
# Oracle-relative computability of bounded simulation

Bounded simulation against a uniformly oracle-computable family of total oracles is itself
uniformly oracle-computable. The simulator first computes a finite initial segment of the
oracle and then uses the primitive-recursive finite-string evaluator. Only the first `k`
answers are needed for fuel `k`, including to certify failure. Normalized stage evaluation
`evalStage` is obtained by applying the program-index and output stage bounds.

This allows a computable approximation of an oracle to be passed to a bounded simulator,
without assuming that its oracle answers are primitive recursive. In particular it supports
approximations to computations in a Turing jump relative to the original oracle.

-/

public section

namespace TauCeti.Oracle.Single.Code

open Encodable

variable {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)} {σ : α → ℕ → ℕ}

/-- Bounded evaluation against a uniformly oracle-computable family of total oracles is
oracle-computable, uniformly in the family parameter, fuel, program and input. -/
theorem computableIn_evaln (hσ : ComputableIn₂ G σ) :
    ComputableIn G (fun p : α × ℕ × Code × ℕ =>
      evaln (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2) := by
  have hp' : ComputableIn G (fun p : α × ℕ => (List.range p.2).map (σ p.1)) :=
    hσ.list_range_map
  have hargs : ComputableIn G (fun p : α × ℕ × Code × ℕ => (p.1, p.2.1)) :=
    ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd)
  have hp := hp'.comp hargs
  have hsim : ComputableIn G (fun p : List ℕ × ℕ × Code × ℕ =>
      evaln (fun z => p.1[z]?) p.2.1 p.2.2.1 p.2.2.2) :=
    primrec_evaln_list.computableIn
  have hr := hsim.comp (hp.pair ComputableIn.snd)
  exact RecursiveIn.of_eq hr fun p => congrArg Part.some (evaln_range_map _ _ _ _)

/-- Normalized stage evaluation against a uniformly oracle-computable family of total oracles is
oracle-computable, uniformly in the family parameter, stage, program, and input. -/
theorem computableIn_evalStage (hσ : ComputableIn₂ G σ) :
    ComputableIn G (fun p : α × ℕ × Code × ℕ =>
      evalStage (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2) := by
  open Primrec in
  have hguard : Primrec fun q : Option Halt × ℕ × Code =>
      if encode q.2.2 < q.2.1 then
        q.1.bind fun d => if d.output < q.2.1 then some d else none
      else none :=
    Primrec.ite (nat_lt.comp (encode_iff.2 (snd.comp snd)) (fst.comp snd))
      (option_bind fst <| Primrec₂.mk <|
        Primrec.ite (nat_lt.comp (Halt.primrec_output.comp snd) (fst.comp (snd.comp fst)))
          (option_some.comp snd) (const none))
      (const none)
  have hargs : ComputableIn G fun p : α × ℕ × Code × ℕ =>
      (evaln (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2, p.2.1, p.2.2.1) :=
    (computableIn_evaln hσ).pair
      ((ComputableIn.fst.comp ComputableIn.snd).pair
        (ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.snd)))
  refine RecursiveIn.of_eq (hguard.computableIn.comp hargs) fun p => congrArg Part.some <|
    Option.ext fun d => ?_
  by_cases hc : encode p.2.2.1 < p.2.1
  · simp only [hc, ↓reduceIte, Option.bind_eq_some_iff, evalStage_eq_some_iff, true_and]
    constructor
    · rintro ⟨d', hd', h⟩
      split_ifs at h with hd
      exact ⟨Option.some.inj h ▸ hd', Option.some.inj h ▸ hd⟩
    · rintro ⟨h, hd⟩
      exact ⟨d, h, by simp [hd]⟩
  · simp [evalStage_eq_none_of_le_encode (Nat.le_of_not_lt hc), hc]

end TauCeti.Oracle.Single.Code
