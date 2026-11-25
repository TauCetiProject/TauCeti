/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Primrec
public import TauCeti.Computability.RecursiveIn
import TauCeti.Computability.Primrec.List

/-!
# Oracle-relative computability of bounded simulation

Bounded evaluation accepts optional answers uniformly computable in the same oracle family
as the evaluation. The simulator computes a finite initial segment of those answers and then
uses the primitive-recursive evaluator. Only the first `k` answers are needed for fuel `k`,
including to certify failure. Total oracles are the special case in which every answer is present.

This allows a computable approximation of an oracle to be passed to a bounded simulator,
without assuming that its oracle answers are primitive recursive. In particular it supports
approximations to computations in a Turing jump relative to the original oracle.

-/

public section

namespace TauCeti.Oracle.Single.Code

variable {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}

/-- Bounded evaluation of optional answers uniformly computable in `G` is uniformly computable
in `G`. With fuel `k`, the simulator needs only the first `k` answers. -/
theorem computableIn_evaln_option {σ : α → ℕ → Option ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evaln (σ p.1) p.2.1 p.2.2.1 p.2.2.2 :=
  hσ.computableIn_of_primrec_range_map_option
    (F := fun τ k (q : Code × ℕ) => evaln τ k q.1 q.2)
    (primrec_evaln Primrec.list_getElem?_bind_id)
    fun a k q => evaln_range_map_option (σ a) k q.1 q.2

/-- Bounded evaluation against a uniformly oracle-computable family of total oracles is
oracle-computable, uniformly in the family parameter, fuel, program and input. -/
theorem computableIn_evaln {σ : α → ℕ → ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evaln (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2 :=
  computableIn_evaln_option (σ := fun a z => some (σ a z))
    (Primrec.option_some.computableIn.comp hσ)

end TauCeti.Oracle.Single.Code
