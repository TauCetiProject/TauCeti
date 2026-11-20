/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Stage
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

variable {α : Type*} [Primcodable α] {G : Set (ℕ →. ℕ)}

/-- Bounded evaluation is uniformly oracle-computable from a uniformly computable family of
optional answers. With fuel `k`, the simulator needs only the first `k` answers. -/
theorem computableIn_evaln_option {σ : α → ℕ → Option ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evaln (σ p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  have hp : ComputableIn G fun p : α × ℕ × Code × ℕ => (List.range p.2.1).map (σ p.1) :=
    hσ.list_range_map.comp (ComputableIn.fst.pair (ComputableIn.fst.comp ComputableIn.snd))
  have hlookup : Primrec₂ fun (l : List (Option ℕ)) z => l[z]?.bind id :=
    (Primrec.option_bind₁ Primrec.id).comp Primrec.list_getElem?
  refine RecursiveIn.of_eq ((primrec_evaln hlookup).computableIn.comp (hp.pair ComputableIn.snd))
    fun p => congrArg Part.some ?_
  ext d
  constructor <;> intro hd <;> refine evaln_eq_some_of_eqOn hd fun z hz => ?_
  all_goals simp [(Set.mem_Iio.1 hz).trans_le (evaln_use_le hd)]

/-- Bounded evaluation against a uniformly oracle-computable family of total oracles is
oracle-computable, uniformly in the family parameter, fuel, program and input. -/
theorem computableIn_evaln {σ : α → ℕ → ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evaln (fun z => some (σ p.1 z)) p.2.1 p.2.2.1 p.2.2.2 :=
  computableIn_evaln_option (σ := fun a z => some (σ a z))
    (Primrec.option_some.computableIn.comp hσ)

/-- Normalized stage evaluation is uniformly oracle-computable from a uniformly computable
family of optional answers. To simulate stage `s` it suffices to read the first `s` answers. -/
theorem computableIn_evalStage {σ : α → ℕ → Option ℕ} (hσ : ComputableIn₂ G σ) :
    ComputableIn G fun p : α × ℕ × Code × ℕ =>
      evalStage (σ p.1) p.2.1 p.2.2.1 p.2.2.2 := by
  have hstage : ComputableIn G fun p : α × ℕ × Code × ℕ => (p.2.1, p.2.2.1) :=
    ComputableIn.fst.comp ComputableIn.snd |>.pair
      (ComputableIn.fst.comp (ComputableIn.snd.comp ComputableIn.snd))
  simpa only [evalStage_def] using primrec_normalizeStage.computableIn.comp
    (hstage.pair (computableIn_evaln_option hσ))

end TauCeti.Oracle.Single.Code
