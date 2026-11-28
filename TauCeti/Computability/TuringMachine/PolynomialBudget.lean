/-
Copyright (c) 2026 Vincent Quenneville-Belair. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Vincent Quenneville-Belair
-/
module

public import TauCeti.Algebra.Polynomial.Eval.Monotone
public import TauCeti.Computability.TuringMachine.Composition

/-!
# Polynomial budgets for candidate generation followed by verification

This file connects the public polynomial monotonicity API to the
TM2 output-length and composition APIs. It supplies budget lemmas;
it does not construct the certificate verifier's component machines.
-/

open Polynomial Turing

@[expose] public section

namespace TauCeti

variable {α β γ αΓ βΓ γΓ : Type}
variable {ea : α → List αΓ} {eb : β → List βΓ} {ec : γ → List γΓ}
variable {f : α → β} {g : β → γ}

/-- A stage's input length plus its maximum total output growth. -/
noncomputable def outputLengthPolynomial
    (hf : TM2ComputableInPolyTime ea eb f) : Polynomial ℕ :=
  X + C hf.tm.maxPushes * hf.time

theorem output_length_le_budget
    (hf : TM2ComputableInPolyTime ea eb f) (a : α) :
    (eb (f a)).length ≤ (outputLengthPolynomial hf).eval (ea a).length := by
  simpa [outputLengthPolynomial] using hf.length_le a

/-- The next stage's time polynomial can be evaluated at the first
stage's output-size bound using the public monotonicity theorem. -/
theorem next_stage_time_le_budget
    (hg : TM2ComputableInPolyTime eb ec g)
    (hf : TM2ComputableInPolyTime ea eb f) (a : α) :
    hg.time.eval (eb (f a)).length ≤
      (hg.time.comp (outputLengthPolynomial hf)).eval (ea a).length := by
  rw [Polynomial.eval_comp]
  exact Polynomial.eval_le_eval hg.time (output_length_le_budget hf a)

/-- The existing finite-machine composition has this explicit budget. -/
theorem composition_time_eq_budget
    (hg : TM2ComputableInPolyTime eb ec g)
    (hf : TM2ComputableInPolyTime ea eb f) :
    (hg.comp hf).time =
      hf.time + 4 * outputLengthPolynomial hf + 2 +
        hg.time.comp (outputLengthPolynomial hf) :=
  rfl


end TauCeti
