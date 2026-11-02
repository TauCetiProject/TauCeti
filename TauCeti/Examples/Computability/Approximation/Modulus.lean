/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.Computability.Approximation.Modulus
import Mathlib.Computability.Halting

/-!
# Regression examples: limit approximations and moduli

These examples exercise the approximation API from a downstream module, through public statements
only:

* the simplifier normalizes constant approximations and stage shifts;
* a bit that changes once and then stays changed: the stages `s ↦ decide (x < s)` converge to
  `true`, and the moduli are exactly the functions with `x < m x`;
* the increasing approximation to the halting problem at input `n` by step-bounded evaluation
  `Nat.Partrec.Code.evaln`: it is monotone in the stage, uniformly computable, converges to the
  halting problem, and has no computable modulus, since such a modulus would decide the halting
  problem.
-/

open TauCeti.Approximation Nat.Partrec Code

-- The simplifier discharges constant approximations and removes stage shifts.
example (g : ℕ → ℕ) (m : ℕ → ℕ) : Converges (fun _ => g) g ∧ IsModulus (fun _ => g) g m := by
  simp

example (f : ℕ → ℕ → ℕ) (g : ℕ → ℕ) (k : ℕ) :
    Converges (fun s => f (s + k)) g ↔ Converges f g := by
  simp

-- A bit that changes once, at stage `x + 1`, and then stays changed: the moduli are exactly the
-- functions above the change.
example (m : ℕ → ℕ) : IsModulus (fun s x => decide (x < s)) (fun _ => true) m ↔ ∀ x, x < m x := by
  refine ⟨fun hm x => by simpa using hm.apply_eq x, fun h => isModulus_iff.2 fun x s hs => ?_⟩
  simpa using (h x).trans_le hs

-- The approximation to the halting problem at input `n` is increasing in the stage.
example (n : ℕ) (c : Code) : Monotone fun s => (evaln s c n).isSome := by
  intro s t hst
  cases h : evaln s c n with
  | none => simp [h]
  | some x => simp [h, Option.mem_def.1 (evaln_mono hst (Option.mem_def.2 h))]

-- The approximation to the halting problem at input `n` is uniformly computable.
example (n : ℕ) : Computable₂ fun s (c : Code) => (evaln s c n).isSome :=
  (Primrec.option_isSome.comp (primrec_evaln.comp (Primrec.id.pair (Primrec.const n)))).to_comp

-- The approximation converges to the halting problem at input `n`.
open scoped Classical in
example (n : ℕ) :
    Converges (fun s (c : Code) => (evaln s c n).isSome) fun c => decide (eval c n).Dom := by
  refine converges_iff_eventually.2 fun c => ?_
  by_cases hc : (eval c n).Dom
  · obtain ⟨k, hk⟩ := evaln_complete.1 (Part.get_mem hc)
    exact Filter.eventually_atTop.2
      ⟨k, fun s hs => by simp [hc, Option.mem_def.1 (evaln_mono hs hk)]⟩
  · refine Filter.Eventually.of_forall fun s => ?_
    cases h : evaln s c n with
    | none => simp [hc]
    | some x => exact (hc (Part.dom_iff_mem.2 ⟨x, evaln_sound h⟩)).elim

-- The approximation to the halting problem at input `n` has no computable modulus: one would decide
-- the halting problem.
open scoped Classical in
example (n : ℕ) {m : Code → ℕ} (hm : Computable m) :
    ¬IsModulus (fun s (c : Code) => (evaln s c n).isSome) (fun c => decide (eval c n).Dom) m := by
  intro h
  have hf : Computable₂ fun s (c : Code) => (evaln s c n).isSome :=
    (Primrec.option_isSome.comp (primrec_evaln.comp (Primrec.id.pair (Primrec.const n)))).to_comp
  exact ComputablePred.halting_problem n (ComputablePred.computable_iff.2
    ⟨_, h.computable hf hm, funext fun c => propext decide_eq_true_iff.symm⟩)
