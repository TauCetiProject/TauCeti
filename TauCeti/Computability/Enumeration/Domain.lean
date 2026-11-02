/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.RE

/-!
# c.e. sets of naturals are domains of codes

A predicate on `ℕ` is c.e. (Mathlib's `REPred`) exactly when it is the domain of the partial
computable function `Nat.Partrec.Code.eval c` of some code `c`. This is the presentation
`W_c = dom φ_c` of the c.e. sets by the standard numbering, through which requirements of the form
"if `W_e` is infinite then ..." quantify over all c.e. sets.

## Main results

* `Nat.Partrec.Code.rePred_dom_eval`: the domain of a code is c.e.
* `TauCeti.Enumeration.rePred_iff_exists_code`: a predicate on `ℕ` is c.e. exactly when it is the
  domain of some code.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1.
-/

public section

open Nat.Partrec

namespace Nat.Partrec.Code

/-- The domain `W_c` of a code `c` is c.e. -/
theorem rePred_dom_eval (c : Code) : REPred fun x => (c.eval x).Dom :=
  (eval_part.comp (Computable.const c) Computable.id).dom_re

end Nat.Partrec.Code

namespace TauCeti

namespace Enumeration

/-- **c.e. sets are domains of codes.** A predicate on `ℕ` is c.e. exactly when it is the domain
of the partial computable function of some code. -/
theorem rePred_iff_exists_code {p : ℕ → Prop} :
    REPred p ↔ ∃ c : Code, ∀ x, p x ↔ (c.eval x).Dom := by
  refine ⟨fun hp => ?_, fun ⟨c, hc⟩ => c.rePred_dom_eval.of_eq fun x => (hc x).symm⟩
  -- recode the `Unit`-valued semidecision procedure as a partial function `ℕ →. ℕ`
  have hf : Nat.Partrec fun x => (Part.assert (p x) fun _ => Part.some ()).map fun _ => 0 :=
    Partrec.nat_iff.1 (hp.map (Computable.const 0).to₂)
  obtain ⟨c, hc⟩ := Code.exists_code.1 hf
  refine ⟨c, fun x => ?_⟩
  by_cases h : p x <;> simp [hc, h, Part.assert_pos, Part.assert_neg]

end Enumeration

end TauCeti
