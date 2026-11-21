/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode

/-!
# Domain lemmas for ordinary program codes

Basic domain equations for pairing and composition of ordinary Mathlib program codes
`Nat.Partrec.Code`:

* `Nat.Partrec.Code.eval_comp_eq`: functional composition equation for `Nat.Partrec.Code.comp`.
* `Nat.Partrec.Code.dom_eval_pair`: the domain of `pair cf cg` is the intersection of the two
  domains.
* `Nat.Partrec.Code.dom_eval_comp`: the domain of `comp cf cg` is the partial preimage of
  `cf.eval.Dom` under `cg.eval`.
* `Nat.Partrec.Code.dom_eval_comp_total`: when `cg` computes a total function `f`, the domain of
  `comp cf cg` is `f ⁻¹' cf.eval.Dom`.
-/

public section

namespace Nat.Partrec.Code

/-- Evaluation of a composed ordinary code is partial-function composition. -/
theorem eval_comp_eq (cf cg : Code) :
    (comp cf cg).eval = cf.eval.comp cg.eval :=
  funext fun x => (PFun.comp_apply cf.eval cg.eval x).symm

/-- The domain of a paired ordinary code is the intersection of the two domains. -/
@[simp]
theorem dom_eval_pair (cf cg : Code) :
    (pair cf cg).eval.Dom = cf.eval.Dom ∩ cg.eval.Dom := by
  ext x
  simp [eval, PFun.Dom, Seq.seq]

/-- The domain of a composed ordinary code is the partial preimage of the outer domain under the
inner code. -/
@[simp]
theorem dom_eval_comp (cf cg : Code) :
    (comp cf cg).eval.Dom = cg.eval.preimage cf.eval.Dom := by
  rw [eval_comp_eq, PFun.dom_comp]

/-- When `cg` computes a total function `f`, the domain of `comp cf cg` is `f ⁻¹' cf.eval.Dom`. -/
theorem dom_eval_comp_total {cf cg : Code} {f : ℕ → ℕ}
    (hf : ∀ x, cg.eval x = Part.some (f x)) :
    (comp cf cg).eval.Dom = f ⁻¹' cf.eval.Dom := by
  have hcg : cg.eval = (f : ℕ →. ℕ) := funext fun x => (hf x).trans (PFun.coe_val f x).symm
  rw [dom_eval_comp, hcg, PFun.coe_preimage]

end Nat.Partrec.Code
