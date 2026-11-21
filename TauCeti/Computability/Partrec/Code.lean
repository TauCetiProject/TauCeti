/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode
import TauCeti.Data.PFun.Basic

/-!
# Domain lemmas and direct combinators for ordinary program codes

Basic domain equations and direct syntactic domain combinators for ordinary Mathlib program
codes `Nat.Partrec.Code`:

* `Nat.Partrec.Code.eval_comp_eq`: functional composition equation for `Nat.Partrec.Code.comp`.
* `Nat.Partrec.Code.dom_eval_pair`: the domain of `pair cf cg` is the intersection of the two
  domains.
* `Nat.Partrec.Code.dom_eval_comp`: the domain of `comp cf cg` is the partial preimage of
  `cf.eval.Dom` under `cg.eval`.
* `Nat.Partrec.Code.dom_eval_comp_total`: when `cg` computes a total function `f`, the domain of
  `comp cf cg` is `f ⁻¹' cf.eval.Dom`.
* `Nat.Partrec.Code.interList`: uniform finite-intersection compiler on program lists.
* `Nat.Partrec.Code.restrictId`: partial identity restricted to a program's domain.
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

/-- Uniform finite-intersection compiler for a list of ordinary codes. -/
def interList (cs : List Code) : Code :=
  cs.foldr pair zero

/-- The empty intersection of ordinary codes is `zero`. -/
@[simp]
theorem interList_nil : interList [] = zero :=
  (rfl)

/-- Consing an ordinary code intersects its domain with the rest of the list. -/
@[simp]
theorem interList_cons (c : Code) (cs : List Code) :
    interList (c :: cs) = pair c (interList cs) :=
  (rfl)

/-- Finite intersection of ordinary code lists is primitive recursive. -/
theorem primrec_interList : _root_.Primrec interList :=
  (_root_.Primrec.list_foldr (h := fun (_ : List Code) (p : Code × Code) => pair p.1 p.2)
    _root_.Primrec.id (_root_.Primrec.const zero) <|
      Primrec₂.mk (primrec₂_pair.comp (_root_.Primrec.fst.comp _root_.Primrec.snd)
        (_root_.Primrec.snd.comp _root_.Primrec.snd))).of_eq
    fun _ => rfl

/-- The domain of `interList cs` is the intersection of the domains of its entries. -/
@[simp]
theorem dom_eval_interList (cs : List Code) :
    (interList cs).eval.Dom = ⋂ c ∈ cs, c.eval.Dom := by
  induction cs with
  | nil =>
    ext x
    simp only [interList_nil, PFun.mem_dom, List.not_mem_nil, Set.iInter_of_empty, Set.iInter_univ,
      Set.mem_univ, iff_true]
    exact ⟨0, Part.mem_some 0⟩
  | cons c cs ih =>
    simp [ih]

/-- Restrict the identity function on `ℕ` to the domain of an ordinary code `c`. -/
def restrictId (c : Code) : Code :=
  comp left (pair Code.id c)

/-- Domain restriction of the identity is primitive recursive on ordinary codes. -/
theorem primrec_restrictId : _root_.Primrec restrictId :=
  primrec₂_comp.comp (_root_.Primrec.const left)
    (primrec₂_pair.comp (_root_.Primrec.const Code.id) _root_.Primrec.id)

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise. -/
theorem eval_restrictId (c : Code) (x : ℕ) :
    (restrictId c).eval x = (c.eval x).map fun _ => x := by
  refine Part.ext fun y => ?_
  simp only [restrictId, eval, eval_id, Seq.seq, Part.map_eq_map, Part.map_some, Part.bind_some,
    Part.mem_map_iff]
  constructor
  · intro h
    obtain ⟨p, hp, hy⟩ := Part.mem_bind_iff.1 h
    obtain ⟨b, hb, rfl⟩ := (Part.mem_map_iff _).1 hp
    exact ⟨b, hb, by simpa [eq_comm] using hy⟩
  · rintro ⟨b, hb, rfl⟩
    exact Part.mem_bind ((Part.mem_map_iff _).2 ⟨b, hb, rfl⟩) (by simp)

/-- `restrictId c` has the same domain as `c`. -/
@[simp]
theorem dom_eval_restrictId (c : Code) :
    (restrictId c).eval.Dom = c.eval.Dom := by
  ext x
  simp [PFun.Dom, eval_restrictId]

/-- The range of `restrictId c` is the domain of `c`. -/
@[simp]
theorem ran_eval_restrictId (c : Code) :
    (restrictId c).eval.ran = c.eval.Dom := by
  have hrestrict : (restrictId c).eval = fun x => (c.eval x).map fun _ => x :=
    funext (eval_restrictId c)
  rw [hrestrict, PFun.ran_map_const]

end Nat.Partrec.Code
