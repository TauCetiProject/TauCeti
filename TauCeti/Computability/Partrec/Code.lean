/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.PartrecCode
public import TauCeti.Computability.SingleOracle.Code
import TauCeti.Data.PFun.Basic

/-!
# Domain lemmas and direct combinators for ordinary program codes

Basic domain equations and direct syntactic domain combinators for ordinary Mathlib program
codes `Nat.Partrec.Code`, transported from `TauCeti.Computability.SingleOracle.Code` via
`toSingleOracleCode` and `toPartrecCode`:

* `Nat.Partrec.Code.eval_comp_eq`: functional composition equation for `Nat.Partrec.Code.comp`.
* `Nat.Partrec.Code.dom_eval_pair`: the domain of `pair cf cg` is the intersection of the two
  domains.
* `Nat.Partrec.Code.dom_eval_comp`: the domain of `comp cf cg` is the partial preimage of
  `cf.eval.Dom` under `cg.eval`.
* `Nat.Partrec.Code.interList`, `Nat.Partrec.Code.toSingleOracleCode_interList`: uniform
  finite-intersection compiler on program lists and its translation into query-free oracle code.
* `Nat.Partrec.Code.restrictId`, `Nat.Partrec.Code.toSingleOracleCode_restrictId`,
  `Nat.Partrec.Code.eval_restrictId`: partial identity restricted to a program's domain and its
  translation into query-free oracle code.
-/

public section

namespace Nat.Partrec.Code

/-- Evaluation of a composed ordinary code is partial-function composition. -/
theorem eval_comp_eq (cf cg : Code) :
    (comp cf cg).eval = cf.eval.comp cg.eval :=
  funext fun x => by rw [eval, PFun.comp_apply]; rfl

/-- The domain of a paired ordinary code is the intersection of the two domains. -/
@[simp]
theorem dom_eval_pair (cf cg : Code) :
    (pair cf cg).eval.Dom = cf.eval.Dom ∩ cg.eval.Dom := by
  let O : ℕ →. ℕ := fun _ => Part.none
  rw [← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode O (pair cf cg),
    toSingleOracleCode_pair, TauCeti.Oracle.Single.Code.dom_eval_pair,
    TauCeti.Oracle.Single.Code.eval_toSingleOracleCode,
    TauCeti.Oracle.Single.Code.eval_toSingleOracleCode]

/-- The domain of a composed ordinary code is the partial preimage of the outer domain under the
inner code. -/
@[simp]
theorem dom_eval_comp (cf cg : Code) :
    (comp cf cg).eval.Dom = cg.eval.preimage cf.eval.Dom := by
  rw [eval_comp_eq, PFun.dom_comp]

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

/-- Translating `interList cs` into query-free oracle code distributes over `interList`. -/
@[simp]
theorem toSingleOracleCode_interList (cs : List Code) :
    (interList cs).toSingleOracleCode =
      TauCeti.Oracle.Single.Code.interList (cs.map toSingleOracleCode) := by
  induction cs with
  | nil => simp [TauCeti.Oracle.Single.Code.interList_nil]
  | cons c cs ih => simp [interList_cons, ih]

/-- Finite intersection of ordinary code lists is primitive recursive. -/
theorem primrec_interList : _root_.Primrec interList := by
  have h : _root_.Primrec fun cs : List Code =>
      (TauCeti.Oracle.Single.Code.interList (cs.map toSingleOracleCode)).toPartrecCode :=
    TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
      TauCeti.Oracle.Single.Code.primrec_interList.comp <|
        _root_.Primrec.list_map _root_.Primrec.id
          (_root_.Primrec₂.mk (primrec_toSingleOracleCode.comp _root_.Primrec.snd))
  exact h.of_eq fun cs => by
    rw [← toSingleOracleCode_interList,
      TauCeti.Oracle.Single.Code.toPartrecCode_toSingleOracleCode]

/-- The domain of `interList cs` is the intersection of the domains of its entries. -/
@[simp]
theorem dom_eval_interList (cs : List Code) :
    (interList cs).eval.Dom = ⋂ c ∈ cs, c.eval.Dom := by
  let O : ℕ →. ℕ := fun _ => Part.none
  rw [← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode O (interList cs),
    toSingleOracleCode_interList, TauCeti.Oracle.Single.Code.dom_eval_interList]
  simp

/-- Restrict the identity function on `ℕ` to the domain of an ordinary code `c`. -/
def restrictId (c : Code) : Code :=
  comp left (pair Code.id c)

/-- Translating `restrictId c` into query-free oracle code commutes with `restrictId`. -/
@[simp]
theorem toSingleOracleCode_restrictId (c : Code) :
    (restrictId c).toSingleOracleCode =
      TauCeti.Oracle.Single.Code.restrictId c.toSingleOracleCode := by
  simp [restrictId, Code.id, TauCeti.Oracle.Single.Code.restrictId_def]

/-- Domain restriction of the identity is primitive recursive on ordinary codes. -/
theorem primrec_restrictId : _root_.Primrec restrictId := by
  have h : _root_.Primrec fun c : Code =>
      (TauCeti.Oracle.Single.Code.restrictId c.toSingleOracleCode).toPartrecCode :=
    TauCeti.Oracle.Single.Code.primrec_toPartrecCode.comp <|
      TauCeti.Oracle.Single.Code.primrec_restrictId.comp primrec_toSingleOracleCode
  exact h.of_eq fun c => by
    rw [← toSingleOracleCode_restrictId,
      TauCeti.Oracle.Single.Code.toPartrecCode_toSingleOracleCode]

/-- `restrictId c` outputs its input `x` whenever `c` halts on `x`, and diverges otherwise. -/
@[simp]
theorem eval_restrictId (c : Code) (x : ℕ) :
    (restrictId c).eval x = (c.eval x).map fun _ => x := by
  let O : ℕ →. ℕ := fun _ => Part.none
  rw [← TauCeti.Oracle.Single.Code.eval_toSingleOracleCode O (restrictId c),
    toSingleOracleCode_restrictId, TauCeti.Oracle.Single.Code.eval_restrictId,
    TauCeti.Oracle.Single.Code.eval_toSingleOracleCode]

/-- `restrictId c` has the same domain as `c`. -/
@[simp]
theorem dom_eval_restrictId (c : Code) :
    (restrictId c).eval.Dom = c.eval.Dom := by
  ext x
  simp only [PFun.mem_dom, eval_restrictId, Part.mem_map_iff]
  exact ⟨fun ⟨_, _, hx, _⟩ => ⟨_, hx⟩, fun ⟨y, hy⟩ => ⟨x, y, hy, rfl⟩⟩

/-- The range of `restrictId c` is the domain of `c`. -/
@[simp]
theorem ran_eval_restrictId (c : Code) :
    (restrictId c).eval.ran = c.eval.Dom := by
  have hrestrict : (restrictId c).eval = fun x => (c.eval x).map fun _ => x :=
    funext (eval_restrictId c)
  rw [hrestrict, PFun.ran_map_const]

end Nat.Partrec.Code
