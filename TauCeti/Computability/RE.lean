/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.RE
public import TauCeti.Data.Nat.Pairing
import TauCeti.Computability.Enumeration.Domain
import TauCeti.Computability.Primrec.FiniteSet
import TauCeti.Computability.Primrec.Pairing

/-!
# Closure properties of computable and c.e. predicates

Mathlib's `ComputablePred` and `REPred` come with complementation and Post's theorem. This file
adds the closure properties needed to read off the effectivity of predicates assembled from
computable pieces:

* `ComputablePred.and`: computable predicates are closed under conjunction;
* `ComputablePred.exists_eq_some_and`: testing a computable predicate on the value of a computable
  optional function, when that value is present, is computable;
* `ComputablePred.exists_lt`: a bounded existential quantifier over a computable predicate is
  computable, uniformly in the bound;
* `ComputablePred.rePred_exists`: an unbounded existential quantifier over a computable predicate
  is c.e., by unbounded search;
* `REPred.and`, `REPred.or`, `REPred.forall_mem_finset`, `REPred.exists_mem_finset`,
  `REPred.exists`: closure of c.e. predicates under binary and finite conjunction/disjunction and
  existential quantification over any primitive-codable type;
* `Partrec.rePred_mem_graph`, `Partrec.rePred_mem_ran`, `Partrec.rePred_mem_image`,
  `Partrec.rePred_mem_preimage`, `Computable.rePred_mem_range`, `Computable.rePred_mem_image`:
  graphs, ranges, partial images, and partial preimages of c.e. sets are c.e.;
* `Set.Finite.computablePred`, `Set.Infinite.of_not_computablePred`: membership in a finite set is
  computable, so every noncomputable set is infinite;
* `Nat.computablePred_mem_pairColumn`: membership in a fixed column `e.pairColumn` is computable.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter II.1.
-/

public section

variable {α : Type*} [Primcodable α]

namespace ComputablePred

/-- Computable predicates are closed under conjunction. -/
protected theorem and {p q : α → Prop} (hp : ComputablePred p) (hq : ComputablePred q) :
    ComputablePred fun a => p a ∧ q a := by
  obtain ⟨_, hp⟩ := hp
  obtain ⟨_, hq⟩ := hq
  exact Computable.computablePred <| (Primrec.and.to_comp.comp hp hq).of_eq fun a => by simp

/-- Testing a computable predicate on the value of a computable optional function, when that value
is present, is computable. -/
theorem exists_eq_some_and {β : Type*} [Primcodable β] {f : α → Option β} {q : α → β → Prop}
    (hf : Computable f) (hq : ComputablePred fun x : α × β => q x.1 x.2) :
    ComputablePred fun a => ∃ b, f a = some b ∧ q a b := by
  classical
  refine Computable.computablePred <|
    (Computable.option_casesOn hf (Computable.const false) hq.decide.to₂).of_eq fun a => ?_
  cases f a <;> simp

/-- A bounded existential quantifier over a computable predicate is computable, uniformly in the
bound. -/
theorem exists_lt {p : α → ℕ → Prop} (hp : ComputablePred fun x : α × ℕ => p x.1 x.2) :
    ComputablePred fun x : α × ℕ => ∃ y < x.2, p x.1 y := by
  classical
  replace hp := hp.decide
  -- scan `0, …, n - 1`, accumulating the disjunction of the tested values
  have h : Computable fun x : α × ℕ =>
      Nat.rec (motive := fun _ => Bool) false (fun y b => b || decide (p x.1 y)) x.2 :=
    Computable.nat_rec Computable.snd (Computable.const false)
      (Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd)
        (hp.comp (Computable.pair (Computable.fst.comp Computable.fst)
          (Computable.fst.comp Computable.snd)))).to₂
  refine Computable.computablePred (h.of_eq fun x => ?_)
  obtain ⟨a, n⟩ := x
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Nat.le_iff_lt_or_eq, or_and_right, exists_or]

/-- An unbounded existential quantifier over a computable predicate is c.e.: search for a
witness. -/
theorem rePred_exists {p : α → ℕ → Prop} (hp : ComputablePred fun x : α × ℕ => p x.1 x.2) :
    REPred fun a => ∃ n, p a n := by
  classical
  replace hp := hp.decide
  have h : Partrec fun a => Nat.rfind fun n => Part.some (decide (p a n)) :=
    Partrec.rfind hp.partrec
  refine h.dom_re.of_eq fun a => ?_
  simpa using Nat.rfind_dom (p := fun n => Part.some (decide (p a n)))

end ComputablePred

namespace REPred

open Encodable

/-- C.e. predicates are closed under conjunction. -/
protected theorem and {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun x => p x ∧ q x :=
  (hp.bind (hq.comp Computable.fst).to₂).dom_re.of_eq fun x => by
    simp [Part.dom_iff_mem]

/-- C.e. predicates are closed under disjunction. -/
protected theorem or {p q : α → Prop} (hp : REPred p) (hq : REPred q) :
    REPred fun x => p x ∨ q x := by
  obtain ⟨k, hk, H⟩ := Partrec.merge' hp hq
  exact hk.dom_re.of_eq fun x => by simpa [Part.dom_iff_mem] using (H x).2

/-- C.e. predicates are closed under finite conjunctions, including the empty family. -/
theorem forall_mem_finset {ι : Type*} {s : Finset ι} {p : ι → α → Prop}
    (hp : ∀ i ∈ s, REPred (p i)) : REPred fun x => ∀ i ∈ s, p i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ((Computable.computablePred (p := fun _ : α => True)
      (Computable.const true)).to_re).of_eq fun _ => by simp
  | @insert i s _ ih =>
    exact ((hp i (Finset.mem_insert_self i s)).and
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))).of_eq fun x => by simp

/-- C.e. predicates are closed under finite disjunctions, including the empty family. -/
theorem exists_mem_finset {ι : Type*} {s : Finset ι} {p : ι → α → Prop}
    (hp : ∀ i ∈ s, REPred (p i)) : REPred fun x => ∃ i ∈ s, p i x := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    exact ((Computable.computablePred (p := fun _ : α => False)
      (Computable.const false)).to_re).of_eq fun _ => by simp
  | @insert i s _ ih =>
    exact ((hp i (Finset.mem_insert_self i s)).or
      (ih fun j hj => hp j (Finset.mem_insert_of_mem hj))).of_eq fun x => by simp

/-- C.e. predicates are closed under existential quantification over any primitive-codable type. -/
protected theorem «exists» {β : Type*} [Primcodable β] {r : α × β → Prop} (hr : REPred r) :
    REPred fun x => ∃ y : β, r (x, y) := by
  have hg : REPred fun n : ℕ =>
      ((Part.ofOption (decode (α := α × β) n)).bind fun p =>
        Part.assert (r p) fun _ => Part.some ()).Dom :=
    (Computable.decode.ofOption.bind (hr.comp Computable.snd).to₂).dom_re
  obtain ⟨c, hc⟩ := TauCeti.Enumeration.rePred_iff_exists_code.1 hg
  have hdec : ∀ (x : α) (y : β), r (x, y) ↔ (c.eval (encode (x, y))).Dom := fun x y => by
    simpa [encodek, Part.dom_iff_mem] using hc (encode (x, y))
  have heval : Computable fun p : (α × ℕ) × β =>
      (c.evaln p.1.2.unpair.2 (encode (p.1.1, p.2))).isSome :=
    Primrec.option_isSome.to_comp.comp <| Nat.Partrec.Code.primrec_evaln.to_comp.comp <|
      ((Computable.snd.comp (Computable.unpair.comp (Computable.snd.comp Computable.fst))).pair
        (Computable.const c)).pair
        (Computable.encode.comp ((Computable.fst.comp Computable.fst).pair Computable.snd))
  have htest : ComputablePred fun q : α × ℕ =>
      ∃ y : β, decode (α := β) q.2.unpair.1 = some y ∧
        (c.evaln q.2.unpair.2 (encode (q.1, y))).isSome = true :=
    ComputablePred.exists_eq_some_and
      (Computable.decode.comp (Computable.fst.comp (Computable.unpair.comp Computable.snd)))
      heval.computablePred
  refine (ComputablePred.rePred_exists
    (p := fun x k => ∃ y : β, decode (α := β) k.unpair.1 = some y ∧
      (c.evaln k.unpair.2 (encode (x, y))).isSome = true) htest).of_eq fun x => ?_
  simp only [hdec, Nat.Partrec.Code.eval_eq_rfindOpt, Nat.rfindOpt_dom, Option.mem_def,
    ← Option.isSome_iff_exists]
  exact ⟨fun ⟨k, y, _, hk⟩ => ⟨y, k.unpair.2, hk⟩,
    fun ⟨y, s, hs⟩ => ⟨Nat.pair (encode y) s, y, by simp [encodek], by simpa using hs⟩⟩

end REPred

namespace Partrec

/-- Membership in the graph `f.graph` of a partial computable function is c.e. -/
theorem rePred_mem_graph {β : Type*} [Primcodable β] {f : α →. β} (hf : Partrec f) :
    REPred (· ∈ f.graph) := by
  let : DecidableEq β := Encodable.decidableEqOfEncodable β
  have heq : REPred fun p : β × β => p.1 = p.2 :=
    (Primrec.eq.decide.to_comp.comp Computable.fst Computable.snd).computablePred.to_re.of_eq
      fun _ => by simp
  exact ((hf.comp Computable.fst).bind
    (heq.comp (Computable.snd.pair (Computable.snd.comp Computable.fst))).to₂).dom_re.of_eq
    fun p => by simp [PFun.graph, Part.dom_iff_mem]

/-- The range of a partial computable function is c.e. -/
theorem rePred_mem_ran {β : Type*} [Primcodable β] {f : α →. β} (hf : Partrec f) :
    REPred (· ∈ f.ran) :=
  (REPred.exists (hf.rePred_mem_graph.comp (Computable.snd.pair Computable.fst))).of_eq fun y => by
    simp [PFun.ran, PFun.graph]

/-- The image of a c.e. set under a partial computable function is c.e. -/
theorem rePred_mem_image {β : Type*} [Primcodable β] {f : α →. β} {S : Set α}
    (hf : Partrec f) (hS : REPred (· ∈ S)) : REPred (· ∈ f.image S) := by
  have hS' : REPred fun p : β × α => p.2 ∈ S := hS.comp Computable.snd
  have hgr : REPred fun p : β × α => (p.2, p.1) ∈ f.graph :=
    hf.rePred_mem_graph.comp (Computable.snd.pair Computable.fst)
  exact (REPred.exists (hS'.and hgr)).of_eq fun y => by
    simp [PFun.mem_image, PFun.graph]

/-- The preimage of a c.e. set under a partial computable function is c.e. -/
theorem rePred_mem_preimage {β : Type*} [Primcodable β] {f : α →. β} {S : Set β}
    (hf : Partrec f) (hS : REPred (· ∈ S)) : REPred (· ∈ f.preimage S) :=
  (hf.bind (hS.comp Computable.snd).to₂).dom_re.of_eq fun x => by
    simp [PFun.mem_preimage, Part.dom_iff_mem, and_comm]

end Partrec

namespace Computable

/-- The range of a total computable function is c.e. -/
theorem rePred_mem_range {β : Type*} [Primcodable β] {f : α → β} (hf : Computable f) :
    REPred (· ∈ Set.range f) := by
  have hf' : Partrec (f : α →. β) := hf.partrec
  simpa only [PFun.ran_coe] using hf'.rePred_mem_ran

/-- The image of a c.e. set under a total computable function is c.e. -/
theorem rePred_mem_image {β : Type*} [Primcodable β] {f : α → β} {S : Set α}
    (hf : Computable f) (hS : REPred (· ∈ S)) : REPred (· ∈ f '' S) :=
  (hf.partrec.rePred_mem_image hS).of_eq fun y => by
    simp [PFun.mem_image, Set.mem_image, PFun.coe_val, eq_comm]

end Computable

namespace Set

/-- Membership in a finite subset of a primitive-codable type is computable. -/
theorem Finite.computablePred {A : Set α} (hA : A.Finite) : ComputablePred (· ∈ A) :=
  hA.primrecPred.computablePred

/-- Every set whose membership predicate is not computable is infinite. -/
theorem Infinite.of_not_computablePred {A : Set α} (h : ¬ComputablePred (· ∈ A)) : A.Infinite :=
  fun hfin => h hfin.computablePred

end Set

/-- Membership in a fixed column `e.pairColumn` is computable. -/
theorem Nat.computablePred_mem_pairColumn (e : ℕ) : ComputablePred (· ∈ e.pairColumn) :=
  (Primrec.mem_pairColumn.comp (.const e) .id).computablePred
