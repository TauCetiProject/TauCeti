/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Jump.Basic
import TauCeti.Computability.RecursiveIn

/-!
# Totalizing partial oracle computations in the Turing jump

Let `f : α →. β` be a partial function between primitive-codable types that is recursive in the
set oracle `Z.oracle`. The jump `Z.jump` decides the halting domain `{a | (f a).Dom}`, while `Z`
itself reduces to `Z.jump`. Combining a `Z.jump`-computable guard with `Nat.RecursiveIn.cond`,
which evaluates only the selected branch, totalizes `f` relative to `Z.jump` as the option-valued
function `fun a => (f a).toOption`: it returns `some y` when `y ∈ f a` and `none` when `f a`
diverges.

Specializing to unrelativized partial recursive functions and c.e. predicates shows that every jump
`Z.jump` (in particular `(∅ : Set ℕ).jump`) computes `(f a).toOption` for `Partrec f` and decides
every `REPred` predicate. This is the effective search-and-branch primitive used in `∅'`-computable
finite-extension constructions.

## Main results

* `RecursiveIn.computableIn_jump_toOption`: if `f` is recursive in `Z.oracle`, then
  `fun a => (f a).toOption` is total computable in `Z.jump.oracle`.
* `RecursiveIn.computableIn_jump_dom`: if `f` is recursive in `Z.oracle`, then `Z.jump.oracle`
  decides `(f a).Dom`.
* `Partrec.computableIn_jump_toOption`, `Partrec.computableIn_jump_dom`: unrelativized forms for
  partial recursive functions relative to any jump `Z.jump`.
* `REPred.computableIn_jump`: every jump `Z.jump` decides every c.e. predicate on a
  primitive-codable type.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter III.2.
-/

public section

open Encodable

namespace RecursiveIn

/-- **Totalizing in the jump.** If `f : α →. β` is recursive in `Z.oracle`, then its option-valued
totalization `fun a => (f a).toOption` is computable in `Z.jump.oracle`: query `Z.jump` to decide
whether `f a` halts, and evaluate `f a` only when it does. -/
theorem computableIn_jump_toOption {α β : Type*} [Primcodable α] [Primcodable β]
    {Z : Set ℕ} {f : α →. β} [∀ a, Decidable (f a).Dom] (hf : RecursiveIn {Z.oracle} f) :
    ComputableIn {Z.jump.oracle} fun a => (f a).toOption := by
  let F : ℕ →. ℕ := fun n => Part.bind (decode (α := α) n) fun a => (f a).map encode
  have hF_jump : Nat.RecursiveIn {Z.jump.oracle} F :=
    Nat.RecursiveIn.subst hf fun _ hg =>
      (Set.mem_singleton_iff.1 hg) ▸ RecursiveIn.iff_nat.1 Z.turingReducible_jump
  have : DecidablePred fun n => (F n).Dom := Classical.decPred _
  have hchi : ComputableIn {Z.jump.oracle} ({n | (F n).Dom}.indicator 1 : ℕ → ℕ) :=
    ({n | (F n).Dom}.turingReducible_iff_computableIn_indicator Z.jump.oracle).1
      (Z.turingReducible_jump_of_recursiveIn hf)
  have hc : ComputableIn {Z.jump.oracle} fun n => decide (F n).Dom :=
    RecursiveIn.of_eq ((Primrec.beq.comp Primrec.id (Primrec.const 1)).computableIn.comp hchi)
      fun n => by by_cases hn : (F n).Dom <;> simp [hn]
  have hsome : Nat.RecursiveIn {Z.jump.oracle}
      fun n => (F n).map fun m => encode (decode (α := β) m) :=
    hF_jump.map_primrec (Primrec.nat_iff.1 (Primrec.encode.comp (Primrec.decode (α := β))))
  have hnone : Nat.Partrec fun n =>
      Part.bind (Part.ofOption (decode (α := α) n))
        fun _ => Part.some (encode (none : Option β)) :=
    Partrec.nat_iff.1 <|
      (((Primrec.decode (α := α)).to_comp.ofOption).map
        (Computable.const (encode (none : Option β))).to₂).of_eq fun n => by
          cases decode (α := α) n <;> simp
  refine (Nat.RecursiveIn.cond hc hsome hnone.recursiveIn).of_eq fun n => ?_
  cases hdec : decode (α := α) n with
  | none => simp [F, hdec]
  | some a =>
    by_cases ha : (f a).Dom
    · obtain ⟨b, hb⟩ := Part.dom_iff_mem.1 ha
      have hFn : F n = Part.some (encode b) := by
        simp [F, hdec, Part.eq_some_iff.2 hb]
      have hto : (f a).toOption = some b := Part.toOption_eq_some_iff.2 hb
      simp [hFn, hto, encodek]
    · have hFn : F n = Part.none := by
        simp [F, hdec, Part.eq_none_iff'.2 ha]
      have hto : (f a).toOption = none := Part.toOption_eq_none_iff.2 ha
      simp [hFn, hto]

/-- **Deciding relative halting domains in the jump.** If `f : α →. β` is recursive in `Z.oracle`,
then `Z.jump.oracle` computes `fun a => decide (f a).Dom`. -/
theorem computableIn_jump_dom {α β : Type*} [Primcodable α] [Primcodable β]
    {Z : Set ℕ} {f : α →. β} [DecidablePred fun a => (f a).Dom]
    (hf : RecursiveIn {Z.oracle} f) :
    ComputableIn {Z.jump.oracle} fun a => decide (f a).Dom :=
  RecursiveIn.of_eq (Primrec.option_isSome.computableIn.comp hf.computableIn_jump_toOption)
    fun a => congrArg Part.some (Bool.eq_iff_iff.2 (by simp))

end RecursiveIn

namespace Partrec

/-- Every jump `Z.jump` computes the option-valued totalization `fun a => (f a).toOption` of a
partial recursive function `f`. -/
theorem computableIn_jump_toOption {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α →. β} [∀ a, Decidable (f a).Dom] (hf : Partrec f) (Z : Set ℕ) :
    ComputableIn {Z.jump.oracle} fun a => (f a).toOption :=
  hf.recursiveIn.computableIn_jump_toOption

/-- Every jump `Z.jump` decides the halting domain of a partial recursive function `f`. -/
theorem computableIn_jump_dom {α β : Type*} [Primcodable α] [Primcodable β]
    {f : α →. β} [DecidablePred fun a => (f a).Dom] (hf : Partrec f) (Z : Set ℕ) :
    ComputableIn {Z.jump.oracle} fun a => decide (f a).Dom :=
  hf.recursiveIn.computableIn_jump_dom

end Partrec

namespace REPred

/-- Every jump `Z.jump` decides every c.e. predicate on a primitive-codable type. -/
theorem computableIn_jump {α : Type*} [Primcodable α] {p : α → Prop} [DecidablePred p]
    (hp : REPred p) (Z : Set ℕ) :
    ComputableIn {Z.jump.oracle} fun a => decide (p a) := by
  classical
  exact RecursiveIn.of_eq
    (Partrec.computableIn_jump_dom (f := fun a => Part.assert (p a) fun _ => Part.some ()) hp Z)
    fun a => by simp [Part.assert]

end REPred
