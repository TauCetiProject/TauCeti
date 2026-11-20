/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code
-- The semantic proof uses the function-valued equations of the evaluator.
import all TauCeti.Computability.SingleOracle.Code

/-!
# Substitution of an oracle program

`c.subst d` replaces every oracle instruction in `c` with the program `d`. Relative to an
oracle `O`, it computes what `c` computes relative to the partial function computed by `d`
in `O`. The compiler is primitive recursive in both programs and its evaluation equation
holds simultaneously for all partial oracles.

The semantic closure under substitution is the indexed counterpart of
`Nat.RecursiveIn.subst`. See R. I. Soare, *Recursively Enumerable Sets and Degrees*,
Springer, 1987, Chapter III.1.

The proof of primitive recursiveness uses Mathlib's `Primrec.nat_strong_rec`.
The recursion table is analogous to the one in `Nat.Partrec.Code.primrec_recOn'`
for ordinary programs.
-/

public section

open Encodable Denumerable Primrec

namespace TauCeti.Oracle.Single.Code

/-- Replace each oracle instruction in the source program by the supplied query program. -/
def subst : Code → Code → Code
  | zero, _ => zero
  | succ, _ => succ
  | left, _ => left
  | right, _ => right
  | oracle, d => d
  | pair cf cg, d => pair (cf.subst d) (cg.subst d)
  | comp cf cg, d => comp (cf.subst d) (cg.subst d)
  | prec cf cg, d => prec (cf.subst d) (cg.subst d)
  | rfind' cf, d => rfind' (cf.subst d)

@[simp]
theorem zero_subst (d : Code) : zero.subst d = zero := (rfl)
@[simp]
theorem succ_subst (d : Code) : succ.subst d = succ := (rfl)
@[simp]
theorem left_subst (d : Code) : left.subst d = left := (rfl)
@[simp]
theorem right_subst (d : Code) : right.subst d = right := (rfl)
@[simp]
theorem oracle_subst (d : Code) : oracle.subst d = d := (rfl)
@[simp]
theorem pair_subst (cf cg d : Code) :
    (pair cf cg).subst d = pair (cf.subst d) (cg.subst d) := (rfl)

@[simp]
theorem comp_subst (cf cg d : Code) :
    (comp cf cg).subst d = comp (cf.subst d) (cg.subst d) := (rfl)

@[simp]
theorem prec_subst (cf cg d : Code) :
    (prec cf cg).subst d = prec (cf.subst d) (cg.subst d) := (rfl)

@[simp]
theorem rfind'_subst (cf d : Code) : (rfind' cf).subst d = rfind' (cf.subst d) := (rfl)

/-- The oracle instruction is the identity for substitution on the right. -/
@[simp]
theorem subst_oracle (c : Code) : c.subst oracle = c := by
  induction c <;> simp_all

/-- Substituting into the replacement before inserting it gives the same program as
substituting afterward. -/
theorem subst_assoc (c d e : Code) : (c.subst d).subst e = c.subst (d.subst e) := by
  induction c <;> simp_all

/-- Evaluation of a substituted program interprets the source oracle by the query program.
The equality includes divergence, even when the intermediate oracle is partial. -/
@[simp]
theorem eval_subst (O : ℕ →. ℕ) (c d : Code) :
    eval O (c.subst d) = eval (eval O d) c := by
  induction c <;> simp [eval, *] <;> rfl

private theorem primrec_lookup_subst (ctor : Code → Code → Code) (hctor : Primrec₂ ctor) :
    Primrec₂ fun (p : Code × List Code) (cs : Code × Code) =>
      p.2[encode cs.1]?.bind fun cf => p.2[encode cs.2]?.map (ctor cf) := by
  have hl : Primrec fun p : (Code × List Code) × (Code × Code) => p.1.2 :=
    snd.comp fst
  have hf := list_getElem?.comp hl (Primrec.encode.comp (fst.comp snd))
  have hg := list_getElem?.comp hl (Primrec.encode.comp (snd.comp snd))
  exact (option_bind hf (option_map (hg.comp fst) (hctor.comp (snd.comp fst) snd).to₂).to₂).to₂

/-- Query substitution is primitive recursive jointly in the source and query programs. -/
theorem primrec₂_subst : Primrec₂ subst := by
  let step (p : Code × List Code) : Option Code :=
    Code.casesOn (ofNat Code p.2.length) (some zero) (some succ) (some left) (some right) (some p.1)
      (fun cf cg => p.2[encode cf]?.bind fun f => p.2[encode cg]?.map (pair f))
      (fun cf cg => p.2[encode cf]?.bind fun f => p.2[encode cg]?.map (comp f))
      (fun cf cg => p.2[encode cf]?.bind fun f => p.2[encode cg]?.map (prec f))
      (fun cf => p.2[encode cf]?.map rfind')
  have hstep : Primrec step :=
    primrec_casesOn ((Primrec.ofNat _).comp (list_length.comp snd))
      (const _) (const _) (const _) (const _) (option_some.comp fst)
      (primrec_lookup_subst _ primrec₂_pair) (primrec_lookup_subst _ primrec₂_comp)
      (primrec_lookup_subst _ primrec₂_prec)
      (option_map (list_getElem?.comp (snd.comp fst) (Primrec.encode.comp snd))
        (primrec_rfind'.comp snd).to₂).to₂
  have h := nat_strong_rec (fun d n => (ofNat Code n).subst d) hstep.to₂ ?_
  · exact (h.comp snd (Primrec.encode.comp fst)).to₂.of_eq fun c d => by simp
  · intro d n
    have hencode : Function.Surjective (encode : Code → ℕ) := (Denumerable.eqv Code).surjective
    obtain ⟨c, rfl⟩ := hencode n
    cases c with
    | zero | succ | left | right | oracle => simp [step]
    | pair cf cg => simp [step, (encode_lt_pair cf cg).1, (encode_lt_pair cf cg).2]
    | comp cf cg => simp [step, (encode_lt_comp cf cg).1, (encode_lt_comp cf cg).2]
    | prec cf cg => simp [step, (encode_lt_prec cf cg).1, (encode_lt_prec cf cg).2]
    | rfind' cf => simp [step, encode_lt_rfind']

end TauCeti.Oracle.Single.Code

namespace Nat.Partrec.Code

/-- An ordinary program contains no oracle instruction for substitution to replace. -/
@[simp]
theorem toSingleOracleCode_subst (c : Nat.Partrec.Code) (d : TauCeti.Oracle.Single.Code) :
    c.toSingleOracleCode.subst d = c.toSingleOracleCode := by
  induction c <;> simp [toSingleOracleCode, *]

end Nat.Partrec.Code
