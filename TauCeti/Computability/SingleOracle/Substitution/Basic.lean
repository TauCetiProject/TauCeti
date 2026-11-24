/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code

/-!
# Substitution of an oracle program

`c.subst d` replaces every oracle instruction in `c` with the program `d`. Relative to an
oracle `O`, it computes what `c` computes relative to the partial function computed by `d`
in `O`. The compiler is primitive recursive in both programs and its evaluation equation
holds simultaneously for all partial oracles.

The semantic closure under substitution is the indexed counterpart of
`Nat.RecursiveIn.subst`. See R. I. Soare, *Recursively Enumerable Sets and Degrees*,
Springer, 1987, Chapter III.1.
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
  induction c with
  | zero | succ | left | right | oracle =>
    funext n
    simp
  | pair cf cg hf hg | comp cf cg hf hg =>
    funext n
    simp [hf, hg]
  | prec cf cg hf hg =>
    funext n
    obtain ⟨a, k, rfl⟩ : ∃ a k, n = Nat.pair a k := ⟨_, _, (Nat.pair_unpair n).symm⟩
    simp only [prec_subst]
    induction k with
    | zero => simp only [eval_prec_zero, hf]
    | succ k ih => simp only [eval_prec_succ, ih, hg]
  | rfind' cf hf =>
    funext n
    obtain ⟨a, m, rfl⟩ : ∃ a m, n = Nat.pair a m := ⟨_, _, (Nat.pair_unpair n).symm⟩
    simp only [rfind'_subst, eval_rfind', hf]

private theorem primrec_lookup_subst (ctor : Code → Code → Code) (hctor : Primrec₂ ctor) :
    Primrec₂ fun (p : Code × List Code) (cs : Code × Code) =>
      Option.map₂ ctor p.2[encode cs.1]? p.2[encode cs.2]? := by
  have hl : Primrec fun p : (Code × List Code) × (Code × Code) => p.1.2 :=
    snd.comp fst
  have hf := list_getElem?.comp hl (Primrec.encode.comp (fst.comp snd))
  have hg := list_getElem?.comp hl (Primrec.encode.comp (snd.comp snd))
  unfold Option.map₂
  exact (option_bind hf (option_map (hg.comp fst) (hctor.comp (snd.comp fst) snd).to₂).to₂).to₂

-- The proof uses Mathlib's `Primrec.nat_strong_rec`. The recursion table is analogous to the
-- one in `Nat.Partrec.Code.primrec_recOn'` for ordinary programs.
/-- Query substitution is primitive recursive jointly in the source and query programs. -/
theorem primrec₂_subst : Primrec₂ subst := by
  let step (p : Code × List Code) : Option Code :=
    Code.casesOn (ofNat Code p.2.length) (some zero) (some succ) (some left) (some right) (some p.1)
      (fun cf cg => Option.map₂ pair p.2[encode cf]? p.2[encode cg]?)
      (fun cf cg => Option.map₂ comp p.2[encode cf]? p.2[encode cg]?)
      (fun cf cg => Option.map₂ prec p.2[encode cf]? p.2[encode cg]?)
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
  induction c <;> rw [toSingleOracleCode_def] <;> simp_all

end Nat.Partrec.Code

namespace TauCeti.Oracle.Single.Code

/-- Substitution commutes with fixing an input, since the constant program makes no query. -/
@[simp]
theorem fixInput_subst (c d : Code) (x : ℕ) :
    (c.fixInput x).subst d = (c.subst d).fixInput x := by
  simp [fixInput_def]

/-- Substitution commutes with parameter specialization, since the program supplying the
parameter makes no query. -/
@[simp]
theorem curry_subst (c d : Code) (a : ℕ) : (c.curry a).subst d = (c.subst d).curry a := by
  simp [curry_def]

end TauCeti.Oracle.Single.Code
