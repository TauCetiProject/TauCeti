/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Code
import Mathlib.Data.Set.Finite.Basic

/-!
# Injective padding of oracle programs

`Code.pad c n` runs `c`, pairs its result with the constant `n`, and projects back to the
result. The compiler is primitive recursive and retains both `c` and `n` injectively in its
syntax. Its semantic equation holds simultaneously for every partial oracle, including on
inputs where `c` diverges. In particular every oracle program has infinitely many distinct
indices with the same semantics, and any computable family of programs can be replaced by
an injective computable family without changing any of its oracle computations.

Padding does not preserve simulation fuel or enumeration stages: the extra instructions
cost time. The semantic equations here concern unbounded evaluation only.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, I.3 (the padding
  lemma) and III.1 (oracle computation).
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-- Pad a program with a numerical tag, without changing its partial function for any oracle. -/
def pad (c : Code) (n : ℕ) : Code :=
  comp left (pair c (Nat.Partrec.Code.const n).toSingleOracleCode)

/-- Padding is primitive recursive in both the source program and its tag. -/
theorem primrec₂_pad : Primrec₂ pad :=
  primrec₂_comp.comp (Primrec.const left) <| primrec₂_pair.comp Primrec.fst
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd))

/-- Padding retains both the source program and the tag in its syntax. -/
@[simp]
theorem pad_inj {c d : Code} {m n : ℕ} : pad c m = pad d n ↔ c = d ∧ m = n := by
  constructor
  · intro h
    simp only [pad, Code.comp.injEq, Code.pair.injEq, true_and] at h
    exact ⟨h.1, Nat.Partrec.Code.const_inj
      (Nat.Partrec.Code.toSingleOracleCode_injective h.2)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The two-argument padding compiler is jointly injective. -/
theorem pad_injective : Function.Injective (Function.uncurry pad) := by
  rintro ⟨c, m⟩ ⟨d, n⟩ h
  exact Prod.ext (pad_inj.1 h).1 (pad_inj.1 h).2

/-- Padding leaves evaluation unchanged, for every partial oracle. -/
@[simp]
theorem eval_pad (O : ℕ →. ℕ) (c : Code) (n x : ℕ) :
    eval O (pad c n) x = eval O c x := by
  have hl : eval O left = fun y => Part.some y.unpair.1 := funext eval_left
  simp [pad, hl, Nat.Partrec.Code.eval_const, Seq.seq, Part.bind_assoc]

/-- Every padded program has a larger index than its source. -/
theorem encode_lt_encode_pad (c : Code) (n : ℕ) : encode c < encode (pad c n) :=
  (encode_lt_pair c _).1.trans (encode_lt_comp left _).2

/-- Infinitely many programs agree with `c` simultaneously for all partial oracles. -/
theorem infinite_forall_eval_eq (c : Code) :
    {d : Code | ∀ O : ℕ →. ℕ, eval O d = eval O c}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := pad c) ?_ ?_
  · intro m n h
    exact (pad_inj.1 h).2
  · intro n O
    exact funext fun x => eval_pad O c n x

/-- Any computable family of oracle programs admits an injective computable replacement,
with the same semantics for all partial oracles. No program is extracted from a semantic
relative-computability proof: the original family is supplied as code. -/
theorem exists_injective_forall_eval_eq {f : ℕ → Code} (hf : Computable f) :
    ∃ g : ℕ → Code, Computable g ∧ Function.Injective g ∧
      ∀ (O : ℕ →. ℕ) n, eval O (g n) = eval O (f n) := by
  refine ⟨fun n => pad (f n) n, primrec₂_pad.to_comp.comp hf Computable.id, ?_, ?_⟩
  · intro m n h
    exact (pad_inj.1 h).2
  · intro O n
    exact funext fun x => eval_pad O (f n) n x

end TauCeti.Oracle.Single.Code
