/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.SingleOracle.Universal
import TauCeti.Data.PFun.Basic

/-!
# Uniform parameter compilation and recursion for oracle programs

`Code.curry` specializes the first input of an oracle program. Both this compiler and
`Code.fixedPoint`, the self-reference compiler, are primitive recursive on programs and do
not depend on the oracle. Their semantic equations hold even for partial oracles.
In particular, the fixed-point compiler supplies its own program number as data, rather than
extracting a program from an extensional relative-computability proof.

`Code.fixed_point` is the corresponding Rogers theorem: every computable transformation of
programs has one semantic fixed point simultaneously for all total oracles. Totality is needed
only for the Rogers theorems, because they use the universal oracle interpreter.
The parameterized versions `Code.fixedPointParam` and `Code.fixed_point_param` retain a free
numerical parameter while supplying the index of each specialized program to its own computation.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, I.3 and III.1.
* M. Carneiro, *Formalizing computability theory via partial recursive functions*, ITP 2019.
  The parameter compiler follows Mathlib's `Nat.Partrec.Code.curry`; self-reference uses the
  usual diagonal specialization of that compiler. Ordinary constant programs and their
  effectiveness certificates are reused from Mathlib, not reimplemented.
-/

public section

open Encodable Denumerable

namespace TauCeti.Oracle.Single.Code

/-- Specialize a program's first input to `a`, leaving the second input free. -/
def curry (c : Code) (a : ℕ) : Code :=
  comp c (pair (Nat.Partrec.Code.const a).toSingleOracleCode (pair left right))

/-- Parameter specialization preserves evaluation, uniformly for every partial oracle. -/
@[simp]
theorem eval_curry (O : ℕ →. ℕ) (c : Code) (a x : ℕ) :
    eval O (curry c a) x = eval O c (Nat.pair a x) := by
  simp [curry, Nat.Partrec.Code.eval_const, Seq.seq]

/-- The parameter compiler is primitive recursive on programs and parameters. -/
theorem primrec₂_curry : Primrec₂ curry :=
  primrec₂_comp.comp Primrec.fst <| primrec₂_pair.comp
    (Nat.Partrec.Code.primrec_toSingleOracleCode.comp
      (Nat.Partrec.Code.primrec_const.comp Primrec.snd))
    (Primrec.const (pair left right))

/-- Specialization retains both the source program and the parameter in its syntax. -/
theorem curry_inj {c d : Code} {a b : ℕ} (h : curry c a = curry d b) :
    c = d ∧ a = b := by
  simp only [curry, Code.comp.injEq, Code.pair.injEq] at h
  exact ⟨h.1, Nat.Partrec.Code.const_inj
    (Nat.Partrec.Code.toSingleOracleCode_injective h.2.1)⟩

/-! ### A self-reference compiler -/

/-- The number of the specialization of the program numbered `n` to `n`. -/
private def diagonal (n : ℕ) : ℕ :=
  encode (curry (ofNat Code n) n)

private theorem primrec_diagonal : Primrec diagonal :=
  Primrec.encode.comp (primrec₂_curry.comp (Primrec.ofNat Code) Primrec.id)

/-- One fixed ordinary program computes diagonal specialization. -/
private noncomputable def diagonalCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.1 primrec_diagonal.to_comp.partrec).choose

private theorem eval_diagonalCode (n : ℕ) :
    diagonalCode.eval n = Part.some (diagonal n) := by
  have h := (Nat.Partrec.Code.exists_code.1 primrec_diagonal.to_comp.partrec).choose_spec
  simpa [diagonalCode] using congrFun h n

/-- On input `⟨n,x⟩`, call `c` with `⟨diagonal(n),x⟩`. -/
private noncomputable def recursionBody (c : Code) : Code :=
  comp c (pair (comp diagonalCode.toSingleOracleCode left) right)

private theorem primrec_recursionBody : Primrec recursionBody :=
  primrec₂_comp.comp Primrec.id (Primrec.const _)

private theorem eval_recursionBody (O : ℕ →. ℕ) (c : Code) (n x : ℕ) :
    eval O (recursionBody c) (Nat.pair n x) = eval O c (Nat.pair (diagonal n) x) := by
  simp [recursionBody, eval_diagonalCode, Seq.seq]

/-- A primitive recursive self-reference compiler. The resulting program runs `c` with its
own number as the first input. The chosen ordinary diagonal program is fixed once and for all. -/
noncomputable def fixedPoint (c : Code) : Code :=
  curry (recursionBody c) (encode (recursionBody c))

/-- Self-reference is a primitive recursive transformation of program syntax. -/
theorem primrec_fixedPoint : Primrec fixedPoint :=
  primrec₂_curry.comp primrec_recursionBody (Primrec.encode.comp primrec_recursionBody)

/-- The compiled program supplies its own number to `c`, for every partial oracle. -/
@[simp]
theorem eval_fixedPoint (O : ℕ →. ℕ) (c : Code) (x : ℕ) :
    eval O (fixedPoint c) x = eval O c (Nat.pair (encode (fixedPoint c)) x) := by
  rw [fixedPoint, eval_curry, eval_recursionBody]
  simp only [diagonal, ofNat_encode]

/-! ### Self-reference with a free parameter -/

/-- Given a program number and a parameter, return the specialized program number. -/
private def specialize (n : ℕ) : ℕ :=
  encode (curry (ofNat Code n.unpair.1) n.unpair.2)

private theorem primrec_specialize : Primrec specialize :=
  Primrec.encode.comp (primrec₂_curry.comp
    ((Primrec.ofNat Code).comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair))

private noncomputable def specializeCode : Nat.Partrec.Code :=
  (Nat.Partrec.Code.exists_code.1 primrec_specialize.to_comp.partrec).choose

private theorem eval_specializeCode (n a : ℕ) :
    specializeCode.eval (Nat.pair n a) = Part.some (encode (curry (ofNat Code n) a)) := by
  have h := (Nat.Partrec.Code.exists_code.1 primrec_specialize.to_comp.partrec).choose_spec
  simpa [specializeCode, specialize] using congrFun h (Nat.pair n a)

/-- Rearrange `⟨self,⟨a,x⟩⟩` into `⟨a,⟨specialize(self,a),x⟩⟩`. -/
private noncomputable def parameterBody (c : Code) : Code :=
  comp c (pair (comp left right)
    (pair (comp specializeCode.toSingleOracleCode (pair left (comp left right)))
      (comp right right)))

private theorem primrec_parameterBody : Primrec parameterBody :=
  primrec₂_comp.comp Primrec.id (Primrec.const _)

private theorem eval_parameterBody (O : ℕ →. ℕ) (c : Code) (n a x : ℕ) :
    eval O (parameterBody c) (Nat.pair n (Nat.pair a x)) =
      eval O c (Nat.pair a (Nat.pair (encode (curry (ofNat Code n) a)) x)) := by
  simp [parameterBody, eval_specializeCode, Seq.seq]

/-- The parameterized self-reference compiler. On input `x` the compiled program passes
`⟨a,⟨its own number,x⟩⟩` to `c`. -/
noncomputable def fixedPointParam (c : Code) (a : ℕ) : Code :=
  curry (fixedPoint (parameterBody c)) a

/-- Parameterized self-reference is primitive recursive in both the source and the parameter. -/
theorem primrec₂_fixedPointParam : Primrec₂ fixedPointParam :=
  primrec₂_curry.comp
    (primrec_fixedPoint.comp (primrec_parameterBody.comp Primrec.fst)) Primrec.snd

/-- The specialized program supplies its own, parameter-specific number, not the number of
the unspecialized family. The equation holds for every partial oracle. -/
@[simp]
theorem eval_fixedPointParam (O : ℕ →. ℕ) (c : Code) (a x : ℕ) :
    eval O (fixedPointParam c a) x =
      eval O c (Nat.pair a (Nat.pair (encode (fixedPointParam c a)) x)) := by
  rw [fixedPointParam, eval_curry, eval_fixedPoint, eval_parameterBody]
  simp only [ofNat_encode]

/-! ### Rogers' theorem -/

/-- The parameterized Rogers theorem. A computable family of program transformations admits
a primitive recursive family of fixed points, uniformly for all total oracles. -/
theorem fixed_point_param {f : ℕ → Code → Code} (hf : Computable₂ f) :
    ∃ g : ℕ → Code, Primrec g ∧ ∀ (O : ℕ → ℕ) a,
      eval (O : ℕ →. ℕ) (f a (g a)) = eval (O : ℕ →. ℕ) (g a) := by
  have h : Computable fun n : ℕ => encode (f n.unpair.1 (ofNat Code n.unpair.2)) :=
    Computable.encode.comp (hf.comp (Computable.fst.comp Computable.unpair)
      ((Computable.ofNat Code).comp (Computable.snd.comp Computable.unpair)))
  obtain ⟨t, ht⟩ := Nat.Partrec.Code.exists_code.1 h.partrec
  have ht' (a n : ℕ) : t.eval (Nat.pair a n) = Part.some (encode (f a (ofNat Code n))) := by
    simpa using congrFun ht (Nat.pair a n)
  let body := comp universal
    (pair (comp t.toSingleOracleCode (pair left (comp left right))) (comp right right))
  refine ⟨fixedPointParam body,
    primrec₂_fixedPointParam.comp (Primrec.const body) Primrec.id, fun O a => funext fun x => ?_⟩
  rw [eval_fixedPointParam]
  simp [body, ht', Seq.seq]

/-- Every computable transformation of oracle programs has a single semantic fixed point
simultaneously for all total oracles. The program is chosen before the oracle. -/
theorem fixed_point {f : Code → Code} (hf : Computable f) :
    ∃ c : Code, ∀ O : ℕ → ℕ, eval (O : ℕ →. ℕ) (f c) = eval (O : ℕ →. ℕ) c := by
  obtain ⟨g, -, hg⟩ := fixed_point_param (f := fun _ c => f c) (hf.comp Computable.snd)
  exact ⟨g 0, fun O => hg O 0⟩

end TauCeti.Oracle.Single.Code
