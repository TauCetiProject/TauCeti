/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.Basic
public import TauCeti.ModelTheory.LanguageMap

/-!
# Primitive encodings of the symbols of a first-order language

Mathlib's list encodings (`Mathlib.ModelTheory.Encoding`) spell a term or a formula as a list of
symbols. Reading such a list back requires the arity of every symbol, so the encodings are
primitive recursive only when the dependent pairs `Σ n, L.Functions n` and `Σ n, L.Relations n`
of symbols with their arities are primitively encoded and the arity `Sigma.fst` is primitive
recursive. This file records the two arity conditions as classes,
`FirstOrder.Language.PrimrecFunctionArity` and `FirstOrder.Language.PrimrecRelationArity`, and
supplies them

* for a language with added constants `L[[A]]`, whose function symbols are coded as a function
  symbol of `L` or a constant from `A` (`FirstOrder.Language.sigmaFunctionsWithConstantsEquiv`);
* for an algebraic language, whose type of relation symbols is empty and keeps Mathlib's
  encoding.
-/

public section

universe u v w

namespace FirstOrder.Language

open Encodable

/-- The arity of a function symbol is a primitive recursive function of the symbol. -/
class PrimrecFunctionArity (L : Language.{u, v}) [Primcodable (Σ n, L.Functions n)] : Prop where
  /-- The arity of a function symbol is primitive recursive. -/
  primrec_fst : Primrec (Sigma.fst : (Σ n, L.Functions n) → ℕ)

/-- The arity of a relation symbol is a primitive recursive function of the symbol. -/
class PrimrecRelationArity (L : Language.{u, v}) [Primcodable (Σ n, L.Relations n)] : Prop where
  /-- The arity of a relation symbol is primitive recursive. -/
  primrec_fst : Primrec (Sigma.fst : (Σ n, L.Relations n) → ℕ)

variable {L : Language.{u, v}} (A : Type w)

section Functions

variable [Primcodable (Σ n, L.Functions n)] [Primcodable A]

/-- Function symbols of `L[[A]]` are coded as function symbols of `L` or elements of `A`. -/
instance instPrimcodableSigmaFunctionsWithConstants : Primcodable (Σ n, L[[A]].Functions n) :=
  Primcodable.ofEquiv _ (sigmaFunctionsWithConstantsEquiv A)

/-- The code of a function symbol of `L[[A]]` is the code of its description as a function
symbol of `L` or a constant from `A`. -/
theorem encode_sigmaFunctionsWithConstants (s : Σ n, L[[A]].Functions n) :
    encode s = encode (sigmaFunctionsWithConstantsEquiv A s) :=
  (rfl)

instance [L.PrimrecFunctionArity] : L[[A]].PrimrecFunctionArity where
  primrec_fst := by
    have h : Primrec fun s : (Σ n, L.Functions n) ⊕ A => Sum.elim Sigma.fst (fun _ => 0) s :=
      (Primrec.sumCasesOn .id (PrimrecFunctionArity.primrec_fst.comp .snd).to₂
        (Primrec.const 0).to₂).of_eq fun s => by cases s <;> rfl
    exact (h.comp Primrec.of_equiv).of_eq (elim_fst_sigmaFunctionsWithConstantsEquiv A)

end Functions

/-- An algebraic language has no relation symbols, so Mathlib's encoding of the empty type of
its relation symbols with their arities is primitive recursive. -/
instance instPrimcodableSigmaRelationsOfIsAlgebraic [L.IsAlgebraic] :
    Primcodable (Σ n, L.Relations n) :=
  { (inferInstance : Encodable (Σ n, L.Relations n)) with
    prim := Nat.Primrec.zero.of_eq fun n => by
      cases decode (α := Σ n, L.Relations n) n with
      | none => rfl
      | some R => exact isEmptyElim R }

instance [L.IsAlgebraic] : L.PrimrecRelationArity where
  primrec_fst := (Primrec.const 0).of_eq fun R => isEmptyElim R

end FirstOrder.Language
