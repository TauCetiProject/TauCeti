/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.Basic
public import TauCeti.ModelTheory.LanguageMap

/-!
# Primitive encodings of the function symbols of a first-order language

Mathlib's list encoding of terms (`Mathlib.ModelTheory.Encoding`) spells a term as a list of
variables and function symbols, and reading such a list back uses the arity of every function
symbol. This file records, as the class `FirstOrder.Language.PrimrecFunctionArity`, the condition
that the arity `Sigma.fst` is primitive recursive on the primitively encoded function symbols
`Σ n, L.Functions n`. Together with primitively encoded variables, this condition suffices for
the encoding of terms to be primitive recursive (`FirstOrder.Language.Term.instPrimcodable`).

For a language with added constants `L[[A]]`, the file codes a function symbol as a function
symbol of `L` or a constant from `A` (`FirstOrder.Language.sigmaFunctionsWithConstantsEquiv`).
This gives an encoding of the function symbols of `L[[A]]` for encoded `Σ n, L.Functions n` and
`A`, which is primitive for primitively encoded ones, and the arity condition for `L[[A]]`.
-/

public section

universe u v w

namespace FirstOrder.Language

open Encodable

/-- The arity of a function symbol is a primitive recursive function of the symbol. -/
class PrimrecFunctionArity (L : Language.{u, v}) [Primcodable (Σ n, L.Functions n)] : Prop where
  /-- The arity of a function symbol is primitive recursive. -/
  primrec_fst : Primrec (Sigma.fst : (Σ n, L.Functions n) → ℕ)

variable {L : Language.{u, v}} (A : Type w)

section Encodable

variable [Encodable (Σ n, L.Functions n)] [Encodable A]

/-- Function symbols of `L[[A]]` are coded as function symbols of `L` or elements of `A`. -/
instance instEncodableSigmaFunctionsWithConstants : Encodable (Σ n, L[[A]].Functions n) :=
  Encodable.ofEquiv _ (sigmaFunctionsWithConstantsEquiv A)

/-- The code of a function symbol of `L[[A]]` is the code of its description as a function
symbol of `L` or a constant from `A`. -/
theorem encode_sigmaFunctionsWithConstants (s : Σ n, L[[A]].Functions n) :
    encode s = encode (sigmaFunctionsWithConstantsEquiv A s) :=
  encode_ofEquiv _ s

end Encodable

variable [Primcodable (Σ n, L.Functions n)] [Primcodable A]

/-- Function symbols of `L[[A]]` are primitively coded as function symbols of `L` or elements
of `A`; the code is that of `FirstOrder.Language.instEncodableSigmaFunctionsWithConstants`. -/
instance instPrimcodableSigmaFunctionsWithConstants : Primcodable (Σ n, L[[A]].Functions n) :=
  Primcodable.ofEquiv _ (sigmaFunctionsWithConstantsEquiv A)

/-- The primitive encoding of the function symbols of `L[[A]]` is their encoding. -/
theorem toEncodable_instPrimcodableSigmaFunctionsWithConstants :
    (Primcodable.toEncodable : Encodable (Σ n, L[[A]].Functions n)) =
      instEncodableSigmaFunctionsWithConstants A :=
  (rfl)

instance [L.PrimrecFunctionArity] : L[[A]].PrimrecFunctionArity where
  primrec_fst := by
    have h : Primrec fun s : (Σ n, L.Functions n) ⊕ A => Sum.elim Sigma.fst (fun _ => 0) s :=
      (Primrec.sumCasesOn .id (PrimrecFunctionArity.primrec_fst.comp .snd).to₂
        (Primrec.const 0).to₂).of_eq fun s => by cases s <;> rfl
    exact (h.comp Primrec.of_equiv).of_eq (sumElim_fst_sigmaFunctionsWithConstantsEquiv A)

end FirstOrder.Language
