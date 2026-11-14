/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.ModelTheory.Algebra.Group.Basic
public import TauCeti.ModelTheory.Encoding.Term

/-!
# Primitive encodings of group terms

The three function symbols of the language of groups are coded by `Fin 3`, in the order
identity, inverse, multiplication, so that the code of a symbol is its arity. With Mathlib's
encoding of terms this makes the terms of `Language.group` and of the coefficient languages
`Language.group[[A]]` primitively encoded, for primitively encoded coefficient names `A` and
variables.

Two properties of the codes of group terms are recorded, for any encoded coefficient names and
variables. The multiplication symbol alone, without its two arguments, spells no term and its
code decodes to no term: missing arguments are not filled in. The code of a variable is
Mathlib's code of the one-letter list.

The language is that of Kharlampovich and Myasnikov, *Implicit function theorem over free
groups*, §2.3; the encoding of terms is the one of `Mathlib.ModelTheory.Encoding`.
-/

public section

open FirstOrder Language

namespace TauCeti.Group

/-- The function symbols of the language of groups, listed as identity, inverse,
multiplication. The number of a symbol is its arity. -/
def sigmaFunctionsEquiv : (Σ n, Language.group.Functions n) ≃ Fin 3 where
  toFun
    | ⟨_, .one⟩ => 0
    | ⟨_, .inv⟩ => 1
    | ⟨_, .mul⟩ => 2
  invFun
    | 0 => ⟨0, oneFunc⟩
    | 1 => ⟨1, invFunc⟩
    | 2 => ⟨2, mulFunc⟩
  left_inv := by rintro ⟨_, f⟩; cases f <;> rfl
  right_inv
    | 0 => rfl
    | 1 => rfl
    | 2 => rfl

@[simp] theorem sigmaFunctionsEquiv_one : sigmaFunctionsEquiv ⟨0, oneFunc⟩ = 0 := (rfl)

@[simp] theorem sigmaFunctionsEquiv_inv : sigmaFunctionsEquiv ⟨1, invFunc⟩ = 1 := (rfl)

@[simp] theorem sigmaFunctionsEquiv_mul : sigmaFunctionsEquiv ⟨2, mulFunc⟩ = 2 := (rfl)

@[simp] theorem sigmaFunctionsEquiv_symm_zero : sigmaFunctionsEquiv.symm 0 = ⟨0, oneFunc⟩ := (rfl)

@[simp] theorem sigmaFunctionsEquiv_symm_one : sigmaFunctionsEquiv.symm 1 = ⟨1, invFunc⟩ := (rfl)

@[simp] theorem sigmaFunctionsEquiv_symm_two : sigmaFunctionsEquiv.symm 2 = ⟨2, mulFunc⟩ := (rfl)

/-- The number of a function symbol of the language of groups is its arity. -/
@[simp]
theorem val_sigmaFunctionsEquiv (s : Σ n, Language.group.Functions n) :
    (sigmaFunctionsEquiv s : ℕ) = s.1 := by
  rcases s with ⟨_, f⟩
  cases f <;> rfl

/-- The function symbols of the language of groups are coded by `Fin 3`. -/
instance : Primcodable (Σ n, Language.group.Functions n) :=
  Primcodable.ofEquiv (Fin 3) sigmaFunctionsEquiv

/-- The code of a function symbol of the language of groups is its arity. -/
theorem encode_sigmaFunctions (s : Σ n, Language.group.Functions n) :
    Encodable.encode s = s.1 := by
  simp [Encodable.encode_ofEquiv, Encodable.Subtype.encode_eq]

instance : Language.group.PrimrecFunctionArity where
  primrec_fst := (Primrec.fin_val.comp Primrec.of_equiv).of_eq val_sigmaFunctionsEquiv

end TauCeti.Group

namespace FirstOrder.Language.group

open TauCeti.Group

variable {A X : Type*}

/-- The multiplication symbol alone, without its two arguments, does not spell a group term. -/
@[simp]
theorem listEncode_ne_singleton_mul (t : Language.group[[A]].Term X) :
    t.listEncode ≠ [Sum.inr ⟨2, Sum.inl mulFunc⟩] :=
  Term.listEncode_ne_singleton_inr_add_one _ t

variable [Encodable A] [Encodable X]

/-- The code of the multiplication symbol alone decodes to no group term: missing arguments
are not filled in. -/
theorem decode_encode_singleton_mul :
    Encodable.decode (α := Language.group[[A]].Term X)
      (Encodable.encode ([Sum.inr ⟨2, Sum.inl mulFunc⟩] :
        List (X ⊕ Σ i, Language.group[[A]].Functions i))) = none :=
  Term.decode_encode_singleton_inr_add_one _

/-- The code of a variable, as a group term, is Mathlib's code of the one-letter list. -/
theorem encode_var (x : X) :
    Encodable.encode (Language.Term.var x : Language.group[[A]].Term X) =
      Encodable.encode ([Sum.inl x] : List (X ⊕ Σ i, Language.group[[A]].Functions i)) :=
  Term.encode_var x

end FirstOrder.Language.group
