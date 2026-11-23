/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Computability.Primrec.List
public import Mathlib.ModelTheory.Encoding
public import TauCeti.Logic.Equiv.List

/-!
# Natural-number codes of bounded formulas

The code `φ.code` of a bounded formula `φ` with `n` bound variables is the natural-number code
of the pair `(n, φ.listEncode)`, where `φ.listEncode` is Mathlib's encoding of `φ` as a list of
letters (`FirstOrder.Language.BoundedFormula.listEncode`), and pairs, lists, sums, dependent
pairs and terms carry Mathlib's `Encodable` instances. No other encoding of formulas is
introduced, and formulas get no `Encodable` instance. The number of bound variables is explicit
in the code (`unpair_code_fst`), so formulas with different numbers of bound variables have
different codes (`code_sigma_injective`); sentences are the formulas coded with `n = 0` over the
empty variable type.

The letters of the list encoding are terms, relation symbols and natural numbers. Mathlib's
encoding of sums tags them: a term letter has an even code, a relation letter a code congruent to
`1` modulo `4`, and the number `k` the code `4 * k + 3`. The letters `0` and `1` mark implication
and universal quantification, and `n + 2` is falsum with `n` bound variables, so these have the
letter codes `3`, `7` and `4 * n + 11`. Since the code of a list depends only on the codes of its
letters, falsum, implication and universal quantification act on codes by explicit operations on
natural numbers, `TauCeti.FormulaCode.bot`, `TauCeti.FormulaCode.imp` and
`TauCeti.FormulaCode.all`, which do not depend on the language or on the variables and are
primitive recursive. The derived connectives `¬`, `⊤`, `⊓`, `⊔`, `↔` and `∃` are compositions of
these, following Mathlib's definitions.

## Main definitions and results

* `FirstOrder.Language.BoundedFormula.code`: the code of a bounded formula.
* `FirstOrder.Language.BoundedFormula.code_sigma_injective`: the code is injective on bounded
  formulas with any number of bound variables.
* `TauCeti.FormulaCode.bot`, `imp`, `all`, `not`, `top`, `inf`, `sup`, `iff`, `ex`: the
  connectives and quantifiers on codes, with `TauCeti.FormulaCode.primrec_bot`,
  `primrec₂_imp`, `primrec_all`, … stating that they are primitive recursive.
* `FirstOrder.Language.BoundedFormula.code_bot`, `code_imp`, `code_all`, …: the code of a
  compound formula is the corresponding operation applied to the codes of its parts.

The operations on codes are only meaningful on codes of formulas with matching numbers of bound
variables; elsewhere they take junk values.

## Implementation notes

The statements assume only `Encodable` structures on the variables and on the function and
relation symbols; the term letters then carry Mathlib's `Encodable` instances for terms and for
dependent pairs. The connectives are given as functions on codes, rather than by existence
statements, so that later constructions can compose them.

The lemmas `code_bot`, `code_imp`, … are not simp lemmas: `code_inj` is, and rewriting the two
sides of an equation of codes into operations on codes would hide the formulas it compares.

## References

The list encoding of formulas is that of `Mathlib.ModelTheory.Encoding`. The language of groups
with coefficients, whose formulas these codes are meant for, is that of Kharlampovich and
Myasnikov, *Implicit function theorem over free groups*, §2.3.
-/

public section

open Encodable Denumerable

namespace TauCeti.FormulaCode

/-- The code of falsum with `n` bound variables. -/
protected def bot (n : ℕ) : ℕ :=
  Nat.pair n (encode [4 * n + 11])

/-- Implication on codes of formulas: from the codes of `φ` and `ψ`, which have the same number
of bound variables, the code of `φ.imp ψ`. -/
protected def imp (c d : ℕ) : ℕ :=
  Nat.pair c.unpair.1 (encode (3 :: (ofNat (List ℕ) c.unpair.2 ++ ofNat (List ℕ) d.unpair.2)))

/-- Universal quantification on codes of formulas: from the code of `φ`, which has `n + 1` bound
variables, the code of `φ.all`. -/
protected def all (c : ℕ) : ℕ :=
  Nat.pair (c.unpair.1 - 1) (encode (7 :: ofNat (List ℕ) c.unpair.2))

/-- Negation on codes of formulas. -/
protected def not (c : ℕ) : ℕ :=
  FormulaCode.imp c (FormulaCode.bot c.unpair.1)

/-- The code of verum with `n` bound variables. -/
protected def top (n : ℕ) : ℕ :=
  FormulaCode.not (FormulaCode.bot n)

/-- Conjunction on codes of formulas with the same number of bound variables. -/
protected def inf (c d : ℕ) : ℕ :=
  FormulaCode.not (FormulaCode.imp c (FormulaCode.not d))

/-- Disjunction on codes of formulas with the same number of bound variables. -/
protected def sup (c d : ℕ) : ℕ :=
  FormulaCode.imp (FormulaCode.not c) d

/-- The biconditional on codes of formulas with the same number of bound variables. -/
protected def iff (c d : ℕ) : ℕ :=
  FormulaCode.inf (FormulaCode.imp c d) (FormulaCode.imp d c)

/-- Existential quantification on codes of formulas: from the code of `φ`, which has `n + 1`
bound variables, the code of `φ.ex`. -/
protected def ex (c : ℕ) : ℕ :=
  FormulaCode.not (FormulaCode.all (FormulaCode.not c))

theorem bot_def (n : ℕ) : FormulaCode.bot n = Nat.pair n (encode [4 * n + 11]) := (rfl)

theorem imp_def (c d : ℕ) : FormulaCode.imp c d = Nat.pair c.unpair.1
    (encode (3 :: (ofNat (List ℕ) c.unpair.2 ++ ofNat (List ℕ) d.unpair.2))) := (rfl)

theorem all_def (c : ℕ) : FormulaCode.all c =
    Nat.pair (c.unpair.1 - 1) (encode (7 :: ofNat (List ℕ) c.unpair.2)) := (rfl)

theorem not_def (c : ℕ) :
    FormulaCode.not c = FormulaCode.imp c (FormulaCode.bot c.unpair.1) := (rfl)

theorem top_def (n : ℕ) : FormulaCode.top n = FormulaCode.not (FormulaCode.bot n) := (rfl)

theorem inf_def (c d : ℕ) :
    FormulaCode.inf c d = FormulaCode.not (FormulaCode.imp c (FormulaCode.not d)) := (rfl)

theorem sup_def (c d : ℕ) : FormulaCode.sup c d = FormulaCode.imp (FormulaCode.not c) d := (rfl)

theorem iff_def (c d : ℕ) :
    FormulaCode.iff c d = FormulaCode.inf (FormulaCode.imp c d) (FormulaCode.imp d c) := (rfl)

theorem ex_def (c : ℕ) :
    FormulaCode.ex c = FormulaCode.not (FormulaCode.all (FormulaCode.not c)) := (rfl)

@[simp]
theorem unpair_bot_fst (n : ℕ) : (FormulaCode.bot n).unpair.1 = n := by
  simp [bot_def]

@[simp]
theorem unpair_imp_fst (c d : ℕ) : (FormulaCode.imp c d).unpair.1 = c.unpair.1 := by
  simp [imp_def]

@[simp]
theorem unpair_all_fst (c : ℕ) : (FormulaCode.all c).unpair.1 = c.unpair.1 - 1 := by
  simp [all_def]

@[simp]
theorem unpair_not_fst (c : ℕ) : (FormulaCode.not c).unpair.1 = c.unpair.1 := by
  simp [not_def]

@[simp]
theorem unpair_top_fst (n : ℕ) : (FormulaCode.top n).unpair.1 = n := by
  simp [top_def]

@[simp]
theorem unpair_inf_fst (c d : ℕ) : (FormulaCode.inf c d).unpair.1 = c.unpair.1 := by
  simp [inf_def]

@[simp]
theorem unpair_sup_fst (c d : ℕ) : (FormulaCode.sup c d).unpair.1 = c.unpair.1 := by
  simp [sup_def]

@[simp]
theorem unpair_iff_fst (c d : ℕ) : (FormulaCode.iff c d).unpair.1 = c.unpair.1 := by
  simp [iff_def]

@[simp]
theorem unpair_ex_fst (c : ℕ) : (FormulaCode.ex c).unpair.1 = c.unpair.1 - 1 := by
  simp [ex_def]

/-- The code of falsum is primitive recursive in the number of bound variables. -/
theorem primrec_bot : Primrec FormulaCode.bot :=
  Primrec₂.natPair.comp .id <| Primrec.encode.comp <| Primrec.list_cons.comp
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 4) .id) (.const 11)) (.const [])

/-- Implication is primitive recursive on codes. -/
theorem primrec₂_imp : Primrec₂ FormulaCode.imp := by
  have hl : Primrec fun c : ℕ => ofNat (List ℕ) c.unpair.2 :=
    (Primrec.ofNat _).comp (Primrec.snd.comp Primrec.unpair)
  exact Primrec₂.natPair.comp (Primrec.fst.comp (Primrec.unpair.comp .fst)) <|
    Primrec.encode.comp <| Primrec.list_cons.comp (.const 3) <|
      Primrec.list_append.comp (hl.comp .fst) (hl.comp .snd)

/-- Universal quantification is primitive recursive on codes. -/
theorem primrec_all : Primrec FormulaCode.all :=
  Primrec₂.natPair.comp
    (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.unpair) (.const 1)) <|
    Primrec.encode.comp <| Primrec.list_cons.comp (.const 7) <|
      (Primrec.ofNat _).comp (Primrec.snd.comp Primrec.unpair)

/-- Negation is primitive recursive on codes. -/
theorem primrec_not : Primrec FormulaCode.not :=
  primrec₂_imp.comp .id (primrec_bot.comp (Primrec.fst.comp Primrec.unpair))

/-- The code of verum is primitive recursive in the number of bound variables. -/
theorem primrec_top : Primrec FormulaCode.top :=
  primrec_not.comp primrec_bot

/-- Conjunction is primitive recursive on codes. -/
theorem primrec₂_inf : Primrec₂ FormulaCode.inf :=
  primrec_not.comp (primrec₂_imp.comp .fst (primrec_not.comp .snd))

/-- Disjunction is primitive recursive on codes. -/
theorem primrec₂_sup : Primrec₂ FormulaCode.sup :=
  primrec₂_imp.comp (primrec_not.comp .fst) .snd

/-- The biconditional is primitive recursive on codes. -/
theorem primrec₂_iff : Primrec₂ FormulaCode.iff :=
  primrec₂_inf.comp (primrec₂_imp.comp .fst .snd) (primrec₂_imp.comp .snd .fst)

/-- Existential quantification is primitive recursive on codes. -/
theorem primrec_ex : Primrec FormulaCode.ex :=
  primrec_not.comp (primrec_all.comp primrec_not)

end TauCeti.FormulaCode

namespace FirstOrder.Language.BoundedFormula

open TauCeti

universe u v w

variable {L : Language.{u, v}} {α : Type w} {n : ℕ}
variable [Encodable α] [Encodable (Σ i, L.Functions i)] [Encodable (Σ i, L.Relations i)]

/-- The code of a bounded formula with `n` bound variables: the natural-number code of the pair
of `n` and Mathlib's list encoding of the formula. -/
def code (φ : L.BoundedFormula α n) : ℕ :=
  encode (n, φ.listEncode)

theorem code_def (φ : L.BoundedFormula α n) : φ.code = encode (n, φ.listEncode) := (rfl)

/-- The number of bound variables is the first component of the code. -/
@[simp]
theorem unpair_code_fst (φ : L.BoundedFormula α n) : φ.code.unpair.1 = n := by
  simp [code_def]

/-- The second component of the code is the code of the list encoding. -/
@[simp]
theorem unpair_code_snd (φ : L.BoundedFormula α n) :
    φ.code.unpair.2 = encode φ.listEncode := by
  simp [code_def]

/-- Bounded formulas, with any numbers of bound variables, are determined by their codes. -/
theorem code_sigma_injective :
    Function.Injective fun φ : Σ n, L.BoundedFormula α n => φ.2.code :=
  fun _ _ h => listEncode_sigma_injective (congrArg Prod.snd (encode_injective h))

/-- Bounded formulas with `n` bound variables are determined by their codes. -/
theorem code_injective : Function.Injective (code : L.BoundedFormula α n → ℕ) :=
  fun φ ψ h => by simpa using code_sigma_injective (a₁ := ⟨n, φ⟩) (a₂ := ⟨n, ψ⟩) h

@[simp]
theorem code_inj {φ ψ : L.BoundedFormula α n} : φ.code = ψ.code ↔ φ = ψ :=
  code_injective.eq_iff

/-- The code of falsum. -/
theorem code_bot : (⊥ : L.BoundedFormula α n).code = FormulaCode.bot n := by
  simp [code_def, FormulaCode.bot_def, listEncode]
  omega

/-- The code of an implication. -/
theorem code_imp (φ ψ : L.BoundedFormula α n) :
    (φ.imp ψ).code = FormulaCode.imp φ.code ψ.code := by
  simp [FormulaCode.imp_def, code_def, listEncode, ← List.map_append]

/-- The code of a universally quantified formula. -/
theorem code_all (φ : L.BoundedFormula α (n + 1)) : φ.all.code = FormulaCode.all φ.code := by
  simp [FormulaCode.all_def, code_def, listEncode]

/-- The code of a negation. -/
theorem code_not (φ : L.BoundedFormula α n) : φ.not.code = FormulaCode.not φ.code := by
  rw [BoundedFormula.not, code_imp, code_bot, FormulaCode.not_def, unpair_code_fst]

/-- The code of verum. -/
theorem code_top : (⊤ : L.BoundedFormula α n).code = FormulaCode.top n := by
  -- Mathlib defines `⊤` as `BoundedFormula.not ⊥` and has no lemma unfolding it.
  change (BoundedFormula.not ⊥ : L.BoundedFormula α n).code = _
  rw [code_not, code_bot, FormulaCode.top_def]

/-- The code of a conjunction. -/
theorem code_inf (φ ψ : L.BoundedFormula α n) :
    (φ ⊓ ψ).code = FormulaCode.inf φ.code ψ.code := by
  -- Mathlib defines `φ ⊓ ψ` as `(φ.imp ψ.not).not` and has no lemma unfolding it.
  change (φ.imp ψ.not).not.code = _
  rw [code_not, code_imp, code_not, FormulaCode.inf_def]

/-- The code of a disjunction. -/
theorem code_sup (φ ψ : L.BoundedFormula α n) :
    (φ ⊔ ψ).code = FormulaCode.sup φ.code ψ.code := by
  -- Mathlib defines `φ ⊔ ψ` as `φ.not.imp ψ` and has no lemma unfolding it.
  change (φ.not.imp ψ).code = _
  rw [code_imp, code_not, FormulaCode.sup_def]

/-- The code of a biconditional. -/
theorem code_iff (φ ψ : L.BoundedFormula α n) :
    (φ.iff ψ).code = FormulaCode.iff φ.code ψ.code := by
  rw [BoundedFormula.iff, code_inf, code_imp, code_imp, FormulaCode.iff_def]

/-- The code of an existentially quantified formula. -/
theorem code_ex (φ : L.BoundedFormula α (n + 1)) : φ.ex.code = FormulaCode.ex φ.code := by
  rw [BoundedFormula.ex, code_not, code_all, code_not, FormulaCode.ex_def]

/-! ### Checks

The marker letters of implication and of universal quantification and the falsum letters have
pairwise distinct codes, different from the codes of all term and relation letters; and codes of
small formulas are explicit numbers, the same for every language and every variable type. -/

section Checks

/-- The alphabet of the list encoding of bounded formulas. -/
local notation "Γ" => (Σ k, L.Term (α ⊕ Fin k)) ⊕ ((Σ n, L.Relations n) ⊕ ℕ)

example (k : ℕ) : encode (Sum.inr (Sum.inr k) : Γ) = 4 * k + 3 := by
  simp only [encode_inr, encode_nat]; omega

example (R : Σ n, L.Relations n) : encode (Sum.inr (Sum.inl R) : Γ) = 4 * encode R + 1 := by
  simp only [encode_inr, encode_inl]; omega

example (t : Σ k, L.Term (α ⊕ Fin k)) : encode (Sum.inl t : Γ) = 2 * encode t := encode_inl t

/-- Term letters carry Mathlib's codes: the pair of the number of bound variables and the code of
Mathlib's list encoding of the term. -/
example (k : ℕ) (t : L.Term (α ⊕ Fin k)) :
    encode (⟨k, t⟩ : Σ k, L.Term (α ⊕ Fin k)) = Nat.pair k (encode t.listEncode) := rfl

example : (⊥ : L.BoundedFormula α 0).code = 17689 := by
  rw [code_bot, FormulaCode.bot_def]
  decide

example : (⊥ : L.BoundedFormula α 1).all.code = 3374331921 := by
  rw [code_all, code_bot, FormulaCode.all_def, FormulaCode.bot_def, Nat.unpair_pair, ofNat_encode]
  decide

example : ((⊥ : L.BoundedFormula α 0).imp ⊥).code = 98172809418414025 := by
  rw [code_imp, code_bot, FormulaCode.imp_def, FormulaCode.bot_def, Nat.unpair_pair, ofNat_encode]
  decide

example (φ ψ : L.BoundedFormula α n) (χ : L.BoundedFormula α (n + 1)) :
    (φ.imp ψ).code ≠ χ.all.code := by
  simp

end Checks

end FirstOrder.Language.BoundedFormula

/-- The code of a sentence is the code of a formula without bound variables over the empty
variable type. -/
example {L : FirstOrder.Language} [Encodable (Σ i, L.Functions i)]
    [Encodable (Σ i, L.Relations i)] (σ : L.Sentence) :
    σ.code = Encodable.encode (0, σ.listEncode) :=
  σ.code_def
