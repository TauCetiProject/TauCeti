/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Basic
public import TauCeti.Computability.SingleOracle.Code
import TauCeti.Data.PFun.Basic

/-!
# Displayed normal-form codes for the arithmetical hierarchy

A displayed normal-form code (`NormalForm`) represents a predicate in the arithmetical hierarchy
by explicit syntactic data: an alternating number-quantifier prefix (`QuantifierPrefix`), the
number of free numerical parameters (`arity`), and a single-oracle program (`matrix`) computing a
Boolean matrix relative to the oracle.

At quantifier depth zero, the existential and universal classes coincide, so `QuantifierPrefix`
has one quantifier-free constructor `qf` together with positive-depth alternating blocks `sigma n`
(starting with `∃` and having `n + 1` quantifiers) and `pi n` (starting with `∀` and having
`n + 1` quantifiers). Free tuples use `ArityTuple`: `Unit` at arity `0`, `ℕ` at arity `1`, and
left-nested `Nat.pair` products `ArityTuple (k + 1) × ℕ` at arity `k + 2`, matching the variable
binding convention of `IsSigma` and `IsPi`.

Totality of the matrix on `{0, 1}` is a semantic promise (`NormalForm.Valid`), not a decidable test
on programs. Under this promise, valid normal-form codes of prefix `sigmaOf n` (respectively
`piOf n`) define predicates in `IsSigma Z n` (respectively `IsPi Z n`), and conversely every
predicate in those pointclasses admits a valid normal-form code. Complementation (`NormalForm.not`)
is a primitive-recursive code transformation that exchanges `sigma` and `pi` prefixes and negates
the Boolean matrix without consulting the oracle.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
* M. Carneiro, *Formalizing computability theory via partial recursive functions*, ITP 2019.
-/

public section

open Encodable Denumerable Primrec TauCeti.Oracle.Single

namespace TauCeti.ArithmeticalHierarchy

/-! ### Alternating quantifier prefixes -/

/-- Alternating number-quantifier prefixes for displayed arithmetical normal forms:
`qf` has zero quantifiers, `sigma n` has `n + 1` alternating quantifiers beginning with `∃`,
and `pi n` has `n + 1` alternating quantifiers beginning with `∀`. -/
inductive QuantifierPrefix : Type
  | qf : QuantifierPrefix
  | sigma : ℕ → QuantifierPrefix
  | pi : ℕ → QuantifierPrefix
  deriving DecidableEq, Repr

namespace QuantifierPrefix

instance : Inhabited QuantifierPrefix := ⟨.qf⟩

/-- Total number of bound number quantifiers in the prefix. -/
def depth : QuantifierPrefix → ℕ
  | qf => 0
  | sigma n => n + 1
  | pi n => n + 1

/-- Dual quantifier prefix obtained by exchanging `∃` and `∀` at every position. -/
def neg : QuantifierPrefix → QuantifierPrefix
  | qf => qf
  | sigma n => pi n
  | pi n => sigma n

/-- The canonical prefix of Σ⁰ₙ: quantifier-free at `0` and `sigma m` at `m + 1`. -/
def sigmaOf : ℕ → QuantifierPrefix
  | 0 => qf
  | m + 1 => sigma m

/-- The canonical prefix of Π⁰ₙ: quantifier-free at `0` and `pi m` at `m + 1`. -/
def piOf : ℕ → QuantifierPrefix
  | 0 => qf
  | m + 1 => pi m

/-- Prefix resulting from prepending an existential quantifier and contracting adjacent `∃`s. -/
def addExists : QuantifierPrefix → QuantifierPrefix
  | qf => sigma 0
  | sigma n => sigma n
  | pi n => sigma (n + 1)

/-- Prefix resulting from prepending a universal quantifier and contracting adjacent `∀`s. -/
def addForall : QuantifierPrefix → QuantifierPrefix
  | qf => pi 0
  | pi n => pi n
  | sigma n => pi (n + 1)

/-- Whether a positive-depth prefix begins with an existential quantifier (`false` on `qf`). -/
def startsExists : QuantifierPrefix → Bool
  | qf => false
  | sigma _ => true
  | pi _ => false

@[simp] theorem depth_qf : qf.depth = 0 := (rfl)
@[simp] theorem depth_sigma (n : ℕ) : (sigma n).depth = n + 1 := (rfl)
@[simp] theorem depth_pi (n : ℕ) : (pi n).depth = n + 1 := (rfl)

@[simp] theorem startsExists_qf : qf.startsExists = false := (rfl)
@[simp] theorem startsExists_sigma (n : ℕ) : (sigma n).startsExists = true := (rfl)
@[simp] theorem startsExists_pi (n : ℕ) : (pi n).startsExists = false := (rfl)

@[simp] theorem neg_qf : qf.neg = qf := (rfl)
@[simp] theorem neg_sigma (n : ℕ) : (sigma n).neg = pi n := (rfl)
@[simp] theorem neg_pi (n : ℕ) : (pi n).neg = sigma n := (rfl)

/-- Prefix duality is an involution. -/
@[simp]
theorem neg_neg (p : QuantifierPrefix) : p.neg.neg = p := by
  cases p <;> rfl

/-- Prefix duality preserves quantifier depth. -/
@[simp]
theorem depth_neg (p : QuantifierPrefix) : p.neg.depth = p.depth := by
  cases p <;> rfl

@[simp] theorem sigmaOf_zero : sigmaOf 0 = qf := (rfl)
@[simp] theorem sigmaOf_succ (n : ℕ) : sigmaOf (n + 1) = sigma n := (rfl)
@[simp] theorem piOf_zero : piOf 0 = qf := (rfl)
@[simp] theorem piOf_succ (n : ℕ) : piOf (n + 1) = pi n := (rfl)

/-- `sigmaOf n` has quantifier depth `n`. -/
@[simp]
theorem depth_sigmaOf (n : ℕ) : (sigmaOf n).depth = n := by
  cases n <;> rfl

/-- `piOf n` has quantifier depth `n`. -/
@[simp]
theorem depth_piOf (n : ℕ) : (piOf n).depth = n := by
  cases n <;> rfl

/-- Negating the Σ⁰ₙ prefix yields the Π⁰ₙ prefix. -/
@[simp]
theorem neg_sigmaOf (n : ℕ) : (sigmaOf n).neg = piOf n := by
  cases n <;> rfl

/-- Negating the Π⁰ₙ prefix yields the Σ⁰ₙ prefix. -/
@[simp]
theorem neg_piOf (n : ℕ) : (piOf n).neg = sigmaOf n := by
  cases n <;> rfl

@[simp] theorem addExists_qf : qf.addExists = sigma 0 := (rfl)
@[simp] theorem addExists_sigma (n : ℕ) : (sigma n).addExists = sigma n := (rfl)
@[simp] theorem addExists_pi (n : ℕ) : (pi n).addExists = sigma (n + 1) := (rfl)

@[simp] theorem addForall_qf : qf.addForall = pi 0 := (rfl)
@[simp] theorem addForall_pi (n : ℕ) : (pi n).addForall = pi n := (rfl)
@[simp] theorem addForall_sigma (n : ℕ) : (sigma n).addForall = pi (n + 1) := (rfl)

/-- De Morgan duality exchanges existential and universal prefix extension. -/
@[simp]
theorem neg_addExists (p : QuantifierPrefix) : p.addExists.neg = p.neg.addForall := by
  cases p <;> rfl

/-- De Morgan duality exchanges universal and existential prefix extension. -/
@[simp]
theorem neg_addForall (p : QuantifierPrefix) : p.addForall.neg = p.neg.addExists := by
  cases p <;> rfl

/-- Explicit numerical encoding of quantifier prefixes: `0` codes `qf`, odd numbers code `sigma`,
and positive even numbers code `pi`. -/
def encodePrefix : QuantifierPrefix → ℕ
  | qf => 0
  | sigma n => 2 * n + 1
  | pi n => 2 * n + 2

/-- Inverse of `encodePrefix`. -/
def ofNatPrefix : ℕ → QuantifierPrefix
  | 0 => qf
  | m + 1 => if m % 2 = 0 then sigma (m / 2) else pi (m / 2)

/-- Decoding any natural number and re-encoding recovers the number. -/
@[simp]
theorem encodePrefix_ofNatPrefix : ∀ k, encodePrefix (ofNatPrefix k) = k
  | 0 => rfl
  | m + 1 => by
    simp only [ofNatPrefix]
    split_ifs with h <;> simp [encodePrefix] <;> omega

/-- Encoding a prefix and decoding recovers the prefix. -/
@[simp]
theorem ofNatPrefix_encodePrefix : ∀ p, ofNatPrefix (encodePrefix p) = p
  | qf => rfl
  | sigma n => by
    have h1 : (2 * n) % 2 = 0 := by omega
    have h2 : (2 * n) / 2 = n := by omega
    simp [encodePrefix, ofNatPrefix, h1, h2]
  | pi n => by
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [encodePrefix, ofNatPrefix, h2]

instance : Denumerable QuantifierPrefix :=
  Denumerable.mk'
    { toFun := encodePrefix
      invFun := ofNatPrefix
      left_inv := ofNatPrefix_encodePrefix
      right_inv := encodePrefix_ofNatPrefix }

theorem encode_eq_encodePrefix : (encode : QuantifierPrefix → ℕ) = encodePrefix := (rfl)
theorem ofNat_eq_ofNatPrefix : ofNat QuantifierPrefix = ofNatPrefix := (rfl)

/-- The `sigma` prefix constructor is primitive recursive. -/
theorem primrec_sigma : Primrec sigma :=
  Primrec.encode_iff.1 <|
    (nat_add.comp (nat_mul.comp (const 2) .id) (const 1)).of_eq fun _ => rfl

/-- The `pi` prefix constructor is primitive recursive. -/
theorem primrec_pi : Primrec pi :=
  Primrec.encode_iff.1 <|
    (nat_add.comp (nat_mul.comp (const 2) .id) (const 2)).of_eq fun _ => rfl

/-- Case analysis on `QuantifierPrefix` is primitive recursive, uniformly in a parameter. -/
theorem primrec_casesOn {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → QuantifierPrefix} (hp : Primrec p) {q : α → β} (hq : Primrec q)
    {fs fp : α → ℕ → β} (hs : Primrec₂ fs) (hpi : Primrec₂ fp) :
    Primrec fun a =>
      QuantifierPrefix.casesOn (motive := fun _ => β) (p a) (q a) (fs a) (fp a) := by
  have he : Primrec fun a => encode (p a) := Primrec.encode.comp hp
  have hm : Primrec fun a => encode (p a) - 1 := nat_sub.comp he (const 1)
  have hidx : Primrec fun a => (encode (p a) - 1) / 2 := nat_div.comp hm (const 2)
  refine (Primrec.ite (Primrec.eq.comp he (const 0)) hq <|
    Primrec.ite (Primrec.eq.comp (nat_mod.comp hm (const 2)) (const 0))
      (hs.comp .id hidx) (hpi.comp .id hidx)).of_eq fun a => ?_
  cases p a with
  | qf => rfl
  | sigma n =>
    have h2 : (2 * n) / 2 = n := by omega
    simp [encode_eq_encodePrefix, encodePrefix, h2]
  | pi n =>
    have h2 : (2 * n + 1) / 2 = n := by omega
    simp [encode_eq_encodePrefix, encodePrefix, h2]

/-- Quantifier depth is primitive recursive. -/
theorem primrec_depth : Primrec depth :=
  (primrec_casesOn .id (const 0) (Primrec.succ.comp snd).to₂ (Primrec.succ.comp snd).to₂).of_eq
    fun p => by cases p <;> rfl

/-- Testing whether a prefix starts with an existential quantifier is primitive recursive. -/
theorem primrec_startsExists : Primrec startsExists :=
  (primrec_casesOn .id (const false) (const true).to₂ (const false).to₂).of_eq
    fun p => by cases p <;> rfl

/-- Prefix negation is primitive recursive. -/
theorem primrec_neg : Primrec neg :=
  (primrec_casesOn .id (const qf) (primrec_pi.comp snd).to₂ (primrec_sigma.comp snd).to₂).of_eq
    fun p => by cases p <;> rfl

/-- Forming the Σ⁰ₙ prefix from `n` is primitive recursive. -/
theorem primrec_sigmaOf : Primrec sigmaOf :=
  (nat_casesOn .id (const qf) (primrec_sigma.comp snd).to₂).of_eq fun n => by cases n <;> rfl

/-- Forming the Π⁰ₙ prefix from `n` is primitive recursive. -/
theorem primrec_piOf : Primrec piOf :=
  (nat_casesOn .id (const qf) (primrec_pi.comp snd).to₂).of_eq fun n => by cases n <;> rfl

/-- Prepending an existential quantifier with contraction is primitive recursive. -/
theorem primrec_addExists : Primrec addExists :=
  (primrec_casesOn .id (const (sigma 0)) (primrec_sigma.comp snd).to₂
    (primrec_sigma.comp (Primrec.succ.comp snd)).to₂).of_eq fun p => by cases p <;> rfl

/-- Prepending a universal quantifier with contraction is primitive recursive. -/
theorem primrec_addForall : Primrec addForall :=
  (primrec_casesOn .id (const (pi 0)) (primrec_pi.comp (Primrec.succ.comp snd)).to₂
    (primrec_pi.comp snd).to₂).of_eq fun p => by cases p <;> rfl

end QuantifierPrefix

/-! ### Tuple-arity convention -/

/-- Free-parameter tuple type of arity `k`: `Unit` at `0`, `ℕ` at `1`, and left-nested products
`ArityTuple (k + 1) × ℕ` at `k + 2`. -/
abbrev ArityTuple : ℕ → Type
  | 0 => Unit
  | 1 => ℕ
  | k + 2 => ArityTuple (k + 1) × ℕ

instance instPrimcodableArityTuple : (k : ℕ) → Primcodable (ArityTuple k)
  | 0 => inferInstanceAs (Primcodable Unit)
  | 1 => inferInstanceAs (Primcodable ℕ)
  | k + 2 => @Primcodable.prod _ _ (instPrimcodableArityTuple (k + 1)) inferInstance

/-- Append a natural number to a `k`-tuple, producing a `(k + 1)`-tuple. -/
abbrev ArityTuple.snoc : {k : ℕ} → ArityTuple k → ℕ → ArityTuple (k + 1)
  | 0, (), y => y
  | _ + 1, xs, y => (xs, y)

/-- At arity `0`, appending `y` produces `y` directly as the unary parameter. -/
theorem ArityTuple.snoc_zero (xs : ArityTuple 0) (y : ℕ) :
    ArityTuple.snoc xs y = y := by
  cases xs
  rfl

/-- Encoding `ArityTuple.snoc xs y` at arity `0` yields `y`. -/
theorem ArityTuple.encode_snoc_zero (xs : ArityTuple 0) (y : ℕ) :
    encode (ArityTuple.snoc xs y) = y := by
  cases xs
  simp

/-- At positive arity, appending `y` encodes via `Nat.pair`. -/
@[simp]
theorem ArityTuple.encode_snoc_succ {k : ℕ} (xs : ArityTuple (k + 1)) (y : ℕ) :
    encode (ArityTuple.snoc xs y) = Nat.pair (encode xs) y :=
  (rfl)

/-- Every natural number is the `Encodable.encode` of a `(k + 1)`-tuple. -/
theorem exists_encode_arityTuple_succ : (k a : ℕ) → ∃ xs : ArityTuple (k + 1), encode xs = a
  | 0, a => ⟨a, rfl⟩
  | k + 1, a => by
    obtain ⟨xs, hxs⟩ := exists_encode_arityTuple_succ k a.unpair.1
    refine ⟨(xs, a.unpair.2), ?_⟩
    change Nat.pair (encode xs) a.unpair.2 = a
    rw [hxs, Nat.pair_unpair]

/-! ### Displayed normal-form codes -/

/-- A displayed arithmetical normal-form code: an alternating quantifier prefix, a free-parameter
tuple arity, and an oracle-program index for the quantifier-free Boolean matrix. -/
@[ext]
structure NormalForm where
  /-- Alternating number-quantifier prefix in front of the matrix. -/
  pref : QuantifierPrefix
  /-- Number of free natural-number arguments expected by the normal form. -/
  arity : ℕ
  /-- Single-oracle program computing the Boolean matrix (`0` for `false`, `1` for `true`). -/
  matrix : Code
  deriving DecidableEq

namespace NormalForm

instance : Inhabited NormalForm := ⟨⟨.qf, 0, .zero⟩⟩

/-- Equivalence of `NormalForm` with its triple of syntactic components. -/
def equivTuple : NormalForm ≃ QuantifierPrefix × ℕ × Code where
  toFun c := (c.pref, c.arity, c.matrix)
  invFun t := ⟨t.1, t.2.1, t.2.2⟩
  left_inv c := by cases c; rfl
  right_inv t := by rcases t with ⟨_, _, _⟩; rfl

instance : Denumerable NormalForm :=
  Denumerable.mk' (equivTuple.trans (Denumerable.eqv (QuantifierPrefix × ℕ × Code)))

@[simp]
theorem encode_mk (p : QuantifierPrefix) (k : ℕ) (m : Code) :
    encode (NormalForm.mk p k m) = encode (p, k, m) :=
  (rfl)

private theorem primrec_equivTuple : Primrec equivTuple :=
  Primrec.encode_iff.1 ((Primrec.encode : Primrec (encode : NormalForm → ℕ)).of_eq fun c => by
    cases c; rfl)

/-- Reading the quantifier prefix of a normal-form code is primitive recursive. -/
theorem primrec_pref : Primrec pref :=
  (fst.comp primrec_equivTuple).of_eq fun _ => rfl

/-- Reading the arity of a normal-form code is primitive recursive. -/
theorem primrec_arity : Primrec arity :=
  ((fst.comp snd).comp primrec_equivTuple).of_eq fun _ => rfl

/-- Reading the matrix program of a normal-form code is primitive recursive. -/
theorem primrec_matrix : Primrec matrix :=
  ((snd.comp snd).comp primrec_equivTuple).of_eq fun _ => rfl

/-- Constructing a normal-form code from its three components is primitive recursive. -/
theorem primrec₃_mk {α : Type*} [Primcodable α] {p : α → QuantifierPrefix} {k : α → ℕ}
    {m : α → Code} (hp : Primrec p) (hk : Primrec k) (hm : Primrec m) :
    Primrec fun a => NormalForm.mk (p a) (k a) (m a) :=
  Primrec.encode_iff.1 <| (Primrec.encode.comp (hp.pair (hk.pair hm))).of_eq fun _ => rfl

/-! ### Semantic totality promise and evaluation -/

/-- Structural totality condition over `d` bound number quantifiers starting from base code `a`:
every valuation of the `d` bound variables causes `m` to halt relative to `Z` with `0` or `1`. -/
def ValidDepth (Z : Set ℕ) (m : Code) : ℕ → ℕ → Prop
  | 0, a => ∃ b : Bool, Code.eval Z.oracle m a = Part.some (encode b)
  | d + 1, a => ∀ y, ValidDepth Z m d (Nat.pair a y)

/-- Structural evaluation of `d` alternating number quantifiers starting with polarity `ex`
(`true` for `∃`, `false` for `∀`) over matrix `m` relative to `Z` at base code `a`. -/
def HoldsBlock (Z : Set ℕ) (m : Code) : Bool → ℕ → ℕ → Prop
  | _, 0, a => encode true ∈ Code.eval Z.oracle m a
  | true, d + 1, a => ∃ y, HoldsBlock Z m false d (Nat.pair a y)
  | false, d + 1, a => ∀ y, HoldsBlock Z m true d (Nat.pair a y)

@[simp]
theorem validDepth_zero (Z : Set ℕ) (m : Code) (a : ℕ) :
    ValidDepth Z m 0 a ↔ ∃ b : Bool, Code.eval Z.oracle m a = Part.some (encode b) :=
  Iff.rfl

@[simp]
theorem validDepth_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    ValidDepth Z m (d + 1) a ↔ ∀ y, ValidDepth Z m d (Nat.pair a y) :=
  Iff.rfl

@[simp]
theorem holdsBlock_zero (Z : Set ℕ) (m : Code) (ex : Bool) (a : ℕ) :
    HoldsBlock Z m ex 0 a ↔ encode true ∈ Code.eval Z.oracle m a :=
  Iff.rfl

@[simp]
theorem holdsBlock_true_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    HoldsBlock Z m true (d + 1) a ↔ ∃ y, HoldsBlock Z m false d (Nat.pair a y) :=
  Iff.rfl

@[simp]
theorem holdsBlock_false_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    HoldsBlock Z m false (d + 1) a ↔ ∀ y, HoldsBlock Z m true d (Nat.pair a y) :=
  Iff.rfl

/-- Semantic totality of `m` under prefix `p` at base code `a`. -/
def ValidAux (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) : Prop :=
  ValidDepth Z m p.depth a

/-- Evaluation of prefix `p` and matrix `m` relative to `Z` at base code `a`. -/
def HoldsAux (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) : Prop :=
  HoldsBlock Z m p.startsExists p.depth a

@[simp]
theorem validAux_eq_validDepth (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    ValidAux Z m p a = ValidDepth Z m p.depth a :=
  (rfl)

@[simp]
theorem holdsAux_eq_holdsBlock (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    HoldsAux Z m p a = HoldsBlock Z m p.startsExists p.depth a :=
  (rfl)

theorem holdsAux_sigmaOf (Z : Set ℕ) (m : Code) (n a : ℕ) :
    HoldsAux Z m (.sigmaOf n) a ↔ HoldsBlock Z m true n a := by
  cases n <;> simp

theorem holdsAux_piOf (Z : Set ℕ) (m : Code) (n a : ℕ) :
    HoldsAux Z m (.piOf n) a ↔ HoldsBlock Z m false n a := by
  cases n <;> simp

theorem holdsAux_neg_eq_holdsBlock (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    HoldsAux Z m p.neg a ↔ HoldsBlock Z m (!p.startsExists) p.depth a := by
  cases p <;> simp

/-- Semantic validity promise on `c` relative to `Z`: for every free `c.arity`-tuple and all bound
quantifier values, `c.matrix` halts relative to `Z` with `0` or `1`. -/
def Valid (Z : Set ℕ) (c : NormalForm) : Prop :=
  ∀ xs : ArityTuple c.arity, ValidAux Z c.matrix c.pref (encode xs)

/-- Truth of `c` relative to `Z` on a raw encoded free-parameter value `a`. -/
def HoldsCode (Z : Set ℕ) (c : NormalForm) (a : ℕ) : Prop :=
  HoldsAux Z c.matrix c.pref a

/-- Truth of `c` relative to `Z` on a `k`-tuple via `ArityTuple` encoding. -/
def EvalTuple (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) : Prop :=
  c.HoldsCode Z (encode xs)

/-- The displayed `c.arity`-ary predicate defined by `c` relative to `Z`. -/
def Pred (Z : Set ℕ) (c : NormalForm) (xs : ArityTuple c.arity) : Prop :=
  c.HoldsCode Z (encode xs)

theorem valid_iff (Z : Set ℕ) (c : NormalForm) :
    c.Valid Z ↔ ∀ xs : ArityTuple c.arity, ValidAux Z c.matrix c.pref (encode xs) :=
  Iff.rfl

@[simp]
theorem holdsCode_iff (Z : Set ℕ) (c : NormalForm) (a : ℕ) :
    c.HoldsCode Z a ↔ HoldsAux Z c.matrix c.pref a :=
  Iff.rfl

theorem evalTuple_iff_holdsCode (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) :
    c.EvalTuple Z xs ↔ c.HoldsCode Z (encode xs) :=
  Iff.rfl

@[simp]
theorem pred_eq_evalTuple (Z : Set ℕ) (c : NormalForm) (xs : ArityTuple c.arity) :
    c.Pred Z xs = c.EvalTuple Z xs :=
  (rfl)

/-- At arity `0`, validity checks input `0`; at positive arity, `ArityTuple` encodings cover `ℕ`. -/
theorem valid_iff_validAux {Z : Set ℕ} {c : NormalForm} :
    c.Valid Z ↔
      if c.arity = 0 then ValidAux Z c.matrix c.pref 0
      else ∀ a : ℕ, ValidAux Z c.matrix c.pref a := by
  unfold Valid
  rcases c.arity with _ | k
  · simp only [↓reduceIte]
    exact ⟨fun h0 => h0 (), fun h0 xs => by cases xs; exact h0⟩
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    refine ⟨fun hv a => ?_, fun hv xs => hv (encode xs)⟩
    obtain ⟨xs, rfl⟩ := exists_encode_arityTuple_succ k a
    exact hv xs

/-! ### Complementation compiler -/

/-- Query-free oracle program computing `n ↦ 1 - n`, exchanging `encode false = 0` and
`encode true = 1`. -/
def notBoolCode : Code :=
  .comp (.prec (.comp .succ .zero) .zero) (.pair .zero (.pair .left .right))

/-- `notBoolCode` computes `1 - n` relative to every partial oracle. -/
@[simp]
theorem eval_notBoolCode (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O notBoolCode n = Part.some (1 - n) := by
  have hid (m : ℕ) :
      Code.eval O (.pair .zero (.pair .left .right)) m = Part.some (Nat.pair 0 m) := by
    simp [Seq.seq]
  rw [notBoolCode, Code.eval_comp, hid n, PFun.some_bind]
  induction n with
  | zero => simp
  | succ k ih =>
    rw [Code.eval_prec_succ, ih]
    simp

/-- On encoded Booleans, `1 - encode b` is `encode (!b)`. -/
private theorem sub_one_encode_bool (b : Bool) : 1 - encode b = encode (!b) := by
  cases b <;> rfl

/-- Uniform primitive-recursive complementation of a normal-form code: negate the quantifier
prefix and postcompose the matrix with `notBoolCode`. -/
def not (c : NormalForm) : NormalForm where
  pref := c.pref.neg
  arity := c.arity
  matrix := .comp notBoolCode c.matrix

@[simp] theorem pref_not (c : NormalForm) : c.not.pref = c.pref.neg := (rfl)
@[simp] theorem arity_not (c : NormalForm) : c.not.arity = c.arity := (rfl)
@[simp] theorem matrix_not (c : NormalForm) : c.not.matrix = .comp notBoolCode c.matrix := (rfl)

/-- Normal-form complementation is primitive recursive. -/
theorem primrec_not : Primrec not :=
  primrec₃_mk (QuantifierPrefix.primrec_neg.comp primrec_pref) primrec_arity
    (Code.primrec₂_comp.comp (const notBoolCode) primrec_matrix)

theorem validDepth_comp_notBoolCode {Z : Set ℕ} {m : Code} :
    ∀ {d a : ℕ}, ValidDepth Z m d a → ValidDepth Z (.comp notBoolCode m) d a
  | 0, a, h => by
    obtain ⟨b, hb⟩ := (validDepth_zero Z m a).1 h
    exact (validDepth_zero Z _ a).2 ⟨!b, by simp [hb, sub_one_encode_bool]⟩
  | d + 1, a, h => by
    rw [validDepth_succ]
    exact fun y => validDepth_comp_notBoolCode ((validDepth_succ Z m d a).1 h y)

theorem holdsBlock_comp_notBoolCode {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {a : ℕ},
      ValidDepth Z m d a →
        (HoldsBlock Z (.comp notBoolCode m) (!ex) d a ↔ ¬HoldsBlock Z m ex d a)
  | 0, ex, a, h => by
    obtain ⟨b, hb⟩ := (validDepth_zero Z m a).1 h
    cases b <;> simp [hb]
  | d + 1, true, a, h => by
    simp only [Bool.not_true, holdsBlock_false_succ, holdsBlock_true_succ, not_exists]
    exact forall_congr' fun y =>
      holdsBlock_comp_notBoolCode (ex := false) ((validDepth_succ Z m d a).1 h y)
  | d + 1, false, a, h => by
    classical
    simp only [Bool.not_false, holdsBlock_true_succ, holdsBlock_false_succ, not_forall]
    exact exists_congr fun y =>
      holdsBlock_comp_notBoolCode (ex := true) ((validDepth_succ Z m d a).1 h y)

theorem validAux_comp_notBoolCode {Z : Set ℕ} {m : Code} {p : QuantifierPrefix} {a : ℕ}
    (h : ValidAux Z m p a) : ValidAux Z (.comp notBoolCode m) p.neg a := by
  simpa using validDepth_comp_notBoolCode h

theorem holdsAux_comp_notBoolCode {Z : Set ℕ} {m : Code} {p : QuantifierPrefix} {a : ℕ}
    (h : ValidAux Z m p a) :
    HoldsAux Z (.comp notBoolCode m) p.neg a ↔ ¬HoldsAux Z m p a := by
  rw [holdsAux_neg_eq_holdsBlock, holdsAux_eq_holdsBlock]
  exact holdsBlock_comp_notBoolCode h

/-- Complementation preserves semantic validity relative to `Z`. -/
theorem Valid.not {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.not.Valid Z :=
  fun xs => validAux_comp_notBoolCode (hc xs)

/-- Complementation negates evaluation on raw codes under validity. -/
theorem holdsCode_not_of_validAux {Z : Set ℕ} {c : NormalForm} {a : ℕ}
    (h : ValidAux Z c.matrix c.pref a) :
    c.not.HoldsCode Z a ↔ ¬c.HoldsCode Z a :=
  holdsAux_comp_notBoolCode h

/-- Complementation negates `EvalTuple` on valid normal forms of matching arity. -/
@[simp]
theorem Valid.evalTuple_not {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) :
    c.not.EvalTuple Z xs ↔ ¬c.EvalTuple Z xs := by
  subst hk
  exact holdsAux_comp_notBoolCode (hc xs)

/-! ### Adequacy with `IsSigma`, `IsPi`, and `IsDelta` -/

/-- Canonical re-encoding `n ↦ ((decode n).map encode).getD 0`, primitive recursive for every
`Primcodable` type. -/
private def canonEncode (α : Type*) [Primcodable α] (n : ℕ) : ℕ :=
  ((decode (α := α) n).map encode).getD 0

private theorem primrec_canonEncode (α : Type*) [Primcodable α] : Primrec (canonEncode α) :=
  option_getD.comp (option_map Primrec.decode (Primrec.encode.comp snd).to₂) (const 0)

/-- A program total on `encode '' univ` with Boolean outputs decides an `IsSigma Z 0` predicate on
any `Primcodable` type. -/
private theorem isSigma_zero_of_validDepth_zero {Z : Set ℕ} {α : Type*} [Primcodable α] {m : Code}
    (hv : ∀ x : α, ValidDepth Z m 0 (encode x)) :
    IsSigma Z 0 (fun x : α => encode true ∈ Code.eval Z.oracle m (encode x)) := by
  classical
  let b : α → Bool := fun x => decide (encode true ∈ Code.eval Z.oracle m (encode x))
  have hb_eval (x : α) : Code.eval Z.oracle m (encode x) = Part.some (encode (b x)) := by
    obtain ⟨bx, hbx⟩ := (validDepth_zero Z m (encode x)).1 (hv x)
    cases bx <;> simp [b, hbx]
  have hdiv : Nat.RecursiveIn {Z.oracle} (fun _ : ℕ => (Part.none : Part ℕ)) :=
    (Code.recursiveIn_eval Z.oracle (.rfind' (.comp .succ .zero))).of_eq fun n => by
      rw [← Nat.pair_unpair n, Code.eval_rfind']
      apply Part.eq_none_iff.2
      intro y hy
      obtain ⟨k, hk, -⟩ := (Part.mem_map_iff _).1 hy
      have hspec := Nat.rfind_spec hk
      simp at hspec
  have hguard : ComputableIn {Z.oracle} (fun n : ℕ => (decode (α := α) n).isSome) :=
    (option_isSome.comp (Primrec.decode (α := α))).computableIn
  have hcomp : ComputableIn {Z.oracle} b := by
    unfold ComputableIn RecursiveIn
    refine (Nat.RecursiveIn.cond hguard
      ((Code.recursiveIn_eval Z.oracle m).comp_primrec
        (Primrec.nat_iff.1 (primrec_canonEncode α))) hdiv).of_eq fun n => ?_
    cases hdec : decode (α := α) n with
    | none => simp
    | some x => simp [canonEncode, hdec, hb_eval x]
  exact isSigma_zero_iff.2 ⟨b, hcomp, fun _ => decide_eq_true_iff⟩

/-- Mutual soundness of valid `HoldsBlock` predicates at depth `n` on any `Primcodable` type. -/
private theorem isSigma_and_isPi_of_validDepth {Z : Set ℕ} :
    ∀ (n : ℕ) {α : Type*} [Primcodable α] {m : Code},
      (∀ x : α, ValidDepth Z m n (encode x)) →
        IsSigma Z n (fun x : α => HoldsBlock Z m true n (encode x)) ∧
          IsPi Z n (fun x : α => HoldsBlock Z m false n (encode x))
  | 0, _, _, _, hv =>
    ⟨isSigma_zero_of_validDepth_zero hv, isPi_zero_iff.2 (isSigma_zero_of_validDepth_zero hv)⟩
  | n + 1, α, _, m, hv => by
    have ih := isSigma_and_isPi_of_validDepth n (α := α × ℕ) (m := m) fun ⟨x, y⟩ => by
      simpa [encode_prod_val] using (validDepth_succ Z m n (encode x)).1 (hv x) y
    exact ⟨isSigma_succ_iff.2 ⟨_, ih.2, fun x => by simp [encode_prod_val]⟩,
      isPi_succ_iff.2 ⟨_, ih.1, fun x => by simp [encode_prod_val]⟩⟩

/-- Every valid normal-form code with prefix `sigmaOf n` defines an `IsSigma Z n` predicate. -/
theorem Valid.isSigma {Z : Set ℕ} {c : NormalForm} {n : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .sigmaOf n) : IsSigma Z n (c.Pred Z) := by
  have hv : ∀ xs : ArityTuple c.arity, ValidDepth Z c.matrix n (encode xs) := fun xs => by
    simpa [hp] using hc xs
  exact ((isSigma_and_isPi_of_validDepth n hv).1).of_eq fun xs => by
    simpa [Pred, hp] using (holdsAux_sigmaOf Z c.matrix n (encode xs)).symm

/-- Every valid normal-form code with prefix `piOf n` defines an `IsPi Z n` predicate. -/
theorem Valid.isPi {Z : Set ℕ} {c : NormalForm} {n : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .piOf n) : IsPi Z n (c.Pred Z) := by
  have hv : ∀ xs : ArityTuple c.arity, ValidDepth Z c.matrix n (encode xs) := fun xs => by
    simpa [hp] using hc xs
  exact ((isSigma_and_isPi_of_validDepth n hv).2).of_eq fun xs => by
    simpa [Pred, hp] using (holdsAux_piOf Z c.matrix n (encode xs)).symm

/-- Every valid normal-form code of arity `k` and prefix `sigmaOf n` defines an `IsSigma Z n`
predicate via `EvalTuple`. -/
theorem Valid.isSigma_evalTuple {Z : Set ℕ} {c : NormalForm} {n k : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .sigmaOf n) (hk : c.arity = k) :
    IsSigma Z n (fun xs : ArityTuple k => c.EvalTuple Z xs) := by
  subst hk
  exact (hc.isSigma hp).of_eq fun _ => Iff.rfl

/-- Every valid normal-form code of arity `k` and prefix `piOf n` defines an `IsPi Z n`
predicate via `EvalTuple`. -/
theorem Valid.isPi_evalTuple {Z : Set ℕ} {c : NormalForm} {n k : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .piOf n) (hk : c.arity = k) :
    IsPi Z n (fun xs : ArityTuple k => c.EvalTuple Z xs) := by
  subst hk
  exact (hc.isPi hp).of_eq fun _ => Iff.rfl

/-- Completeness helper: every `IsSigma Z n` predicate on any `Primcodable` type is represented by
a matrix valid on *all* natural numbers at depth `n`. -/
private theorem exists_matrix_of_isSigma {Z : Set ℕ} :
    ∀ (n : ℕ) {α : Type*} [Primcodable α] {p : α → Prop},
      IsSigma Z n p →
        ∃ m : Code, (∀ a : ℕ, ValidDepth Z m n a) ∧
          ∀ x : α, HoldsBlock Z m true n (encode x) ↔ p x
  | 0, α, _, p, hp => by
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hp
    unfold ComputableIn RecursiveIn at hb
    have hguard : ComputableIn {Z.oracle} (fun a : ℕ => (decode (α := α) a).isSome) :=
      (option_isSome.comp (Primrec.decode (α := α))).computableIn
    have hzero : Nat.RecursiveIn {Z.oracle} (fun _ : ℕ => Part.some 0) :=
      (Code.recursiveIn_eval Z.oracle .zero).of_eq fun n => Code.eval_zero n
    have htot : Nat.RecursiveIn {Z.oracle}
        (fun a : ℕ => Part.some (encode (match decode (α := α) a with
          | none => false
          | some x => b x))) := by
      refine (Nat.RecursiveIn.cond hguard
        (hb.comp_primrec (Primrec.nat_iff.1 (primrec_canonEncode α))) hzero).of_eq fun a => ?_
      cases hdec : decode (α := α) a with
      | none => simp
      | some x => simp [canonEncode, hdec, encodek]
    obtain ⟨m, hm⟩ := Code.exists_code.1 htot
    refine ⟨m, fun a => ?_, fun x => ?_⟩
    · rw [validDepth_zero]
      exact ⟨match decode (α := α) a with | none => false | some x => b x,
        by simpa using congrFun hm a⟩
    · have hmx : Code.eval Z.oracle m (encode x) = Part.some (encode (b x)) := by
        simpa [encodek] using congrFun hm (encode x)
      rw [holdsBlock_zero, hmx, Part.mem_some_iff, encode_inj]
      exact ⟨fun h => (heq x).1 h.symm, fun h => ((heq x).2 h).symm⟩
  | n + 1, α, _, p, hp => by
    classical
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hp
    obtain ⟨m₀, hm₀v, hm₀h⟩ := exists_matrix_of_isSigma n (α := α × ℕ) (isSigma_not_iff.2 hq)
    refine ⟨.comp notBoolCode m₀, fun a => ?_, fun x => ?_⟩
    · rw [validDepth_succ]
      exact fun y => validDepth_comp_notBoolCode (hm₀v (Nat.pair a y))
    · rw [holdsBlock_true_succ, heq x]
      refine exists_congr fun y => ?_
      have hneg := holdsBlock_comp_notBoolCode (ex := true) (hm₀v (encode (x, y)))
      rw [Bool.not_true, encode_prod_val] at hneg
      exact hneg.trans ((not_congr (hm₀h (x, y))).trans Classical.not_not)

end NormalForm

/-- **Normal-form adequacy for Σ⁰ₙ on `k`-tuples.** A predicate on `ArityTuple k` belongs to
`IsSigma Z n` if and only if it is defined by a valid normal-form code of prefix `sigmaOf n`
and arity `k`. -/
theorem isSigma_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsSigma Z n p ↔
      ∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = k ∧ c.Valid Z ∧
        ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs := by
  constructor
  · intro hp
    obtain ⟨m, hmv, hmh⟩ := NormalForm.exists_matrix_of_isSigma n hp
    refine ⟨⟨.sigmaOf n, k, m⟩, rfl, rfl, fun xs => by simpa using hmv (encode xs), fun xs => ?_⟩
    exact (NormalForm.holdsAux_sigmaOf Z m n (encode xs)).trans (hmh xs)
  · rintro ⟨c, hpref, har, hc, heq⟩
    exact (hc.isSigma_evalTuple hpref har).of_eq heq

/-- **Normal-form adequacy for Π⁰ₙ on `k`-tuples.** A predicate on `ArityTuple k` belongs to
`IsPi Z n` if and only if it is defined by a valid normal-form code of prefix `piOf n`
and arity `k`. -/
theorem isPi_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsPi Z n p ↔
      ∃ c : NormalForm, c.pref = .piOf n ∧ c.arity = k ∧ c.Valid Z ∧
        ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs := by
  classical
  constructor
  · intro hp
    obtain ⟨c, hpref, har, hc, heq⟩ := isSigma_iff_exists_normalForm.1 (isSigma_not_iff.2 hp)
    refine ⟨c.not, by simp [hpref], by simp [har], hc.not, fun xs => ?_⟩
    exact (hc.evalTuple_not har xs).trans ((not_congr (heq xs)).trans Classical.not_not)
  · rintro ⟨c, hpref, har, hc, heq⟩
    exact (hc.isPi_evalTuple hpref har).of_eq heq

/-- **Normal-form adequacy for Δ⁰ₙ on `k`-tuples.** Membership in `IsDelta Z n` is simultaneous
representation by valid `sigmaOf n` and `piOf n` normal-form codes. -/
theorem isDelta_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsDelta Z n p ↔
      (∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = k ∧ c.Valid Z ∧
        ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs) ∧
      (∃ d : NormalForm, d.pref = .piOf n ∧ d.arity = k ∧ d.Valid Z ∧
        ∀ xs : ArityTuple k, d.EvalTuple Z xs ↔ p xs) := by
  rw [isDelta_iff, isSigma_iff_exists_normalForm, isPi_iff_exists_normalForm]

/-- **Unary normal-form adequacy on arbitrary `Primcodable` types (Σ⁰ₙ).** Every `IsSigma Z n`
predicate on `α` is represented along `Encodable.encode` by a valid unary normal-form code of
prefix `sigmaOf n`, and conversely. -/
theorem isSigma_iff_exists_unary_normalForm {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α]
    {p : α → Prop} :
    IsSigma Z n p ↔
      ∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = 1 ∧ c.Valid Z ∧
        ∀ x : α, c.HoldsCode Z (encode x) ↔ p x := by
  constructor
  · intro hp
    obtain ⟨m, hmv, hmh⟩ := NormalForm.exists_matrix_of_isSigma n hp
    refine ⟨⟨.sigmaOf n, 1, m⟩, rfl, rfl, fun x => by simpa using hmv x, fun x => ?_⟩
    exact (NormalForm.holdsAux_sigmaOf Z m n (encode x)).trans (hmh x)
  · rintro ⟨c, hpref, har, hc, heq⟩
    have hu : IsSigma Z n (fun y : ArityTuple 1 => c.EvalTuple Z y) :=
      hc.isSigma_evalTuple hpref har
    exact (hu.preimage Primrec.encode.computableIn).of_eq fun x => heq x

/-- **Unary normal-form adequacy on arbitrary `Primcodable` types (Π⁰ₙ).** Every `IsPi Z n`
predicate on `α` is represented along `Encodable.encode` by a valid unary normal-form code of
prefix `piOf n`, and conversely. -/
theorem isPi_iff_exists_unary_normalForm {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α]
    {p : α → Prop} :
    IsPi Z n p ↔
      ∃ c : NormalForm, c.pref = .piOf n ∧ c.arity = 1 ∧ c.Valid Z ∧
        ∀ x : α, c.HoldsCode Z (encode x) ↔ p x := by
  classical
  constructor
  · intro hp
    obtain ⟨c, hpref, har, hc, heq⟩ :=
      isSigma_iff_exists_unary_normalForm.1 (isSigma_not_iff.2 hp)
    have hcv : ∀ a : ℕ, NormalForm.ValidAux Z c.matrix c.pref a := by
      have hiff := NormalForm.valid_iff_validAux.1 hc
      simpa [har] using hiff
    refine ⟨c.not, by simp [hpref], by simp [har], hc.not, fun x => ?_⟩
    exact (NormalForm.holdsCode_not_of_validAux (hcv (encode x))).trans
      ((not_congr (heq x)).trans Classical.not_not)
  · rintro ⟨c, hpref, har, hc, heq⟩
    have hu : IsPi Z n (fun y : ArityTuple 1 => c.EvalTuple Z y) :=
      hc.isPi_evalTuple hpref har
    exact (hu.preimage Primrec.encode.computableIn).of_eq fun x => heq x

end TauCeti.ArithmeticalHierarchy
