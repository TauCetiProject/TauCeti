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

A displayed normal-form code (`NormalForm`) represents a predicate in the arithmetical hierarchy by
syntactic data: an alternating number-quantifier prefix (`QuantifierPrefix`), a free-parameter arity
(`arity`), and a single-oracle program (`matrix`) computing a Boolean matrix relative to `Z`. Under
the totality promise `NormalForm.Valid Z`, valid codes of prefix `sigmaOf n` (`piOf n`) characterize
`IsSigma Z n` (`IsPi Z n`), and `NormalForm.not` uniformly complements codes.

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
def depth : QuantifierPrefix → ℕ | qf => 0 | sigma n => n + 1 | pi n => n + 1

/-- Dual quantifier prefix obtained by exchanging `∃` and `∀` at every position. -/
def neg : QuantifierPrefix → QuantifierPrefix | qf => qf | sigma n => pi n | pi n => sigma n

/-- The canonical prefix of Σ⁰ₙ: quantifier-free at `0` and `sigma m` at `m + 1`. -/
def sigmaOf : ℕ → QuantifierPrefix | 0 => qf | m + 1 => sigma m

/-- The canonical prefix of Π⁰ₙ: quantifier-free at `0` and `pi m` at `m + 1`. -/
def piOf : ℕ → QuantifierPrefix | 0 => qf | m + 1 => pi m

/-- Prefix resulting from prepending an existential quantifier and contracting adjacent `∃`s. -/
def addExists : QuantifierPrefix → QuantifierPrefix
  | qf => sigma 0 | sigma n => sigma n | pi n => sigma (n + 1)

/-- Prefix resulting from prepending a universal quantifier and contracting adjacent `∀`s. -/
def addForall : QuantifierPrefix → QuantifierPrefix
  | qf => pi 0 | pi n => pi n | sigma n => pi (n + 1)

/-- Whether a positive-depth prefix begins with an existential quantifier (`false` on `qf`). -/
def startsExists : QuantifierPrefix → Bool | qf => false | sigma _ => true | pi _ => false

@[simp] theorem depth_qf : qf.depth = 0 := (rfl)
@[simp] theorem depth_sigma (n : ℕ) : (sigma n).depth = n + 1 := (rfl)
@[simp] theorem depth_pi (n : ℕ) : (pi n).depth = n + 1 := (rfl)
@[simp] theorem startsExists_qf : qf.startsExists = false := (rfl)
@[simp] theorem startsExists_sigma (n : ℕ) : (sigma n).startsExists = true := (rfl)
@[simp] theorem startsExists_pi (n : ℕ) : (pi n).startsExists = false := (rfl)
@[simp] theorem neg_qf : qf.neg = qf := (rfl)
@[simp] theorem neg_sigma (n : ℕ) : (sigma n).neg = pi n := (rfl)
@[simp] theorem neg_pi (n : ℕ) : (pi n).neg = sigma n := (rfl)
@[simp] theorem sigmaOf_zero : sigmaOf 0 = qf := (rfl)
@[simp] theorem sigmaOf_succ (n : ℕ) : sigmaOf (n + 1) = sigma n := (rfl)
@[simp] theorem piOf_zero : piOf 0 = qf := (rfl)
@[simp] theorem piOf_succ (n : ℕ) : piOf (n + 1) = pi n := (rfl)
@[simp] theorem addExists_qf : qf.addExists = sigma 0 := (rfl)
@[simp] theorem addExists_sigma (n : ℕ) : (sigma n).addExists = sigma n := (rfl)
@[simp] theorem addExists_pi (n : ℕ) : (pi n).addExists = sigma (n + 1) := (rfl)
@[simp] theorem addForall_qf : qf.addForall = pi 0 := (rfl)
@[simp] theorem addForall_pi (n : ℕ) : (pi n).addForall = pi n := (rfl)
@[simp] theorem addForall_sigma (n : ℕ) : (sigma n).addForall = pi (n + 1) := (rfl)
@[simp] theorem neg_neg (p : QuantifierPrefix) : p.neg.neg = p := by cases p <;> rfl
@[simp] theorem depth_neg (p : QuantifierPrefix) : p.neg.depth = p.depth := by cases p <;> rfl
@[simp] theorem depth_sigmaOf (n : ℕ) : (sigmaOf n).depth = n := by cases n <;> rfl
@[simp] theorem depth_piOf (n : ℕ) : (piOf n).depth = n := by cases n <;> rfl
@[simp] theorem neg_sigmaOf (n : ℕ) : (sigmaOf n).neg = piOf n := by cases n <;> rfl
@[simp] theorem neg_piOf (n : ℕ) : (piOf n).neg = sigmaOf n := by cases n <;> rfl
@[simp] theorem neg_addExists (p : QuantifierPrefix) : p.addExists.neg = p.neg.addForall := by
  cases p <;> rfl
@[simp] theorem neg_addForall (p : QuantifierPrefix) : p.addForall.neg = p.neg.addExists := by
  cases p <;> rfl

/-- Numerical encoding of quantifier prefixes (`0` for `qf`, odd for `sigma`, positive even for
`pi`). -/
def encodePrefix : QuantifierPrefix → ℕ
  | qf => 0
  | sigma n => 2 * n + 1
  | pi n => 2 * n + 2

/-- Inverse of `encodePrefix`. -/
def ofNatPrefix : ℕ → QuantifierPrefix
  | 0 => qf
  | m + 1 => if m % 2 = 0 then sigma (m / 2) else pi (m / 2)

@[simp] theorem encodePrefix_ofNatPrefix : ∀ k, encodePrefix (ofNatPrefix k) = k
  | 0 => rfl
  | m + 1 => by simp only [ofNatPrefix]; split_ifs <;> simp [encodePrefix] <;> omega

@[simp] theorem ofNatPrefix_encodePrefix : ∀ p, ofNatPrefix (encodePrefix p) = p
  | qf => rfl
  | sigma n => by simp [encodePrefix, ofNatPrefix, Nat.mul_mod_right]
  | pi n => by simp [encodePrefix, ofNatPrefix, show (2 * n + 1) / 2 = n by omega]

instance : Denumerable QuantifierPrefix :=
  Denumerable.mk' ⟨encodePrefix, ofNatPrefix, ofNatPrefix_encodePrefix, encodePrefix_ofNatPrefix⟩

theorem encode_eq_encodePrefix : (encode : QuantifierPrefix → ℕ) = encodePrefix := (rfl)
theorem ofNat_eq_ofNatPrefix : ofNat QuantifierPrefix = ofNatPrefix := (rfl)

theorem primrec_sigma : Primrec sigma :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 2) .id) (const 1)).of_eq fun _ => rfl
theorem primrec_pi : Primrec pi :=
  Primrec.encode_iff.1 <| (nat_add.comp (nat_mul.comp (const 2) .id) (const 2)).of_eq fun _ => rfl

/-- Case analysis on `QuantifierPrefix` is primitive recursive, uniformly in a parameter. -/
theorem primrec_casesOn {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → QuantifierPrefix} (hp : Primrec p) {q : α → β} (hq : Primrec q)
    {fs fp : α → ℕ → β} (hs : Primrec₂ fs) (hpi : Primrec₂ fp) :
    Primrec fun a =>
      QuantifierPrefix.casesOn (motive := fun _ => β) (p a) (q a) (fs a) (fp a) := by
  have he := Primrec.encode.comp hp
  have hm := nat_sub.comp he (const 1)
  have hidx := nat_div.comp hm (const 2)
  refine (Primrec.ite (Primrec.eq.comp he (const 0)) hq <|
    Primrec.ite (Primrec.eq.comp (nat_mod.comp hm (const 2)) (const 0))
      (hs.comp .id hidx) (hpi.comp .id hidx)).of_eq fun a => ?_
  cases p a with
  | qf => rfl
  | sigma n => simp [encode_eq_encodePrefix, encodePrefix, show (2 * n) / 2 = n by omega]
  | pi n => simp [encode_eq_encodePrefix, encodePrefix, show (2 * n + 1) / 2 = n by omega]

theorem primrec_depth : Primrec depth :=
  (primrec_casesOn .id (const 0) (Primrec.succ.comp snd).to₂ (Primrec.succ.comp snd).to₂).of_eq
    fun p => by cases p <;> rfl
theorem primrec_startsExists : Primrec startsExists :=
  (primrec_casesOn .id (const false) (const true).to₂ (const false).to₂).of_eq
    fun p => by cases p <;> rfl
theorem primrec_neg : Primrec neg :=
  (primrec_casesOn .id (const qf) (primrec_pi.comp snd).to₂ (primrec_sigma.comp snd).to₂).of_eq
    fun p => by cases p <;> rfl
theorem primrec_sigmaOf : Primrec sigmaOf :=
  (nat_casesOn .id (const qf) (primrec_sigma.comp snd).to₂).of_eq fun n => by cases n <;> rfl
theorem primrec_piOf : Primrec piOf :=
  (nat_casesOn .id (const qf) (primrec_pi.comp snd).to₂).of_eq fun n => by cases n <;> rfl
theorem primrec_addExists : Primrec addExists :=
  (primrec_casesOn .id (const (sigma 0)) (primrec_sigma.comp snd).to₂
    (primrec_sigma.comp (Primrec.succ.comp snd)).to₂).of_eq fun p => by cases p <;> rfl
theorem primrec_addForall : Primrec addForall :=
  (primrec_casesOn .id (const (pi 0)) (primrec_pi.comp (Primrec.succ.comp snd)).to₂
    (primrec_pi.comp snd).to₂).of_eq fun p => by cases p <;> rfl

end QuantifierPrefix

/-! ### Tuple-arity convention -/

/-- Free-parameter tuple type of arity `k`: `Unit` at `0`, `ℕ` at `1`, and `ArityTuple (k + 1) × ℕ`
at `k + 2`. -/
abbrev ArityTuple : ℕ → Type | 0 => Unit | 1 => ℕ | k + 2 => ArityTuple (k + 1) × ℕ

instance instPrimcodableArityTuple : (k : ℕ) → Primcodable (ArityTuple k)
  | 0 => inferInstanceAs (Primcodable Unit)
  | 1 => inferInstanceAs (Primcodable ℕ)
  | k + 2 => @Primcodable.prod _ _ (instPrimcodableArityTuple (k + 1)) inferInstance

/-- Append a natural number to a `k`-tuple, producing a `(k + 1)`-tuple. -/
abbrev ArityTuple.snoc : {k : ℕ} → ArityTuple k → ℕ → ArityTuple (k + 1)
  | 0, (), y => y | _ + 1, xs, y => (xs, y)
theorem ArityTuple.snoc_zero (xs : ArityTuple 0) (y : ℕ) : ArityTuple.snoc xs y = y := by
  cases xs; rfl
theorem ArityTuple.encode_snoc_zero (xs : ArityTuple 0) (y : ℕ) :
    encode (ArityTuple.snoc xs y) = y := by cases xs; simp
@[simp] theorem ArityTuple.encode_snoc_succ {k : ℕ} (xs : ArityTuple (k + 1)) (y : ℕ) :
    encode (ArityTuple.snoc xs y) = Nat.pair (encode xs) y := (rfl)

/-- Every natural number is the `Encodable.encode` of a `(k + 1)`-tuple. -/
theorem exists_encode_arityTuple_succ : (k a : ℕ) → ∃ xs : ArityTuple (k + 1), encode xs = a
  | 0, a => ⟨a, rfl⟩
  | k + 1, a =>
    let ⟨xs, hxs⟩ := exists_encode_arityTuple_succ k a.unpair.1
    ⟨(xs, a.unpair.2), (congrArg (Nat.pair · a.unpair.2) hxs).trans (Nat.pair_unpair a)⟩

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
def equivTuple : NormalForm ≃ QuantifierPrefix × ℕ × Code :=
  ⟨fun c => (c.pref, c.arity, c.matrix), fun t => ⟨t.1, t.2.1, t.2.2⟩,
    fun ⟨_, _, _⟩ => rfl, fun ⟨_, _, _⟩ => rfl⟩
instance : Denumerable NormalForm :=
  Denumerable.mk' (equivTuple.trans (Denumerable.eqv (QuantifierPrefix × ℕ × Code)))
@[simp] theorem encode_mk (p : QuantifierPrefix) (k : ℕ) (m : Code) :
    encode (NormalForm.mk p k m) = encode (p, k, m) := (rfl)

private theorem primrec_equivTuple : Primrec equivTuple :=
  Primrec.encode_iff.1 ((Primrec.encode : Primrec (encode : NormalForm → ℕ)).of_eq
    fun ⟨_, _, _⟩ => rfl)
theorem primrec_pref : Primrec pref := (fst.comp primrec_equivTuple).of_eq fun _ => rfl
theorem primrec_arity : Primrec arity := ((fst.comp snd).comp primrec_equivTuple).of_eq fun _ => rfl
theorem primrec_matrix : Primrec matrix :=
  ((snd.comp snd).comp primrec_equivTuple).of_eq fun _ => rfl
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

@[simp] theorem validDepth_zero (Z : Set ℕ) (m : Code) (a : ℕ) :
    ValidDepth Z m 0 a ↔ ∃ b : Bool, Code.eval Z.oracle m a = Part.some (encode b) := Iff.rfl
@[simp] theorem validDepth_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    ValidDepth Z m (d + 1) a ↔ ∀ y, ValidDepth Z m d (Nat.pair a y) := Iff.rfl
@[simp] theorem holdsBlock_zero (Z : Set ℕ) (m : Code) (ex : Bool) (a : ℕ) :
    HoldsBlock Z m ex 0 a ↔ encode true ∈ Code.eval Z.oracle m a := Iff.rfl
@[simp] theorem holdsBlock_true_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    HoldsBlock Z m true (d + 1) a ↔ ∃ y, HoldsBlock Z m false d (Nat.pair a y) := Iff.rfl
@[simp] theorem holdsBlock_false_succ (Z : Set ℕ) (m : Code) (d a : ℕ) :
    HoldsBlock Z m false (d + 1) a ↔ ∀ y, HoldsBlock Z m true d (Nat.pair a y) := Iff.rfl

/-- Semantic totality of `m` under prefix `p` at base code `a`. -/
def ValidAux (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) : Prop :=
  ValidDepth Z m p.depth a
/-- Evaluation of prefix `p` and matrix `m` relative to `Z` at base code `a`. -/
def HoldsAux (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) : Prop :=
  HoldsBlock Z m p.startsExists p.depth a
@[simp] theorem validAux_eq_validDepth (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    ValidAux Z m p a = ValidDepth Z m p.depth a := (rfl)
@[simp] theorem holdsAux_eq_holdsBlock (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    HoldsAux Z m p a = HoldsBlock Z m p.startsExists p.depth a := (rfl)
theorem holdsAux_sigmaOf (Z : Set ℕ) (m : Code) (n a : ℕ) :
    HoldsAux Z m (.sigmaOf n) a ↔ HoldsBlock Z m true n a := by cases n <;> simp
theorem holdsAux_piOf (Z : Set ℕ) (m : Code) (n a : ℕ) :
    HoldsAux Z m (.piOf n) a ↔ HoldsBlock Z m false n a := by cases n <;> simp
theorem holdsAux_neg_eq_holdsBlock (Z : Set ℕ) (m : Code) (p : QuantifierPrefix) (a : ℕ) :
    HoldsAux Z m p.neg a ↔ HoldsBlock Z m (!p.startsExists) p.depth a := by cases p <;> simp

/-- Semantic validity promise on `c` relative to `Z`: for every free `c.arity`-tuple and all bound
quantifier values, `c.matrix` halts relative to `Z` with `0` or `1`. -/
def Valid (Z : Set ℕ) (c : NormalForm) : Prop :=
  ∀ xs : ArityTuple c.arity, ValidAux Z c.matrix c.pref (encode xs)
/-- Truth of `c` relative to `Z` on a raw encoded free-parameter value `a`. -/
def HoldsCode (Z : Set ℕ) (c : NormalForm) (a : ℕ) : Prop := HoldsAux Z c.matrix c.pref a
/-- Truth of `c` relative to `Z` on a `k`-tuple via `ArityTuple` encoding. -/
def EvalTuple (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) : Prop :=
  c.HoldsCode Z (encode xs)
/-- The displayed `c.arity`-ary predicate defined by `c` relative to `Z`. -/
def Pred (Z : Set ℕ) (c : NormalForm) (xs : ArityTuple c.arity) : Prop := c.HoldsCode Z (encode xs)

theorem valid_iff (Z : Set ℕ) (c : NormalForm) :
    c.Valid Z ↔ ∀ xs : ArityTuple c.arity, ValidAux Z c.matrix c.pref (encode xs) := Iff.rfl
@[simp] theorem holdsCode_iff (Z : Set ℕ) (c : NormalForm) (a : ℕ) :
    c.HoldsCode Z a ↔ HoldsAux Z c.matrix c.pref a := Iff.rfl
theorem evalTuple_iff_holdsCode (Z : Set ℕ) (c : NormalForm) {k : ℕ} (xs : ArityTuple k) :
    c.EvalTuple Z xs ↔ c.HoldsCode Z (encode xs) := Iff.rfl
@[simp] theorem pred_eq_evalTuple (Z : Set ℕ) (c : NormalForm) (xs : ArityTuple c.arity) :
    c.Pred Z xs = c.EvalTuple Z xs := (rfl)

/-- At arity `0`, validity checks input `0`; at positive arity, `ArityTuple` encodings cover `ℕ`. -/
theorem valid_iff_validAux {Z : Set ℕ} {c : NormalForm} :
    c.Valid Z ↔
      if c.arity = 0 then ValidAux Z c.matrix c.pref 0
      else ∀ a : ℕ, ValidAux Z c.matrix c.pref a := by
  unfold Valid; rcases c.arity with _ | k
  · exact ⟨fun h0 => h0 (), fun h0 xs => by cases xs; exact h0⟩
  · simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    exact ⟨fun hv a => let ⟨xs, hxs⟩ := exists_encode_arityTuple_succ k a; hxs ▸ hv xs,
      fun hv xs => hv (encode xs)⟩

/-! ### Complementation compiler -/

/-- Query-free oracle program computing `n ↦ 1 - n`, exchanging `0` (`false`) and `1` (`true`). -/
def notBoolCode : Code :=
  .comp (.prec (.comp .succ .zero) .zero) (.pair .zero (.pair .left .right))

@[simp] theorem eval_notBoolCode (O : ℕ →. ℕ) (n : ℕ) :
    Code.eval O notBoolCode n = Part.some (1 - n) := by
  rw [notBoolCode, Code.eval_comp, show Code.eval O (.pair .zero (.pair .left .right)) n =
    Part.some (Nat.pair 0 n) by simp [Seq.seq], PFun.some_bind]
  induction n with
  | zero => simp
  | succ _ ih => rw [Code.eval_prec_succ, ih]; simp

private theorem sub_one_encode_bool (b : Bool) : 1 - encode b = encode (!b) := by cases b <;> rfl

/-- Uniform primitive-recursive complementation of a normal-form code. -/
def not (c : NormalForm) : NormalForm := ⟨c.pref.neg, c.arity, .comp notBoolCode c.matrix⟩
@[simp] theorem pref_not (c : NormalForm) : c.not.pref = c.pref.neg := (rfl)
@[simp] theorem arity_not (c : NormalForm) : c.not.arity = c.arity := (rfl)
@[simp] theorem matrix_not (c : NormalForm) : c.not.matrix = .comp notBoolCode c.matrix := (rfl)
theorem primrec_not : Primrec not :=
  primrec₃_mk (QuantifierPrefix.primrec_neg.comp primrec_pref) primrec_arity
    (Code.primrec₂_comp.comp (const notBoolCode) primrec_matrix)

theorem validDepth_comp_notBoolCode {Z : Set ℕ} {m : Code} :
    ∀ {d a : ℕ}, ValidDepth Z m d a → ValidDepth Z (.comp notBoolCode m) d a
  | 0, a, h => let ⟨b, hb⟩ := (validDepth_zero Z m a).1 h
    (validDepth_zero Z _ a).2 ⟨!b, by simp [hb, sub_one_encode_bool]⟩
  | d + 1, a, h => (validDepth_succ Z _ d a).2 fun y =>
    validDepth_comp_notBoolCode ((validDepth_succ Z m d a).1 h y)

theorem holdsBlock_comp_notBoolCode {Z : Set ℕ} {m : Code} :
    ∀ {d : ℕ} {ex : Bool} {a : ℕ}, ValidDepth Z m d a →
      (HoldsBlock Z (.comp notBoolCode m) (!ex) d a ↔ ¬HoldsBlock Z m ex d a)
  | 0, _, a, h => by obtain ⟨b, hb⟩ := (validDepth_zero Z m a).1 h; cases b <;> simp [hb]
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
    (h : ValidAux Z m p a) : HoldsAux Z (.comp notBoolCode m) p.neg a ↔ ¬HoldsAux Z m p a := by
  rw [holdsAux_neg_eq_holdsBlock, holdsAux_eq_holdsBlock]; exact holdsBlock_comp_notBoolCode h
theorem Valid.not {Z : Set ℕ} {c : NormalForm} (hc : c.Valid Z) : c.not.Valid Z :=
  fun xs => validAux_comp_notBoolCode (hc xs)
theorem holdsCode_not_of_validAux {Z : Set ℕ} {c : NormalForm} {a : ℕ}
    (h : ValidAux Z c.matrix c.pref a) : c.not.HoldsCode Z a ↔ ¬c.HoldsCode Z a :=
  holdsAux_comp_notBoolCode h
@[simp] theorem Valid.evalTuple_not {Z : Set ℕ} {c : NormalForm} {k : ℕ} (hc : c.Valid Z)
    (hk : c.arity = k) (xs : ArityTuple k) : c.not.EvalTuple Z xs ↔ ¬c.EvalTuple Z xs := by
  subst hk; exact holdsAux_comp_notBoolCode (hc xs)

/-! ### Adequacy with `IsSigma`, `IsPi`, and `IsDelta` -/

private def canonEncode (α : Type*) [Primcodable α] (n : ℕ) : ℕ :=
  ((decode (α := α) n).map encode).getD 0
private theorem primrec_canonEncode (α : Type*) [Primcodable α] : Primrec (canonEncode α) :=
  option_getD.comp (option_map Primrec.decode (Primrec.encode.comp snd).to₂) (const 0)

private theorem isSigma_zero_of_validDepth_zero {Z : Set ℕ} {α : Type*} [Primcodable α] {m : Code}
    (hv : ∀ x : α, ValidDepth Z m 0 (encode x)) :
    IsSigma Z 0 (fun x : α => encode true ∈ Code.eval Z.oracle m (encode x)) := by
  classical
  let b : α → Bool := fun x => decide (encode true ∈ Code.eval Z.oracle m (encode x))
  have hb_eval (x : α) : Code.eval Z.oracle m (encode x) = Part.some (encode (b x)) := by
    obtain ⟨bx, hbx⟩ := (validDepth_zero Z m (encode x)).1 (hv x); cases bx <;> simp [b, hbx]
  have hdiv : Nat.RecursiveIn {Z.oracle} (fun _ : ℕ => (Part.none : Part ℕ)) :=
    (Nat.Primrec.succ.recursiveIn).rfind.of_eq fun _ =>
      Part.eq_none_iff.2 fun _ h => absurd (Nat.rfind_spec h) (by simp)
  have hcomp : ComputableIn {Z.oracle} b := by
    unfold ComputableIn RecursiveIn
    refine (Nat.RecursiveIn.cond (option_isSome.comp (Primrec.decode (α := α))).computableIn
      ((Code.recursiveIn_eval Z.oracle m).comp_primrec
        (Primrec.nat_iff.1 (primrec_canonEncode α))) hdiv).of_eq fun n => ?_
    cases hdec : decode (α := α) n <;> simp [canonEncode, hdec, hb_eval]
  exact isSigma_zero_iff.2 ⟨b, hcomp, fun _ => decide_eq_true_iff⟩

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

theorem Valid.isSigma {Z : Set ℕ} {c : NormalForm} {n : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .sigmaOf n) : IsSigma Z n (c.Pred Z) :=
  ((isSigma_and_isPi_of_validDepth n fun xs => by simpa [hp] using hc xs).1).of_eq fun xs => by
    simpa [Pred, hp] using (holdsAux_sigmaOf Z c.matrix n (encode xs)).symm
theorem Valid.isPi {Z : Set ℕ} {c : NormalForm} {n : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .piOf n) : IsPi Z n (c.Pred Z) :=
  ((isSigma_and_isPi_of_validDepth n fun xs => by simpa [hp] using hc xs).2).of_eq fun xs => by
    simpa [Pred, hp] using (holdsAux_piOf Z c.matrix n (encode xs)).symm
theorem Valid.isSigma_evalTuple {Z : Set ℕ} {c : NormalForm} {n k : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .sigmaOf n) (hk : c.arity = k) :
    IsSigma Z n (fun xs : ArityTuple k => c.EvalTuple Z xs) := by
  subst hk; exact (hc.isSigma hp).of_eq fun _ => Iff.rfl
theorem Valid.isPi_evalTuple {Z : Set ℕ} {c : NormalForm} {n k : ℕ} (hc : c.Valid Z)
    (hp : c.pref = .piOf n) (hk : c.arity = k) :
    IsPi Z n (fun xs : ArityTuple k => c.EvalTuple Z xs) := by
  subst hk; exact (hc.isPi hp).of_eq fun _ => Iff.rfl

private theorem exists_matrix_of_isSigma {Z : Set ℕ} :
    ∀ (n : ℕ) {α : Type*} [Primcodable α] {p : α → Prop}, IsSigma Z n p →
      ∃ m : Code, (∀ a : ℕ, ValidDepth Z m n a) ∧ ∀ x : α, HoldsBlock Z m true n (encode x) ↔ p x
  | 0, α, _, p, hp => by
    obtain ⟨b, hb, heq⟩ := isSigma_zero_iff.1 hp
    unfold ComputableIn RecursiveIn at hb
    have htot : Nat.RecursiveIn {Z.oracle}
        (fun a : ℕ => Part.some (encode (match decode (α := α) a with
          | none => false | some x => b x))) :=
      (Nat.RecursiveIn.cond (option_isSome.comp (Primrec.decode (α := α))).computableIn
        (hb.comp_primrec (Primrec.nat_iff.1 (primrec_canonEncode α)))
        Nat.Primrec.zero.recursiveIn).of_eq fun a => by
        cases hdec : decode (α := α) a <;> simp [canonEncode, hdec, encodek]
    obtain ⟨m, hm⟩ := Code.exists_code.1 htot
    refine ⟨m, fun a => (validDepth_zero Z m a).2 ⟨_, by simpa using congrFun hm a⟩, fun x => ?_⟩
    have hmx : Code.eval Z.oracle m (encode x) = Part.some (encode (b x)) := by
      simpa [encodek] using congrFun hm (encode x)
    rw [holdsBlock_zero, hmx, Part.mem_some_iff, encode_inj]
    exact ⟨fun h => (heq x).1 h.symm, fun h => ((heq x).2 h).symm⟩
  | n + 1, α, _, p, hp => by
    classical
    obtain ⟨q, hq, heq⟩ := isSigma_succ_iff.1 hp
    obtain ⟨m₀, hm₀v, hm₀h⟩ := exists_matrix_of_isSigma n (α := α × ℕ) (isSigma_not_iff.2 hq)
    refine ⟨.comp notBoolCode m₀, fun a => (validDepth_succ Z _ n a).2 fun y =>
      validDepth_comp_notBoolCode (hm₀v (Nat.pair a y)), fun x => ?_⟩
    rw [holdsBlock_true_succ, heq x]; refine exists_congr fun y => ?_
    have hneg := holdsBlock_comp_notBoolCode (ex := true) (hm₀v (encode (x, y)))
    rw [Bool.not_true, encode_prod_val] at hneg
    exact hneg.trans ((not_congr (hm₀h (x, y))).trans Classical.not_not)

end NormalForm

/-- **Normal-form adequacy for Σ⁰ₙ on `k`-tuples.** -/
theorem isSigma_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsSigma Z n p ↔ ∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = k ∧ c.Valid Z ∧
      ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs :=
  ⟨fun hp => let ⟨m, hmv, hmh⟩ := NormalForm.exists_matrix_of_isSigma n hp
    ⟨⟨.sigmaOf n, k, m⟩, rfl, rfl, fun xs => by simpa using hmv (encode xs),
      fun xs => (NormalForm.holdsAux_sigmaOf Z m n (encode xs)).trans (hmh xs)⟩,
    fun ⟨_, hpref, har, hc, heq⟩ => (hc.isSigma_evalTuple hpref har).of_eq heq⟩

/-- **Normal-form adequacy for Π⁰ₙ on `k`-tuples.** -/
theorem isPi_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsPi Z n p ↔ ∃ c : NormalForm, c.pref = .piOf n ∧ c.arity = k ∧ c.Valid Z ∧
      ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs := by
  classical
  refine ⟨fun hp => ?_, fun ⟨_, hpref, har, hc, heq⟩ => (hc.isPi_evalTuple hpref har).of_eq heq⟩
  obtain ⟨c, hpref, har, hc, heq⟩ := isSigma_iff_exists_normalForm.1 (isSigma_not_iff.2 hp)
  exact ⟨c.not, by simp [hpref], by simp [har], hc.not, fun xs =>
    (hc.evalTuple_not har xs).trans ((not_congr (heq xs)).trans Classical.not_not)⟩

/-- **Normal-form adequacy for Δ⁰ₙ on `k`-tuples.** -/
theorem isDelta_iff_exists_normalForm {Z : Set ℕ} {n k : ℕ} {p : ArityTuple k → Prop} :
    IsDelta Z n p ↔
      (∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = k ∧ c.Valid Z ∧
        ∀ xs : ArityTuple k, c.EvalTuple Z xs ↔ p xs) ∧
      (∃ d : NormalForm, d.pref = .piOf n ∧ d.arity = k ∧ d.Valid Z ∧
        ∀ xs : ArityTuple k, d.EvalTuple Z xs ↔ p xs) := by
  rw [isDelta_iff, isSigma_iff_exists_normalForm, isPi_iff_exists_normalForm]

/-- **Unary normal-form adequacy on arbitrary `Primcodable` types (Σ⁰ₙ).** -/
theorem isSigma_iff_exists_unary_normalForm {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α]
    {p : α → Prop} :
    IsSigma Z n p ↔ ∃ c : NormalForm, c.pref = .sigmaOf n ∧ c.arity = 1 ∧ c.Valid Z ∧
      ∀ x : α, c.HoldsCode Z (encode x) ↔ p x :=
  ⟨fun hp => let ⟨m, hmv, hmh⟩ := NormalForm.exists_matrix_of_isSigma n hp
    ⟨⟨.sigmaOf n, 1, m⟩, rfl, rfl, fun x => by simpa using hmv x,
      fun x => (NormalForm.holdsAux_sigmaOf Z m n (encode x)).trans (hmh x)⟩,
    fun ⟨_, hpref, har, hc, heq⟩ =>
      ((hc.isSigma_evalTuple hpref har).preimage Primrec.encode.computableIn).of_eq heq⟩

/-- **Unary normal-form adequacy on arbitrary `Primcodable` types (Π⁰ₙ).** -/
theorem isPi_iff_exists_unary_normalForm {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α]
    {p : α → Prop} :
    IsPi Z n p ↔ ∃ c : NormalForm, c.pref = .piOf n ∧ c.arity = 1 ∧ c.Valid Z ∧
      ∀ x : α, c.HoldsCode Z (encode x) ↔ p x := by
  classical
  refine ⟨fun hp => ?_, fun ⟨_, hpref, har, hc, heq⟩ =>
    ((hc.isPi_evalTuple hpref har).preimage Primrec.encode.computableIn).of_eq heq⟩
  obtain ⟨c, hpref, har, hc, heq⟩ := isSigma_iff_exists_unary_normalForm.1 (isSigma_not_iff.2 hp)
  have hcv : ∀ a : ℕ, NormalForm.ValidAux Z c.matrix c.pref a := by
    simpa [har] using NormalForm.valid_iff_validAux.1 hc
  exact ⟨c.not, by simp [hpref], by simp [har], hc.not, fun x =>
    (NormalForm.holdsCode_not_of_validAux (hcv (encode x))).trans
      ((not_congr (heq x)).trans Classical.not_not)⟩

end TauCeti.ArithmeticalHierarchy
