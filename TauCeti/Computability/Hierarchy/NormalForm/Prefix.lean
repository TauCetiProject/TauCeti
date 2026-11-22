/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Computability.Hierarchy.Closure

/-!
# Alternating quantifier prefixes for arithmetical normal forms

`QuantifierPrefix` represents the alternating number-quantifier prefix of an arithmetical normal
form: `zero` for the quantifier-free level Δ⁰₀, `sigma n` for Σ⁰ₙ₊₁, and `pi n` for Π⁰ₙ₊₁.
Because level zero is represented by a single constructor, there is no redundant polarity bit at
depth zero.

This module provides:
* the hierarchy partial order `p ≤ q ↔ p = q ∨ p.depth < q.depth` with least element `zero`;
* prefix operations (`depth`, `dual`, `ofSigma`, `ofPi`, `addExists`, `addForall`,
  `expandExists`, `expandForall`) together with a `Primcodable` instance and
  primitive-recursiveness certificates;
* `QuantifierPrefix.Eval`, evaluating a prefix on a matrix predicate of variable lists, along with
  duality, quantifier addition with same-polarity contraction (`eval_addExists`, `eval_addForall`),
  simultaneous unpairing of conjunctions and disjunctions (`eval_and_unpair_iff`,
  `eval_or_unpair_iff`), pulling out bound-variable-independent connectives, and dropping dummy
  variables;
* `QuantifierPrefix.IsClass`, matching each prefix to the corresponding arithmetical pointclass
  `IsSigma` or `IsPi`, together with closure under `addExists` and `addForall`.

## References

* R. I. Soare, *Recursively Enumerable Sets and Degrees*, Springer, 1987, Chapter IV.1.
-/

public section

open Encodable

namespace TauCeti.ArithmeticalHierarchy

/-- An alternating number-quantifier prefix for an arithmetical normal form.
`zero` represents the quantifier-free level Δ⁰₀, `sigma n` represents `n + 1` alternating
quantifiers starting with `∃` (Σ⁰ₙ₊₁), and `pi n` represents `n + 1` alternating quantifiers
starting with `∀` (Π⁰ₙ₊₁). -/
inductive QuantifierPrefix : Type
  | zero
  | sigma (n : ℕ)
  | pi (n : ℕ)
  deriving DecidableEq

namespace QuantifierPrefix

/-! ### Prefix operations and hierarchy order -/

/-- The number of alternating quantifiers in a prefix. -/
def depth : QuantifierPrefix → ℕ
  | .zero => 0
  | .sigma n => n + 1
  | .pi n => n + 1

/-- The quantifier-free prefix has depth zero. -/
@[simp]
theorem depth_zero : depth .zero = 0 := (rfl)

/-- An existential prefix `sigma n` has depth `n + 1`. -/
@[simp]
theorem depth_sigma (n : ℕ) : depth (.sigma n) = n + 1 := (rfl)

/-- A universal prefix `pi n` has depth `n + 1`. -/
@[simp]
theorem depth_pi (n : ℕ) : depth (.pi n) = n + 1 := (rfl)

/-- A prefix has depth zero if and only if it is `zero`. -/
@[simp]
theorem depth_eq_zero {p : QuantifierPrefix} : p.depth = 0 ↔ p = .zero := by
  cases p <;> simp

/-- Dualize a quantifier prefix by exchanging `∃` and `∀` throughout. -/
def dual : QuantifierPrefix → QuantifierPrefix
  | .zero => .zero
  | .sigma n => .pi n
  | .pi n => .sigma n

/-- Dualizing the quantifier-free prefix fixes it. -/
@[simp]
theorem dual_zero : dual .zero = .zero := (rfl)

/-- Dualizing `sigma n` yields `pi n`. -/
@[simp]
theorem dual_sigma (n : ℕ) : dual (.sigma n) = .pi n := (rfl)

/-- Dualizing `pi n` yields `sigma n`. -/
@[simp]
theorem dual_pi (n : ℕ) : dual (.pi n) = .sigma n := (rfl)

/-- Dualization is an involution. -/
@[simp]
theorem dual_dual (p : QuantifierPrefix) : p.dual.dual = p := by
  cases p <;> rfl

/-- Dualization preserves quantifier depth. -/
@[simp]
theorem depth_dual (p : QuantifierPrefix) : p.dual.depth = p.depth := by
  cases p <;> rfl

/-- Dualization is injective. -/
theorem dual_injective : Function.Injective dual :=
  Function.LeftInverse.injective dual_dual

/-- The prefix representing Σ⁰ₙ (with `0 ↦ zero` and `n + 1 ↦ sigma n`). -/
def ofSigma : ℕ → QuantifierPrefix
  | 0 => .zero
  | n + 1 => .sigma n

/-- The prefix representing Π⁰ₙ (with `0 ↦ zero` and `n + 1 ↦ pi n`). -/
def ofPi : ℕ → QuantifierPrefix
  | 0 => .zero
  | n + 1 => .pi n

/-- `ofSigma 0` is `zero`. -/
@[simp]
theorem ofSigma_zero : ofSigma 0 = .zero := (rfl)

/-- `ofSigma (n + 1)` is `sigma n`. -/
@[simp]
theorem ofSigma_succ (n : ℕ) : ofSigma (n + 1) = .sigma n := (rfl)

/-- `ofPi 0` is `zero`. -/
@[simp]
theorem ofPi_zero : ofPi 0 = .zero := (rfl)

/-- `ofPi (n + 1)` is `pi n`. -/
@[simp]
theorem ofPi_succ (n : ℕ) : ofPi (n + 1) = .pi n := (rfl)

/-- `ofSigma n` has depth `n`. -/
@[simp]
theorem depth_ofSigma (n : ℕ) : (ofSigma n).depth = n := by
  cases n <;> rfl

/-- `ofPi n` has depth `n`. -/
@[simp]
theorem depth_ofPi (n : ℕ) : (ofPi n).depth = n := by
  cases n <;> rfl

/-- Dualizing `ofSigma n` produces `ofPi n`. -/
@[simp]
theorem dual_ofSigma (n : ℕ) : (ofSigma n).dual = ofPi n := by
  cases n <;> rfl

/-- Dualizing `ofPi n` produces `ofSigma n`. -/
@[simp]
theorem dual_ofPi (n : ℕ) : (ofPi n).dual = ofSigma n := by
  cases n <;> rfl

/-- The resulting prefix when prepending an existential quantifier, contracting with a leading
existential block if present. -/
def addExists : QuantifierPrefix → QuantifierPrefix
  | .zero => .sigma 0
  | .sigma n => .sigma n
  | .pi n => .sigma (n + 1)

/-- The resulting prefix when prepending a universal quantifier, contracting with a leading
universal block if present. -/
def addForall : QuantifierPrefix → QuantifierPrefix
  | .zero => .pi 0
  | .sigma n => .pi (n + 1)
  | .pi n => .pi n

/-- Prepending `∃` to `zero` gives `sigma 0`. -/
@[simp]
theorem addExists_zero : addExists .zero = .sigma 0 := (rfl)

/-- Prepending `∃` to `sigma n` contracts to `sigma n`. -/
@[simp]
theorem addExists_sigma (n : ℕ) : addExists (.sigma n) = .sigma n := (rfl)

/-- Prepending `∃` to `pi n` alternates to `sigma (n + 1)`. -/
@[simp]
theorem addExists_pi (n : ℕ) : addExists (.pi n) = .sigma (n + 1) := (rfl)

/-- Prepending `∀` to `zero` gives `pi 0`. -/
@[simp]
theorem addForall_zero : addForall .zero = .pi 0 := (rfl)

/-- Prepending `∀` to `sigma n` alternates to `pi (n + 1)`. -/
@[simp]
theorem addForall_sigma (n : ℕ) : addForall (.sigma n) = .pi (n + 1) := (rfl)

/-- Prepending `∀` to `pi n` contracts to `pi n`. -/
@[simp]
theorem addForall_pi (n : ℕ) : addForall (.pi n) = .pi n := (rfl)

/-- Dualizing `addExists` yields `addForall` on the dual prefix. -/
@[simp]
theorem dual_addExists (p : QuantifierPrefix) : p.addExists.dual = p.dual.addForall := by
  cases p <;> rfl

/-- Dualizing `addForall` yields `addExists` on the dual prefix. -/
@[simp]
theorem dual_addForall (p : QuantifierPrefix) : p.addForall.dual = p.dual.addExists := by
  cases p <;> rfl

/-- Adapt a variable list from `p.addExists` to `p` with one extra free variable: when
`p = .sigma n`, the outermost bound variable (at index `n`) is unpaired into two variables to
undo same-polarity contraction; otherwise the list is unchanged. -/
def expandExists : QuantifierPrefix → List ℕ → List ℕ
  | .zero, l => l
  | .sigma n, l =>
    match l.drop n with
    | [] => l
    | w :: rest => l.take n ++ w.unpair.1 :: w.unpair.2 :: rest
  | .pi _, l => l

/-- Adapt a variable list from `p.addForall` to `p` with one extra free variable: when
`p = .pi n`, the outermost bound variable (at index `n`) is unpaired into two variables to undo
same-polarity contraction; otherwise the list is unchanged. -/
def expandForall (p : QuantifierPrefix) (l : List ℕ) : List ℕ :=
  p.dual.expandExists l

/-- `expandExists` leaves variable lists unchanged at depth zero. -/
@[simp]
theorem expandExists_zero (l : List ℕ) : expandExists .zero l = l := (rfl)

/-- `expandExists` leaves variable lists unchanged for universal prefixes. -/
@[simp]
theorem expandExists_pi (n : ℕ) (l : List ℕ) : expandExists (.pi n) l = l := (rfl)

/-- On an existential prefix `sigma n`, `expandExists` unpairs the element at index `n`. -/
theorem expandExists_sigma_append {n : ℕ} {bs xs : List ℕ} {w : ℕ} (hbs : bs.length = n) :
    expandExists (.sigma n) (bs ++ w :: xs) = bs ++ w.unpair.1 :: w.unpair.2 :: xs := by
  simp [expandExists, hbs]

/-- On an existential prefix `sigma n`, `expandExists` leaves lists of length at most `n`
unchanged. -/
theorem expandExists_sigma_of_length_le {n : ℕ} {l : List ℕ} (hl : l.length ≤ n) :
    expandExists (.sigma n) l = l := by
  simp [expandExists, List.drop_eq_nil_of_le hl]

/-- `expandForall` leaves variable lists unchanged at depth zero. -/
@[simp]
theorem expandForall_zero (l : List ℕ) : expandForall .zero l = l := (rfl)

/-- `expandForall` leaves variable lists unchanged for existential prefixes. -/
@[simp]
theorem expandForall_sigma (n : ℕ) (l : List ℕ) : expandForall (.sigma n) l = l := (rfl)

/-- On a universal prefix `pi n`, `expandForall` unpairs the element at index `n`. -/
theorem expandForall_pi_append {n : ℕ} {bs xs : List ℕ} {w : ℕ} (hbs : bs.length = n) :
    expandForall (.pi n) (bs ++ w :: xs) = bs ++ w.unpair.1 :: w.unpair.2 :: xs :=
  expandExists_sigma_append hbs

/-- On a universal prefix `pi n`, `expandForall` leaves lists of length at most `n` unchanged. -/
theorem expandForall_pi_of_length_le {n : ℕ} {l : List ℕ} (hl : l.length ≤ n) :
    expandForall (.pi n) l = l :=
  expandExists_sigma_of_length_le hl

/-- Dualizing the prefix exchanges `expandExists` with `expandForall`. -/
@[simp]
theorem expandExists_dual (p : QuantifierPrefix) (l : List ℕ) :
    p.dual.expandExists l = p.expandForall l := (rfl)

/-- Dualizing the prefix exchanges `expandForall` with `expandExists`. -/
@[simp]
theorem expandForall_dual (p : QuantifierPrefix) (l : List ℕ) :
    p.dual.expandForall l = p.expandExists l := by
  cases p <;> rfl

/-- Length relation for `expandExists` on lists containing at least `p.addExists.depth`
variables. -/
theorem length_expandExists {p : QuantifierPrefix} {l : List ℕ}
    (hl : p.addExists.depth ≤ l.length) :
    (p.expandExists l).length + p.addExists.depth = l.length + p.depth + 1 := by
  cases p with
  | zero => simp
  | pi n => simp [Nat.add_assoc]
  | sigma n =>
    simp only [addExists_sigma, depth_sigma] at hl ⊢
    have hlt : n < l.length := Nat.lt_of_succ_le hl
    have hdrop : l.drop n = l[n] :: l.drop (n + 1) := List.drop_eq_getElem_cons hlt
    have hlen : (expandExists (.sigma n) l).length = l.length + 1 := by
      simp only [expandExists, hdrop, List.length_append, List.length_take, List.length_cons,
        List.length_drop]
      omega
    omega

/-- Length relation for `expandForall` on lists containing at least `p.addForall.depth`
variables. -/
theorem length_expandForall {p : QuantifierPrefix} {l : List ℕ}
    (hl : p.addForall.depth ≤ l.length) :
    (p.expandForall l).length + p.addForall.depth = l.length + p.depth + 1 := by
  have hl' : p.dual.addExists.depth ≤ l.length := by
    simpa [← dual_addForall] using hl
  simpa [← dual_addForall] using length_expandExists hl'

/-- Hierarchy inclusion order on quantifier prefixes: `p ≤ q` holds when `p = q` or
`p.depth < q.depth`. At each positive depth `n + 1`, `sigma n` and `pi n` are incomparable. -/
instance : PartialOrder QuantifierPrefix where
  le p q := p = q ∨ p.depth < q.depth
  lt p q := p.depth < q.depth
  le_refl _ := Or.inl rfl
  le_trans _ _ _ hpq hqr := by
    rcases hpq with rfl | hpq
    · exact hqr
    · rcases hqr with rfl | hqr
      · exact Or.inr hpq
      · exact Or.inr (hpq.trans hqr)
  lt_iff_le_not_ge _ _ := by
    constructor
    · intro h
      refine ⟨Or.inr h, ?_⟩
      rintro (rfl | h')
      · exact Nat.lt_irrefl _ h
      · exact Nat.lt_asymm h h'
    · rintro ⟨rfl | h, hng⟩
      · exact (hng (Or.inl rfl)).elim
      · exact h
  le_antisymm _ _ hpq hqp := by
    rcases hpq with rfl | hpq
    · rfl
    · rcases hqp with rfl | hqp
      · rfl
      · exact (Nat.lt_asymm hpq hqp).elim

/-- The quantifier-free prefix `zero` is the least element of the hierarchy order. -/
instance : OrderBot QuantifierPrefix where
  bot := .zero
  bot_le p := by
    cases p
    · exact Or.inl rfl
    · exact Or.inr (Nat.zero_lt_succ _)
    · exact Or.inr (Nat.zero_lt_succ _)

/-- Decidability of the hierarchy order on quantifier prefixes. -/
instance : DecidableLE QuantifierPrefix := fun p q =>
  inferInstanceAs (Decidable (p = q ∨ p.depth < q.depth))

/-- Decidability of the strict hierarchy order on quantifier prefixes. -/
instance : DecidableLT QuantifierPrefix := fun p q =>
  inferInstanceAs (Decidable (p.depth < q.depth))

/-- Characterization of the hierarchy order on prefixes. -/
theorem le_iff {p q : QuantifierPrefix} : p ≤ q ↔ p = q ∨ p.depth < q.depth := (Iff.rfl)

/-- Strict order on prefixes is strict inequality of depth. -/
theorem lt_iff {p q : QuantifierPrefix} : p < q ↔ p.depth < q.depth := (Iff.rfl)

/-- The bottom prefix is `zero`. -/
@[simp]
theorem bot_eq_zero : (⊥ : QuantifierPrefix) = .zero := (rfl)

/-- Hierarchy inclusion implies depth inequality. -/
theorem depth_mono {p q : QuantifierPrefix} (h : p ≤ q) : p.depth ≤ q.depth := by
  rcases h with rfl | h
  · exact le_rfl
  · exact h.le

/-- Dualization preserves and reflects the hierarchy order. -/
@[simp]
theorem dual_le_dual_iff {p q : QuantifierPrefix} : p.dual ≤ q.dual ↔ p ≤ q := by
  simp only [le_iff, dual_injective.eq_iff, depth_dual]

/-- Adding an existential quantifier moves up (or stays) in the hierarchy order. -/
theorem le_addExists (p : QuantifierPrefix) : p ≤ p.addExists := by
  cases p <;> simp [le_iff]

/-- Adding a universal quantifier moves up (or stays) in the hierarchy order. -/
theorem le_addForall (p : QuantifierPrefix) : p ≤ p.addForall := by
  cases p <;> simp [le_iff]

/-! ### Encoding and primitive recursiveness -/

/-- Equivalence encoding quantifier prefixes as `Unit ⊕ (ℕ ⊕ ℕ)`. -/
def equivSum : QuantifierPrefix ≃ Unit ⊕ (ℕ ⊕ ℕ) where
  toFun
    | .zero => Sum.inl ()
    | .sigma n => Sum.inr (Sum.inl n)
    | .pi n => Sum.inr (Sum.inr n)
  invFun
    | Sum.inl () => .zero
    | Sum.inr (Sum.inl n) => .sigma n
    | Sum.inr (Sum.inr n) => .pi n
  left_inv p := by cases p <;> rfl
  right_inv s := by rcases s with ⟨⟩ | (n | n) <;> rfl

/-- Quantifier prefixes are primitive-codable via `equivSum`. -/
instance : Primcodable QuantifierPrefix :=
  Primcodable.ofEquiv (Unit ⊕ (ℕ ⊕ ℕ)) equivSum

/-- `equivSum` on `zero`. -/
@[simp]
theorem equivSum_zero : equivSum .zero = Sum.inl () := (rfl)

/-- `equivSum` on `sigma n`. -/
@[simp]
theorem equivSum_sigma (n : ℕ) : equivSum (.sigma n) = Sum.inr (Sum.inl n) := (rfl)

/-- `equivSum` on `pi n`. -/
@[simp]
theorem equivSum_pi (n : ℕ) : equivSum (.pi n) = Sum.inr (Sum.inr n) := (rfl)

/-- `equivSum.symm` on `Sum.inl ()`. -/
@[simp]
theorem equivSum_symm_inl : equivSum.symm (Sum.inl ()) = .zero := (rfl)

/-- `equivSum.symm` on `Sum.inr (Sum.inl n)`. -/
@[simp]
theorem equivSum_symm_inr_inl (n : ℕ) : equivSum.symm (Sum.inr (Sum.inl n)) = .sigma n := (rfl)

/-- `equivSum.symm` on `Sum.inr (Sum.inr n)`. -/
@[simp]
theorem equivSum_symm_inr_inr (n : ℕ) : equivSum.symm (Sum.inr (Sum.inr n)) = .pi n := (rfl)

/-- Constructing `sigma n` is primitive recursive. -/
theorem primrec_sigma : Primrec sigma :=
  (Primrec.of_equiv_symm (e := equivSum)).comp
    (Primrec.sumInr.comp Primrec.sumInl)

/-- Constructing `pi n` is primitive recursive. -/
theorem primrec_pi : Primrec pi :=
  (Primrec.of_equiv_symm (e := equivSum)).comp
    (Primrec.sumInr.comp Primrec.sumInr)

/-- Case analysis on a quantifier prefix is primitive recursive. -/
theorem primrec_casesOn {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → QuantifierPrefix} {z : α → β} {fs fp : α → ℕ → β}
    (hp : Primrec p) (hz : Primrec z) (hfs : Primrec₂ fs) (hfp : Primrec₂ fp) :
    Primrec fun a => QuantifierPrefix.casesOn (motive := fun _ => β) (p a)
      (z a) (fs a) (fp a) := by
  have h := Primrec.sumCasesOn ((Primrec.of_equiv (e := equivSum)).comp hp)
    (hz.comp Primrec.fst).to₂
    (Primrec.sumCasesOn Primrec.snd
      (hfs.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂
      (hfp.comp (Primrec.fst.comp Primrec.fst) Primrec.snd).to₂).to₂
  exact h.of_eq fun a => by cases p a <;> rfl

/-- Prefix depth is primitive recursive. -/
theorem primrec_depth : Primrec depth :=
  (primrec_casesOn Primrec.id (Primrec.const 0)
    (Primrec.succ.comp Primrec.snd).to₂ (Primrec.succ.comp Primrec.snd).to₂).of_eq fun p => by
      cases p <;> rfl

/-- Prefix dualization is primitive recursive. -/
theorem primrec_dual : Primrec dual :=
  (primrec_casesOn Primrec.id (Primrec.const .zero)
    (primrec_pi.comp Primrec.snd).to₂ (primrec_sigma.comp Primrec.snd).to₂).of_eq fun p => by
      cases p <;> rfl

/-- `ofSigma` is primitive recursive. -/
theorem primrec_ofSigma : Primrec ofSigma :=
  (Primrec.nat_casesOn Primrec.id (Primrec.const .zero)
    (primrec_sigma.comp Primrec.snd).to₂).of_eq fun n => by
      cases n <;> rfl

/-- `ofPi` is primitive recursive. -/
theorem primrec_ofPi : Primrec ofPi :=
  (Primrec.nat_casesOn Primrec.id (Primrec.const .zero)
    (primrec_pi.comp Primrec.snd).to₂).of_eq fun n => by
      cases n <;> rfl

/-- `addExists` is primitive recursive. -/
theorem primrec_addExists : Primrec addExists :=
  (primrec_casesOn Primrec.id (Primrec.const (.sigma 0))
    (primrec_sigma.comp Primrec.snd).to₂
    (primrec_sigma.comp (Primrec.succ.comp Primrec.snd)).to₂).of_eq fun p => by
      cases p <;> rfl

/-- `addForall` is primitive recursive. -/
theorem primrec_addForall : Primrec addForall :=
  (primrec_casesOn Primrec.id (Primrec.const (.pi 0))
    (primrec_pi.comp (Primrec.succ.comp Primrec.snd)).to₂
    (primrec_pi.comp Primrec.snd).to₂).of_eq fun p => by
      cases p <;> rfl

/-- `expandExists` is primitive recursive. -/
theorem primrec₂_expandExists : Primrec₂ expandExists := by
  have hsigma :
      Primrec₂ fun (a : QuantifierPrefix × List ℕ) (n : ℕ) =>
        match a.2.drop n with
        | [] => a.2
        | w :: rest => a.2.take n ++ w.unpair.1 :: w.unpair.2 :: rest := by
    refine (Primrec.list_casesOn
      (Primrec.list_drop.comp Primrec.snd (Primrec.snd.comp Primrec.fst))
      (Primrec.snd.comp Primrec.fst)
      (Primrec.list_append.comp
        (Primrec.list_take.comp (Primrec.snd.comp Primrec.fst)
          (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)))
        (Primrec.list_cons.comp
          (Primrec.fst.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
          (Primrec.list_cons.comp
            (Primrec.snd.comp (Primrec.unpair.comp (Primrec.fst.comp Primrec.snd)))
            (Primrec.snd.comp Primrec.snd)))).to₂).to₂.of_eq fun a n => ?_
    cases a.2.drop n <;> rfl
  exact (primrec_casesOn Primrec.fst Primrec.snd hsigma
    (Primrec.snd.comp Primrec.fst).to₂).to₂.of_eq fun p l => by
      cases p <;> rfl

/-- `expandForall` is primitive recursive. -/
theorem primrec₂_expandForall : Primrec₂ expandForall :=
  (primrec₂_expandExists.comp (primrec_dual.comp Primrec.fst) Primrec.snd).to₂

/-! ### Quantifier evaluation on variable lists -/

/-- Evaluate an alternating quantifier prefix on a matrix predicate `R : List ℕ → Prop` and free
variable list `xs`. Each quantifier prepends its bound variable to the list, so at depth `d` the
matrix receives `bs ++ xs` where `bs.length = d` lists the bound variables from innermost to
outermost. -/
def Eval : QuantifierPrefix → (List ℕ → Prop) → List ℕ → Prop
  | .zero, R, xs => R xs
  | .sigma 0, R, xs => ∃ y, R (y :: xs)
  | .sigma (n + 1), R, xs => ∃ y, Eval (.pi n) R (y :: xs)
  | .pi 0, R, xs => ∀ y, R (y :: xs)
  | .pi (n + 1), R, xs => ∀ y, Eval (.sigma n) R (y :: xs)

/-- Evaluating `zero` applies the matrix directly. -/
@[simp]
theorem eval_zero (R : List ℕ → Prop) (xs : List ℕ) :
    Eval .zero R xs ↔ R xs := by
  rw [Eval]

/-- Evaluating `sigma 0` adds one existential quantifier. -/
@[simp]
theorem eval_sigma_zero (R : List ℕ → Prop) (xs : List ℕ) :
    Eval (.sigma 0) R xs ↔ ∃ y, R (y :: xs) := by
  rw [Eval]

/-- Evaluating `sigma (n + 1)` peels off the leading existential quantifier. -/
@[simp]
theorem eval_sigma_succ (n : ℕ) (R : List ℕ → Prop) (xs : List ℕ) :
    Eval (.sigma (n + 1)) R xs ↔ ∃ y, Eval (.pi n) R (y :: xs) := by
  rw [Eval]

/-- Evaluating `pi 0` adds one universal quantifier. -/
@[simp]
theorem eval_pi_zero (R : List ℕ → Prop) (xs : List ℕ) :
    Eval (.pi 0) R xs ↔ ∀ y, R (y :: xs) := by
  rw [Eval]

/-- Evaluating `pi (n + 1)` peels off the leading universal quantifier. -/
@[simp]
theorem eval_pi_succ (n : ℕ) (R : List ℕ → Prop) (xs : List ℕ) :
    Eval (.pi (n + 1)) R xs ↔ ∀ y, Eval (.sigma n) R (y :: xs) := by
  rw [Eval]

-- Simultaneous depth induction for `sigma n` and `pi n`, avoiding repeated mutual inductions.
private theorem eval_sigma_pi_induction (P : QuantifierPrefix → Prop)
    (hs0 : P (.sigma 0)) (hp0 : P (.pi 0))
    (hss : ∀ n, P (.pi n) → P (.sigma (n + 1)))
    (hps : ∀ n, P (.sigma n) → P (.pi (n + 1))) :
    ∀ n, P (.sigma n) ∧ P (.pi n)
  | 0 => ⟨hs0, hp0⟩
  | n + 1 =>
    let ⟨hs, hp⟩ := eval_sigma_pi_induction P hs0 hp0 hss hps n
    ⟨hss n hp, hps n hs⟩

/-- Induction principle following the recursive structure of `Eval`. -/
theorem eval_induction {motive : QuantifierPrefix → Prop}
    (zero : motive .zero) (sigma_zero : motive (.sigma 0)) (pi_zero : motive (.pi 0))
    (sigma_succ : ∀ n, motive (.pi n) → motive (.sigma (n + 1)))
    (pi_succ : ∀ n, motive (.sigma n) → motive (.pi (n + 1)))
    (p : QuantifierPrefix) : motive p := by
  cases p with
  | zero => exact zero
  | sigma n => exact (eval_sigma_pi_induction motive sigma_zero pi_zero sigma_succ pi_succ n).1
  | pi n => exact (eval_sigma_pi_induction motive sigma_zero pi_zero sigma_succ pi_succ n).2

/-- `Eval p R xs` depends only on the values of `R` on lists `bs ++ xs` with
`bs.length = p.depth`, even across distinct free-variable tails. -/
theorem eval_congr_append {p : QuantifierPrefix} {R₁ R₂ : List ℕ → Prop} {xs₁ xs₂ : List ℕ}
    (h : ∀ bs : List ℕ, bs.length = p.depth → (R₁ (bs ++ xs₁) ↔ R₂ (bs ++ xs₂))) :
    p.Eval R₁ xs₁ ↔ p.Eval R₂ xs₂ := by
  induction p using eval_induction generalizing xs₁ xs₂ with
  | zero => simpa using h [] rfl
  | sigma_zero =>
    simp only [eval_sigma_zero]
    exact exists_congr fun y => h [y] rfl
  | pi_zero =>
    simp only [eval_pi_zero]
    exact forall_congr' fun y => h [y] rfl
  | sigma_succ n ih =>
    simp only [eval_sigma_succ]
    refine exists_congr fun y => ih fun bs hbs => ?_
    simpa [List.append_assoc] using h (bs ++ [y]) (by simp [hbs])
  | pi_succ n ih =>
    simp only [eval_pi_succ]
    refine forall_congr' fun y => ih fun bs hbs => ?_
    simpa [List.append_assoc] using h (bs ++ [y]) (by simp [hbs])

/-- `Eval` is extensional in its matrix predicate. -/
theorem eval_congr {p : QuantifierPrefix} {R₁ R₂ : List ℕ → Prop} {xs : List ℕ}
    (h : ∀ l, R₁ l ↔ R₂ l) : p.Eval R₁ xs ↔ p.Eval R₂ xs :=
  eval_congr_append fun bs _ => h (bs ++ xs)

/-- Evaluating a prefix on a constant matrix predicate returns that proposition, since `ℕ` is
nonempty. -/
@[simp]
theorem eval_const_iff (p : QuantifierPrefix) (P : Prop) (xs : List ℕ) :
    p.Eval (fun _ => P) xs ↔ P := by
  induction p using eval_induction generalizing xs with
  | zero => simp
  | sigma_zero => simp
  | pi_zero => simp
  | sigma_succ n ih => simp [ih]
  | pi_succ n ih => simp [ih]

/-- Negating an evaluated prefix dualizes the prefix and negates the matrix. -/
theorem not_eval_iff (p : QuantifierPrefix) (R : List ℕ → Prop) (xs : List ℕ) :
    ¬p.Eval R xs ↔ p.dual.Eval (fun l => ¬R l) xs := by
  induction p using eval_induction generalizing xs with
  | zero => simp
  | sigma_zero => simp
  | pi_zero => simp
  | sigma_succ n ih => simp [ih]
  | pi_succ n ih => simp [ih]

/-- A proposition independent of the bound variables pulls out of any quantifier prefix under
conjunction, since `ℕ` is nonempty. -/
@[simp]
theorem eval_and_const_iff (p : QuantifierPrefix) (P : Prop) (R : List ℕ → Prop) (xs : List ℕ) :
    p.Eval (fun l => P ∧ R l) xs ↔ P ∧ p.Eval R xs := by
  induction p using eval_induction generalizing xs with
  | zero => simp
  | sigma_zero => simp [exists_and_left]
  | pi_zero =>
    simp only [eval_pi_zero]
    exact ⟨fun h => ⟨(h 0).1, fun y => (h y).2⟩, fun ⟨hP, hR⟩ y => ⟨hP, hR y⟩⟩
  | sigma_succ n ih =>
    simp [ih, exists_and_left]
  | pi_succ n ih =>
    simp only [eval_pi_succ, ih]
    exact ⟨fun h => ⟨(h 0).1, fun y => (h y).2⟩, fun ⟨hP, hR⟩ y => ⟨hP, hR y⟩⟩

/-- A proposition independent of the bound variables pulls out of any quantifier prefix under
disjunction. -/
@[simp]
theorem eval_or_const_iff (p : QuantifierPrefix) (P : Prop) (R : List ℕ → Prop) (xs : List ℕ) :
    p.Eval (fun l => P ∨ R l) xs ↔ P ∨ p.Eval R xs := by
  classical
  induction p using eval_induction generalizing xs with
  | zero => simp
  | sigma_zero =>
    simp only [eval_sigma_zero]
    exact ⟨fun ⟨y, h⟩ => h.imp_right fun hy => ⟨y, hy⟩,
      fun h => h.elim (fun hP => ⟨0, Or.inl hP⟩) fun ⟨y, hy⟩ => ⟨y, Or.inr hy⟩⟩
  | pi_zero =>
    simp only [eval_pi_zero]
    exact ⟨fun h => (em P).imp_right fun hnP y => (h y).resolve_left hnP,
      fun h y => h.imp_right fun hR => hR y⟩
  | sigma_succ n ih =>
    simp only [eval_sigma_succ, ih]
    exact ⟨fun ⟨y, h⟩ => h.imp_right fun hy => ⟨y, hy⟩,
      fun h => h.elim (fun hP => ⟨0, Or.inl hP⟩) fun ⟨y, hy⟩ => ⟨y, Or.inr hy⟩⟩
  | pi_succ n ih =>
    simp only [eval_pi_succ, ih]
    exact ⟨fun h => (em P).imp_right fun hnP y => (h y).resolve_left hnP,
      fun h y => h.imp_right fun hR => hR y⟩

/-- A premise independent of the bound variables pulls out of any quantifier prefix under
implication. -/
@[simp]
theorem eval_imp_const_iff (p : QuantifierPrefix) (P : Prop) (R : List ℕ → Prop) (xs : List ℕ) :
    p.Eval (fun l => P → R l) xs ↔ (P → p.Eval R xs) := by
  classical
  simp [imp_iff_not_or]

/-- Evaluating a prefix on a matrix that drops all `p.depth` bound variables reduces to the
underlying predicate on `xs`. -/
@[simp]
theorem eval_drop_iff (p : QuantifierPrefix) (R : List ℕ → Prop) (xs : List ℕ) :
    p.Eval (fun l => R (l.drop p.depth)) xs ↔ R xs :=
  (eval_congr_append fun bs hbs => by simp [hbs]).trans (eval_const_iff p (R xs) xs)

/-- Semantic characterization of `addExists`: evaluating `p.addExists` on a matrix adapted by
`p.expandExists` prepends an existential quantifier to `p.Eval`, contracting with a leading
existential block when `p = .sigma n`. -/
@[simp]
theorem eval_addExists (p : QuantifierPrefix) (R : List ℕ → Prop) (xs : List ℕ) :
    p.addExists.Eval (fun l => R (p.expandExists l)) xs ↔ ∃ y, p.Eval R (y :: xs) := by
  cases p with
  | zero => simp
  | pi n => simp
  | sigma n =>
    cases n with
    | zero =>
      simp only [addExists_sigma, eval_sigma_zero]
      have h : ∀ w : ℕ, expandExists (.sigma 0) (w :: xs) = w.unpair.1 :: w.unpair.2 :: xs :=
        fun w => expandExists_sigma_append (bs := []) rfl
      simp only [h]
      rw [Nat.pairEquiv.symm.exists_congr_left]
      simpa using (exists_comm (p := fun y₀ y => R (y₀ :: y :: xs)))
    | succ n =>
      simp only [addExists_sigma, eval_sigma_succ]
      have h (w : ℕ) :
          Eval (.pi n) (fun l => R (expandExists (.sigma (n + 1)) l)) (w :: xs) ↔
            Eval (.pi n) R (w.unpair.1 :: w.unpair.2 :: xs) :=
        eval_congr_append fun bs hbs => by
          rw [expandExists_sigma_append (by simpa using hbs)]
      refine (exists_congr h).trans ?_
      rw [Nat.pairEquiv.symm.exists_congr_left]
      simpa using (exists_comm (p := fun y₀ y => Eval (.pi n) R (y₀ :: y :: xs)))

/-- Semantic characterization of `addForall`: evaluating `p.addForall` on a matrix adapted by
`p.expandForall` prepends a universal quantifier to `p.Eval`, contracting with a leading universal
block when `p = .pi n`. -/
@[simp]
theorem eval_addForall (p : QuantifierPrefix) (R : List ℕ → Prop) (xs : List ℕ) :
    p.addForall.Eval (fun l => R (p.expandForall l)) xs ↔ ∀ y, p.Eval R (y :: xs) := by
  classical
  have h := eval_addExists p.dual (fun l => ¬R l) xs
  rw [← dual_addForall, ← not_eval_iff] at h
  simpa [← not_eval_iff] using h.not

-- Inductive step for `eval_and_or_unpair_aux`, peeling off the outermost paired variable `y`.
private theorem eval_and_or_unpair_step (q : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop)
    (xs₁ xs₂ xs : List ℕ) (y : ℕ)
    (ih :
      (q.Eval (fun l =>
          R₁ ((l.take q.depth).map (fun z => z.unpair.1) ++ (y.unpair.1 :: xs₁)) ∧
          R₂ ((l.take q.depth).map (fun z => z.unpair.2) ++ (y.unpair.2 :: xs₂))) (y :: xs) ↔
        q.Eval R₁ (y.unpair.1 :: xs₁) ∧ q.Eval R₂ (y.unpair.2 :: xs₂)) ∧
      (q.Eval (fun l =>
          R₁ ((l.take q.depth).map (fun z => z.unpair.1) ++ (y.unpair.1 :: xs₁)) ∨
          R₂ ((l.take q.depth).map (fun z => z.unpair.2) ++ (y.unpair.2 :: xs₂))) (y :: xs) ↔
        q.Eval R₁ (y.unpair.1 :: xs₁) ∨ q.Eval R₂ (y.unpair.2 :: xs₂))) :
    (q.Eval (fun l =>
        R₁ ((l.take (q.depth + 1)).map (fun z => z.unpair.1) ++ xs₁) ∧
        R₂ ((l.take (q.depth + 1)).map (fun z => z.unpair.2) ++ xs₂)) (y :: xs) ↔
      q.Eval R₁ (y.unpair.1 :: xs₁) ∧ q.Eval R₂ (y.unpair.2 :: xs₂)) ∧
    (q.Eval (fun l =>
        R₁ ((l.take (q.depth + 1)).map (fun z => z.unpair.1) ++ xs₁) ∨
        R₂ ((l.take (q.depth + 1)).map (fun z => z.unpair.2) ++ xs₂)) (y :: xs) ↔
      q.Eval R₁ (y.unpair.1 :: xs₁) ∨ q.Eval R₂ (y.unpair.2 :: xs₂)) := by
  have htake (bs : List ℕ) (hbs : bs.length = q.depth) (f : ℕ → ℕ) :
      ((bs ++ y :: xs).take (q.depth + 1)).map f = bs.map f ++ [f y] := by
    rw [← hbs, List.take_append, List.take_of_length_le (Nat.le_succ _)]
    simp
  have hcongr (bs : List ℕ) (hbs : bs.length = q.depth) :
      ((bs ++ y :: xs).take (q.depth + 1)).map (fun z => z.unpair.1) ++ xs₁ =
        ((bs ++ y :: xs).take q.depth).map (fun z => z.unpair.1) ++ (y.unpair.1 :: xs₁) ∧
      ((bs ++ y :: xs).take (q.depth + 1)).map (fun z => z.unpair.2) ++ xs₂ =
        ((bs ++ y :: xs).take q.depth).map (fun z => z.unpair.2) ++ (y.unpair.2 :: xs₂) := by
    simp [htake bs hbs, List.take_left' hbs]
  constructor
  · refine (eval_congr_append fun bs hbs => ?_).trans ih.1
    rw [(hcongr bs hbs).1, (hcongr bs hbs).2]
  · refine (eval_congr_append fun bs hbs => ?_).trans ih.2
    rw [(hcongr bs hbs).1, (hcongr bs hbs).2]

-- Unpairing all `p.depth` bound variables simultaneously distributes over both `∧` and `∨`.
private theorem eval_and_or_unpair_aux (p : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop)
    (xs₁ xs₂ xs : List ℕ) :
    (p.Eval (fun l =>
        R₁ ((l.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∧
        R₂ ((l.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
      p.Eval R₁ xs₁ ∧ p.Eval R₂ xs₂) ∧
    (p.Eval (fun l =>
        R₁ ((l.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∨
        R₂ ((l.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
      p.Eval R₁ xs₁ ∨ p.Eval R₂ xs₂) := by
  classical
  induction p using eval_induction generalizing xs₁ xs₂ xs with
  | zero => simp
  | sigma_zero =>
    simp only [eval_sigma_zero, depth_sigma, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.singleton_append]
    constructor
    · rw [Nat.pairEquiv.symm.exists_congr_left]; simp [exists_and_left, exists_and_right]
    · rw [Nat.pairEquiv.symm.exists_congr_left]; simp [exists_or]
  | pi_zero =>
    simp only [eval_pi_zero, depth_pi, Nat.zero_add,
      List.take_succ_cons, List.take_zero, List.map_cons, List.map_nil, List.singleton_append]
    constructor
    · rw [Nat.pairEquiv.symm.forall_congr_left]; simp [forall_and]
    · rw [Nat.pairEquiv.symm.forall_congr_left]; simp [forall_or_left, forall_or_right]
  | sigma_succ n ih =>
    simp only [eval_sigma_succ, depth_sigma]
    have hstep (y : ℕ) :=
      eval_and_or_unpair_step (.pi n) R₁ R₂ xs₁ xs₂ xs y
        (ih (y.unpair.1 :: xs₁) (y.unpair.2 :: xs₂) (y :: xs))
    simp only [depth_pi] at hstep
    constructor
    · refine (exists_congr fun y => (hstep y).1).trans ?_
      rw [Nat.pairEquiv.symm.exists_congr_left]; simp [exists_and_left, exists_and_right]
    · refine (exists_congr fun y => (hstep y).2).trans ?_
      rw [Nat.pairEquiv.symm.exists_congr_left]; simp [exists_or]
  | pi_succ n ih =>
    simp only [eval_pi_succ, depth_pi]
    have hstep (y : ℕ) :=
      eval_and_or_unpair_step (.sigma n) R₁ R₂ xs₁ xs₂ xs y
        (ih (y.unpair.1 :: xs₁) (y.unpair.2 :: xs₂) (y :: xs))
    simp only [depth_sigma] at hstep
    constructor
    · refine (forall_congr' fun y => (hstep y).1).trans ?_
      rw [Nat.pairEquiv.symm.forall_congr_left]; simp [forall_and]
    · refine (forall_congr' fun y => (hstep y).2).trans ?_
      rw [Nat.pairEquiv.symm.forall_congr_left]; simp [forall_or_left, forall_or_right]

/-- Simultaneous unpairing of bound variables distributes any quantifier prefix over conjunction
of two matrices. -/
theorem eval_and_unpair_iff (p : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop)
    (xs₁ xs₂ xs : List ℕ) :
    p.Eval (fun l =>
      R₁ ((l.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∧
      R₂ ((l.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
    p.Eval R₁ xs₁ ∧ p.Eval R₂ xs₂ :=
  (eval_and_or_unpair_aux p R₁ R₂ xs₁ xs₂ xs).1

/-- Simultaneous unpairing of bound variables distributes any quantifier prefix over disjunction
of two matrices. -/
theorem eval_or_unpair_iff (p : QuantifierPrefix) (R₁ R₂ : List ℕ → Prop)
    (xs₁ xs₂ xs : List ℕ) :
    p.Eval (fun l =>
      R₁ ((l.take p.depth).map (fun y => y.unpair.1) ++ xs₁) ∨
      R₂ ((l.take p.depth).map (fun y => y.unpair.2) ++ xs₂)) xs ↔
    p.Eval R₁ xs₁ ∨ p.Eval R₂ xs₂ :=
  (eval_and_or_unpair_aux p R₁ R₂ xs₁ xs₂ xs).2

/-! ### Associated arithmetical pointclasses -/

/-- The arithmetical pointclass named by a quantifier prefix relative to `Z`:
`zero ↦ IsSigma Z 0`, `sigma n ↦ IsSigma Z (n + 1)`, `pi n ↦ IsPi Z (n + 1)`. -/
def IsClass (Z : Set ℕ) : QuantifierPrefix → {α : Type*} → [Primcodable α] → (α → Prop) → Prop
  | .zero, _, _, P => IsSigma Z 0 P
  | .sigma n, _, _, P => IsSigma Z (n + 1) P
  | .pi n, _, _, P => IsPi Z (n + 1) P

/-- `zero` names the quantifier-free class Σ⁰₀. -/
@[simp]
theorem isClass_zero {Z : Set ℕ} {α : Type*} [Primcodable α] {P : α → Prop} :
    IsClass Z .zero P ↔ IsSigma Z 0 P := (Iff.rfl)

/-- `sigma n` names Σ⁰ₙ₊₁. -/
@[simp]
theorem isClass_sigma {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α] {P : α → Prop} :
    IsClass Z (.sigma n) P ↔ IsSigma Z (n + 1) P := (Iff.rfl)

/-- `pi n` names Π⁰ₙ₊₁. -/
@[simp]
theorem isClass_pi {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α] {P : α → Prop} :
    IsClass Z (.pi n) P ↔ IsPi Z (n + 1) P := (Iff.rfl)

/-- `ofSigma n` names Σ⁰ₙ for every `n`. -/
@[simp]
theorem isClass_ofSigma {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α] {P : α → Prop} :
    IsClass Z (ofSigma n) P ↔ IsSigma Z n P := by
  cases n <;> rfl

/-- `ofPi n` names Π⁰ₙ for every `n`. -/
@[simp]
theorem isClass_ofPi {Z : Set ℕ} {n : ℕ} {α : Type*} [Primcodable α] {P : α → Prop} :
    IsClass Z (ofPi n) P ↔ IsPi Z n P := by
  cases n with
  | zero => exact isPi_zero_iff.symm
  | succ n => rfl

/-- Pointclass membership depends only on the extension of the predicate. -/
theorem IsClass.of_eq {Z : Set ℕ} {p : QuantifierPrefix} {α : Type*} [Primcodable α]
    {P Q : α → Prop} (h : p.IsClass Z P) (hPQ : ∀ x, P x ↔ Q x) : p.IsClass Z Q := by
  cases p with
  | zero => exact IsSigma.of_eq h hPQ
  | sigma n => exact IsSigma.of_eq h hPQ
  | pi n => exact IsPi.of_eq h hPQ

/-- Every prefix pointclass is closed under `Z`-computable changes of parameters. -/
theorem IsClass.preimage {Z : Set ℕ} {p : QuantifierPrefix} {α β : Type*}
    [Primcodable α] [Primcodable β] {P : α → Prop} (h : p.IsClass Z P)
    {f : β → α} (hf : ComputableIn {Z.oracle} f) : p.IsClass Z (fun x => P (f x)) := by
  cases p with
  | zero => exact IsSigma.preimage h hf
  | sigma n => exact IsSigma.preimage h hf
  | pi n => exact IsPi.preimage h hf

/-- Complementation dualizes the prefix pointclass. -/
@[simp]
theorem isClass_not_iff {Z : Set ℕ} {p : QuantifierPrefix} {α : Type*} [Primcodable α]
    {P : α → Prop} : p.IsClass Z (fun x => ¬P x) ↔ p.dual.IsClass Z P := by
  cases p with
  | zero => exact isSigma_not_iff.trans isPi_zero_iff
  | sigma n => exact isSigma_not_iff
  | pi n => exact isPi_not_iff

/-- Hierarchy order on prefixes corresponds to inclusion of arithmetical pointclasses. -/
theorem IsClass.mono {Z : Set ℕ} {p q : QuantifierPrefix} {α : Type*} [Primcodable α]
    {P : α → Prop} (h : p.IsClass Z P) (hpq : p ≤ q) : q.IsClass Z P := by
  rcases hpq with rfl | hlt
  · exact h
  · cases p with
    | zero =>
      cases q with
      | zero => exact h
      | sigma m => exact h.of_le (Nat.zero_le _)
      | pi m => exact (isPi_zero_iff.2 h).of_le (Nat.zero_le _)
    | sigma n =>
      cases q with
      | zero => simp at hlt
      | sigma m => exact h.of_le hlt.le
      | pi m =>
        have hnm : n + 2 ≤ m + 1 := hlt
        exact h.pi_succ.of_le hnm
    | pi n =>
      cases q with
      | zero => simp at hlt
      | sigma m =>
        have hnm : n + 2 ≤ m + 1 := hlt
        exact h.sigma_succ.of_le hnm
      | pi m => exact h.of_le hlt.le

/-- Adding an existential number quantifier lands in `p.addExists.IsClass Z`, contracting with a
leading existential block when `p` is already existential. -/
theorem IsClass.exists_nat {Z : Set ℕ} {p : QuantifierPrefix} {α : Type*} [Primcodable α]
    {R : α × ℕ → Prop} (h : p.IsClass Z R) :
    p.addExists.IsClass Z (fun x => ∃ y, R (x, y)) := by
  cases p with
  | zero => exact isSigma_succ_iff.2 ⟨R, isPi_zero_iff.2 h, fun _ => Iff.rfl⟩
  | sigma _ => exact IsSigma.exists_nat h
  | pi _ => exact isSigma_succ_iff.2 ⟨R, h, fun _ => Iff.rfl⟩

/-- Adding a universal number quantifier lands in `p.addForall.IsClass Z`, contracting with a
leading universal block when `p` is already universal. -/
theorem IsClass.forall_nat {Z : Set ℕ} {p : QuantifierPrefix} {α : Type*} [Primcodable α]
    {R : α × ℕ → Prop} (h : p.IsClass Z R) :
    p.addForall.IsClass Z (fun x => ∀ y, R (x, y)) := by
  cases p with
  | zero => exact isPi_succ_iff.2 ⟨R, h, fun _ => Iff.rfl⟩
  | sigma _ => exact isPi_succ_iff.2 ⟨R, h, fun _ => Iff.rfl⟩
  | pi _ => exact IsPi.forall_nat h

end QuantifierPrefix

end TauCeti.ArithmeticalHierarchy
