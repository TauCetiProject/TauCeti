/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Sign.Basic
public import TauCeti.ModelTheory.Algebra.OrderedRing.MvPolynomial
public import TauCeti.ModelTheory.Complexity

/-!
# Quantifier-free formulas of ordered rings as sign conditions

A quantifier-free formula of the language of ordered rings `Language.ring.sum Language.order` is a
Boolean combination of equations `t₁ = t₂` and inequalities `t₁ ≤ t₂` between terms, and a term is
an integer polynomial (`FirstOrder.Language.Term.toMvPolynomial`). This file proves that such
formulas are exactly the sign conditions on finitely many integer polynomials: conditions that
depend only on the signs of the values of the polynomials.

* `FirstOrder.Language.BoundedFormula.IsQF.exists_realize_iff_sign`: a quantifier-free formula
  holds exactly when a fixed condition `Φ` holds of the signs of finitely many fixed integer
  polynomials `p i` in its free and bound variables.
* `FirstOrder.Language.BoundedFormula.exists_isQF_realize_iff_sign`: conversely, every condition
  on the signs of finitely many integer polynomials is expressed by a quantifier-free formula,
  built from the atomic formulas `FirstOrder.Language.Term.signFormula` saying that a term has a
  given sign.

The polynomials, the sign condition and the formula do not depend on the structure in which the
formula is interpreted: the equivalences hold in every commutative ring with a compatible linear
order, with the ring symbols and `≤` interpreted as usual. The first statement needs the order to
be compatible with addition, since `t₁ ≤ t₂` becomes the condition that `t₁ - t₂` is not positive.
The second needs no such compatibility, since a sign condition on `p` compares `p` with `0`.

These are the formula-level translation laws between formulas of ordered rings and polynomial sign
conditions. Over a fixed ring they identify semialgebraic sets with quantifier-free definable sets,
as in `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Formula`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Section 2.3, for quantifier-free formulas and sign conditions.
-/

public section

universe u

open FirstOrder FirstOrder.Language MvPolynomial

namespace FirstOrder.Language.Term

variable {α : Type*} {n : ℕ}

/-- The quantifier-free formula saying that the value of the term `t` has sign `s`. -/
noncomputable def signFormula (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n)) :
    SignType → (Language.ring.sum Language.order).BoundedFormula α n
  | .zero => t.bdEqual (func (Sum.inl Ring.zeroFunc) ![])
  | .neg => (leSymb.boundedFormula₂ (func (Sum.inl Ring.zeroFunc) ![]) t).not
  | .pos => (leSymb.boundedFormula₂ t (func (Sum.inl Ring.zeroFunc) ![])).not

/-- The formula `t.signFormula s` is quantifier-free. -/
theorem isQF_signFormula (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n))
    (s : SignType) : (t.signFormula s).IsQF := by
  cases s
  · exact (BoundedFormula.IsAtomic.equal _ _).isQF
  · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not
  · exact (BoundedFormula.IsAtomic.rel _ _).isQF.not

/-- The formula `t.signFormula s` holds exactly when the value of `t` has sign `s`. -/
@[simp]
theorem realize_signFormula {R : Type*} [CommRing R] [Ring.CompatibleRing R]
    [Language.order.Structure R] [LinearOrder R]
    [(Language.ring.sum Language.order).OrderedStructure R]
    (t : (Language.ring.sum Language.order).Term (α ⊕ Fin n)) (s : SignType) (v : α → R)
    (xs : Fin n → R) :
    (t.signFormula s).Realize v xs ↔ SignType.sign (t.realize (Sum.elim v xs)) = s := by
  have h0 : (func (Sum.inl Ring.zeroFunc) ![] :
      (Language.ring.sum Language.order).Term (α ⊕ Fin n)).realize (Sum.elim v xs) = 0 := by
    simp [realize_eq_aeval_toMvPolynomial]
  cases s <;>
    simp [signFormula, h0, relMap_leSymb (L := Language.ring.sum Language.order),
      sign_eq_neg_one_iff, sign_eq_one_iff]

end FirstOrder.Language.Term

namespace FirstOrder.Language.BoundedFormula

variable {α : Type*} {n : ℕ}

/-- A **quantifier-free formula is a sign condition**. For a quantifier-free formula `φ` of
ordered rings there are finitely many integer polynomials `p i` in the free and bound variables of
`φ`, and a condition `Φ` on their signs, such that in every commutative ring with a compatible
linear order `φ` holds exactly when `Φ` holds of the signs of the values of the `p i`. -/
theorem IsQF.exists_realize_iff_sign {φ : (Language.ring.sum Language.order).BoundedFormula α n}
    (hφ : φ.IsQF) :
    ∃ (m : ℕ) (p : Fin m → MvPolynomial (α ⊕ Fin n) ℤ) (Φ : (Fin m → SignType) → Prop),
      ∀ (R : Type u) [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
        [LinearOrder R] [IsOrderedAddMonoid R]
        [(Language.ring.sum Language.order).OrderedStructure R] (v : α → R) (xs : Fin n → R),
        φ.Realize v xs ↔ Φ fun i ↦ SignType.sign (aeval (Sum.elim v xs) (p i)) := by
  induction hφ with
  | falsum => exact ⟨0, finZeroElim, fun _ ↦ False, fun _ _ _ _ _ _ _ _ _ ↦ realize_bot⟩
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      -- `t₁ = t₂` holds exactly when `t₁ - t₂` has sign zero.
      refine ⟨1, ![t₁.toMvPolynomial - t₂.toMvPolynomial], fun s ↦ s 0 = 0,
        fun _ _ _ _ _ _ _ v xs ↦ ?_⟩
      simp [Term.realize_eq_aeval_toMvPolynomial, sub_eq_zero]
    | rel r ts =>
      -- The ring language has no relation symbols; the only one of the order language is `≤`,
      -- and `t₁ ≤ t₂` holds exactly when `t₁ - t₂` is not positive.
      rcases r with r | r
      · exact nomatch r
      · cases r
        refine ⟨1, ![(ts 0).toMvPolynomial - (ts 1).toMvPolynomial], fun s ↦ s 0 ≠ 1,
          fun _ _ _ _ _ _ _ v xs ↦ ?_⟩
        refine (relMap_leSymb (L := Language.ring.sum Language.order) _).trans ?_
        simp [Term.realize_eq_aeval_toMvPolynomial, sign_eq_one_iff]
  | imp _ _ ih₁ ih₂ =>
    -- Concatenate the two lists of polynomials.
    obtain ⟨m₁, p₁, Φ₁, h₁⟩ := ih₁
    obtain ⟨m₂, p₂, Φ₂, h₂⟩ := ih₂
    refine ⟨m₁ + m₂, Fin.append p₁ p₂,
      fun s ↦ Φ₁ (fun i ↦ s (Fin.castAdd m₂ i)) → Φ₂ (fun j ↦ s (Fin.natAdd m₁ j)),
      fun R _ _ _ _ _ _ v xs ↦ ?_⟩
    simp only [realize_imp, h₁ R v xs, h₂ R v xs, Fin.append_left, Fin.append_right]

/-- A **sign condition is a quantifier-free formula**. For finitely many integer polynomials
`p i` and a condition `Φ` on their signs there is a quantifier-free formula of ordered rings which,
in every commutative ring with a compatible linear order, holds exactly when `Φ` holds of the signs
of the values of the `p i`. -/
theorem exists_isQF_realize_iff_sign {m : ℕ} (p : Fin m → MvPolynomial (α ⊕ Fin n) ℤ)
    (Φ : (Fin m → SignType) → Prop) :
    ∃ φ : (Language.ring.sum Language.order).BoundedFormula α n, φ.IsQF ∧
      ∀ (R : Type u) [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]
        [LinearOrder R] [(Language.ring.sum Language.order).OrderedStructure R]
        (v : α → R) (xs : Fin n → R),
        φ.Realize v xs ↔ Φ fun i ↦ SignType.sign (aeval (Sum.elim v xs) (p i)) := by
  choose t ht using fun i ↦ Term.toMvPolynomial_surjective (p i)
  -- The disjunction, over the sign vectors `s` satisfying `Φ`, of the statements that the
  -- polynomials have the signs `s`.
  refine ⟨iSup fun s : {s // Φ s} ↦ iInf fun i ↦ (t i).signFormula (s.1 i),
    IsQF.iSup fun _ ↦ IsQF.iInf fun _ ↦ Term.isQF_signFormula _ _, fun R _ _ _ _ _ v xs ↦ ?_⟩
  simp only [realize_iSup, realize_iInf, Term.realize_signFormula,
    Term.realize_eq_aeval_toMvPolynomial, ht]
  exact ⟨fun ⟨s, hs⟩ ↦ (funext hs : _ = s.1) ▸ s.2, fun h ↦ ⟨⟨_, h⟩, fun _ ↦ rfl⟩⟩

end FirstOrder.Language.BoundedFormula
