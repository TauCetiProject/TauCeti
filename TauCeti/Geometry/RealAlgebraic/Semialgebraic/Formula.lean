/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Definability
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.ModelTheory.Algebra.OrderedRing.MvPolynomial

/-!
# Semialgebraic sets are the quantifier-free definable sets

Let `R` be a commutative ring with a linear order compatible with addition, regarded as a structure
in the first-order language of ordered rings `Language.ring.sum Language.order`, with the ring
symbols and `≤` interpreted as usual. This file identifies the semialgebraic subsets of `σ → R`,
defined intrinsically as finite Boolean combinations of polynomial zero sets and positivity sets
(`TauCeti.IsSemialgebraic`), with the sets defined by quantifier-free formulas with parameters
from `R`.

* `FirstOrder.Language.BoundedFormula.IsQF.isSemialgebraic_setOf_realize` and
  `FirstOrder.Language.BoundedFormula.IsQF.isSemialgebraic_setOf_formula_realize`: a
  quantifier-free formula without parameters defines a semialgebraic set. An equation of terms
  becomes the zero set of the difference of their polynomials and `t₁ ≤ t₂` becomes a weak sign
  condition.
* `TauCeti.isSemialgebraic_iff_exists_isQF`: a set is semialgebraic if and only if it is defined
  by a quantifier-free formula whose extra variables `Sum.inl r` are assigned the parameters
  `r ∈ R`. The strict inequality `0 < p` is expressed as the negation `¬ p ≤ 0`.
* `TauCeti.IsSemialgebraic.definable`: hence every semialgebraic set is definable with parameters,
  in the sense of Mathlib's `Set.Definable`.

The converse of the last statement, that every definable set is semialgebraic, is quantifier
elimination; over a real closed field it is the Tarski–Seidenberg theorem.

To apply these results to a concrete ordered field such as `ℝ`, install the structures
`FirstOrder.Ring.compatibleRingOfRing ℝ` and `FirstOrder.Language.orderStructure ℝ`; the
`OrderedStructure` hypothesis then holds by `⟨fun _ => Iff.rfl⟩`.

## References

S. Basu, R. Pollack, and M.-F. Roy,
[Algorithms in Real Algebraic Geometry](https://doi.org/10.1007/3-540-33099-2),
second edition, Chapter 2, for semi-algebraic sets as the realizations of quantifier-free formulas.
-/

public section

open FirstOrder FirstOrder.Language MvPolynomial TauCeti

variable {R : Type*} [CommRing R] [Ring.CompatibleRing R] [Language.order.Structure R]

variable [LinearOrder R] [IsOrderedAddMonoid R]
  [(Language.ring.sum Language.order).OrderedStructure R]

namespace FirstOrder.Language.BoundedFormula.IsQF

variable {α : Type*} {n : ℕ}

/-- A quantifier-free formula of ordered rings, with free variables `α` and `n` bound variables,
defines a semialgebraic subset of `α ⊕ Fin n → R`. -/
theorem isSemialgebraic_setOf_realize {φ : (Language.ring.sum Language.order).BoundedFormula α n}
    (hφ : φ.IsQF) :
    IsSemialgebraic {x : α ⊕ Fin n → R | φ.Realize (x ∘ Sum.inl) (x ∘ Sum.inr)} := by
  induction hφ with
  | falsum =>
    convert isSemialgebraic_empty (σ := α ⊕ Fin n) (R := R)
    exact Set.eq_empty_of_forall_notMem fun _ h => realize_bot.1 h
  | of_isAtomic h =>
    cases h with
    | equal t₁ t₂ =>
      convert isSemialgebraic_eval_eq (t₁.toMvPolynomial.map (Int.castRingHom R))
        (t₂.toMvPolynomial.map (Int.castRingHom R)) using 3 with x
      rw [realize_bdEqual, Sum.elim_comp_inl_inr, Term.realize_eq_eval_map_toMvPolynomial,
        Term.realize_eq_eval_map_toMvPolynomial]
    | rel r ts =>
      simp only [realize_rel]
      -- The ring language has no relation symbols; the only one of the order language is `≤`.
      rcases r with r | r
      · exact nomatch r
      · cases r
        convert isSemialgebraic_eval_le ((ts 0).toMvPolynomial.map (Int.castRingHom R))
          ((ts 1).toMvPolynomial.map (Int.castRingHom R)) using 3 with x
        refine (relMap_leSymb (L := Language.ring.sum Language.order) _).trans ?_
        simp [Sum.elim_comp_inl_inr, Term.realize_eq_eval_map_toMvPolynomial]
  | imp h₁ h₂ ih₁ ih₂ =>
    simpa [Set.ofPred_or, imp_iff_not_or, Set.compl_ofPred] using ih₁.compl.union ih₂

/-- A quantifier-free formula of ordered rings with free variables `α` defines a semialgebraic
subset of `α → R`. -/
theorem isSemialgebraic_setOf_formula_realize
    {φ : (Language.ring.sum Language.order).Formula α} (hφ : φ.IsQF) :
    IsSemialgebraic {v : α → R | φ.Realize v} := by
  convert (hφ.isSemialgebraic_setOf_realize (R := R)).preimage_comp
    (Sum.elim id finZeroElim : α ⊕ Fin 0 → α) using 1
  ext v
  simp only [Set.mem_preimage, Set.mem_ofPred_eq, Formula.Realize, Function.comp_assoc,
    Sum.elim_comp_inl, Function.comp_id]
  exact iff_of_eq (congrArg _ (Subsingleton.elim _ _))

end FirstOrder.Language.BoundedFormula.IsQF

namespace TauCeti

variable {σ : Type*}

/-- A subset of `σ → R` is semialgebraic if and only if it is defined by a quantifier-free formula
of ordered rings with parameters from `R`: the formula has free variables `R ⊕ σ`, and each
variable `Sum.inl r` is assigned the value `r`. -/
theorem isSemialgebraic_iff_exists_isQF {s : Set (σ → R)} :
    IsSemialgebraic s ↔ ∃ φ : (Language.ring.sum Language.order).Formula (R ⊕ σ),
      φ.IsQF ∧ s = {v | φ.Realize (Sum.elim id v)} := by
  constructor
  · intro hs
    refine IsSemialgebraic.induction (fun p => ?_) (fun p => ?_)
      ⟨⊥, BoundedFormula.isQF_bot, by simp⟩
      (fun s _ ⟨φ, hφ, hs⟩ => ⟨φ.not, hφ.not, by ext; simp [hs]⟩)
      (fun s t _ _ ⟨φ, hφ, hs⟩ ⟨ψ, hψ, ht⟩ => ⟨φ ⊔ ψ, hφ.sup hψ, by ext; simp [hs, ht]⟩) hs
    · -- The zero set of `p` is defined by the equation `p = 0`.
      obtain ⟨t, ht⟩ := p.exists_term_realize_eq_eval
      obtain ⟨z, hz⟩ := (0 : MvPolynomial σ R).exists_term_realize_eq_eval
      refine ⟨t.equal z, (BoundedFormula.IsAtomic.equal _ _).isQF, ?_⟩
      ext v
      simp [ht, hz]
    · -- The positivity set of `p` is defined by `¬ p ≤ 0`.
      obtain ⟨t, ht⟩ := p.exists_term_realize_eq_eval
      obtain ⟨z, hz⟩ := (0 : MvPolynomial σ R).exists_term_realize_eq_eval
      refine ⟨(leSymb.formula₂ t z).not, (BoundedFormula.IsAtomic.rel _ _).isQF.not, ?_⟩
      ext v
      simp [ht, hz]
  · rintro ⟨φ, hφ, rfl⟩
    -- Substituting the parameters is a polynomial map.
    have h := hφ.isSemialgebraic_setOf_formula_realize.preimage_eval
      (Sum.elim C X : R ⊕ σ → MvPolynomial σ R)
    have hf : (fun (v : σ → R) i => eval v (Sum.elim C X i)) = fun v => Sum.elim id v := by
      ext v (r | i) <;> simp
    rwa [hf] at h

/-- A semialgebraic subset of `σ → R` is definable in the language of ordered rings with
parameters from `R`. -/
theorem IsSemialgebraic.definable {s : Set (σ → R)} (hs : IsSemialgebraic s) :
    (Set.univ : Set R).Definable (Language.ring.sum Language.order) s := by
  obtain ⟨φ, -, rfl⟩ := isSemialgebraic_iff_exists_isQF.1 hs
  rw [Set.definable_iff_exists_formula_sum]
  refine ⟨φ.relabel (Sum.map (fun r => ⟨r, Set.mem_univ r⟩) id), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, Formula.realize_relabel]
  congr! 1
  ext (r | i) <;> simp

end TauCeti
