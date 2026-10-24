/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.ModelTheory.Complexity
public import Mathlib.ModelTheory.Definability
public import TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic
public import TauCeti.ModelTheory.Algebra.OrderedRing.SignCondition

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
  quantifier-free formula without parameters defines a semialgebraic set, since it is a sign
  condition on finitely many integer polynomials
  (`FirstOrder.Language.BoundedFormula.IsQF.exists_realize_iff_sign`).
* `TauCeti.isSemialgebraic_iff_exists_isQF`: a set is semialgebraic if and only if it is defined
  by a quantifier-free formula whose extra variables `Sum.inl r` are assigned the parameters
  `r ∈ R`. The strict inequality `0 < p` is expressed as the negation `¬ p ≤ 0`.
* `TauCeti.IsSemialgebraic.definable`: hence every semialgebraic set is definable with parameters,
  in the sense of Mathlib's `Set.Definable`.

The converse of the last statement, that every definable set is semialgebraic, is quantifier
elimination; over a real closed field it is the Tarski–Seidenberg theorem.
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.QuantifierElimination` derives it from closure of
semialgebraic sets under projection.

To apply these results to a concrete ordered field such as `ℝ`, install the structures
`FirstOrder.Ring.compatibleRingOfRing ℝ` and `FirstOrder.Language.orderStructure ℝ`; the
`OrderedStructure` hypothesis is then found by the instances
`FirstOrder.Language.orderedStructure_orderStructure` and
`FirstOrder.Language.orderedStructure_sum` of `TauCeti.ModelTheory.Order`.

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
  -- The formula is a sign condition on finitely many integer polynomials.
  obtain ⟨m, p, Φ, h⟩ := hφ.exists_realize_iff_sign
  convert isSemialgebraic_setOf_sign_eval (fun i ↦ (p i).map (Int.castRingHom R)) Φ using 3 with x
  rw [h R, Sum.elim_comp_inl_inr]
  simp only [aeval_def, algebraMap_int_eq, eval_map]

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
