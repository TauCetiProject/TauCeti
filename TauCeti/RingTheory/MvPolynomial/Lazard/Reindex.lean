/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Lazard.Valuation

/-!
# Lazard valuations in a specified coordinate order

The Lazard valuation depends on the linear order of the polynomial variables.  An equivalence
from the variables of a polynomial to a linearly ordered type therefore specifies an elimination
order: rename the polynomial along the equivalence and reindex the point by its inverse before
taking the ordinary Lazard valuation.

`MvPolynomial.lazardValuationReindex` packages this simultaneous reindexing.  It preserves
evaluation at the original point, so its zero and top cases have the same intrinsic
characterizations as the ordinary valuation.  Reindexings compose, renaming by the
inverse equivalence cancels the reindexing, and the basic product law continues to hold.  The
finite rotation formula identifies the coordinate order used when a cylindrical stack moves its
distinguished coordinate from the front to the end.

This interface makes the coordinate order explicit in projection-and-lifting arguments, where
successive stages use different presentations of the same ambient variables.

## References

S. McCallum, A. Parusiński, and L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), 52–69, Sections 2 and 5.
-/

public section

namespace MvPolynomial

variable {R σ τ υ : Type*}

/-- The Lazard valuation after ordering the variables of `p` through an equivalence `e`.
The point is reindexed simultaneously, so polynomial evaluation is unchanged. -/
noncomputable def lazardValuationReindex [CommSemiring R] [LinearOrder τ] [WellFoundedGT τ]
    (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) : WithTop (Lex (τ →₀ ℕ)) :=
  (rename e p).lazardValuation (a ∘ e.symm)

/-- Lazard valuation in a reindexed coordinate order, unfolded. -/
theorem lazardValuationReindex_def [CommSemiring R] [LinearOrder τ] [WellFoundedGT τ]
    (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) :
    p.lazardValuationReindex e a = (rename e p).lazardValuation (a ∘ e.symm) :=
  (rfl)

/-- Reindexing by the identity equivalence gives the ordinary Lazard valuation. -/
@[simp]
theorem lazardValuationReindex_refl [CommSemiring R] [LinearOrder σ] [WellFoundedGT σ]
    (p : MvPolynomial σ R) (a : σ → R) :
    p.lazardValuationReindex (Equiv.refl σ) a = p.lazardValuation a := by
  rw [lazardValuationReindex_def]
  simp

/-- Successive changes of coordinate order combine by composition of their equivalences. -/
theorem lazardValuationReindex_trans [CommSemiring R]
    [LinearOrder υ] [WellFoundedGT υ]
    (p : MvPolynomial σ R) (e : σ ≃ τ) (f : τ ≃ υ) (a : σ → R) :
    p.lazardValuationReindex (e.trans f) a =
      (rename e p).lazardValuationReindex f (a ∘ e.symm) := by
  rw [lazardValuationReindex_def, lazardValuationReindex_def]
  simp [Function.comp_def]

/-- Reindexing a polynomial renamed by the inverse equivalence gives the ordinary Lazard
valuation at the reindexed point. -/
@[simp]
theorem lazardValuationReindex_rename_symm [CommSemiring R] [LinearOrder τ] [WellFoundedGT τ]
    (p : MvPolynomial τ R) (e : σ ≃ τ) (a : σ → R) :
    (rename e.symm p).lazardValuationReindex e a = p.lazardValuation (a ∘ e.symm) := by
  rw [lazardValuationReindex_def, rename_rename, e.self_comp_symm, rename_id_apply]

/-- A reindexed Lazard valuation is zero exactly when the original polynomial does not vanish
at the original point. -/
@[simp]
theorem lazardValuationReindex_eq_zero_iff [CommSemiring R]
    [LinearOrder τ] [WellFoundedGT τ] (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) :
    p.lazardValuationReindex e a = 0 ↔ eval a p ≠ 0 := by
  rw [lazardValuationReindex_def, lazardValuation_eq_zero_iff, eval_rename]
  simp [Function.comp_def]

/-- The reindexed Lazard valuation of the zero polynomial is top. -/
@[simp]
theorem lazardValuationReindex_zero [CommSemiring R]
    [LinearOrder τ] [WellFoundedGT τ] (e : σ ≃ τ) (a : σ → R) :
    (0 : MvPolynomial σ R).lazardValuationReindex e a = ⊤ := by
  rw [lazardValuationReindex_def, map_zero, lazardValuation_zero]

/-- A reindexed Lazard valuation is top exactly for the zero polynomial. -/
@[simp]
theorem lazardValuationReindex_eq_top_iff [CommRing R]
    [LinearOrder τ] [WellFoundedGT τ] (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) :
    p.lazardValuationReindex e a = ⊤ ↔ p = 0 := by
  rw [lazardValuationReindex_def, lazardValuation_eq_top_iff,
    rename_eq_zero_iff_of_injective _ e.injective]

/-- The reindexed Lazard valuation of one is zero. -/
@[simp]
theorem lazardValuationReindex_one [CommSemiring R] [Nontrivial R]
    [LinearOrder τ] [WellFoundedGT τ] (e : σ ≃ τ) (a : σ → R) :
    (1 : MvPolynomial σ R).lazardValuationReindex e a = 0 := by
  rw [lazardValuationReindex_def, map_one, lazardValuation_one]

/-- Reindexed Lazard valuation is additive on products over a domain. -/
theorem lazardValuationReindex_mul [CommSemiring R] [NoZeroDivisors R]
    [LinearOrder τ] [WellFoundedGT τ] (p q : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) :
    (p * q).lazardValuationReindex e a =
      p.lazardValuationReindex e a + q.lazardValuationReindex e a := by
  rw [lazardValuationReindex_def, lazardValuationReindex_def,
    lazardValuationReindex_def, map_mul, lazardValuation_mul]

/-- Reindexed Lazard valuation scales by the exponent under powers. -/
theorem lazardValuationReindex_pow [CommSemiring R] [NoZeroDivisors R] [Nontrivial R]
    [LinearOrder τ] [WellFoundedGT τ] (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R)
    (n : ℕ) :
    (p ^ n).lazardValuationReindex e a = n • p.lazardValuationReindex e a := by
  rw [lazardValuationReindex_def, lazardValuationReindex_def, map_pow,
    lazardValuation_pow]

/-- Negation does not change a reindexed Lazard valuation. -/
@[simp]
theorem lazardValuationReindex_neg [CommRing R]
    [LinearOrder τ] [WellFoundedGT τ] (p : MvPolynomial σ R) (e : σ ≃ τ) (a : σ → R) :
    (-p).lazardValuationReindex e a = p.lazardValuationReindex e a := by
  rw [lazardValuationReindex_def, lazardValuationReindex_def, map_neg,
    lazardValuation_neg]

/-- A polynomial has only finitely many Lazard valuations in any fixed reindexed coordinate
order. -/
theorem finite_range_lazardValuationReindex [CommSemiring R]
    [LinearOrder τ] [WellFoundedGT τ] (p : MvPolynomial σ R) (e : σ ≃ τ) :
    (Set.range (p.lazardValuationReindex e)).Finite := by
  refine (finite_range_lazardValuation (rename e p)).subset ?_
  rintro _ ⟨a, rfl⟩
  exact ⟨a ∘ e.symm, lazardValuationReindex_def p e a⟩

/-- Moving coordinate zero to the end is reindexing by the inverse finite rotation. -/
theorem lazardValuationReindex_finRotate_symm {n : ℕ} [CommSemiring R]
    (p : MvPolynomial (Fin (n + 1)) R) (a : Fin (n + 1) → R) :
    p.lazardValuationReindex (finRotate (n + 1)).symm a =
      (rename (finRotate (n + 1)).symm p).lazardValuation
        (Fin.snoc (Fin.tail a) (a 0)) := by
  rw [lazardValuationReindex_def, Fin.snoc_eq_cons_rotate]
  rw [Fin.cons_self_tail]
  rfl

end MvPolynomial
