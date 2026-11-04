/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.MvPolynomial.Box
public import TauCeti.RingTheory.MvPolynomial.WeightedIndex
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Linear conditions imposing prescribed weighted indices

A polynomial of partial degrees at most `d` has weighted index at least `t` at a point
exactly when its Hasse derivatives of weighted order strictly less than `t` vanish there.
Only derivative orders in the coefficient box need to be tested.

`MvPolynomial.indexConditionMap` writes these conditions as a linear map on coefficient
vectors, allowing several points in a commutative algebra. Its kernel parametrizes exactly the
polynomials with the prescribed indices. Over a base field, each equation in a finite-dimensional
algebra costs at most the algebra's dimension. Thus, if the number of coefficients exceeds that
cost, a nonzero polynomial with all the prescribed indices exists.

This is the linear-algebraic existence step in the construction of auxiliary polynomials;
it does not bound the height of the polynomial. The explicit rows are `hasseDerivRow`, so
height estimates for those rows can be used when selecting small vectors in the kernel.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, Lemma 6.3.4.
-/

public section

namespace MvPolynomial

open scoped ENNReal

variable {σ κ R F : Type*} [Fintype σ] [DecidableEq σ]

/-- The derivative orders in the box whose weighted order is strictly less than `t`.
These are precisely the potentially nontrivial equations imposing index at least `t`
on a polynomial of partial degrees at most `d`. -/
noncomputable def indexConditions (d : σ → ℕ) (t : ℝ) : Finset (∀ j, Fin (d j + 1)) :=
  Finset.univ.filter fun I ↦ ∑ j, (I j : ℝ) / d j < t

@[simp]
theorem mem_indexConditions {d : σ → ℕ} {t : ℝ} {I : ∀ j, Fin (d j + 1)} :
    I ∈ indexConditions d t ↔ ∑ j, (I j : ℝ) / d j < t := by
  simp [indexConditions]

section Semiring

variable [CommSemiring R]

/-- A bounded-degree polynomial has index at least `t` exactly when the jets indexed by
`indexConditions d t` vanish. Zero partial-degree bounds and nonpositive thresholds are allowed. -/
theorem ofReal_le_weightedIndex_iff_indexConditions {d : σ → ℕ} {t : ℝ}
    {a : σ → R} {P : MvPolynomial σ R} (hP : ∀ j, P.degreeOf j ≤ d j) :
    ENNReal.ofReal t ≤ weightedIndex d a P ↔
      ∀ I ∈ indexConditions d t, eval a (hasseDeriv (boxMonomial d I) P) = 0 := by
  constructor
  · intro h I hI
    by_contra hne
    have hle := (le_sum_div_of_le_weightedIndex hP h hne).2
    simp only [boxMonomial_apply] at hle
    exact (not_lt_of_ge hle) (mem_indexConditions.mp hI)
  · intro h
    apply ofReal_le_weightedIndex_of_eval_hasseDeriv_eq_zero hP
    intro μ hμ ht
    obtain ⟨I, rfl⟩ := exists_boxMonomial_eq hμ
    exact h I (mem_indexConditions.mpr (by simpa using ht))

variable [CommSemiring F] [Algebra R F]

/-- The linear system on box coefficients imposing the indices `t k` at the points `a k`.
The equations take values in `F`, but the coefficient vectors and linearity are over `R`. -/
noncomputable def indexConditionMap (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ) :
    ((∀ j, Fin (d j + 1)) → R) →ₗ[R]
      ((k : κ) → indexConditions d (t k) → F) :=
  LinearMap.pi fun k ↦ LinearMap.pi fun I ↦
    (aeval (a k)).toLinearMap ∘ₗ hasseDeriv (boxMonomial d I.1) ∘ₗ ofBox d

/-- An equation of the index system is the corresponding Hasse jet of the box polynomial. -/
@[simp]
theorem indexConditionMap_apply (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ)
    (x : (∀ j, Fin (d j + 1)) → R) (k : κ) (I : indexConditions d (t k)) :
    indexConditionMap d a t x k I = aeval (a k) (hasseDeriv (boxMonomial d I.1) (ofBox d x)) :=
  (rfl)

/-- The row of the index system is the explicit binomial-and-power row of Hasse evaluation. -/
theorem indexConditionMap_apply_eq_sum (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ)
    (x : (∀ j, Fin (d j + 1)) → R) (k : κ) (I : indexConditions d (t k)) :
    indexConditionMap d a t x k I =
      ∑ J, hasseDerivRow d (a k) (boxMonomial d I.1) J * algebraMap R F (x J) := by
  rw [indexConditionMap_apply, aeval_hasseDeriv_ofBox]

/-- The kernel of the index system consists exactly of coefficient vectors whose polynomials,
after coefficient extension, have the prescribed indices. -/
theorem mem_ker_indexConditionMap_iff (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ)
    (x : (∀ j, Fin (d j + 1)) → R) :
    x ∈ LinearMap.ker (indexConditionMap d a t) ↔
      ∀ k, ENNReal.ofReal (t k) ≤ weightedIndex d (a k) (map (algebraMap R F) (ofBox d x)) := by
  have hdeg (j) : (map (algebraMap R F) (ofBox d x)).degreeOf j ≤ d j := by
    rw [map_ofBox]
    exact degreeOf_ofBox_le _ j
  simp only [LinearMap.mem_ker, funext_iff, Pi.zero_apply, indexConditionMap_apply,
    ofReal_le_weightedIndex_iff_indexConditions hdeg]
  constructor
  · intro h k I hI
    simpa only [hasseDeriv_map, eval_map, ← aeval_def] using h k ⟨I, hI⟩
  · intro h k I
    simpa only [hasseDeriv_map, eval_map, ← aeval_def] using h k I.1 I.2

end Semiring

section Field

variable [Field R] [CommRing F] [Algebra R F] [Module.Finite R F] [Fintype κ]

/-- The dimension left after imposing the index conditions is at least the coefficient count
minus the algebra's dimension times the number of algebra-valued equations. Dependencies among
conditions can only increase this dimension. -/
theorem sub_le_finrank_ker_indexConditionMap (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ) :
    (∏ j, (d j + 1)) - Module.finrank R F * ∑ k, (indexConditions d (t k)).card ≤
      Module.finrank R (LinearMap.ker (indexConditionMap (R := R) d a t)) := by
  have hdim : Module.finrank R ((k : κ) → indexConditions d (t k) → F) =
      Module.finrank R F * ∑ k, (indexConditions d (t k)).card := by
    simp [Module.finrank_pi_fintype, Finset.mul_sum, mul_comm]
  have hnull := (indexConditionMap (R := R) d a t).finrank_range_add_finrank_ker
  have hrange := (LinearMap.range (indexConditionMap (R := R) d a t)).finrank_le
  rw [hdim] at hrange
  simp only [Module.finrank_pi, Fintype.card_pi, Fintype.card_fin] at hnull
  omega

/-- If there are more coefficients than the dimension cost of the index conditions,
there is a nonzero base-field polynomial of the given partial degrees with all the prescribed
indices at the algebra-valued points. No assertion about its height is made. -/
theorem exists_ne_zero_forall_le_weightedIndex (d : σ → ℕ) (a : κ → σ → F) (t : κ → ℝ)
    (hcount : Module.finrank R F * ∑ k, (indexConditions d (t k)).card < ∏ j, (d j + 1)) :
    ∃ P : MvPolynomial σ R, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ d j) ∧
      ∀ k, ENNReal.ofReal (t k) ≤ weightedIndex d (a k) (map (algebraMap R F) P) := by
  have hpos : 0 < Module.finrank R (LinearMap.ker (indexConditionMap (R := R) d a t)) := by
    have := sub_le_finrank_ker_indexConditionMap (R := R) d a t
    omega
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (Submodule.one_le_finrank_iff.mp hpos)
  refine ⟨ofBox d x, ?_, degreeOf_ofBox_le x, (mem_ker_indexConditionMap_iff d a t x).mp hx⟩
  exact fun h ↦ hx0 (ofBox_injective (by simpa using h))

end Field

/-! The boundary order is not a condition: for degree three and index one third, only the
zeroth jet is constrained. Two such conditions leave a nonzero polynomial over the base. -/
example (a : Fin 2 → Unit → ℚ) :
    ∃ P : MvPolynomial Unit ℚ, P ≠ 0 ∧ (∀ j, P.degreeOf j ≤ 3) ∧
      ∀ k, ENNReal.ofReal (1 / 3) ≤ weightedIndex (fun _ ↦ 3) (a k) P := by
  classical
  have hcard : (indexConditions (fun _ : Unit ↦ 3) (1 / 3)).card = 1 := by
    have heq : indexConditions (fun _ : Unit ↦ 3) (1 / 3) = {fun _ ↦ 0} := by
      ext I
      simp only [mem_indexConditions, Fintype.sum_unique, Finset.mem_singleton]
      constructor
      · intro h
        have hzero : (I () : ℕ) = 0 := by
          have hlt : (I () : ℝ) < 1 := (div_lt_div_iff_of_pos_right (by norm_num)).mp h
          exact Nat.lt_one_iff.mp (by exact_mod_cast hlt)
        funext j
        exact Fin.ext (by simpa using hzero)
      · rintro rfl
        norm_num
    rw [heq, Finset.card_singleton]
  simp only [one_div] at hcard
  have h := exists_ne_zero_forall_le_weightedIndex (R := ℚ) (fun _ : Unit ↦ 3) a
    (fun _ ↦ 1 / 3) (by simp [hcard])
  simpa [map_id] using h

-- With no variables and a positive threshold, the single constant coefficient is constrained.
-- Thus the condition count cannot produce a nonzero constant of positive index.
example [IsEmpty σ] (d : σ → ℕ) {t : ℝ} (ht : 0 < t) :
    (indexConditions d t).card = 1 := by
  classical
  simp [indexConditions, ht]

end MvPolynomial
