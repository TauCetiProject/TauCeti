/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Tactic.LinearCombination

/-! # Polynomial Rolle and mean value

`TauCeti.PolynomialRolle R` states that equal polynomial values at distinct endpoints give
an interior root of the formal derivative. From this explicit hypothesis over an ordered
field, `PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul` derives polynomial mean value;
`PolynomialRolle.monotoneOn`, `antitoneOn`, `strictMonoOn`, and `strictAntiOn` derive the
corresponding order properties from derivative signs.

`TauCeti.FieldTheory.RealClosure.AbstractRolle` supplies this hypothesis from `IsRealClosed`
and exports direct `Polynomial` versions of these results for real closed ordered fields.
The `IsRealClosed ℝ` instance specializes those statements to the real numbers.
-/

public section

open Polynomial Set

namespace TauCeti

/-- Polynomial Rolle, stated without topology or completeness hypotheses. -/
def PolynomialRolle (R : Type*) [Field R] [LinearOrder R] : Prop :=
  ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0

variable {R : Type*} [Field R] [LinearOrder R]

/-- Construct the polynomial Rolle property from its quantified statement. -/
theorem PolynomialRolle.of_forall
    (h : ∀ (p : R[X]) (a b : R), a < b → p.eval a = p.eval b →
      ∃ c ∈ Ioo a b, p.derivative.eval c = 0) : PolynomialRolle R := h

/-- Equal polynomial values at distinct endpoints give an interior derivative root. -/
theorem PolynomialRolle.exists_derivative_root (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hab : a < b) (heq : p.eval a = p.eval b) :
    ∃ c ∈ Ioo a b, p.derivative.eval c = 0 := h p a b hab heq

variable [IsStrictOrderedRing R]

/-- Polynomial Rolle implies the mean value equality
`p.eval b - p.eval a = p.derivative.eval c * (b - a)` at some point `c ∈ Ioo a b`. -/
theorem PolynomialRolle.exists_eval_sub_eq_derivative_eval_mul
    (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hab : a < b) :
    ∃ c ∈ Ioo a b, p.eval b - p.eval a = p.derivative.eval c * (b-a) := by
  let m := (p.eval b - p.eval a) / (b-a)
  have hba : b-a ≠ 0 := sub_ne_zero.mpr hab.ne'
  have hm : m * (b-a) = p.eval b - p.eval a := div_mul_cancel₀ _ hba
  have heq : (p - C m * X).eval a = (p - C m * X).eval b := by
    simp only [eval_sub, eval_mul, eval_C, eval_X]
    linear_combination hm
  obtain ⟨c, hc, hd⟩ := h.exists_derivative_root (p - C m * X) hab heq
  refine ⟨c, hc, ?_⟩
  have hd' : p.derivative.eval c = m := by
    simpa [sub_eq_zero] using hd
  rw [hd']
  exact hm.symm

/-- The mean value point for a subinterval lies in the surrounding open interval. -/
private theorem PolynomialRolle.exists_sub_eq (h : PolynomialRolle R) (p : R[X]) {a b u v : R}
    (hu : u ∈ Icc a b) (hv : v ∈ Icc a b) (huv : u < v) :
    ∃ c ∈ Ioo a b, p.eval v - p.eval u = p.derivative.eval c * (v - u) := by
  obtain ⟨c, hc, he⟩ := h.exists_eval_sub_eq_derivative_eval_mul p huv
  exact ⟨c, ⟨hu.1.trans_lt hc.1, hc.2.trans_le hv.2⟩, he⟩

/-- Polynomial Rolle implies monotonicity where the derivative is nonnegative. -/
theorem PolynomialRolle.monotoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 ≤ p.derivative.eval x) : MonotoneOn p.eval (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  exact sub_nonneg.mp (he.symm ▸ mul_nonneg (hd c hc) (sub_pos.mpr huv).le)

/-- Polynomial Rolle implies antitonicity where the derivative is nonpositive. -/
theorem PolynomialRolle.antitoneOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x ≤ 0) : AntitoneOn p.eval (Icc a b) := by
  intro u hu v hv huv
  rcases huv.eq_or_lt with rfl | huv
  · exact le_rfl
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  exact sub_nonpos.mp (he.symm ▸ mul_nonpos_of_nonpos_of_nonneg (hd c hc) (sub_pos.mpr huv).le)

/-- Strict positivity of the derivative gives strict monotonicity. -/
theorem PolynomialRolle.strictMonoOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, 0 < p.derivative.eval x) : StrictMonoOn p.eval (Icc a b) := by
  intro u hu v hv huv
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  exact sub_pos.mp (he.symm ▸ mul_pos (hd c hc) (sub_pos.mpr huv))

/-- Strict negativity of the derivative gives strict antitonicity. -/
theorem PolynomialRolle.strictAntiOn (h : PolynomialRolle R) (p : R[X]) {a b : R}
    (hd : ∀ x ∈ Ioo a b, p.derivative.eval x < 0) : StrictAntiOn p.eval (Icc a b) := by
  intro u hu v hv huv
  obtain ⟨c, hc, he⟩ := h.exists_sub_eq p hu hv huv
  exact sub_neg.mp (he.symm ▸ mul_neg_of_neg_of_pos (hd c hc) (sub_pos.mpr huv))

end TauCeti
