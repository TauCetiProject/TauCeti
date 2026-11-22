/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.DFinite.Order
import Mathlib.RingTheory.PrincipalIdealDomain
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Singular points of minimal differential equations

Let `f : K⟦X⟧` be D-finite over a field `k`. A point `ξ` of a commutative `k`-algebra `L` is a
*singular point of the minimal equation* of `f` (`PowerSeries.IsMinimalSingularPoint k f ξ`) if the
leading coefficient of every differential equation `∑ i ≤ n, pᵢ • f⁽ⁱ⁾ = 0` of the minimal order
`n = PowerSeries.dfiniteOrder k f` vanishes at `ξ`.

Quantifying over all minimal equations matters: multiplying a minimal equation by `X - ξ` gives
another minimal equation whose leading coefficient vanishes at `ξ`, so an arbitrary minimal
equation cannot decide whether `ξ` is singular. For instance, `exp` satisfies the minimal equation
`(X - 1) (f' - f) = 0` but has no singular point (`PowerSeries.not_isMinimalSingularPoint_exp`).
Since any two minimal equations are proportional (`PowerSeries.minimal_equation_unique`), a minimal
equation whose coefficients generate the unit ideal of `k[X]` does decide it: the leading
coefficient of every other minimal equation is a multiple of its leading coefficient, so the
singular points are exactly the roots of that coefficient
(`PowerSeries.isMinimalSingularPoint_iff_of_sum_mul_eq_one`). Dividing any minimal equation by the
greatest common divisor of its coefficients gives such an equation
(`PowerSeries.IsDFinite.exists_minimal_equation_sum_mul_eq_one`).

A singular point of the minimal equation need not be a singularity of `f` or of the solutions: the
series `(X - a) exp` has the minimal equation `(X - a) f' - (X - a + 1) f = 0`, singular exactly
at `a` (`PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp_iff`), although its solutions
`c (X - a) exp` are entire. Such apparent singularities are the subject of Beukers' refinement of
the Siegel–Shidlovskii theorem.

A series that is not D-finite has no singular points. In a ring `L` without zero divisors a
D-finite series has only finitely many (`PowerSeries.finite_setOf_isMinimalSingularPoint`).

## Main definitions

* `PowerSeries.IsMinimalSingularPoint k f ξ`: `f` is D-finite over `k` and the leading coefficient
  of every minimal equation of `f` vanishes at `ξ`.

## Main results

* `PowerSeries.isMinimalSingularPoint_iff_of_sum_mul_eq_one`: a minimal equation whose
  coefficients generate the unit ideal has the singular points as the roots of its leading
  coefficient.
* `PowerSeries.IsDFinite.exists_minimal_equation_sum_mul_eq_one`: such a minimal equation exists.
* `PowerSeries.finite_setOf_isMinimalSingularPoint`: the singular points in a ring without zero
  divisors form a finite set.
* `PowerSeries.not_isMinimalSingularPoint_exp`,
  `PowerSeries.isMinimalSingularPoint_X_sub_C_smul_exp_iff`: the exponential series has no
  singular point, and `(X - a) exp` has exactly the singular point `a`.

## References

* F. Beukers, *A refined version of the Siegel–Shidlovskii theorem*, Ann. of Math. 163 (2006),
  §1, p. 1, and §2.
* F. Beukers, *E-functions and G-functions*, Arizona Winter School lecture notes (2008), §3.4,
  Theorem 3.4.1.
-/

public section

open Polynomial

namespace PowerSeries

variable {k K L : Type*} [Field k] [CommRing K] [Algebra k K] [CommRing L] [Algebra k L]

variable (k) in
/-- A point `ξ` is a *singular point of the minimal equation* of `f` over `k` if `f` is D-finite
over `k` and every differential equation `∑ i, pᵢ • f⁽ⁱ⁾ = 0` of the minimal order
`dfiniteOrder k f` with coefficients in `k[X]` has leading coefficient vanishing at `ξ`. -/
def IsMinimalSingularPoint (f : K⟦X⟧) (ξ : L) : Prop :=
  IsDFinite k f ∧ ∀ p : Fin (dfiniteOrder k f + 1) → k[X],
    ∑ i, p i • (d⁄dX)^[i] f = 0 → Polynomial.aeval ξ (p (Fin.last _)) = 0

/-- Unfolding `IsMinimalSingularPoint`: `f` is D-finite and the leading coefficient of every
minimal equation of `f` vanishes at `ξ`. -/
theorem isMinimalSingularPoint_def {f : K⟦X⟧} {ξ : L} :
    IsMinimalSingularPoint k f ξ ↔ IsDFinite k f ∧ ∀ p : Fin (dfiniteOrder k f + 1) → k[X],
      ∑ i, p i • (d⁄dX)^[i] f = 0 → Polynomial.aeval ξ (p (Fin.last _)) = 0 :=
  Iff.rfl

/-- A series with a singular point is D-finite. -/
theorem IsMinimalSingularPoint.isDFinite {f : K⟦X⟧} {ξ : L}
    (h : IsMinimalSingularPoint k f ξ) : IsDFinite k f :=
  h.1

/-- At a singular point, the leading coefficient of every minimal equation vanishes. The order is
given through an equation `dfiniteOrder k f = n`, so that the equation can have a concrete
order. -/
theorem IsMinimalSingularPoint.aeval_eq_zero {f : K⟦X⟧} {ξ : L}
    (h : IsMinimalSingularPoint k f ξ) {n : ℕ} (hn : dfiniteOrder k f = n)
    {p : Fin (n + 1) → k[X]} (hp : ∑ i, p i • (d⁄dX)^[i] f = 0) :
    Polynomial.aeval ξ (p (Fin.last n)) = 0 := by
  subst hn
  exact h.2 p hp

/-- A minimal equation of `f` whose coefficients generate the unit ideal of `k[X]` decides every
singular point: `ξ` is singular exactly when the leading coefficient vanishes at `ξ`. Indeed the
leading coefficient of every other minimal equation is a multiple of this one. -/
theorem isMinimalSingularPoint_iff_of_sum_mul_eq_one {f : K⟦X⟧} {ξ : L} {n : ℕ}
    (hn : dfiniteOrder k f = n) {p c : Fin (n + 1) → k[X]}
    (hp : ∑ i, p i • (d⁄dX)^[i] f = 0) (hc : ∑ i, c i * p i = 1) :
    IsMinimalSingularPoint k f ξ ↔ Polynomial.aeval ξ (p (Fin.last n)) = 0 := by
  refine ⟨fun h ↦ h.aeval_eq_zero hn hp, fun hξ ↦ ⟨?_, ?_⟩⟩
  · refine isDFinite_iff_not_linearIndependent.mpr fun hli ↦ one_ne_zero (α := k[X]) ?_
    simp [← hc, Fintype.linearIndependent_iff.mp (hli.comp _ Fin.val_injective) p hp]
  · subst hn
    intro q hq
    have hq : q (Fin.last _) = p (Fin.last _) * ∑ i, c i * q i := by
      calc q (Fin.last _) = ∑ i, c i * (q (Fin.last _) * p i) := by
            conv_lhs => rw [← mul_one (q _), ← hc, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
        _ = p (Fin.last _) * ∑ i, c i * q i := by
            simp_rw [minimal_equation_unique hp hq, Finset.mul_sum]
            exact Finset.sum_congr rfl fun i _ ↦ by ring
    rw [hq, map_mul, hξ, zero_mul]

/-- Every D-finite series has a minimal equation whose coefficients generate the unit ideal of
`k[X]`, obtained by dividing the coefficients of any minimal equation by their greatest common
divisor. By `isMinimalSingularPoint_iff_of_sum_mul_eq_one`, the singular points are the roots of
its leading coefficient. -/
theorem IsDFinite.exists_minimal_equation_sum_mul_eq_one {f : K⟦X⟧} (hf : IsDFinite k f) :
    ∃ p c : Fin (dfiniteOrder k f + 1) → k[X], p (Fin.last _) ≠ 0 ∧
      ∑ i, p i • (d⁄dX)^[i] f = 0 ∧ ∑ i, c i * p i = 1 := by
  obtain ⟨p, hp, h⟩ := hf.exists_minimal_equation
  choose q hq using fun i ↦ (Submodule.IsPrincipal.mem_iff_generator_dvd _).mp
    (Ideal.subset_span ⟨i, rfl⟩ : p i ∈ Ideal.span (Set.range p))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).mp
    (Submodule.IsPrincipal.generator_mem (Ideal.span (Set.range p)))
  generalize Submodule.IsPrincipal.generator (Ideal.span (Set.range p)) = g at hq hc
  have hg : g ≠ 0 := fun hg ↦ hp (by rw [hq, hg, zero_mul])
  refine ⟨q, c, fun h0 ↦ hp (by rw [hq, h0, mul_zero]), ?_, ?_⟩
  · refine (smul_eq_zero_iff_right hg).mp ?_
    rw [Finset.smul_sum, ← h]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_smul, ← hq]
  · refine mul_left_cancel₀ hg ?_
    rw [mul_one, Finset.mul_sum]
    conv_rhs => rw [← hc]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [smul_eq_mul, hq]; ring

/-- A D-finite series has only finitely many singular points in a ring without zero divisors; a
series that is not D-finite has none. -/
theorem finite_setOf_isMinimalSingularPoint [NoZeroDivisors L] (f : K⟦X⟧) :
    {ξ : L | IsMinimalSingularPoint k f ξ}.Finite := by
  rcases subsingleton_or_nontrivial L with hL | hL
  · exact Set.toFinite _
  have : IsDomain L := NoZeroDivisors.to_isDomain L
  by_cases hf : IsDFinite k f
  · obtain ⟨p, hp, h⟩ := hf.exists_minimal_equation
    refine ((p (Fin.last _)).rootSet_finite L).subset fun ξ hξ ↦ ?_
    exact mem_rootSet.mpr ⟨hp, hξ.2 p h⟩
  · simp [isMinimalSingularPoint_def, hf]

/-- The exponential series has no singular point: its minimal equation `f' - f = 0` has leading
coefficient one. -/
@[simp]
theorem not_isMinimalSingularPoint_exp [Algebra ℚ K] [Nontrivial L] (ξ : L) :
    ¬IsMinimalSingularPoint k (exp K) ξ := by
  rcases subsingleton_or_nontrivial K with hK | hK
  · have h0 : exp K = 0 := by ext; exact Subsingleton.elim _ _
    rw [h0]
    exact fun h ↦ by simpa using h.aeval_eq_zero dfiniteOrder_zero (p := ![1]) (by simp)
  · rw [isMinimalSingularPoint_iff_of_sum_mul_eq_one dfiniteOrder_exp (p := ![-1, 1])
      (c := ![-1, 0]) (by simp [Fin.sum_univ_two, derivative_exp]) (by simp [Fin.sum_univ_two])]
    simp

/-- The series `(X - a) exp` satisfies the first-order equation `(X - a) f' - (X - a + 1) f = 0`. -/
private theorem sum_X_sub_C_smul_exp [Algebra ℚ K] (a : k) :
    ∑ i, ![-(Polynomial.X - Polynomial.C a + 1), Polynomial.X - Polynomial.C a] i •
      (d⁄dX)^[i] ((Polynomial.X - Polynomial.C a : k[X]) • exp K) = 0 := by
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Fin.val_zero, Fin.val_one,
    Function.iterate_zero, id_eq, Function.iterate_one, derivative_polynomial_smul,
    derivative_exp, ← add_smul, smul_smul, Polynomial.derivative_sub, Polynomial.derivative_X,
    Polynomial.derivative_C]
  convert zero_smul k[X] (exp K) using 2
  ring

/-- The series `(X - a) exp` has differential order one. -/
@[simp]
theorem dfiniteOrder_X_sub_C_smul_exp [Nontrivial K] [Algebra ℚ K] (a : k) :
    dfiniteOrder k ((Polynomial.X - Polynomial.C a : k[X]) • exp K) = 1 := by
  have ha : (Polynomial.X - Polynomial.C a : k[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero a
  have hf : IsDFinite k ((Polynomial.X - Polynomial.C a : k[X]) • exp K) :=
    (isDFinite_polynomial_smul_iff ha).mpr isDFinite_exp
  refine Nat.le_antisymm ?_ (hf.dfiniteOrder_pos ?_)
  · exact dfiniteOrder_le (by simpa using ha) (sum_X_sub_C_smul_exp a)
  · rw [Ne, smul_eq_zero_iff_right ha]
    exact (isUnit_exp K).ne_zero

/-- The series `(X - a) exp` has exactly one singular point, `a`, in every `k`-algebra. It is an
apparent singularity: the solutions `c (X - a) exp` of the minimal equation
`(X - a) f' - (X - a + 1) f = 0` are entire. -/
theorem isMinimalSingularPoint_X_sub_C_smul_exp_iff [Nontrivial K] [Algebra ℚ K] (a : k)
    (ξ : L) :
    IsMinimalSingularPoint k ((Polynomial.X - Polynomial.C a : k[X]) • exp K) ξ ↔
      ξ = algebraMap k L a := by
  rw [isMinimalSingularPoint_iff_of_sum_mul_eq_one (dfiniteOrder_X_sub_C_smul_exp a)
    (sum_X_sub_C_smul_exp a) (c := ![-1, -1]) (by simp [Fin.sum_univ_two]; ring)]
  simp [sub_eq_zero]

end PowerSeries
