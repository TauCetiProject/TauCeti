/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.SimpleRoots.Covering
public import Mathlib.Algebra.Polynomial.FieldDivision
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analytic roots with constant multiplicity

A continuous root of an analytic polynomial family is analytic if its positive multiplicity
is locally constant. This includes repeated roots: the derivative of order one less than that
multiplicity has a simple root, to which the analytic implicit-root theorem applies.

This supplies the analytic regularity of continuous root sections when delineability has
already established constant multiplicities. The polynomial degree need only be locally bounded;
no separability of the original family is required.

## References

S. McCallum, *An improved projection operation for cylindrical algebraic decomposition*,
Springer (1998), 242–268 (analytic delineability).
-/

public section

open Filter Polynomial Topology

namespace TauCeti.Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [CharZero 𝕜] [CompleteSpace 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
  {F : E → 𝕜[X]} {r : E → 𝕜} {x₀ : E} {d m : ℕ}

/-- A continuous root of an analytic polynomial family is analytic wherever its positive
multiplicity is locally constant. The degrees of the fibers need only be locally bounded. -/
theorem analyticAt_of_eventually_rootMultiplicity_eq
    (hF : ∀ i ≤ d, AnalyticAt 𝕜 (fun x ↦ (F x).coeff i) x₀)
    (hdeg : ∀ᶠ x in 𝓝 x₀, (F x).natDegree ≤ d) (hr : ContinuousAt r x₀)
    (hm : 0 < m) (hmult : ∀ᶠ x in 𝓝 x₀, (F x).rootMultiplicity (r x) = m) :
    AnalyticAt 𝕜 r x₀ := by
  have hcoeff (i : ℕ) :
      AnalyticAt 𝕜 (fun x ↦ (derivative^[m - 1] (F x)).coeff i) x₀ := by
    by_cases hi : i + (m - 1) ≤ d
    · simp only [coeff_iterate_derivative, nsmul_eq_mul]
      exact (hF _ hi).const_smul (c := ((i + (m - 1)).descFactorial (m - 1) : 𝕜))
    · refine (analyticAt_const (v := (0 : 𝕜))).congr ?_
      filter_upwards [hdeg] with x hx
      rw [coeff_iterate_derivative,
        coeff_eq_zero_of_natDegree_lt (hx.trans_lt (Nat.lt_of_not_ge hi)), smul_zero]
  have hdegree : ∀ᶠ x in 𝓝 x₀, (derivative^[m - 1] (F x)).natDegree ≤ d :=
    hdeg.mono fun x hx ↦ (natDegree_iterate_derivative _ _).trans
      ((Nat.sub_le _ _).trans hx)
  have hroot : ∀ᶠ x in 𝓝 x₀, (derivative^[m - 1] (F x)).IsRoot (r x) := by
    filter_upwards [hmult] with x hx
    apply isRoot_iterate_derivative_of_lt_rootMultiplicity
    rw [hx]
    omega
  have h₀ := hmult.self_of_nhds
  have hne : F x₀ ≠ 0 := by
    intro h
    simp [h] at h₀
    omega
  have hsimple : (derivative (derivative^[m - 1] (F x₀))).eval (r x₀) ≠ 0 := by
    rw [← Function.iterate_succ_apply' derivative (m - 1), Nat.succ_eq_add_one,
      Nat.sub_add_cancel hm, ← h₀, eval_iterate_derivative_rootMultiplicity, nsmul_eq_mul]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _))
      (eval_divByMonic_pow_rootMultiplicity_ne_zero _ hne)
  exact analyticAt_of_eventually_isRoot (fun i _ ↦ hcoeff i) hdegree hr hroot hsimple

end TauCeti.Polynomial
