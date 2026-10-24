/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Order
public import Mathlib.Analysis.Analytic.Polynomial
public import Mathlib.Algebra.Polynomial.Div
public import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
public import TauCeti.Algebra.Polynomial.Reverse

/-!
# Analytic order of polynomial evaluation

At zero, the analytic order of polynomial evaluation equals its trailing degree, including
infinite order for the zero polynomial. This connects coefficient calculations for polynomial
slices to the analytic order used in preparation theorems. At an arbitrary point, the analytic
order of a nonzero polynomial function is the root multiplicity of the polynomial there.

Dividing a power by the evaluation of the reversal of a nonzero polynomial gives a function
analytic at zero, since the reversal takes the nonzero leading coefficient there. This is the
reciprocal-coordinate form of a polynomial near infinity.
-/

public section

open Filter Topology

namespace Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

/-- The analytic order at zero of a polynomial function is its trailing degree. -/
@[simp]
theorem analyticOrderAt_eval_zero (p : Polynomial 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) 0 = p.trailingDegree := by
  by_cases hp : p = 0
  · rw [hp]
    simpa only [eval_zero, Pi.zero_def, trailingDegree_zero] using
      (analyticOrderAt_zero (𝕜 := 𝕜) (E := 𝕜) (z₀ := 0))
  rw [trailingDegree_eq_natTrailingDegree hp]
  have ha : AnalyticAt 𝕜 (fun t ↦ p.eval t) 0 :=
    (AnalyticOnNhd.eval_polynomial p) 0 (Set.mem_univ _)
  obtain ⟨q, hq⟩ := X_pow_dvd_iff.2
    (fun k hk ↦ coeff_eq_zero_of_lt_natTrailingDegree hk :
      ∀ k < p.natTrailingDegree, p.coeff k = 0)
  have hq0 : q.eval 0 ≠ 0 := by
    have hc := coeff_natTrailingDegree_ne_zero.2 hp
    have hcoeff : (X ^ p.natTrailingDegree * q).coeff p.natTrailingDegree = q.coeff 0 := by
      simpa only [zero_add] using coeff_X_pow_mul q p.natTrailingDegree 0
    have heq := congrArg (fun r : Polynomial 𝕜 ↦ r.coeff p.natTrailingDegree) hq
    rw [hcoeff] at heq
    simpa only [← coeff_zero_eq_eval_zero, ← heq] using hc
  refine ha.analyticOrderAt_eq_natCast.2 ⟨fun t ↦ q.eval t,
    (AnalyticOnNhd.eval_polynomial q) 0 (Set.mem_univ _), hq0, ?_⟩
  exact Eventually.of_forall fun t ↦ by
    conv_lhs => rw [hq]
    simp only [eval_mul, eval_pow, eval_X, sub_zero, smul_eq_mul]

/-- The analytic order of a nonzero polynomial function at a point is the multiplicity of that
point as a root of the polynomial. -/
theorem analyticOrderAt_eval {p : Polynomial 𝕜} (hp : p ≠ 0) (a : 𝕜) :
    analyticOrderAt (fun t ↦ p.eval t) a = p.rootMultiplicity a := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp a
  refine ((AnalyticOnNhd.eval_polynomial p) a (Set.mem_univ _)).analyticOrderAt_eq_natCast.2
    ⟨fun t ↦ q.eval t, (AnalyticOnNhd.eval_polynomial q) a (Set.mem_univ _),
      fun h ↦ hq (dvd_iff_isRoot.2 h), .of_forall fun t ↦ ?_⟩
  conv_lhs => rw [hpq]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul]

/-- For a nonzero polynomial `p`, the function `w ↦ w ^ n / p.reverse.eval w` is analytic at `0`:
the reversal does not vanish at `0`, where it takes the leading coefficient of `p`. -/
theorem analyticAt_pow_div_eval_reverse {p : Polynomial 𝕜} (hp : p ≠ 0) (n : ℕ) :
    AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ n / p.reverse.eval w) 0 :=
  ((analyticAt_id (𝕜 := 𝕜)).pow _).div ((AnalyticOnNhd.eval_polynomial _) 0 (Set.mem_univ _))
    (eval_zero_reverse_ne_zero hp)

end Polynomial
