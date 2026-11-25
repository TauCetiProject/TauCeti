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
import Mathlib.Topology.Algebra.Polynomial

/-!
# Analytic order of polynomial evaluation

At zero, the analytic order of polynomial evaluation equals its trailing degree, including
infinite order for the zero polynomial. This connects coefficient calculations for polynomial
slices to the analytic order used in preparation theorems. At an arbitrary point, the analytic
order of a nonzero polynomial function — including shifted evaluation `w ↦ p.eval (w - w₀)` and
its product with a nonvanishing analytic factor — is the corresponding root multiplicity of the
polynomial.

Dividing a power by the evaluation of the reversal of a nonzero polynomial gives a function
analytic at zero, since the reversal takes the nonzero leading coefficient there. This is the
reciprocal-coordinate form of a polynomial near infinity.

A polynomial divisible by `X ^ n` is `O(tⁿ)` at zero (`Polynomial.isBigO_eval_of_X_pow_dvd`).
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

/-- The analytic order of a shifted nonzero polynomial function `w ↦ p.eval (w - w₀)` at `a` is
the multiplicity of `a - w₀` as a root of `p`. -/
theorem analyticOrderAt_eval_sub {p : Polynomial 𝕜} (hp : p ≠ 0) (w₀ a : 𝕜) :
    analyticOrderAt (fun w ↦ p.eval (w - w₀)) a = p.rootMultiplicity (a - w₀) := by
  obtain ⟨q, hpq, hq⟩ := p.exists_eq_pow_rootMultiplicity_mul_and_not_dvd hp (a - w₀)
  have hp_an : AnalyticAt 𝕜 (fun w ↦ p.eval (w - w₀)) a :=
    ((AnalyticOnNhd.eval_polynomial p) _ (Set.mem_univ _)).comp
      (analyticAt_id.fun_sub analyticAt_const)
  refine hp_an.analyticOrderAt_eq_natCast.2
    ⟨fun w ↦ q.eval (w - w₀),
      ((AnalyticOnNhd.eval_polynomial q) _ (Set.mem_univ _)).comp
        (analyticAt_id.fun_sub analyticAt_const),
      fun h ↦ hq (dvd_iff_isRoot.2 h), .of_forall fun w ↦ ?_⟩
  conv_lhs => rw [hpq]
  simp only [eval_mul, eval_pow, eval_sub, eval_X, eval_C, smul_eq_mul, sub_sub_sub_cancel_right]

/-- The analytic order of the product of a shifted nonzero polynomial function
`w ↦ p.eval (w - w₀)` with a function `v` analytic and nonzero at `a` is the multiplicity of
`a - w₀` as a root of `p`. -/
theorem analyticOrderAt_eval_sub_mul_of_ne_zero {p : Polynomial 𝕜} (hp : p ≠ 0) (w₀ : 𝕜)
    {v : 𝕜 → 𝕜} {a : 𝕜} (hv : AnalyticAt 𝕜 v a) (hv0 : v a ≠ 0) :
    analyticOrderAt (fun w ↦ p.eval (w - w₀) * v w) a = p.rootMultiplicity (a - w₀) := by
  have hp_an : AnalyticAt 𝕜 (fun w ↦ p.eval (w - w₀)) a :=
    ((AnalyticOnNhd.eval_polynomial p) _ (Set.mem_univ _)).comp
      (analyticAt_id.fun_sub analyticAt_const)
  exact (analyticOrderAt_mul hp_an hv).trans <| by
    rw [analyticOrderAt_eval_sub hp w₀ a, hv.analyticOrderAt_eq_zero.2 hv0, add_zero]

/-- For a polynomial `p`, the function `w ↦ w ^ n / p.reverse.eval w` is analytic at `0`: for
nonzero `p` the reversal does not vanish at `0`, where it takes the leading coefficient of `p`,
and for `p = 0` the function is identically `0`. -/
theorem analyticAt_pow_div_eval_reverse (p : Polynomial 𝕜) (n : ℕ) :
    AnalyticAt 𝕜 (fun w : 𝕜 ↦ w ^ n / p.reverse.eval w) 0 := by
  by_cases hp : p = 0
  · subst hp
    simpa using analyticAt_const (v := (0 : 𝕜))
  · exact ((analyticAt_id (𝕜 := 𝕜)).pow _).div ((AnalyticOnNhd.eval_polynomial _) 0
      (Set.mem_univ _)) (eval_zero_reverse_ne_zero hp)

/-- A polynomial divisible by `X ^ n` is `O(tⁿ)` as `t → 0`. -/
theorem isBigO_eval_of_X_pow_dvd {n : ℕ} {p : Polynomial 𝕜} (hp : X ^ n ∣ p) :
    (fun t ↦ p.eval t) =O[𝓝 0] fun t ↦ t ^ n := by
  obtain ⟨q, rfl⟩ := hp
  simpa using (Asymptotics.isBigO_refl (fun t : 𝕜 ↦ t ^ n) _).mul
    ((q.continuous.tendsto 0).isBigO_one 𝕜)

end Polynomial
