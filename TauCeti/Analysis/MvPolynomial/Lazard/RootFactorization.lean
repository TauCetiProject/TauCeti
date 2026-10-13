/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Polynomial.Puiseux.Laurent.Limit
public import TauCeti.RingTheory.MvPolynomial.Lazard.Uniform
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.Polynomial.Bivariate

/-!
# Lazard root multisets from Laurent branches

A complete Laurent splitting along an evaluator's monomial curve determines the roots of
the Lazard evaluation, counted with multiplicity. Divide out the lowest monomial-curve
power using the uniform Taylor expansion, then specialize the resulting analytic family.
Its central fiber is the nonzero Lazard evaluation. The central-fiber factorization theorem
discards the branches with poles and retains exactly the finite branch limits.

No nonnullification or preservation of ordinary fiber degree is assumed. This supplies
root coverage and multiplicities when descending a Puiseux Laurent splitting to Lazard
evaluation; it does not yet prove constancy of these multiplicities along a base manifold.

## References

S. McCallum, A. Parusiński, L. Paunescu, *Validity proof of Lazard's method for CAD
construction*, Journal of Symbolic Computation 92 (2019), §5.1, Proposition 5.6,
and §5.2, proof of Theorem 5.1.
-/

public section

open Filter Finsupp Polynomial Topology

namespace MvPolynomial

variable {𝕜 ι : Type*} [NontriviallyNormedField 𝕜] [Fintype ι] {n : ℕ}

/-- A complete Laurent splitting along a Lazard evaluator determines the Lazard evaluation's
root multiset. A branch of exponent zero contributes its unit value at the origin, a branch
of positive exponent contributes zero, and a branch with a pole contributes no finite root.
Coincident limits are counted separately, so the equality includes root multiplicities. -/
theorem roots_lazardEval_eq_map_of_laurent
    (p : MvPolynomial (Fin n) (Polynomial 𝕜)) (hp : p ≠ 0)
    (x : Fin n → 𝕜) (c : Fin n → ℕ)
    (hc : TauCeti.IsLazardEvaluator {p.lazardExponent (Polynomial.C ∘ x)} c)
    {a : ℤ} {e : ι → ℤ} {u : 𝕜 → 𝕜} {w : ι → 𝕜 → 𝕜}
    (hu : AnalyticAt 𝕜 u 0) (hu0 : u 0 ≠ 0)
    (hw : ∀ i, AnalyticAt 𝕜 (w i) 0) (hw0 : ∀ i, e i < 0 → w i 0 ≠ 0)
    (hfac : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      (aeval (monomialCurve (Polynomial.C ∘ x) c) p).eval (Polynomial.C y) =
        Polynomial.C (y ^ a * u y) *
          ∏ i, (Polynomial.X - Polynomial.C (y ^ e i * w i y))) :
    (p.lazardEval (Polynomial.C ∘ x)).roots =
      (Finset.univ.filter (fun i ↦ 0 ≤ e i)).val.map
        (fun i ↦ if e i = 0 then w i 0 else 0) := by
  classical
  -- Divide out the lowest Taylor weight, leaving the Lazard evaluation at the center.
  let v := p.lazardExponent (Polynomial.C ∘ x)
  obtain ⟨Q, hQ⟩ := p.exists_aeval_monomialCurve_eq_pow_mul
    (S := {Polynomial.C ∘ x}) (V := {v}) (v := v) (c := c)
    (by simp) hc (by
      intro b hb j hj
      subst b
      exact coeff_taylor_eq_zero_of_lt_lazardExponent hj)
  let q := p.lazardEval (Polynomial.C ∘ x)
  let T := Polynomial.C q + Polynomial.X * Q.map (eval (Polynomial.C ∘ x))
  let F (y : 𝕜) := T.eval (Polynomial.C y)
  have hfactor := hQ (Polynomial.C ∘ x) (by simp)
  rw [coeff_taylor_lazardExponent] at hfactor
  -- Swapping the two variables expresses every coefficient as a polynomial in the curve parameter.
  have hFmap (y : 𝕜) : F y = (Polynomial.Bivariate.swap T).map
      (Polynomial.evalRingHom y) := by
    simpa [F, Polynomial.aeval_def, Polynomial.coe_mapAlgHom, Algebra.algebraMap_self] using
      Polynomial.Bivariate.aeval_eq_map_swap y T
  have hF0 : F 0 = q := by simp [F, T]
  have hFcoeff (j : ℕ) : AnalyticAt 𝕜 (fun y ↦ (F y).coeff j) 0 := by
    simp only [hFmap, Polynomial.coeff_map, Polynomial.coe_evalRingHom]
    simpa only [Polynomial.coe_aeval_eq_eval, id_eq] using
      (analyticAt_id (𝕜 := 𝕜) (z := (0 : 𝕜))).aeval_polynomial
        ((Polynomial.Bivariate.swap T).coeff j)
  have hFdeg : ∀ᶠ y in 𝓝 (0 : 𝕜),
      (F y).natDegree ≤ (Polynomial.Bivariate.swap T).natDegree := by
    exact .of_forall fun y ↦ hFmap y ▸ Polynomial.natDegree_map_le
  -- Off the origin, division shifts only the scalar Laurent exponent.
  have hsplit : ∀ᶠ y in 𝓝[≠] (0 : 𝕜),
      F y = Polynomial.C (y ^ (a - weight c v) * u y) *
        ∏ i, (Polynomial.X - Polynomial.C (y ^ e i * w i y)) := by
    filter_upwards [hfac, self_mem_nhdsWithin] with y hy hy0
    have hy0' : y ≠ 0 := by simpa using hy0
    have hpow : y ^ weight c v * (y ^ (a - weight c v) * u y) = y ^ a * u y := by
      rw [← zpow_natCast, ← mul_assoc, ← zpow_add₀ hy0']
      congr 2
      omega
    apply mul_left_cancel₀ (Polynomial.C_ne_zero.mpr (pow_ne_zero (weight c v) hy0'))
    rw [← mul_assoc, ← Polynomial.C_mul, hpow]
    simpa only [hfactor, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_X, ← Polynomial.C_pow,
      q, T, F] using hy
  simpa only [hF0, q] using TauCeti.roots_eq_map_of_laurent
    (fun j _ ↦ hFcoeff j) hFdeg (hF0 ▸ lazardEval_ne_zero hp _) hu hu0 hw hw0 hsplit

end MvPolynomial
