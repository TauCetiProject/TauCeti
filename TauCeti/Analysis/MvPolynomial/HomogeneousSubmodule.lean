/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.MvPolynomial.HomogeneousSubmodule
public import Mathlib.Analysis.Analytic.Polynomial

/-!
# Analyticity on the coefficient space of homogeneous polynomials

Over a nontrivially normed field `𝕜`, evaluation of a homogeneous polynomial in finitely many
variables, and of its partial derivatives, is analytic in the coefficients and the point jointly.
This is the holomorphic counterpart, over `ℂ`, of the joint continuity statements in
`TauCeti.Topology.Algebra.MvPolynomial.HomogeneousSubmodule`.

The coefficient space `homogeneousSubmodule σ 𝕜 n` carries the module topology but no chosen
norm, so it cannot itself be the domain of `AnalyticAt`. The statements are therefore made along
an arbitrary continuous linear parametrization `Φ` of the coefficients by a normed space, for
instance the inverse of the coefficient equivalence `TauCeti.homogeneousCoeffEquiv n`.

## Main results

* `TauCeti.analyticAt_eval_homogeneousSubmodule_comp`,
  `TauCeti.analyticAt_eval_pderiv_homogeneousSubmodule_comp`: evaluation and the evaluated
  partial derivatives are analytic in the coefficients and the point jointly.
-/

public section

namespace TauCeti

open MvPolynomial

variable {σ 𝕜 F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [Fintype σ]

/-- **Evaluation is analytic in the coefficients and the point.** For any continuous linear
parametrization `Φ` of the homogeneous polynomials of degree `n` by a normed space, for instance
the inverse of the coefficient equivalence `homogeneousCoeffEquiv n`, the map
`(a, v) ↦ (Φ a)(v)` is analytic. -/
theorem analyticAt_eval_homogeneousSubmodule_comp {n : ℕ}
    (Φ : F →L[𝕜] homogeneousSubmodule σ 𝕜 n) (z : F × (σ → 𝕜)) :
    AnalyticAt 𝕜 (fun q : F × (σ → 𝕜) ↦ eval q.2 (Φ q.1 : MvPolynomial σ 𝕜)) z := by
  have := Fintype.ofFinite {s : σ →₀ ℕ // s.degree = n}
  simp only [eval_coe_homogeneousSubmodule_eq_sum, ← homogeneousCoeffEquiv_apply]
  refine Finset.analyticAt_fun_sum _ fun s _ ↦ ?_
  exact (ContinuousLinearMap.analyticAt
    (ContinuousLinearMap.proj (R := 𝕜) (φ := fun _ : {s : σ →₀ ℕ // s.degree = n} ↦ 𝕜) s ∘L
      (homogeneousCoeffEquiv (σ := σ) (R := 𝕜) n).toContinuousLinearMap ∘L Φ ∘L
        ContinuousLinearMap.fst 𝕜 F (σ → 𝕜)) z).mul
    (AnalyticOnNhd.eval_continuousLinearMap (ContinuousLinearMap.snd 𝕜 F (σ → 𝕜))
      (monomial s.1 1) z (Set.mem_univ _))

/-- The partial derivatives of a homogeneous polynomial, evaluated at a point, are analytic in the
coefficients and the point, along any continuous linear parametrization `Φ` of the
coefficients. -/
theorem analyticAt_eval_pderiv_homogeneousSubmodule_comp {n : ℕ}
    (Φ : F →L[𝕜] homogeneousSubmodule σ 𝕜 n) (j : σ) (z : F × (σ → 𝕜)) :
    AnalyticAt 𝕜 (fun q : F × (σ → 𝕜) ↦ eval q.2 (pderiv j (Φ q.1 : MvPolynomial σ 𝕜))) z := by
  simpa only [ContinuousLinearMap.comp_apply, coe_homogeneousPDeriv_apply] using
    analyticAt_eval_homogeneousSubmodule_comp (homogeneousPDeriv j n ∘L Φ) z

end TauCeti
