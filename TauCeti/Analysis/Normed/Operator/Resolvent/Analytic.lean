/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.Unbounded
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analyticity of an unbounded operator's resolvent

The resolvent of a `LinearPMap` on a complete normed space over a nontrivially normed field is
analytic on its resolvent set. Locally at a resolvent point `lambda`, the Neumann formula
identifies it with

`R(mu) = R(lambda) * (1 - (lambda - mu) R(lambda))⁻¹`.

The second factor is analytic near `lambda` because inversion in a complete normed algebra is
analytic at every unit. This gives analyticity in operator norm, rather than merely pointwise
analyticity after applying the resolvent to a vector.

## Main results

* `TauCeti.LinearPMap.analyticAt_resolvent`: the resolvent is analytic at each point of its
  resolvent set.
* `TauCeti.LinearPMap.analyticOnNhd_resolvent`: the resolvent is analytic throughout its
  resolvent set.

## References

* K.-J. Engel and R. Nagel, *One-Parameter Semigroups for Linear Evolution Equations*,
  Section IV.1.
* A. Pazy, *Semigroups of Linear Operators and Applications to Partial Differential Equations*,
  Chapter 1, Section 1.3.
-/

public section

noncomputable section

open scoped Topology

open Filter

namespace TauCeti.LinearPMap

variable {𝕜 X : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [CompleteSpace X]

variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜}

omit [CompleteSpace X] in
private theorem eventually_norm_sub_mul_norm_resolvent_lt_one :
    ∀ᶠ mu in 𝓝 lambda, ‖mu - lambda‖ * ‖resolvent A lambda‖ < 1 := by
  filter_upwards [Metric.ball_mem_nhds lambda
    (ε := 1 / (‖resolvent A lambda‖ + 1)) (by positivity)] with mu hmu
  rw [Metric.mem_ball, dist_eq_norm] at hmu
  have hprod : ‖mu - lambda‖ * (‖resolvent A lambda‖ + 1) < 1 :=
    (lt_div_iff₀ (by positivity)).mp (by simpa using hmu)
  exact lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (by linarith) (norm_nonneg (mu - lambda))) hprod

/-- The resolvent of a `LinearPMap` is analytic at every point of its resolvent set. -/
theorem analyticAt_resolvent (h : lambda ∈ resolventSet A) :
    AnalyticAt 𝕜 (resolvent A) lambda := by
  let R : X →L[𝕜] X := resolvent A lambda
  let localResolvent : 𝕜 → X →L[𝕜] X := fun mu =>
    R * Ring.inverse (1 - (lambda - mu) • R)
  have heq : resolvent A =ᶠ[𝓝 lambda] localResolvent := by
    filter_upwards [eventually_norm_sub_mul_norm_resolvent_lt_one
      (A := A) (lambda := lambda)] with mu hmu
    simpa only [R, localResolvent] using resolvent_eq_mul_inverse_one_sub h hmu
  have hinner : AnalyticAt 𝕜 (fun mu : 𝕜 => 1 - (lambda - mu) • R) lambda := by
    fun_prop
  have hinv : AnalyticAt 𝕜 (fun mu : 𝕜 => Ring.inverse (1 - (lambda - mu) • R)) lambda := by
    have hInvAt : AnalyticAt 𝕜 (@Ring.inverse (X →L[𝕜] X) _)
        (1 : X →L[𝕜] X) := analyticAt_inverse (𝕜 := 𝕜) (1 : (X →L[𝕜] X)ˣ)
    exact hInvAt.comp_of_eq hinner (by simp)
  exact (analyticAt_const.mul hinv).congr heq.symm

/-- The resolvent of a `LinearPMap` is analytic in operator norm on its resolvent set. -/
theorem analyticOnNhd_resolvent (A : X →ₗ.[𝕜] X) :
    AnalyticOnNhd 𝕜 (resolvent A) (resolventSet A) :=
  fun _ h => analyticAt_resolvent h

end TauCeti.LinearPMap

end
