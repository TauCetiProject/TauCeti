/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Module.LinearPMap.Resolvent.SpectralMapping
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.Constructions

/-!
# Analyticity of an unbounded operator's resolvent

The resolvent of a `LinearPMap` on a normed space over a nontrivially normed field is
analytic on its resolvent set when its algebra of continuous endomorphisms has summable
geometric series. In particular, this holds on every complete normed space. Locally at a
resolvent point `lambda`, the Neumann formula identifies it with

`R(mu) = R(lambda) * (1 - (lambda - mu) R(lambda))⁻¹`.

The second factor is analytic near `lambda` because inversion in a normed algebra with summable
geometric series is analytic at every unit. This gives analyticity in operator norm, rather than
merely pointwise analyticity after applying the resolvent to a vector.

## Main results

* `TauCeti.LinearPMap.analyticAt_resolvent`: the resolvent is analytic at each point of its
  resolvent set.
* `LinearPMap.analyticOnNhd_resolvent`: the resolvent is analytic throughout its
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
  [NormedAddCommGroup X] [NormedSpace 𝕜 X] [HasSummableGeomSeries (X →L[𝕜] X)]

variable {A : X →ₗ.[𝕜] X} {lambda : 𝕜}

/-- The resolvent of a `LinearPMap` is analytic at every point of its resolvent set. -/
theorem analyticAt_resolvent (h : lambda ∈ A.resolventSet) :
    AnalyticAt 𝕜 (A.resolvent) lambda := by
  let R : X →L[𝕜] X := A.resolvent lambda
  let localResolvent : 𝕜 → X →L[𝕜] X := fun mu =>
    R * Ring.inverse (1 - (lambda - mu) • R)
  have hinner : AnalyticAt 𝕜 (fun mu : 𝕜 => (lambda - mu) • R) lambda := by
    fun_prop
  have heq : A.resolvent =ᶠ[𝓝 lambda] localResolvent := by
    filter_upwards [hinner.continuousAt.norm.eventually_lt
        (continuousAt_const (y := (1 : ℝ))) (by simp)]
      with mu hmu
    exact resolvent_eq_mul_inverse_one_sub_smul_resolvent h
      (isUnit_one_sub_of_norm_lt_one hmu)
  have hinv : AnalyticAt 𝕜 (fun mu : 𝕜 => Ring.inverse (1 - (lambda - mu) • R)) lambda :=
    (analyticAt_inverse_one_sub 𝕜 (X →L[𝕜] X)).comp_of_eq hinner (by simp)
  exact (analyticAt_const.mul hinv).congr heq.symm

/-- The resolvent of a `LinearPMap` is analytic in operator norm on its resolvent set. -/
theorem _root_.LinearPMap.analyticOnNhd_resolvent (A : X →ₗ.[𝕜] X) :
    AnalyticOnNhd 𝕜 (A.resolvent) (A.resolventSet) :=
  fun _ h => analyticAt_resolvent h

end TauCeti.LinearPMap

end
