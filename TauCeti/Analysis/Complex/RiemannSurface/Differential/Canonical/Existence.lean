/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Basic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
import TauCeti.Analysis.Complex.RiemannSurface.Differential.RiemannHurwitz

/-!
# Existence of a canonical divisor

Let `X` be a compact connected Hausdorff Riemann surface. Riemann–Roch
gives a finite holomorphic map `f : X → ℙ¹`
(`TauCeti.RiemannSurface.exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one`; Forster's
construction of a finite meromorphic map). Pulling back the meromorphic `1`-form `dz` of the
sphere along `f`, that is, pulling back its divisor `-2[∞]` and adding the ramification divisor
`R_f`, produces a canonical divisor of `X` (`TauCeti.RiemannSurface.exists_isCanonicalDivisor`).

Identifying `deg K = 2g - 2` for the analytic genus needs Serre duality and is not done here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §16 (existence of meromorphic functions from Riemann–Roch) and §17 (the canonical divisor and the
  Riemann–Hurwitz formula).
-/

public section

open TauCeti.Topology
open scoped Manifold

namespace TauCeti.RiemannSurface

open TauCeti.AlgebraicGeometry

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]

/-- **Existence of a canonical divisor.** A compact connected Riemann surface
has a canonical divisor. -/
theorem exists_isCanonicalDivisor : ∃ K : WeilDivisor X, IsCanonicalDivisor K := by
  obtain ⟨F, -⟩ := exists_finiteHolomorphicMap_degree_le_analyticGenus_add_one (X := X)
  obtain ⟨K, hK, -⟩ :=
    F.exists_isCanonicalDivisor_degree_eq_neg_two_mul_degree_add_ramificationDegree
  exact ⟨K, hK⟩

end TauCeti.RiemannSurface
