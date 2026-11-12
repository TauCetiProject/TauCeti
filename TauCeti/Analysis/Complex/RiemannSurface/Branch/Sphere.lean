/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Analysis.Complex.RiemannSurface.PowerMap
import TauCeti.Geometry.Manifold.Triangulation.Complex

/-!
# The branched-cover Euler formula over the Riemann sphere

The complement of every finite set of points of the Riemann sphere `OnePoint ℂ` has finite CW
type (`Set.Finite.finiteCWType_compl_onePoint_complex`, in `Triangulation.Complex`). Applying the
topological Riemann–Hurwitz formula
(`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`)
with the branch values as punctures and with `χ(ℙ¹) = 2` gives `-2 deg f + deg R_f = -χ(X)` for
every finite holomorphic map `f : X → ℙ¹` from a compact Riemann surface of finite CW type
(`FiniteHolomorphicMap.neg_two_mul_degree_add_ramificationDegree_eq_neg_eulerChar`, in the
namespace `TauCeti.RiemannSurface`).

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (punctured surfaces in the topological proof of Riemann–Hurwitz).
-/

public section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X]

/-- **Riemann–Hurwitz over the sphere, topological form.** A finite holomorphic map `f : X → ℙ¹`
from a compact Riemann surface of finite CW type satisfies `-2 deg f + deg R_f = -χ(X)`. -/
theorem neg_two_mul_degree_add_ramificationDegree_eq_neg_eulerChar [FiniteCWType X]
    (f : FiniteHolomorphicMap X (OnePoint ℂ)) :
    -2 * (degree f : ℤ) + ramificationDegree f = -eulerChar X := by
  have := f.finite_branchValues.finiteCWType_compl_onePoint_complex
  rw [f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset f.finite_branchValues
    subset_rfl, eulerChar_onePoint, Complex.finrank_real_complex]
  ring

/-- For the power map `z ↦ z²` of the sphere both sides are `-2`: the analytic count is
`-2 · 2 + 2` and the topological side is `-χ(ℙ¹)`. -/
example : -2 * (degree (spherePow two_ne_zero) : ℤ) + ramificationDegree (spherePow two_ne_zero) =
      -2 ∧ -eulerChar (OnePoint ℂ) = -2 := by
  refine ⟨?_, by rw [eulerChar_onePoint, Complex.finrank_real_complex]; norm_num⟩
  rw [coe_spherePow, ramificationDegree_onePointMap_pow two_ne_zero,
    degree_onePointMap_pow]
  norm_num

end TauCeti.RiemannSurface.FiniteHolomorphicMap
