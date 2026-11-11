/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.Differential.Canonical.Degree
public import TauCeti.Topology.Triangulable.FiniteCWType
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Topology.Triangulable.Sphere

/-!
# The degree of a canonical divisor is minus the Euler characteristic

Let `X` be a compact connected Riemann surface of finite CW type admitting a finite holomorphic
map `f : X → ℙ¹`. The topological Riemann–Hurwitz formula
(`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree_of_subset`),
applied with the branch values as punctures and with `χ(ℙ¹) = 2`, gives
`-2 deg f + deg R_f = -χ(X)`
(`FiniteHolomorphicMap.neg_two_mul_degree_add_ramificationDegree_eq_neg_eulerChar`, in the
namespace `TauCeti.RiemannSurface`).
The punctured Riemann sphere has finite CW type because the sphere is triangulable
(`Set.Finite.finiteCWType_compl_onePoint_complex`).

The canonical-divisor form of Riemann–Hurwitz says that every canonical divisor `K` of `X` has
degree `-2 deg f + deg R_f`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_two_mul_degree_add_ramificationDegree`).
Comparing the two analytic and topological counts gives `deg K = -χ(X)`
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_eulerChar`), and the same holds for
triangulable `X` without a separate finite CW hypothesis
(`TauCeti.RiemannSurface.IsCanonicalDivisor.degree_eq_neg_eulerChar_of_isTriangulable`).

With the topological genus defined by `χ(X) = 2 - 2g` this is `deg K = 2g - 2`. Identifying `g`
with the analytic genus `dim H¹(X, 𝒪)` needs Serre duality and is not done here.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81, Springer, 1981,
  §17 (the Riemann–Hurwitz formula, analytic and topological forms).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4 and Chapter IV §2.
-/

public section

open OnePoint
open scoped Manifold

namespace TauCeti.RiemannSurface

open AlgebraicGeometry

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X]

namespace FiniteHolomorphicMap

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
    degree_onePointMap_pow two_ne_zero]
  norm_num

end FiniteHolomorphicMap

namespace IsCanonicalDivisor

variable [ConnectedSpace X] {K : WeilDivisor X}

/-- **The degree of a canonical divisor is minus the Euler characteristic.** If a compact
connected Riemann surface `X` of finite CW type admits a finite holomorphic map to `ℙ¹`, then
every canonical divisor `K` of `X` has `deg K = -χ(X)`. -/
theorem degree_eq_neg_eulerChar [FiniteCWType X] (hK : IsCanonicalDivisor K)
    (f : FiniteHolomorphicMap X (OnePoint ℂ)) : WeilDivisor.degree K = -eulerChar X := by
  rw [hK.degree_eq_neg_two_mul_degree_add_ramificationDegree f,
    f.neg_two_mul_degree_add_ramificationDegree_eq_neg_eulerChar]

/-- **The degree of a canonical divisor is minus the Euler characteristic**, for a triangulable
compact connected Riemann surface `X` admitting a finite holomorphic map to `ℙ¹`. The finite CW
type of `X` is derived from its triangulation. -/
theorem degree_eq_neg_eulerChar_of_isTriangulable.{v} (hX : IsTriangulable.{v} X)
    (hK : IsCanonicalDivisor K) (f : FiniteHolomorphicMap X (OnePoint ℂ)) :
    haveI := hX.finiteCWType
    WeilDivisor.degree K = -eulerChar X :=
  haveI := hX.finiteCWType
  hK.degree_eq_neg_eulerChar f

/-- On the Riemann sphere, the canonical divisor `-2[∞]` has degree `-2 = -χ(S²)`. -/
example : WeilDivisor.degree (-2 • WeilDivisor.ofPoint (∞ : OnePoint ℂ)) =
    -eulerChar (OnePoint ℂ) := by
  rw [isCanonicalDivisor_neg_two_infty.degree_eq_neg_two_of_sphere, eulerChar_onePoint,
    Complex.finrank_real_complex]
  norm_num

end IsCanonicalDivisor

end TauCeti.RiemannSurface
