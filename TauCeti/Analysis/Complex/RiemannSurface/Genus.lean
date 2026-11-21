/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
public import TauCeti.Analysis.Complex.RiemannSurface.Divisor.RiemannRoch
public import TauCeti.Geometry.Manifold.Complex.FiniteCWType
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.Analysis.Complex.RiemannSurface.Branch.Sphere

/-!
# The genus of a Riemann surface

The topological genus `TauCeti.RiemannSurface.genus X = ((2 - χ(X)) / 2).toNat` is defined in
the finite-CW Euler-characteristic library. This file connects it to the complex-analytic theory.

Given `χ = 2 - 2 · genus` on both sides, the branched-cover formula
`χ(X) = deg f · χ(Y) - R(f)` becomes the Riemann–Hurwitz formula in genus form
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`).

In analytic genus zero, Riemann–Roch gives a finite holomorphic map `X → ℙ¹` of degree one
(`TauCeti.RiemannSurface.exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero`).
It is unramified
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.ramificationDegree_eq_zero_of_degree_eq_one`), so
the topological Riemann–Hurwitz formula over the sphere gives `χ(X) = 2` and topological genus
`0`.

## Main results

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`:
  Riemann–Hurwitz in genus form, for surfaces satisfying `χ = 2 - 2 · genus`.
* `TauCeti.RiemannSurface.eulerChar_eq_two_of_analyticGenus_eq_zero` and
  `TauCeti.RiemannSurface.genus_eq_zero_of_analyticGenus_eq_zero`: a compact connected Riemann
  surface with finite-dimensional `H¹(X, 𝒪)` and analytic genus `0` has `χ(X) = 2` and topological
  genus `0`.

## Checks

* `TauCeti.RiemannSurface.genus_onePoint_complex`: the Riemann sphere has genus `0`.

The level-one modular curve has genus `0`: see
`TauCeti.ModularGroup.genus_compactifiedQuotient`.

## References

* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17.
-/

public section

noncomputable section

open scoped Manifold

universe u

namespace TauCeti

namespace RiemannSurface

namespace FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  (f : FiniteHolomorphicMap X Y)

/-- **Riemann--Hurwitz in genus form**, for compact Riemann surfaces whose Euler numbers are
`2 - 2 · genus`: if `χ(X) = 2 - 2 · genus X` and `χ(Y) = 2 - 2 · genus Y`, then
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`, where `R(f)` is the ramification degree. The
two Euler-number hypotheses hold for every compact connected Riemann surface; they are explicit
here because they need Poincaré duality. -/
theorem two_mul_genus_sub_two_eq_of_eulerChar_eq (hX : eulerChar X = 2 - 2 * genus X)
    (hY : @eulerChar Y _ f.finiteCWType_codomain = 2 - 2 * @genus Y _ f.finiteCWType_codomain) :
    2 * (genus X : ℤ) - 2 =
      degree f * (2 * (@genus Y _ f.finiteCWType_codomain : ℤ) - 2) + ramificationDegree f := by
  linear_combination -f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree + hX -
    (degree f : ℤ) * hY

end FiniteHolomorphicMap

/-- **The Riemann sphere has genus `0`**: its Euler characteristic is `2`. -/
@[simp]
theorem genus_onePoint_complex : genus (OnePoint ℂ) = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_onePoint, Complex.finrank_real_complex]; norm_num)

section AnalyticGenus

variable {X : Type} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) 1 X]
  [CompactSpace X] [T2Space X] [ConnectedSpace X]
  [FiniteDimensional ℂ ((TauCeti.Topology.cechCohomology (TopCat.of X) (ModuleCat.{0} ℂ) 1).obj
    (holomorphicStructureSheafModules 𝓘(ℂ) X).obj)]

/-- **Analytic genus zero gives Euler characteristic two.** A compact connected Riemann surface
with finite-dimensional `H¹(X, 𝒪)` and analytic genus `0` has `χ(X) = 2`. -/
theorem eulerChar_eq_two_of_analyticGenus_eq_zero (h : analyticGenus X = 0) :
    eulerChar X = 2 := by
  obtain ⟨F, hF⟩ := exists_finiteHolomorphicMap_degree_eq_one_of_analyticGenus_eq_zero h
  rw [F.eulerChar_eq_two_mul_degree_sub_ramificationDegree, hF,
    F.ramificationDegree_eq_zero_of_degree_eq_one hF]
  norm_num

/-- **Analytic genus zero gives topological genus zero.** A compact connected Riemann surface with
finite-dimensional `H¹(X, 𝒪)` and analytic genus `0` has topological genus `0`. -/
theorem genus_eq_zero_of_analyticGenus_eq_zero (h : analyticGenus X = 0) : genus X = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_eq_two_of_analyticGenus_eq_zero h]; norm_num)

end AnalyticGenus

end RiemannSurface

end TauCeti
