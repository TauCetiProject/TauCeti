/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Genus
public import TauCeti.Analysis.Complex.RiemannSurface.Branch.EulerCharacteristic
import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# The genus of a Riemann surface

The topological genus `TauCeti.RiemannSurface.genus X = ((2 - χ(X)) / 2).toNat` is defined in
the finite-CW Euler-characteristic library. This file connects it to the complex-analytic theory.

Given `χ = 2 - 2 · genus` on both sides, the branched-cover formula
`χ(X) = deg f · χ(Y) - R(f)` becomes the Riemann–Hurwitz formula in genus form
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`).

## Main results

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.two_mul_genus_sub_two_eq_of_eulerChar_eq`:
  Riemann–Hurwitz in genus form, for surfaces satisfying `χ = 2 - 2 · genus`.

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
  [FiniteCWType X] [FiniteCWType Y]
  (f : FiniteHolomorphicMap X Y) [FiniteCWType ↥f.branchValuesᶜ]

/-- **Riemann–Hurwitz in genus form**, for surfaces whose Euler numbers are `2 - 2 · genus`: if
`X`, `Y` and the complement of the branch values have finite CW type, and
`χ(X) = 2 - 2 · genus X` and `χ(Y) = 2 - 2 · genus Y`, then
`2 genus X - 2 = deg f · (2 genus Y - 2) + R(f)`, where `R(f)` is the ramification degree. The
two Euler-number hypotheses hold for every compact connected Riemann surface; they are explicit
here because they need Poincaré duality. -/
theorem two_mul_genus_sub_two_eq_of_eulerChar_eq (hX : eulerChar X = 2 - 2 * genus X)
    (hY : eulerChar Y = 2 - 2 * genus Y) :
    2 * (genus X : ℤ) - 2 = degree f * (2 * (genus Y : ℤ) - 2) + ramificationDegree f := by
  linear_combination -f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree + hX -
    (degree f : ℤ) * hY

end FiniteHolomorphicMap

/-- **The Riemann sphere has genus `0`**: its Euler characteristic is `2`. -/
@[simp]
theorem genus_onePoint_complex : genus (OnePoint ℂ) = 0 :=
  genus_eq_of_eulerChar_eq (by rw [eulerChar_onePoint, Complex.finrank_real_complex]; norm_num)

end RiemannSurface

end TauCeti
