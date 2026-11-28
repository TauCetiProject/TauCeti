/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Genus

/-!
# Branched covers of a surface of genus one

Let `f : X → Y` be a finite holomorphic map from a compact Riemann surface to a connected Riemann
surface whose Euler characteristic is `0`, such as a one-dimensional complex torus. The
Riemann–Hurwitz formula `χ(X) = deg f · χ(Y) - R(f)`
(`FiniteHolomorphicMap.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree`)
loses its degree term, and the Euler characteristic of the source is minus the ramification
degree:

`χ(X) = -R(f)`.

Since `R(f) ≥ 0`, the source has `χ(X) ≤ 0`, so its genus is at least one: a compact Riemann
surface of genus zero admits no nonconstant holomorphic map to a surface of genus one. Moreover
`f` is unramified exactly when `χ(X) = 0`, and a finite holomorphic map with compact source is
unramified exactly when it is a covering map
(`TauCeti.RiemannSurface.FiniteHolomorphicMap.isCoveringMap_iff_ramificationDegree_eq_zero`).
When `X` is connected, `χ(X) = 2 - 2 · genus X`
(`TauCeti.RiemannSurface.eulerChar_eq_two_sub_two_mul_genus`), so this reads
`R(f) = 2 genus X - 2`, and `f` is a covering map exactly when `X` has genus one.

This is the Riemann–Hurwitz step in the analysis of curves near a pseudoholomorphic torus: a
compact holomorphic curve projecting with positive degree onto a torus, and of genus at most one,
is an unbranched covering of it
(`FiniteHolomorphicMap.isCoveringMap_and_genus_eq_one_and_singularity_eq_zero_of_le_zero`).

## Main results

* `TauCeti.RiemannSurface.FiniteHolomorphicMap.eulerChar_eq_neg_ramificationDegree`:
  `χ(X) = -R(f)` over a target with `χ(Y) = 0`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.one_le_genus`: the source has genus at least one.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.isCoveringMap_iff_eulerChar_eq_zero`: `f` is a
  covering map exactly when `χ(X) = 0`.
* `TauCeti.RiemannSurface.FiniteHolomorphicMap.isCoveringMap_iff_genus_eq_one`: `f` is then a
  covering map exactly when `X` has genus one.

## References

* Otto Forster, *Lectures on Riemann Surfaces*, Graduate Texts in Mathematics 81,
  Springer, 1981, §17 (the Riemann–Hurwitz formula).
* Rick Miranda, *Algebraic Curves and Riemann Surfaces*, Graduate Studies in Mathematics 5,
  American Mathematical Society, 1995, Chapter II §4.
-/

public section

open scoped Manifold

universe u

namespace TauCeti.RiemannSurface.FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  [FiniteCWType X] [FiniteCWType Y]
  (f : FiniteHolomorphicMap X Y)

/-- **Riemann–Hurwitz over a surface of Euler characteristic zero.** If `X` and `Y` have finite
CW type and `χ(Y) = 0`, then `χ(X) = -R(f)`, where `R(f)` is the ramification degree. -/
theorem eulerChar_eq_neg_ramificationDegree (hY : eulerChar Y = 0) :
    eulerChar X = -ramificationDegree f := by
  rw [f.eulerChar_eq_degree_mul_eulerChar_sub_ramificationDegree, hY, mul_zero, zero_sub]

include f in
/-- A compact Riemann surface with a finite holomorphic map to a surface of Euler characteristic
zero has genus at least one. -/
theorem one_le_genus (hY : eulerChar Y = 0) : 1 ≤ genus X := by
  have := f.eulerChar_eq_neg_ramificationDegree hY
  rw [genus_def]
  omega

/-- A finite holomorphic map from a compact Riemann surface to a surface of Euler characteristic
zero is a covering map exactly when its source also has Euler characteristic zero. -/
theorem isCoveringMap_iff_eulerChar_eq_zero (hY : eulerChar Y = 0) :
    IsCoveringMap f ↔ eulerChar X = 0 := by
  rw [f.isCoveringMap_iff_ramificationDegree_eq_zero, f.eulerChar_eq_neg_ramificationDegree hY]
  omega

/-- A finite holomorphic map from a compact connected Riemann surface to a surface of Euler
characteristic zero is a covering map exactly when `X` has genus one. -/
theorem isCoveringMap_iff_genus_eq_one [ConnectedSpace X] (hY : eulerChar Y = 0) :
    IsCoveringMap f ↔ genus X = 1 := by
  rw [f.isCoveringMap_iff_eulerChar_eq_zero hY, eulerChar_eq_two_sub_two_mul_genus X]
  omega

end TauCeti.RiemannSurface.FiniteHolomorphicMap

end
