/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.RiemannSurface.Genus

/-!
# The virtual dimension of a multiple cover

A nonconstant closed pseudoholomorphic curve `u` factors as `u = v ∘ f` through a simple curve
`v` and a finite holomorphic map `f` of some degree `d`. The unmarked virtual dimension
`D(g, c) = (m - 3)(2 - 2 g) + 2 c` of a closed curve of genus `g` and first Chern number `c` in a
target of complex dimension `m` (`TauCeti.unmarkedVirtualDimension`) relates those of `u` and
`v`: by Riemann–Hurwitz, `D(v ∘ f) = deg f · D(v) - (m - 3) R(f)` when the Chern number of
`v ∘ f` is `deg f` times that of `v`, where `R(f)` is the ramification degree of `f`.

The Chern number of the composite is a parameter here: the statement is the arithmetic identity
for the genera related by Riemann–Hurwitz.

## Main results

* `TauCeti.unmarkedVirtualDimension`: the unmarked virtual dimension `(m - 3)(2 - 2 g) + 2 c`.
* `FiniteHolomorphicMap.unmarkedVirtualDimension_eq_degree_mul_unmarkedVirtualDimension_sub`:
  the unmarked virtual dimension of a multiple cover.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications 52, 2012, Section 2.5 (simple curves and multiple covers).
-/

public section

open scoped Manifold

universe u

namespace TauCeti

/-- The unmarked virtual dimension `(m - 3)(2 - 2 g) + 2 c` of a closed pseudoholomorphic curve of
genus `g` and first Chern number `c` in a target of complex dimension `m`. -/
def unmarkedVirtualDimension (m : ℤ) (g : ℕ) (c : ℤ) : ℤ :=
  (m - 3) * (2 - 2 * g) + 2 * c

/-- The defining formula of `TauCeti.unmarkedVirtualDimension`. -/
theorem unmarkedVirtualDimension_def (m : ℤ) (g : ℕ) (c : ℤ) :
    unmarkedVirtualDimension m g c = (m - 3) * (2 - 2 * g) + 2 * c := by
  rw [unmarkedVirtualDimension]

namespace RiemannSurface

namespace FiniteHolomorphicMap

variable {X Y : Type u} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]
  [IsManifold 𝓘(ℂ) 1 X] [IsManifold 𝓘(ℂ) 1 Y]
  [CompactSpace X] [T2Space X] [T2Space Y] [PreconnectedSpace Y]
  [FiniteCWType Y] (f : FiniteHolomorphicMap X Y)

/-- **The unmarked virtual dimension of a multiple cover.** Let `f : X → Y` be a finite
holomorphic map of compact Riemann surfaces satisfying `χ = 2 - 2 · genus`. Then
`D(genus X, deg f · c) = deg f · D(genus Y, c) - (m - 3) R(f)` for every integer `c`, where `D` is
`TauCeti.unmarkedVirtualDimension m`. For a curve `v` on `Y` with Chern number `c` whose composite
`v ∘ f` has Chern number `deg f · c`, this is `D(v ∘ f) = deg f · D(v) - (m - 3) R(f)`. -/
theorem unmarkedVirtualDimension_eq_degree_mul_unmarkedVirtualDimension_sub (m c : ℤ)
    (hX : eulerChar X = 2 - 2 * genus X) (hY : eulerChar Y = 2 - 2 * genus Y) :
    unmarkedVirtualDimension m (genus X) (degree f * c) =
      degree f * unmarkedVirtualDimension m (genus Y) c - (m - 3) * ramificationDegree f := by
  rw [unmarkedVirtualDimension_def, unmarkedVirtualDimension_def]
  linear_combination (3 - m) * f.two_mul_genus_sub_two_eq_of_eulerChar_eq hX hY

end FiniteHolomorphicMap

end RiemannSurface

end TauCeti
