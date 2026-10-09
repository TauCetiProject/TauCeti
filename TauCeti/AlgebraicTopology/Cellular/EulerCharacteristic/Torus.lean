/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Product
public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
public import TauCeti.Topology.CWComplex.Classical.Circle

/-!
# The Euler characteristic of a torus

The circle is the sphere `S¹`, so `χ(S¹) = 1 + (-1)¹ = 0` (`TauCeti.eulerChar_sphere`).  The
Euler characteristic is multiplicative on finite products (`TauCeti.eulerChar_pi`), so every torus
`Tⁿ = S¹ × ⋯ × S¹` with `n > 0` factors has Euler characteristic zero.  The torus is modelled as
`∀ i, AddCircle (p i)` over a nonempty finite index type, with positive periods.

## Main results

* `TauCeti.eulerChar_circle`, `TauCeti.eulerChar_addCircle`: `χ(S¹) = 0`.
* `TauCeti.eulerChar_torus`: `χ(Tⁿ) = 0` for `n > 0`.

## References

* A. Hatcher, [*Algebraic Topology*](https://pi.math.cornell.edu/~hatcher/AT/AT.pdf),
  Section 2.2, the Euler characteristic after Theorem 2.44.
-/

public section

namespace TauCeti

/-- The unit circle has Euler characteristic zero. -/
@[simp]
theorem eulerChar_circle : eulerChar Circle = 0 := by
  rw [Circle.homeomorphSphere.eulerChar_eq, eulerChar_sphere (n := 1) Complex.finrank_real_complex]
  norm_num

/-- An additive circle of positive period has Euler characteristic zero. -/
@[simp]
theorem eulerChar_addCircle (p : ℝ) [hp : Fact (0 < p)] : eulerChar (AddCircle p) = 0 := by
  rw [(AddCircle.homeomorphCircle hp.out.ne').eulerChar_eq, eulerChar_circle]

/-- **The Euler characteristic of a torus.**  A product `∀ i, AddCircle (p i)` of finitely many
circles of positive periods, with at least one factor, has Euler characteristic zero. -/
@[simp]
theorem eulerChar_torus {ι : Type} [Finite ι] [Nonempty ι] (p : ι → ℝ) [∀ i, Fact (0 < p i)] :
    eulerChar (∀ i, AddCircle (p i)) = 0 := by
  have := Fintype.ofFinite ι
  rw [eulerChar_pi]
  exact Finset.prod_eq_zero (Finset.mem_univ (Classical.arbitrary ι)) (eulerChar_addCircle _)

end TauCeti
