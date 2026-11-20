/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.FiniteCWType
public import TauCeti.Geometry.Manifold.Complex.Analytic
public import TauCeti.Geometry.Manifold.IsManifold.RestrictScalars
public import TauCeti.Geometry.Manifold.Instances.OnePoint.Basic
public import TauCeti.Geometry.Manifold.Morse.CWModel
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Manifold
import TauCeti.AlgebraicTopology.Cellular.EulerCharacteristic.Sphere
import TauCeti.Geometry.Manifold.Morse.EulerCharacteristic

/-!
# Compact complex manifolds have finite CW type

A compact complex manifold `M` of complex dimension `n` is, with the same charts, a compact smooth
boundaryless real manifold of real dimension `2n`. By the Morse-theoretic CW model of compact
manifolds (`TauCeti.FiniteCWType.of_isManifold`) it therefore has finite CW type, so its finite-CW
Euler characteristic `TauCeti.eulerChar M` is defined. This applies in particular to every compact
Riemann surface.

Since a complex vector space of dimension `n` is a real normed space of dimension `2n`,
`TauCeti.eulerChar_eq_sum_range_finrank_singularHomology` gives
`eulerChar M = ∑ᵢ₌₀²ⁿ (-1)ⁱ dim Hᵢ(M; k)` over any division ring `k`, and
`TauCeti.eulerChar_eq_one_sub_finrank_add_finrank` gives `eulerChar M = 1 - b₁ + b₂` for a compact
connected Riemann surface (see the check on the Riemann sphere below).

These statements do not assert `b₂ = 1` or that `b₁` is even. The first needs the fundamental
class of the complex orientation, the second Poincaré duality.

With the underlying real manifold structure `IsManifold.restrictScalars`, `eulerChar M` is the
signed count of the critical points of any Morse function on `M`, by
`TauCeti.IsMorse.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar` (see the example at
the end of this file).

## Main results

* `TauCeti.ComplexManifold.finiteCWType`: a compact Hausdorff manifold modelled on a boundaryless
  complex model over a finite-dimensional space, of class `C^n` for some `n ≠ 0`, has finite CW
  type.
* `TauCeti.ComplexManifold.instFiniteCWType`: the corresponding low-priority instance for compact
  Riemann surfaces, charted on `ℂ`.

## Checks

* For the Riemann sphere the Euler characteristic of this file is `2`, as computed by
  `TauCeti.eulerChar_onePoint`.
* Hence `b₂ = b₁ + 1` for the Riemann sphere, over every division ring.

## References

* J. Milnor, *Morse Theory*, Annals of Mathematics Studies 51, Princeton University Press, 1963,
  Theorem 3.5.
* A. Hatcher, *Algebraic Topology*, Theorem 2.44 and Proposition 3.29.
-/

public section

noncomputable section

open AlgebraicTopology CategoryTheory Module
open scoped Manifold ContDiff

universe u

namespace TauCeti

namespace ComplexManifold

section FiniteCWType

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
  [TopologicalSpace H] {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]

variable (I : ModelWithCorners ℂ E H) [I.Boundaryless] (M) [ChartedSpace H M] in
/-- **Compact complex manifolds have finite CW type.** A compact Hausdorff manifold modelled on a
boundaryless complex model `I` over a finite-dimensional space, of class `C^n` for some `n ≠ 0`, is
homotopy equivalent to a finite CW complex. With the same charts it is a compact smooth
boundaryless real manifold, modelled on `I.restrictScalars ℝ`, so this is
`TauCeti.FiniteCWType.of_isManifold`. -/
theorem finiteCWType {n : ℕ∞ω} (hn : n ≠ 0) [h : IsManifold I n M] : FiniteCWType M :=
  have : IsManifold (I.restrictScalars ℝ) ∞ M :=
    I.isManifold_restrictScalars ℝ (h.of_ne_zero ∞ hn)
  FiniteCWType.of_isManifold (I := I.restrictScalars ℝ) M

/-- **Compact Riemann surfaces have finite CW type.** A compact Hausdorff complex manifold charted
on `ℂ` has finite CW type. This is a low-priority instance, the case `I = 𝓘(ℂ)` of
`TauCeti.ComplexManifold.finiteCWType`. Since `TauCeti.FiniteCWType` is a proposition, it agrees
with every other instance, for example on the Riemann sphere. -/
instance (priority := 100) instFiniteCWType [ChartedSpace ℂ M] [IsManifold 𝓘(ℂ) 1 M] :
    FiniteCWType M :=
  finiteCWType M 𝓘(ℂ) one_ne_zero

end FiniteCWType

/-! ### Checks -/

section Checks

/-- **Check: the Riemann sphere.** The finite CW type of `OnePoint ℂ` as a compact complex
manifold gives Euler characteristic `2`, the value of `TauCeti.eulerChar_onePoint`. -/
example :
    @eulerChar (OnePoint ℂ) _ (finiteCWType (OnePoint ℂ) 𝓘(ℂ) (n := ω) (by simp)) = 2 := by
  rw [eulerChar_onePoint, Complex.finrank_real_complex]
  norm_num

/-- **Check: Betti numbers of the Riemann sphere.** By
`TauCeti.eulerChar_eq_one_sub_finrank_add_finrank` and `TauCeti.eulerChar_onePoint`, the Riemann
sphere has `b₂ = b₁ + 1` over every division ring. -/
example (k : Type) [DivisionRing k] :
    finrank k (((singularHomologyFunctor (ModuleCat.{0} k) 2).obj (ModuleCat.of k k)).obj
        (TopCat.of (OnePoint ℂ))) =
      finrank k (((singularHomologyFunctor (ModuleCat.{0} k) 1).obj (ModuleCat.of k k)).obj
        (TopCat.of (OnePoint ℂ))) + 1 := by
  have := eulerChar_eq_one_sub_finrank_add_finrank (OnePoint ℂ) k (E := ℂ)
    Complex.finrank_real_complex
  rw [eulerChar_onePoint, Complex.finrank_real_complex] at this
  omega

/-- On a compact Riemann surface the Euler characteristic is the signed count of the critical
points of any Morse function on the underlying real surface. -/
example {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M] [ChartedSpace ℂ M]
    [IsManifold 𝓘(ℂ) ∞ M] {f : M → ℝ} (hf : IsMorse 𝓘(ℝ, ℂ) f) :
    ∑ i ∈ Finset.range (finrank ℝ ℂ + 1), (-1 : ℤ) ^ i * (criticalCount 𝓘(ℝ, ℂ) f i).toNat =
      eulerChar M :=
  have : IsManifold 𝓘(ℝ, ℂ) ∞ M := IsManifold.restrictScalars ℝ ‹_›
  hf.sum_range_neg_one_pow_mul_toNat_criticalCount_eq_eulerChar

end Checks

end ComplexManifold

end TauCeti
