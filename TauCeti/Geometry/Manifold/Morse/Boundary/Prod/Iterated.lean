/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Integral
public import TauCeti.Geometry.Manifold.Morse.Stable.IteratedProd
import TauCeti.Geometry.Manifold.Morse.Boundary.OrientationChange

/-!
# The integral Morse complex of an iterated product

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`. On the product `IteratedProd M n` of `n + 1` copies of `M`, the
iterated separated sum `iteratedProdSum f n (x₀, …, xₙ) = f x₀ + ⋯ + f xₙ`
(`TauCeti.iteratedProdSum`) is a Morse function, and the iterated product field
`iteratedProdField X n = (X, …, X)` (`TauCeti.iteratedProdField`) is a Morse–Smale pseudo-gradient
adapted to it (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.iteratedProd`). Each step of the
iteration is a separated sum on a binary product, read in the product charts, so the results on the
Morse complexes of products apply to it.

The main result is that **perfection passes to iterated products over `ℤ`**: if the integral Morse
boundary of `(f, X)` vanishes, then so does that of `(iteratedProdSum f n, iteratedProdField X n)`,
for every choice of orientation data
(`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_iteratedProd_eq_zero`).
By the Künneth formula `∂ (p ⊗ q) = ∂ p ⊗ q + (-1) ^ ind p p ⊗ ∂ q` of the integral Morse boundary
of a product, this holds at each step for the product orientation data, and whether the boundary
vanishes does not depend on the orientation data. The integral Morse complex of the iterated
product then has zero differential, and its homology in degree `k` is free of rank the number of
critical points of index `k`. For the height function on a sphere this computes the integral Morse
homology of the powers of spheres, among them the tori `Tⁿ⁺¹`
(`TauCeti.Geometry.Manifold.Morse.Sphere.Prod.Iterated`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundaryCoeff_iteratedProd_eq_zero` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.signedMorseBoundary_iteratedProd_eq_zero`: the
  integral Morse boundary of the iterated product vanishes when that of the factor does.

## References

* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product).
* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the integral Morse complex, and its computation for the torus).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

attribute [local instance low] chartedSpaceProd

attribute [local instance] isManifold_chartedSpaceProd

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {f : M → ℝ}

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] [CompactSpace M] [T2Space M] [FiniteDimensional ℝ E]
  {X : (x : M) → TangentSpace 𝓘(ℝ, E) x} {hX : IsAdaptedPseudoGradient f X}

/-- **The integral Morse boundary of an iterated product vanishes when that of the factor does.**
Let `X` be a Morse–Smale pseudo-gradient adapted to a Morse function `f`, and suppose that every
coefficient of the integral Morse boundary of `(f, X)` vanishes for some orientation data `𝔬`.
Then for every `n` and every choice `𝔬n` of orientation data for the iterated product field on
`n + 1` copies of `M`, every coefficient of the integral Morse boundary of the iterated separated
sum vanishes. -/
theorem IsMorseSmale.signedMorseBoundaryCoeff_iteratedProd_eq_zero (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {𝔬 : MorseOrientation f X}
    (h𝔬 : ∀ p q, hX.signedMorseBoundaryCoeff 𝔬 p q = 0) :
    ∀ (n : ℕ) (𝔬n : MorseOrientation (iteratedProdSum f n) (iteratedProdField X n)) (p q),
      (hX.iteratedProd n).signedMorseBoundaryCoeff 𝔬n p q = 0
  | 0, 𝔬n, p, q => (signedMorseBoundaryCoeff_eq_zero_iff_eq_zero 𝔬 𝔬n hf p q).2 (h𝔬 p q)
  | n + 1, 𝔬n, p, q => by
    -- Each step is a binary product, whose first factor has vanishing boundary for any choice of
    -- orientation data, by induction.
    obtain ⟨𝔬'⟩ := (hX.iteratedProd n).nonempty_morseOrientation
    exact (h.iteratedProd n).signedMorseBoundaryCoeff_prod_eq_zero (hf.iteratedProdSum n) hf h
      (signedMorseBoundaryCoeff_iteratedProd_eq_zero h hf h𝔬 n 𝔬') h𝔬 𝔬n p q

/-- **The integral Morse boundary of an iterated product vanishes when that of the factor does**,
with coefficients in any ring: if every coefficient of the integral Morse boundary of `(f, X)`
vanishes for some orientation data, then the integral Morse complex of the iterated separated sum
on `n + 1` copies of `M` has zero differential, for every choice of orientation data. -/
theorem IsMorseSmale.signedMorseBoundary_iteratedProd_eq_zero (h : hX.IsMorseSmale)
    (hf : IsMorse 𝓘(ℝ, E) f) {𝔬 : MorseOrientation f X}
    (h𝔬 : ∀ p q, hX.signedMorseBoundaryCoeff 𝔬 p q = 0) (n : ℕ)
    (𝔬n : MorseOrientation (iteratedProdSum f n) (iteratedProdField X n))
    (hfn : IsMorse 𝓘(ℝ, IteratedProdModel E n) (iteratedProdSum f n)) (R : Type*) [Ring R] :
    (hX.iteratedProd n).signedMorseBoundary 𝔬n hfn R = 0 := by
  ext p q
  simp [h.signedMorseBoundaryCoeff_iteratedProd_eq_zero hf h𝔬]

end IsAdaptedPseudoGradient

end TauCeti
