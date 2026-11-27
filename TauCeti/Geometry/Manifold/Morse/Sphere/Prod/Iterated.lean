/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Iterated
public import TauCeti.Geometry.Manifold.Morse.Sphere.Boundary
public import TauCeti.Geometry.Manifold.Morse.Sphere.Prod.Basic

/-!
# The integral Morse homology of powers of spheres and of tori

On the product `(Sⁿ)ʳ⁺¹ = IteratedProd (sphere (0 : E) 1) r` of `r + 1` copies of the unit sphere
`Sⁿ`, the sum of the height functions of the factors
`iteratedProdSum (sphereHeight v) r (x₀, …, xᵣ) = ⟪x₀, v⟫ + ⋯ + ⟪xᵣ, v⟫` is a Morse function. Its
critical points are the tuples of poles, and the index of such a tuple is `n` times the number of
north poles in it, so its Morse polynomial is `(1 + tⁿ)ʳ⁺¹`
(`TauCeti.criticalCount_iteratedProdSum_sphereHeight`). For `n = 1` the product is the torus
`Tʳ⁺¹ = S¹ × ⋯ × S¹`, and the function is the standard Morse function on the torus, with
`(r + 1 choose k)` critical points of index `k`.

The integral Morse boundary of the height function on a sphere vanishes for every adapted
pseudo-gradient and every choice of orientations
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundaryCoeff_sphereHeight`), and every such
pseudo-gradient is Morse–Smale, so the integral Morse boundary of the iterated product field
vanishes as well, for every choice of orientation data
(`TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_iteratedProd_sphereHeight`). Hence the
integral Morse homology of `(Sⁿ)ʳ⁺¹` in degree `k`, with coefficients in any ring with the strong
rank condition, has rank the coefficient of `tᵏ` in `(1 + tⁿ)ʳ⁺¹`
(`TauCeti.IsAdaptedPseudoGradient.finrank_homology_signedMorseComplex_iteratedProd_sphereHeight`).
Over `ℤ` these are the ranks of the integral singular homology of `(Sⁿ)ʳ⁺¹`, which is free by the
Künneth theorem; the comparison of Morse and singular homology is not made here. For the torus
`Tʳ⁺¹` the integral Morse homology in degree `k` has rank `(r + 1 choose k)`
(`finrank_homology_signedMorseComplex_iteratedProd_sphereHeight_eq_choose`, in the namespace
`TauCeti.IsAdaptedPseudoGradient`).

## Main results

* `TauCeti.IsAdaptedPseudoGradient.signedMorseBoundary_iteratedProd_sphereHeight`: its integral
  Morse boundary vanishes, for every adapted pseudo-gradient of the factor and every choice of
  orientation data.
* `TauCeti.IsAdaptedPseudoGradient.finrank_homology_signedMorseComplex_iteratedProd_sphereHeight`:
  its integral Morse homology in degree `k` has rank the coefficient of `tᵏ` in `(1 + tⁿ)ʳ⁺¹`.
* `finrank_homology_signedMorseComplex_iteratedProd_sphereHeight_eq_choose`, in the namespace
  `TauCeti.IsAdaptedPseudoGradient`: the integral Morse homology of the torus `Tʳ⁺¹` in degree `k`
  has rank `(r + 1 choose k)`.

## References

* M. Audin and M. Damian, *Morse Theory and Floer Homology*, Springer Universitext, 2014,
  Chapter 4 (the integral Morse complex, and its computation for the torus).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, §3, Exercise 2 (the Morse complex of a product).
-/

public section

open Metric Module Polynomial
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

section Sphere

variable {n : ℕ} [Fact (finrank ℝ E = n + 1)]

namespace IsAdaptedPseudoGradient

variable [FiniteDimensional ℝ E] {v : sphere (0 : E) 1}
  {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 n) x}
  (hX : IsAdaptedPseudoGradient (sphereHeight v) X)
  (r : ℕ) (𝔬 : MorseOrientation (iteratedProdSum (sphereHeight v) r) (iteratedProdField X r))
  (hf : IsMorse 𝓘(ℝ, IteratedProdModel (EuclideanSpace ℝ (Fin n)) r)
    (iteratedProdSum (sphereHeight v) r))

/-- **The integral Morse boundary of a sum of height functions on a power of a sphere is zero.** For
every pseudo-gradient `X` adapted to the height function on `Sⁿ`, and every choice of orientation
data for the iterated product field on `(Sⁿ)ʳ⁺¹`, such as the torus `Tʳ⁺¹ = S¹ × ⋯ × S¹`, the
integral Morse complex of the sum of the height functions, with coefficients in any ring, has zero
differential. -/
@[simp]
theorem signedMorseBoundary_iteratedProd_sphereHeight (R : Type*) [Ring R] :
    (hX.iteratedProd r).signedMorseBoundary 𝔬 hf R = 0 := by
  obtain ⟨𝔬₀⟩ := hX.nonempty_morseOrientation
  exact hX.isMorseSmale_sphereHeight.signedMorseBoundary_iteratedProd_eq_zero
    (isMorse_sphereHeight v) (signedMorseBoundaryCoeff_sphereHeight 𝔬₀) r 𝔬 hf R

/-- **The integral Morse homology of a power of a sphere.** For every pseudo-gradient `X` adapted
to the height function on `Sⁿ` and every choice of orientation data for the iterated product field
on `(Sⁿ)ʳ⁺¹`, the integral Morse homology of the sum of the height functions in degree `k`, with
coefficients in any ring with the strong rank condition such as `ℤ`, has rank the coefficient of
`tᵏ` in `(1 + tⁿ)ʳ⁺¹`, the rank of the integral homology of `(Sⁿ)ʳ⁺¹`. -/
theorem finrank_homology_signedMorseComplex_iteratedProd_sphereHeight {R : Type*} [Ring R]
    [StrongRankCondition R]
    (hsq : (hX.iteratedProd r).signedMorseBoundary 𝔬 hf R ∘ₗ
      (hX.iteratedProd r).signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    finrank R (((hX.iteratedProd r).signedMorseComplex 𝔬 hf R hsq).homology k) =
      ((1 + Polynomial.X ^ n) ^ (r + 1) : ℕ[X]).coeff k := by
  rw [finrank_homology_signedMorseComplex_of_signedMorseBoundary_eq_zero hsq
    (signedMorseBoundary_iteratedProd_sphereHeight hX r 𝔬 hf R),
    criticalCount_iteratedProdSum_sphereHeight, ENat.toNat_natCast]

end IsAdaptedPseudoGradient

end Sphere

namespace IsAdaptedPseudoGradient

/-- **The integral Morse homology of a torus.** For every pseudo-gradient `X` adapted to the height
function on the circle `S¹` and every choice of orientation data for the iterated product field on
the torus `Tʳ⁺¹ = S¹ × ⋯ × S¹`, the integral Morse homology of the sum of the height functions in
degree `k`, with coefficients in any ring with the strong rank condition such as `ℤ`, has rank
`(r + 1 choose k)`, the rank of the integral homology of `Tʳ⁺¹`. -/
theorem finrank_homology_signedMorseComplex_iteratedProd_sphereHeight_eq_choose
    [Fact (finrank ℝ E = 1 + 1)] [FiniteDimensional ℝ E] {v : sphere (0 : E) 1}
    {X : (x : sphere (0 : E) 1) → TangentSpace (𝓡 1) x}
    (hX : IsAdaptedPseudoGradient (sphereHeight v) X) (r : ℕ)
    (𝔬 : MorseOrientation (iteratedProdSum (sphereHeight v) r) (iteratedProdField X r))
    (hf : IsMorse 𝓘(ℝ, IteratedProdModel (EuclideanSpace ℝ (Fin 1)) r)
      (iteratedProdSum (sphereHeight v) r))
    {R : Type*} [Ring R] [StrongRankCondition R]
    (hsq : (hX.iteratedProd r).signedMorseBoundary 𝔬 hf R ∘ₗ
      (hX.iteratedProd r).signedMorseBoundary 𝔬 hf R = 0) (k : ℕ) :
    finrank R (((hX.iteratedProd r).signedMorseComplex 𝔬 hf R hsq).homology k) =
      (r + 1).choose k := by
  rw [finrank_homology_signedMorseComplex_iteratedProd_sphereHeight hX r 𝔬 hf hsq, pow_one,
    coeff_one_add_X_pow, Nat.cast_id]

end IsAdaptedPseudoGradient

end TauCeti
