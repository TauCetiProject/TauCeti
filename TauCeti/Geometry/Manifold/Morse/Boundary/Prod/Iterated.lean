/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.IteratedProd
public import TauCeti.Geometry.Manifold.Morse.Boundary.Prod.Integral
import TauCeti.Geometry.Manifold.Morse.Boundary.OrientationChange

/-!
# The integral Morse complex of an iterated product

Let `f` be a Morse function on a compact boundaryless manifold `M` and `X` a Morse–Smale
pseudo-gradient adapted to `f`. On the product `IteratedProd M n` of `n + 1` copies of `M`
(`TauCeti.IteratedProd`), the iterated separated sum

`iteratedProdSum f n (x₀, …, xₙ) = f x₀ + ⋯ + f xₙ`

(`TauCeti.iteratedProdSum`) is a Morse function (`TauCeti.IsMorse.iteratedProdSum`), the iterated
product field `iteratedProdField X n = (X, …, X)` (`TauCeti.iteratedProdField`) is a Morse–Smale
pseudo-gradient adapted to it (`TauCeti.IsAdaptedPseudoGradient.iteratedProd` and
`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.iteratedProd`), and its critical counts are the
iterated convolutions of those of `f` (`TauCeti.criticalCount_iteratedProdSum_succ`), so that its
Morse polynomial is the `(n + 1)`-th power of that of `f`. Each step of the iteration is a separated
sum on a binary product, read in the product charts, so the results on the Morse complexes of
products apply to it.

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

## Main definitions

* `TauCeti.iteratedProdSum`: the iterated separated sum of `f` on `IteratedProd M n`.
* `TauCeti.iteratedProdField`: the iterated product field of `X` on `IteratedProd M n`.

## Main results

* `TauCeti.IsMorse.iteratedProdSum`: the iterated separated sum of a Morse function is Morse.
* `ContMDiff.iteratedProdSum`: the iterated separated sum of a `C^k` function is `C^k`.
* `TauCeti.IsAdaptedPseudoGradient.iteratedProd` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.iteratedProd`: the iterated product field of an
  adapted pseudo-gradient is an adapted pseudo-gradient, Morse–Smale when the factor is.
* `TauCeti.criticalCount_iteratedProdSum_zero` and `TauCeti.criticalCount_iteratedProdSum_succ`:
  the critical counts of the iterated separated sum are iterated convolutions of those of `f`.
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

/-! ### The iterated separated sum and the iterated product field -/

section Definitions

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The **iterated separated sum** of a function `f` on `M`: the function
`(x₀, …, xₙ) ↦ f x₀ + ⋯ + f xₙ` on the product `IteratedProd M n` of `n + 1` copies of `M`. -/
def iteratedProdSum (f : M → ℝ) : (n : ℕ) → IteratedProd M n → ℝ
  | 0 => f
  | n + 1 => iteratedProdSum f n ∘ Prod.fst + f ∘ Prod.snd

/-- On one copy of `M`, the iterated separated sum of `f` is `f`. -/
@[simp]
theorem iteratedProdSum_zero (f : M → ℝ) : iteratedProdSum f 0 = f :=
  (rfl)

/-- On `n + 2` copies of `M`, the iterated separated sum of `f` is the separated sum of the one on
`n + 1` copies and of `f`. -/
@[simp]
theorem iteratedProdSum_succ (f : M → ℝ) (n : ℕ) :
    iteratedProdSum f (n + 1) = iteratedProdSum f n ∘ Prod.fst + f ∘ Prod.snd :=
  (rfl)

variable [TopologicalSpace M] [ChartedSpace E M]

/-- The **iterated product field** of a vector field `X` on `M`: the vector field `(X, …, X)` on the
product `IteratedProd M n` of `n + 1` copies of `M`, in the product charts. -/
noncomputable def iteratedProdField (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) :
    (n : ℕ) → (x : IteratedProd M n) → TangentSpace 𝓘(ℝ, IteratedProdModel E n) x
  | 0 => X
  | n + 1 => Manifold.prodVectorField (iteratedProdField X n) X

/-- On one copy of `M`, the iterated product field of `X` is `X`. -/
@[simp]
theorem iteratedProdField_zero (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) :
    iteratedProdField X 0 = X :=
  (rfl)

/-- On `n + 2` copies of `M`, the iterated product field of `X` is the product of the one on
`n + 1` copies and of `X`. -/
@[simp]
theorem iteratedProdField_succ (X : (x : M) → TangentSpace 𝓘(ℝ, E) x) (n : ℕ) :
    iteratedProdField X (n + 1) = Manifold.prodVectorField (iteratedProdField X n) X :=
  (rfl)

end Definitions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] {f : M → ℝ}

/-- **The iterated separated sum of a Morse function is a Morse function.** -/
theorem IsMorse.iteratedProdSum (hf : IsMorse 𝓘(ℝ, E) f) :
    ∀ n, IsMorse 𝓘(ℝ, IteratedProdModel E n) (iteratedProdSum f n)
  | 0 => hf
  | n + 1 => (IsMorse.iteratedProdSum hf n).comp_fst_add_comp_snd_chartedSpaceProd hf

/-- **The iterated separated sum of a `C^k` function is `C^k`.** -/
theorem _root_.ContMDiff.iteratedProdSum {k : WithTop ℕ∞} (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) k f) :
    ∀ n, ContMDiff 𝓘(ℝ, IteratedProdModel E n) 𝓘(ℝ) k (iteratedProdSum f n)
  | 0 => hf
  | n + 1 => ((ContMDiff.iteratedProdSum hf n).comp contMDiff_fst).add (hf.comp contMDiff_snd)

/-- On one copy of `M`, the critical counts of the iterated separated sum of `f` are those of `f`,
for the model `𝓘(ℝ, E)`. Not a `simp` lemma: `simp` first rewrites `iteratedProdSum f 0` to `f`
by `TauCeti.iteratedProdSum_zero`, keeping the model `𝓘(ℝ, IteratedProdModel E 0)`. -/
theorem criticalCount_iteratedProdSum_zero (k : ℕ) :
    criticalCount 𝓘(ℝ, IteratedProdModel E 0) (iteratedProdSum f 0) k =
      criticalCount 𝓘(ℝ, E) f k :=
  (rfl)

/-- **The critical counts of the iterated separated sum are iterated convolutions.** For a `C²`
function `f`, the critical points of index `k` of the iterated separated sum on `n + 2` copies of
`M` are the pairs of a critical point of index `i` of the one on `n + 1` copies and a critical
point of index `j` of `f`, for `i + j = k`. -/
theorem criticalCount_iteratedProdSum_succ [FiniteDimensional ℝ E]
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ) 2 f) (n k : ℕ) :
    criticalCount 𝓘(ℝ, IteratedProdModel E (n + 1)) (iteratedProdSum f (n + 1)) k =
      ∑ ij ∈ Finset.antidiagonal k,
        criticalCount 𝓘(ℝ, IteratedProdModel E n) (iteratedProdSum f n) ij.1 *
          criticalCount 𝓘(ℝ, E) f ij.2 :=
  criticalCount_comp_fst_add_comp_snd_chartedSpaceProd (hf.iteratedProdSum n) hf k

namespace IsAdaptedPseudoGradient

variable [IsManifold 𝓘(ℝ, E) ∞ M] {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

/-- **The iterated product field of an adapted pseudo-gradient** is a pseudo-gradient adapted to
the iterated separated sum. -/
theorem iteratedProd (hX : IsAdaptedPseudoGradient f X) :
    ∀ n, IsAdaptedPseudoGradient (iteratedProdSum f n) (iteratedProdField X n)
  | 0 => hX
  | n + 1 => (IsAdaptedPseudoGradient.iteratedProd hX n).prod hX

variable [CompactSpace M] [T2Space M] [FiniteDimensional ℝ E] {hX : IsAdaptedPseudoGradient f X}

/-- **The iterated product field of a Morse–Smale pseudo-gradient is Morse–Smale.** -/
theorem IsMorseSmale.iteratedProd (h : hX.IsMorseSmale) : ∀ n, (hX.iteratedProd n).IsMorseSmale
  | 0 => h
  | n + 1 => (IsMorseSmale.iteratedProd h n).prod h

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
