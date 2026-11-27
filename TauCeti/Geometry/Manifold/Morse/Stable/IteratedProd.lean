/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Morse.IteratedProd
public import TauCeti.Geometry.Manifold.Morse.Stable.Prod

/-!
# The iterated product of a Morse–Smale pseudo-gradient

Let `X` be a pseudo-gradient adapted to a Morse function `f` on `M`. On the product
`IteratedProd M n` of `n + 1` copies of `M`, the iterated product field
`iteratedProdField X n = (X, …, X)` (`TauCeti.iteratedProdField`) is a pseudo-gradient adapted to
the iterated separated sum `iteratedProdSum f n` (`TauCeti.IsAdaptedPseudoGradient.iteratedProd`),
and it is Morse–Smale when `X` is (`TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.iteratedProd`).
Each step of the iteration is a product field on a binary product, read in the product charts, so
the results on products of pseudo-gradients apply to it.

## Main definitions

* `TauCeti.iteratedProdField`: the iterated product field of `X` on `IteratedProd M n`.

## Main results

* `TauCeti.IsAdaptedPseudoGradient.iteratedProd` and
  `TauCeti.IsAdaptedPseudoGradient.IsMorseSmale.iteratedProd`: the iterated product field of an
  adapted pseudo-gradient is an adapted pseudo-gradient, Morse–Smale when the factor is.

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

section Definitions

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
  [ChartedSpace E M]

/-- The **iterated product field** of a vector field `X` on `M`: the vector field `(X, …, X)` on the
product `IteratedProd M n` of `n + 1` copies of `M`, in the product charts. -/
@[expose]
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

namespace IsAdaptedPseudoGradient

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type*} [TopologicalSpace M]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ} {X : (x : M) → TangentSpace 𝓘(ℝ, E) x}

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

end IsAdaptedPseudoGradient

end TauCeti
