/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.IsManifold.IteratedProd
public import TauCeti.Geometry.Manifold.Morse.Prod

/-!
# The iterated separated sum of a Morse function

Let `f` be a function on a manifold `M`. On the product `IteratedProd M n` of `n + 1` copies of `M`
(`TauCeti.IteratedProd`), the iterated separated sum

`iteratedProdSum f n (x₀, …, xₙ) = f x₀ + ⋯ + f xₙ`

(`TauCeti.iteratedProdSum`) is a Morse function when `f` is (`TauCeti.IsMorse.iteratedProdSum`),
and its critical counts are the iterated convolutions of those of `f`
(`TauCeti.criticalCount_iteratedProdSum_succ`), so that its Morse polynomial is the `(n + 1)`-th
power of that of `f`. Each step of the iteration is a separated sum on a binary product, read in the
product charts, so the results on separated sums of `TauCeti.Geometry.Manifold.Morse.Prod` apply to
it.

## Main definitions

* `TauCeti.iteratedProdSum`: the iterated separated sum of `f` on `IteratedProd M n`.

## Main results

* `TauCeti.IsMorse.iteratedProdSum`: the iterated separated sum of a Morse function is Morse.
* `ContMDiff.iteratedProdSum`: the iterated separated sum of a `C^k` function is `C^k`.
* `TauCeti.criticalCount_iteratedProdSum_zero` and `TauCeti.criticalCount_iteratedProdSum_succ`:
  the critical counts of the iterated separated sum are iterated convolutions of those of `f`.

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

variable {M : Type*}

/-- The **iterated separated sum** of a function `f` on `M`: the function
`(x₀, …, xₙ) ↦ f x₀ + ⋯ + f xₙ` on the product `IteratedProd M n` of `n + 1` copies of `M`. -/
@[expose]
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

end TauCeti
