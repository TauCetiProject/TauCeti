/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Meromorphic.Conj
public import TauCeti.Analysis.Meromorphic.Counting.Basic

/-!
# Reflecting zero counts across the real axis

The reflected function `conj ∘ f ∘ conj` has at `z` the divisor that `f` has at `conj z`
(`TauCeti.divisor_conj_conj`). Summed over a region, its signed count and its zero count over `R`,
on the reflected domain `conj ⁻¹' U`, are those of `f` over the reflected region `conj ⁻¹' R`,
on `U`.

These identities compare the zeros of a completed L-function below the real axis with the zeros
of its dual above it, since the completed function of the dual is the reflection of the original
one.

## Main results

* `TauCeti.divisorCount_conj_conj`, `TauCeti.zeroCount_conj_conj`: reflection of the two counts.
* `TauCeti.divisorCount_conj_conj_univ`, `TauCeti.zeroCount_conj_conj_univ`: the whole-plane
  cases, as simp lemmas.
-/

public section

open Set ComplexConjugate

namespace TauCeti

/-- **Reflection of the signed count.** The signed count of `conj ∘ f ∘ conj` over `R`, with
respect to the reflected domain `conj ⁻¹' U`, is the signed count of `f` over the reflected region
`conj ⁻¹' R`, with respect to `U`. -/
theorem divisorCount_conj_conj (f : ℂ → ℂ) (U R : Set ℂ) :
    divisorCount (conj ∘ f ∘ conj) (conj ⁻¹' U) R = divisorCount f U (conj ⁻¹' R) := by
  rw [divisorCount_def, divisorCount_def]
  refine (finsum_mem_eq_of_bijOn conj
    ((Function.Involutive.bijective Complex.conj_conj).bijOn_preimage (t := R)) fun z _ ↦ ?_).symm
  rw [divisor_conj_conj, Complex.conj_conj]

/-- **Reflection of the zero count.** The zero count of `conj ∘ f ∘ conj` over `R`, with respect
to the reflected domain `conj ⁻¹' U`, is the zero count of `f` over the reflected region
`conj ⁻¹' R`, with respect to `U`. -/
theorem zeroCount_conj_conj (f : ℂ → ℂ) (U R : Set ℂ) :
    zeroCount (conj ∘ f ∘ conj) (conj ⁻¹' U) R = zeroCount f U (conj ⁻¹' R) := by
  rw [zeroCount_def, zeroCount_def]
  refine (finsum_mem_eq_of_bijOn conj
    ((Function.Involutive.bijective Complex.conj_conj).bijOn_preimage (t := R)) fun z _ ↦ ?_).symm
  rw [divisor_conj_conj, Complex.conj_conj]

/-- **Reflection of the signed count on the whole plane.** The signed count of `conj ∘ f ∘ conj`
over `R` is the signed count of `f` over the reflected region `conj ⁻¹' R`. -/
@[simp]
theorem divisorCount_conj_conj_univ (f : ℂ → ℂ) (R : Set ℂ) :
    divisorCount (conj ∘ f ∘ conj) univ R = divisorCount f univ (conj ⁻¹' R) := by
  rw [← divisorCount_conj_conj, preimage_univ]

/-- **Reflection of the zero count on the whole plane.** The zero count of `conj ∘ f ∘ conj` over
`R` is the zero count of `f` over the reflected region `conj ⁻¹' R`. -/
@[simp]
theorem zeroCount_conj_conj_univ (f : ℂ → ℂ) (R : Set ℂ) :
    zeroCount (conj ∘ f ∘ conj) univ R = zeroCount f univ (conj ⁻¹' R) := by
  rw [← zeroCount_conj_conj, preimage_univ]

end TauCeti
