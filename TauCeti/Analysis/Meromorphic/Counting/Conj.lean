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
on `U`. The reflection of a rectangle `s ×ℂ t` is `s ×ℂ (-t)`.

These identities compare the zeros of a completed L-function below the real axis with the zeros
of its dual above it, since the completed function of the dual is the reflection of the original
one.

## Main results

* `TauCeti.divisorCount_conj_conj`, `TauCeti.zeroCount_conj_conj`: reflection of the two counts.
* `Complex.preimage_conj_reProdIm`: the reflection of a rectangle.
-/

public section

open Set ComplexConjugate
open scoped Pointwise

/-- Complex conjugation reflects the rectangle `s ×ℂ t` to `s ×ℂ (-t)`. -/
@[simp]
theorem Complex.preimage_conj_reProdIm (s t : Set ℝ) : conj ⁻¹' (s ×ℂ t) = s ×ℂ (-t) := by
  ext z
  simp [Complex.mem_reProdIm, Set.mem_neg]

namespace TauCeti

/-- Conjugation maps a region bijectively onto its reflection `conj ⁻¹' R`. -/
private theorem bijOn_conj_preimage (R : Set ℂ) : BijOn conj R (conj ⁻¹' R) :=
  ⟨fun z hz ↦ by simpa using hz, (starRingEnd ℂ).injective.injOn,
    fun w hw ↦ ⟨conj w, hw, Complex.conj_conj w⟩⟩

/-- **Reflection of the signed count.** The signed count of `conj ∘ f ∘ conj` over `R`, with
respect to the reflected domain `conj ⁻¹' U`, is the signed count of `f` over the reflected region
`conj ⁻¹' R`, with respect to `U`. -/
theorem divisorCount_conj_conj (f : ℂ → ℂ) (U R : Set ℂ) :
    divisorCount (conj ∘ f ∘ conj) (conj ⁻¹' U) R = divisorCount f U (conj ⁻¹' R) := by
  rw [divisorCount_def, divisorCount_def]
  exact finsum_mem_eq_of_bijOn conj (bijOn_conj_preimage R) fun z _ ↦ divisor_conj_conj U z

/-- **Reflection of the zero count.** The zero count of `conj ∘ f ∘ conj` over `R`, with respect
to the reflected domain `conj ⁻¹' U`, is the zero count of `f` over the reflected region
`conj ⁻¹' R`, with respect to `U`. -/
theorem zeroCount_conj_conj (f : ℂ → ℂ) (U R : Set ℂ) :
    zeroCount (conj ∘ f ∘ conj) (conj ⁻¹' U) R = zeroCount f U (conj ⁻¹' R) := by
  rw [zeroCount_def, zeroCount_def]
  exact finsum_mem_eq_of_bijOn conj (bijOn_conj_preimage R) fun z _ ↦ by
    rw [divisor_conj_conj]

end TauCeti
