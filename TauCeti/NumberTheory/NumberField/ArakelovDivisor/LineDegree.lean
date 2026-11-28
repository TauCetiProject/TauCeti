/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.HermitianLine
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Line
public import TauCeti.RingTheory.FractionalIdeal.Projective

import TauCeti.RingTheory.PicardGroup.Contraction

/-!
# The Arakelov degree of the line of an Arakelov divisor

The section-free Arakelov degree `TauCeti.HermitianMetric.lineDegree` of the hermitian line
`O(D)` of an Arakelov divisor `D` is the degree of `D`.

## Main results

* `TauCeti.ArakelovDivisor.lineDegree_hermitianMetric`: `deg^(O(D)) = deg^(D)`.

## References

* L. Szpiro, *Degrés, intersections, hauteurs*, Astérisque 127, §1.1–1.2.
-/

public section

open scoped nonZeroDivisors
open NumberField

namespace TauCeti.ArakelovDivisor

variable {K : Type*} [Field K] [NumberField K]

/-- **The Arakelov degree of `O(D)` is the degree of `D`.** -/
@[simp]
theorem lineDegree_hermitianMetric (D : ArakelovDivisor K) :
    D.hermitianMetric.lineDegree = degree K D := by
  have := Module.Invertible.nontrivial (𝓞 K)
    (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K)
  obtain ⟨s, hs⟩ := exists_ne (0 : (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K))
  rw [D.hermitianMetric.lineDegree_eq_sectionDegree_of_invertible hs,
    D.sectionDegree_hermitianMetric hs]

end TauCeti.ArakelovDivisor
