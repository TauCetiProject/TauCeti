/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ArakelovDivisor.HermitianLine
public import TauCeti.NumberTheory.NumberField.HermitianBundle.Degree.Line

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
  obtain ⟨s, hs⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    ((FractionalIdeal.coeToSubmodule_ne_bot).mpr (Units.ne_zero (D.finitePart⁻¹)))
  set s' : (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) :
      Submodule (𝓞 K) K) := ⟨s, hs.1⟩
  have hs' : s' ≠ 0 := fun h0 ↦ hs.2 (congrArg Subtype.val h0)
  -- The carrier is the submodule underlying a unit of `Submodule (𝓞 K) K`, hence invertible.
  have : Module.Invertible (𝓞 K) (((D.finitePart⁻¹ : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
      FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K) :=
    inferInstanceAs (Module.Invertible (𝓞 K)
      (Units.map (FractionalIdeal.coeSubmoduleHom (𝓞 K)⁰ K).toMonoidHom D.finitePart⁻¹ :
        Submodule (𝓞 K) K))
  rw [D.hermitianMetric.lineDegree_eq_sectionDegree_of_invertible hs',
    D.sectionDegree_hermitianMetric hs']

end TauCeti.ArakelovDivisor
