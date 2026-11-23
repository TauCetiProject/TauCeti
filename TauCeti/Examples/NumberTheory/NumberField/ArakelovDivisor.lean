/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.NumberTheory.NumberField.ArakelovDivisor.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Tests of Arakelov divisors over `ℚ`

The principal divisor `(2) = [2] - log 2 · [∞]` of `ℚ` has archimedean coefficient `-log 2` and
finite part of norm `2`, so its degree `log 2 - log 2` vanishes. Since `ℤ` has trivial class group
and `ℚ` has a single infinite place, the degree identifies the compactified Picard group of `ℚ`
with `ℝ`; this is Gillet–Soulé's `deg : \widehat{CH}¹(Spec ℤ) ≃ ℝ`.
-/

open NumberField TauCeti

/-- The principal divisor of `2` has coefficient `-log 2` at the infinite place of `ℚ`. -/
example (v : InfinitePlace ℚ) :
    (ArakelovDivisor.principal ℚ (Additive.ofMul (Units.mk0 2 two_ne_zero))).infinitePart v =
      -Real.log 2 := by
  have hv : v.IsReal := Subsingleton.elim v Rat.infinitePlace ▸ Rat.isReal_infinitePlace
  simp [Rat.infinitePlace_apply, InfinitePlace.mult, hv]

/-- The degree is a bijection from the compactified Picard group of `ℚ` onto `ℝ`. -/
example : Function.Bijective (ArakelovPicardGroup.degree ℚ) := by
  have : Subsingleton (ClassGroup (𝓞 ℚ)) :=
    isPrincipalIdealRing_iff_subsingleton_classGroup.mp inferInstance
  refine ⟨(injective_iff_map_eq_zero _).mpr fun P hP ↦ ?_, fun c ↦
    ⟨ArakelovPicardGroup.ofInfinitePart ℚ fun _ ↦ c, by simp⟩⟩
  obtain ⟨l, rfl⟩ :=
    (ArakelovPicardGroup.exact_ofInfinitePart_toClassGroup P).mp (Subsingleton.elim _ _)
  have hl : l = 0 := by
    funext v
    simpa [Subsingleton.elim v default] using hP
  rw [hl, map_zero]
