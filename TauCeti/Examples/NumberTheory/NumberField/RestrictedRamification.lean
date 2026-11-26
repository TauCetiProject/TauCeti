/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.RestrictedRamification.Basic
import Mathlib.NumberTheory.NumberField.ExistsRamified

/-!
# Checks for the maximal extension unramified outside `S`

* For `K = ℚ` and `S = ∅` (no finite places allowed to ramify), `K_S = ℚ`: every number field of
  degree `> 1` has `|disc| > 2`, so some prime ramifies in it (Minkowski, through Mathlib's
  `NumberField.exists_not_isUnramifiedAt_int`). A definition of `K_S` that ignored ramification
  would give all of `Ω`.
* For `S` the set of all finite places, `K_S = Ω` for `Ω` algebraic over `K`
  (`TauCeti.RestrictedRamification.maxUnramifiedOutside_univ`), so `G_{K,S} ≃ Gal(Ω / K)`.
-/

public section

open IntermediateField IsDedekindDomain

open scoped NumberField

namespace TauCeti.Examples.RestrictedRamification

open TauCeti.RestrictedRamification

variable (Ω : Type*) [Field Ω] [Algebra ℚ Ω]

/-- **`ℚ` has no nontrivial extension unramified at every finite prime**: `ℚ_∅ = ℚ`. -/
theorem maxUnramifiedOutside_rat_empty : maxUnramifiedOutside ℚ Ω ∅ = ⊥ := by
  refine eq_bot_iff.2 (maxUnramifiedOutside_le fun L hfin hL ↦ ?_)
  -- the `ℚ`-algebra structure of `L` as an intermediate field, as in `maxUnramifiedOutside`
  let : Algebra ℚ L := L.algebra'
  have : NumberField L := NumberField.of_module_finite ℚ L
  by_contra hne
  obtain ⟨P, hP, hPr⟩ := NumberField.exists_not_isUnramifiedAt_int (K := L) (𝒪 := 𝓞 L)
    fun h ↦ hne <| (IntermediateField.finrank_eq_one_iff.1 <| by
      convert h
      exact Subsingleton.elim _ _).le
  -- `P` lies over a height-one prime `v` of `𝓞 ℚ`
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hP (NumberField.RingOfIntegers.not_isField L)
  let v : HeightOneSpectrum (𝓞 ℚ) :=
    ⟨P.under (𝓞 ℚ), Ideal.IsPrime.under _ _, mt Ideal.eq_bot_of_under_eq_bot hP0⟩
  have hv : Algebra.IsUnramifiedAt (𝓞 ℚ) P :=
    hL v (Set.notMem_empty v) P hP.isPrime ⟨rfl⟩
  -- `ℤ → 𝓞 ℚ` is surjective, so unramified over `𝓞 ℚ` is unramified over `ℤ`
  have hsurj : Function.Surjective (algebraMap ℤ (𝓞 ℚ)) := by
    rw [show algebraMap ℤ (𝓞 ℚ) = (Rat.ringOfIntegersEquiv.symm : ℤ →+* 𝓞 ℚ) from
      RingHom.ext_int _ _]
    exact Rat.ringOfIntegersEquiv.symm.surjective
  have : Algebra.FormallyUnramified ℤ (𝓞 ℚ) :=
    .of_surjective (Algebra.ofId ℤ (𝓞 ℚ)) hsurj
  have : Algebra.FormallyUnramified (𝓞 ℚ) (Localization.AtPrime P) := hv
  exact hPr (Algebra.FormallyUnramified.comp ℤ (𝓞 ℚ) (Localization.AtPrime P))

/-- For `S` the set of all finite places of `ℚ`, `K_S` is all of an algebraic closure. -/
example : maxUnramifiedOutside ℚ (AlgebraicClosure ℚ) Set.univ = ⊤ :=
  maxUnramifiedOutside_univ

end TauCeti.Examples.RestrictedRamification
