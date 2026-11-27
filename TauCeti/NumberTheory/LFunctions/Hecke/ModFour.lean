/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.ZModChar
public import TauCeti.NumberTheory.LFunctions.Hecke.Nonvanishing
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# The quadratic ray class character modulo `(4)·∞` over `ℚ`

Transporting Mathlib's quadratic Dirichlet character `ZMod.χ₄` across `ratDirichletEquiv` produces
`TauCeti.LFunctions.ratModFourChar`, the unique nontrivial ray class character of the modulus
`ratModulus 4 four_ne_zero` over `ℚ`. It serves as an explicit witness for two design constraints of
`TauCeti.LFunctions.UnitaryCancelling` and `TauCeti.LFunctions.IsUnitaryCharacterFamily`:

* `ratModFourChar` satisfies `UnitaryCancelling` through the square-twist branch even though its
  square is trivial on its good ideals and therefore does **not** have partial-sum cancellation;
* the identity member `(1 : RayClassCharacter (ratModulus 4 four_ne_zero)).toUnitaryIdealWeight` of
  the mod-`4` family vanishes at the bad ideal `(2 : 𝓞 ℚ)`, showing that the family identity law
  holds only on good ideals.

## Main definitions and results

* `TauCeti.LFunctions.ratModFourChar`: the nontrivial ray class character modulo `(4)·∞` over `ℚ`
  associated with `ZMod.χ₄`.
* `TauCeti.LFunctions.unitaryCancelling_toUnitaryIdealWeight_ratModFourChar`,
  `TauCeti.LFunctions.isTrivialOnGood_toUnitaryIdealWeight_ratModFourChar_sq`, and
  `TauCeti.LFunctions.not_hasCancellation_toUnitaryIdealWeight_ratModFourChar_sq`: quadratic
  instantiation and non-cancellation of the square.
* `TauCeti.LFunctions.toUnitaryIdealWeight_one_ratModulus_four_apply_span_two`: the trivial member
  of the mod-`4` family vanishes at `Ideal.span {(2 : 𝓞 ℚ)}`.
-/

public section
noncomputable section

open IsDedekindDomain NumberField
open scoped NumberField

namespace TauCeti.LFunctions

open GlobalNumberFields

/-- **The nontrivial ray class character modulo `(4)·∞` over `ℚ`**, corresponding to Mathlib's
quadratic character `ZMod.χ₄` under `ratDirichletEquiv`. -/
def ratModFourChar : RayClassCharacter (ratModulus 4 four_ne_zero) :=
  (ratDirichletEquiv 4 four_ne_zero).symm (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ))

/-- Defining equation of `TauCeti.LFunctions.ratModFourChar`. -/
theorem ratModFourChar_def :
    ratModFourChar =
      (ratDirichletEquiv 4 four_ne_zero).symm (ZMod.χ₄.ringHomComp (Int.castRingHom ℂ)) := (rfl)

/-- `ratDirichletEquiv` sends `ratModFourChar` back to the complex-valued `ZMod.χ₄`. -/
@[simp]
theorem ratDirichletEquiv_ratModFourChar :
    ratDirichletEquiv 4 four_ne_zero ratModFourChar = ZMod.χ₄.ringHomComp (Int.castRingHom ℂ) :=
  MulEquiv.apply_symm_apply _ _

/-- `ratModFourChar` is nontrivial (`χ₄(-1) = -1 ≠ 1`). -/
theorem ratModFourChar_ne_one : ratModFourChar ≠ 1 := by
  intro h
  have h1 := congrArg (fun η ↦ ratDirichletEquiv 4 four_ne_zero η (-1 : ZMod 4)) h
  rw [ratDirichletEquiv_ratModFourChar, map_one, MulChar.ringHomComp_apply] at h1
  have hχ : ZMod.χ₄ ((-1 : ℤ) : ZMod 4) = -1 := ZMod.χ₄_int_three_mod_four (by decide)
  rw [Int.cast_neg, Int.cast_one] at hχ
  have hone : (1 : DirichletCharacter ℂ 4) (-1 : ZMod 4) = 1 :=
    MulChar.one_apply (Units.isUnit (-1 : (ZMod 4)ˣ))
  rw [hχ, hone] at h1
  norm_num at h1

/-- `ratModFourChar` has order two (`ratModFourChar ^ 2 = 1`). -/
@[simp]
theorem ratModFourChar_sq : ratModFourChar ^ 2 = 1 := by
  apply (ratDirichletEquiv 4 four_ne_zero).injective
  rw [map_pow, map_one, ratDirichletEquiv_ratModFourChar]
  exact (ZMod.isQuadratic_χ₄.comp (Int.castRingHom ℂ)).sq_eq_one

/-- The unitary weight of `ratModFourChar` satisfies `UnitaryCancelling`. -/
theorem unitaryCancelling_toUnitaryIdealWeight_ratModFourChar :
    UnitaryCancelling ratModFourChar.toUnitaryIdealWeight :=
  RayClassCharacter.unitaryCancelling_toUnitaryIdealWeight ratModFourChar_ne_one

/-- The pointwise square of `ratModFourChar.toUnitaryIdealWeight` is trivial on its good ideals. -/
theorem isTrivialOnGood_toUnitaryIdealWeight_ratModFourChar_sq :
    (ratModFourChar.toUnitaryIdealWeight ^ 2).val.IsTrivialOnGood := by
  have hsq : ratModFourChar.toUnitaryIdealWeight ^ 2 =
      (1 : RayClassCharacter (ratModulus 4 four_ne_zero)).toUnitaryIdealWeight := by
    rw [← (RayClassCharacter.isUnitaryCharacterFamily_toUnitaryIdealWeight _).map_sq,
      ratModFourChar_sq]
  rw [hsq]
  exact (RayClassCharacter.isUnitaryCharacterFamily_toUnitaryIdealWeight _).isTrivialOnGood_one

/-- The pointwise square of `ratModFourChar.toUnitaryIdealWeight` does **not** have cancellation,
witnessing that `UnitaryCancelling` must permit the quadratic norm-twist branch rather than
requiring `χ ^ 2` to cancel. -/
theorem not_hasCancellation_toUnitaryIdealWeight_ratModFourChar_sq :
    ¬ HasCancellation (ratModFourChar.toUnitaryIdealWeight ^ 2) :=
  not_hasCancellation_of_isTrivialOnGood isTrivialOnGood_toUnitaryIdealWeight_ratModFourChar_sq

/-- The continued L-function of `ratModFourChar` does not vanish on `Re s ≥ 1` away from `s = 1`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ratModFourChar_ne_zero {s : ℂ}
    (hs : 1 ≤ s.re) (hs1 : s ≠ 1) :
    continuedLFunctionOfWeight ratModFourChar.toUnitaryIdealWeight s ≠ 0 :=
  RayClassCharacter.continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero ratModFourChar_ne_one hs
    (Or.inr hs1)

/-- The trivial ray class character modulo `(4)·∞` over `ℚ` vanishes at `Ideal.span {(2 : 𝓞 ℚ)}`,
witnessing that the identity member of a unitary character family satisfies `w 1 I = 1` only on its
good ideals. -/
theorem toUnitaryIdealWeight_one_ratModulus_four_apply_span_two :
    (1 : RayClassCharacter (ratModulus 4 four_ne_zero)).toUnitaryIdealWeight.val
      (Ideal.span {(2 : 𝓞 ℚ)}) = 0 := by
  obtain ⟨𝔭, h𝔭⟩ := Rat.HeightOneSpectrum.exists_absNorm_eq Nat.prime_two
  have hspan : Ideal.span {(2 : 𝓞 ℚ)} = 𝔭.asIdeal := by
    simpa [h𝔭] using Rat.RingOfIntegers.ideal_span_absNorm_eq_self 𝔭.asIdeal
  have hmem : 𝔭 ∈ (ratModulus 4 four_ne_zero).support :=
    mem_ratModulus_support_iff.mpr
      ((Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mpr (by rw [h𝔭]; decide))
  rw [RayClassCharacter.val_toUnitaryIdealWeight, hspan,
    ← MultiplicativeIdealWeight.mem_badPrimes,
    RayClassCharacter.badPrimes_toMultiplicativeIdealWeight]
  exact hmem

end TauCeti.LFunctions
