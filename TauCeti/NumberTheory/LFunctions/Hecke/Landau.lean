/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Meromorphic.Order
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation
public import TauCeti.NumberTheory.LFunctions.Hecke.Basic
public import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Cancellation.Nonvanishing
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
import TauCeti.NumberTheory.NumberField.Global.RayClass.Character.Cancellation
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat

/-!
# Landau nonvanishing for ray class characters

For a quadratic ray class character `χ` of a modulus `𝔪` of a number field `K` (`χ ^ 2 = 1`), the
squared ideal weight `χ.toMultiplicativeIdealWeight ^ 2` is trivial on its good ideals
(`RayClassCharacter.isTrivialOnGood_sq_iff_sq_eq_one`). Together with the abstract Landau theorem
for ideal weights (`TauCeti.NumberTheory.ArithmeticDirichletSeries.Landau`), this provides the
ray-class bridge for any continuation of `ζ_K` and `L(χ, ·)` down to `Re s = 1 / 2`.

This file records the unconditional applications currently available without Layer 6 general-modulus
whole-plane continuation of `heckeLFunctionC`:

* For every number field `K` of degree `1` over `ℚ` and every nontrivial ray class character
  `χ ≠ 1` of any modulus `𝔪`, the cancellation-continued L-function
  `TauCeti.continuedLFunctionOfWeight χ.toUnitaryIdealWeight` is holomorphic on `Re s > 0` and does
  not vanish anywhere on `Re s ≥ 1`
  (`continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one`),
  closing the quadratic `s = 1` exception left open by `3-4-1` via Landau's theorem and handling
  `χ ^ 2 ≠ 1` via `TauCeti.continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq`.
* Over `ℚ`, `TauCeti.GlobalNumberFields.ratDirichletEquiv` identifies `heckeLFunctionC χ` for
  `χ ≠ 1` with Mathlib's `DirichletCharacter.LFunction`, yielding unconditional whole-plane
  holomorphicity, Dirichlet series agreement on `Re s > 1`, and nonvanishing (meromorphic order `0`)
  on `Re s ≥ 1`.

## Main results

* `TauCeti.GlobalNumberFields.RayClassCharacter.isTrivialOnGood_sq_iff_sq_eq_one`: a ray class
  character has squared ideal weight trivial on good ideals iff `χ ^ 2 = 1`.
* `continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one`
  (in `TauCeti.LFunctions`): unconditional nonvanishing on `Re s ≥ 1` of
  `continuedLFunctionOfWeight` for `χ.toUnitaryIdealWeight` when `[K : ℚ] = 1` and `χ ≠ 1`.
* `TauCeti.LFunctions.heckeLFunctionC_eq_LFunction_rat`,
  `TauCeti.LFunctions.differentiable_heckeLFunctionC_rat`,
  `TauCeti.LFunctions.heckeLFunctionC_eq_LSeries_rat`,
  `TauCeti.LFunctions.heckeLFunctionC_ne_zero_of_one_le_re_rat`, and
  `TauCeti.LFunctions.meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat`: unconditional
  identification, entire continuation, series agreement, and `Re s ≥ 1` nonvanishing for
  `heckeLFunctionC χ` over `ℚ` when `χ ≠ 1`.

## References

* E. Landau, *Über die zu einem algebraischen Zahlkörper gehörige Zetafunction und die Ausdehnung
  der Tschebyschefschen Primzahlentheorie auf das Problem der Vertheilung der Primideale*,
  J. Reine Angew. Math. 125 (1903), 64–188.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §6 and §8.
-/

public section

open Filter IsDedekindDomain NumberField Set
open scoped nonZeroDivisors NumberField Topology

namespace TauCeti.GlobalNumberFields.RayClassCharacter

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- A ray class character has squared ideal weight trivial on its good ideals if and only if
`χ ^ 2 = 1` in the character group. -/
theorem isTrivialOnGood_sq_iff_sq_eq_one (χ : RayClassCharacter 𝔪) :
    (χ.toMultiplicativeIdealWeight ^ 2).IsTrivialOnGood ↔ χ ^ 2 = 1 := by
  have hsq : χ.toMultiplicativeIdealWeight ^ 2 = (χ ^ 2).toMultiplicativeIdealWeight := by
    rw [sq, sq, toMultiplicativeIdealWeight_mul]
  constructor
  · intro h
    apply toMultiplicativeIdealWeight_injective
    ext I
    rw [← hsq]
    by_cases hI : Ideal.IsPrimeTo I 𝔪.support
    · have hval : χ.toMultiplicativeIdealWeight I ≠ 0 := by
        rw [toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hI]
        exact Units.ne_zero _
      have hgood : (χ.toMultiplicativeIdealWeight ^ 2).IsGood I := by
        rw [← MultiplicativeIdealWeight.apply_ne_zero_iff_isGood, sq,
          MultiplicativeIdealWeight.mul_apply]
        exact mul_ne_zero hval hval
      rw [h.apply_eq_one hgood, toMultiplicativeIdealWeight_one,
        MultiplicativeIdealWeight.ofBadPrimes_apply]
      simp [hI]
    · rw [sq, MultiplicativeIdealWeight.mul_apply,
        toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hI, mul_zero,
        toMultiplicativeIdealWeight_apply_of_not_isPrimeTo 1 hI]
  · intro hχ
    rw [hsq, hχ, toMultiplicativeIdealWeight_one]
    exact MultiplicativeIdealWeight.isTrivialOnGood_ofBadPrimes 𝔪.support.finite_toSet

end TauCeti.GlobalNumberFields.RayClassCharacter

namespace TauCeti.LFunctions

open GlobalNumberFields

section FinrankEqOne

variable {K : Type*} [Field K] [NumberField K] {𝔪 : Modulus K}

/-- **Unconditional nonvanishing on `Re s ≥ 1` of the cancellation-continued ray class L-function
when `[K : ℚ] = 1`.** For any nontrivial ray class character `χ ≠ 1` of any modulus `𝔪`,
`continuedLFunctionOfWeight χ.toUnitaryIdealWeight` does not vanish on `Re s ≥ 1`: when
`χ ^ 2 = 1` this follows from Landau's theorem (`[K : ℚ] = 1`), and when `χ ^ 2 ≠ 1` it follows
from `3-4-1` and cancellation for `χ ^ 2`. -/
theorem continuedLFunctionOfWeight_toUnitaryIdealWeight_ne_zero_of_one_le_re_of_finrank_eq_one
    (hK : Module.finrank ℚ K = 1) {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) {s : ℂ}
    (hs : 1 ≤ s.re) :
    continuedLFunctionOfWeight χ.toUnitaryIdealWeight s ≠ 0 := by
  by_cases hsq : χ ^ 2 = 1
  · refine continuedLFunctionOfWeight_ne_zero_of_isTrivialOnGood_sq_of_finrank_eq_one hK
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ) ?_ hs
    rw [UnitaryIdealWeight.val_pow, RayClassCharacter.val_toUnitaryIdealWeight]
    exact χ.isTrivialOnGood_sq_iff_sq_eq_one.mpr hsq
  · have hpow : χ.toUnitaryIdealWeight ^ 2 = (χ ^ 2).toUnitaryIdealWeight := by
      ext I
      simp [sq, UnitaryIdealWeight.val_mul]
    exact continuedLFunctionOfWeight_ne_zero_of_hasCancellation_sq
      (RayClassCharacter.hasCancellation_toUnitaryIdealWeight hχ)
      (hpow ▸ RayClassCharacter.hasCancellation_toUnitaryIdealWeight hsq) hs

end FinrankEqOne

section Rat

private theorem normCoeff_rayClassCharacter_rat_eq {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪)
    {k : ℕ} (hk : k ≠ 0) :
    normCoeff ℚ χ.toUnitaryIdealWeight.toIdealArithmeticFunction k =
      ((ratDirichletEquiv (Ideal.absNorm 𝔪.finitePart)
        (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
        (χ.induced (dvd_ratModulus_absNorm 𝔪)) : DirichletCharacter ℂ _) (k : ZMod _)) := by
  set n := Ideal.absNorm 𝔪.finitePart
  have hn : n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot
  have : NeZero n := ⟨hn⟩
  have h𝔪 : 𝔪 ∣ ratModulus n hn := dvd_ratModulus_absNorm 𝔪
  set ψ := ratDirichletEquiv n hn (χ.induced h𝔪)
  let I : Ideal (𝓞 ℚ) := Ideal.span {(k : 𝓞 ℚ)}
  have hI_ne : I ≠ 0 := mt (fun h ↦ Ideal.span_singleton_eq_bot.mp h) (by exact_mod_cast hk)
  let I₀ : (Ideal (𝓞 ℚ))⁰ := ⟨I, mem_nonZeroDivisors_of_ne_zero hI_ne⟩
  have hnorm : Ideal.absNorm I = k := by
    simp only [I, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank,
      Module.finrank_self, pow_one]
  rw [normCoeff_eq_sum_normFiber, ← hnorm, normFiber_rat_absNorm I₀, Finset.sum_singleton,
    UnitaryIdealWeight.toIdealArithmeticFunction_apply, RayClassCharacter.val_toUnitaryIdealWeight,
    hnorm]
  have hfin : 𝔪.finitePart = Ideal.span {(n : 𝓞 ℚ)} :=
    (Rat.RingOfIntegers.ideal_span_absNorm_eq_self 𝔪.finitePart).symm
  have hprimeTo_iff : I.IsPrimeTo 𝔪.support ↔ 𝔪.IsCoprimeTo I :=
    Ideal.isPrimeTo_iff.trans Modulus.isCoprimeTo_iff.symm
  have hcop : I.IsPrimeTo 𝔪.support ↔ IsUnit (k : ZMod n) := by
    rw [hprimeTo_iff, Modulus.isCoprimeTo_iff_sup_eq_top, hfin, ← Ideal.isCoprime_iff_sup_eq,
      Ideal.isCoprime_span_singleton_iff]
    constructor
    · intro ⟨_, h⟩
      rw [ZMod.isUnit_iff_coprime]
      simpa using h.map Rat.ringOfIntegersEquiv.toRingHom
    · intro h
      refine ⟨hI_ne, ?_⟩
      rw [ZMod.isUnit_iff_coprime] at h
      have hInt : IsCoprime (k : ℤ) (n : ℤ) := Int.isCoprime_iff_nat_coprime.mpr (by simpa using h)
      simpa using hInt.map Rat.ringOfIntegersEquiv.symm.toRingHom
  by_cases hI : I.IsPrimeTo 𝔪.support
  · have hI' : (I : Ideal (𝓞 ℚ)) ∈ integralIdealsPrimeTo (ratModulus n hn) := by
      rw [Modulus.mem_integralIdealsPrimeTo, Modulus.isCoprimeTo_iff_sup_eq_top,
        ratModulus_finitePart, ← hfin, ← Modulus.isCoprimeTo_iff_sup_eq_top]
      exact hprimeTo_iff.mp hI
    have hval := ratDirichletEquiv_absNorm (χ.induced h𝔪) ⟨I, hI'⟩
    simp only [hnorm] at hval
    have hI₀ : (I₀ : Ideal (𝓞 ℚ)) = I := rfl
    rw [hI₀, RayClassCharacter.toMultiplicativeIdealWeight_apply_of_isPrimeTo χ hI]
    have hmem : (I : Ideal (𝓞 ℚ)) ∈ integralIdealsPrimeTo 𝔪 :=
      Modulus.mem_integralIdealsPrimeTo.mpr (hprimeTo_iff.mp hI)
    change (χ.onIdeals ⟨I, hmem⟩ : ℂ) = (ψ (k : ZMod n) : ℂ)
    have hincl : (⟨I, hmem⟩ : integralIdealsPrimeTo 𝔪) =
        integralIdealsPrimeToInclusion h𝔪 ⟨I, hI'⟩ :=
      Subtype.ext (coe_integralIdealsPrimeToInclusion h𝔪 ⟨I, hI'⟩).symm
    rw [hincl, ← RayClassCharacter.onIdeals_induced h𝔪 χ ⟨I, hI'⟩, ← hval]
  · have hnu : ¬ IsUnit (k : ZMod n) := hcop.not.mp hI
    have hI₀ : (I₀ : Ideal (𝓞 ℚ)) = I := rfl
    rw [hI₀, RayClassCharacter.toMultiplicativeIdealWeight_apply_of_not_isPrimeTo χ hI,
      MulChar.map_nonunit _ hnu]

private theorem lSeries_rayClassCharacter_rat_eq {𝔪 : Modulus ℚ} (χ : RayClassCharacter 𝔪) :
    LSeries (normCoeff ℚ χ.toUnitaryIdealWeight.toIdealArithmeticFunction) =
      LSeries ((ratDirichletEquiv (Ideal.absNorm 𝔪.finitePart)
        (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
        (χ.induced (dvd_ratModulus_absNorm 𝔪)) : DirichletCharacter ℂ _) ·) := by
  funext s
  exact LSeries_congr (fun {k} hk ↦ normCoeff_rayClassCharacter_rat_eq χ hk) s

/-- **Over `ℚ`, the presented Hecke L-function of a nontrivial ray class character is the
corresponding Dirichlet L-function.** -/
theorem heckeLFunctionC_eq_LFunction_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) :
    heckeLFunctionC χ =
      @DirichletCharacter.LFunction (Ideal.absNorm 𝔪.finitePart)
        ⟨Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot⟩
        (ratDirichletEquiv (Ideal.absNorm 𝔪.finitePart)
          (Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot)
          (χ.induced (dvd_ratModulus_absNorm 𝔪))) := by
  set n := Ideal.absNorm 𝔪.finitePart
  have hn : n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot
  have : NeZero n := ⟨hn⟩
  have h𝔪 : 𝔪 ∣ ratModulus n hn := dvd_ratModulus_absNorm 𝔪
  set ψ := ratDirichletEquiv n hn (χ.induced h𝔪)
  have hψ : ψ ≠ 1 := by
    intro h
    apply hχ
    exact RayClassCharacter.induced_injective h𝔪
      ((ratDirichletEquiv n hn).injective (by simpa [ψ] using h))
  rw [heckeLFunctionC_def, lSeries_rayClassCharacter_rat_eq χ]
  exact meromorphicContinuation_eq
    (Complex.analyticOnNhd_univ_iff_differentiable.mpr
      (DirichletCharacter.differentiable_LFunction hψ)).meromorphicNFOn
    fun _ hs ↦ DirichletCharacter.LFunction_eq_LSeries ψ hs

/-- **Entire continuation over `ℚ`.** For any modulus `𝔪` of `ℚ` and any nontrivial ray class
character `χ ≠ 1`, `heckeLFunctionC χ` is entire. -/
theorem differentiable_heckeLFunctionC_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) : Differentiable ℂ (heckeLFunctionC χ) := by
  set n := Ideal.absNorm 𝔪.finitePart
  have hn : n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot
  have : NeZero n := ⟨hn⟩
  have h𝔪 : 𝔪 ∣ ratModulus n hn := dvd_ratModulus_absNorm 𝔪
  have hψ : ratDirichletEquiv n hn (χ.induced h𝔪) ≠ 1 := fun h ↦
    hχ (RayClassCharacter.induced_injective h𝔪
      ((ratDirichletEquiv n hn).injective (by simpa using h)))
  rw [heckeLFunctionC_eq_LFunction_rat hχ]
  exact DirichletCharacter.differentiable_LFunction hψ

/-- **Dirichlet series agreement over `ℚ`.** For any modulus `𝔪` of `ℚ` and any nontrivial ray
class character `χ ≠ 1`, `heckeLFunctionC χ` agrees with its defining `L`-series on `Re s > 1`. -/
theorem heckeLFunctionC_eq_LSeries_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1)
    {s : ℂ} (hs : 1 < s.re) :
    heckeLFunctionC χ s =
      LSeries (normCoeff ℚ χ.toUnitaryIdealWeight.toIdealArithmeticFunction) s := by
  have hn : Ideal.absNorm 𝔪.finitePart ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot
  have : NeZero (Ideal.absNorm 𝔪.finitePart) := ⟨hn⟩
  rw [heckeLFunctionC_eq_LFunction_rat hχ, lSeries_rayClassCharacter_rat_eq χ,
    DirichletCharacter.LFunction_eq_LSeries _ hs]

/-- **Unconditional nonvanishing on `Re s ≥ 1` over `ℚ`.** For any modulus `𝔪` of `ℚ` and any
nontrivial ray class character `χ ≠ 1`, `heckeLFunctionC χ s ≠ 0` everywhere on `Re s ≥ 1`. -/
theorem heckeLFunctionC_ne_zero_of_one_le_re_rat {𝔪 : Modulus ℚ} {χ : RayClassCharacter 𝔪}
    (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) : heckeLFunctionC χ s ≠ 0 := by
  set n := Ideal.absNorm 𝔪.finitePart
  have hn : n ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr 𝔪.finitePart_ne_bot
  have : NeZero n := ⟨hn⟩
  have h𝔪 : 𝔪 ∣ ratModulus n hn := dvd_ratModulus_absNorm 𝔪
  have hψ : ratDirichletEquiv n hn (χ.induced h𝔪) ≠ 1 := fun h ↦
    hχ (RayClassCharacter.induced_injective h𝔪
      ((ratDirichletEquiv n hn).injective (by simpa using h)))
  rw [heckeLFunctionC_eq_LFunction_rat hχ]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (.inl hψ) hs

/-- **Meromorphic order zero on `Re s ≥ 1` over `ℚ`.** -/
theorem meromorphicOrderAt_heckeLFunctionC_eq_zero_of_one_le_re_rat {𝔪 : Modulus ℚ}
    {χ : RayClassCharacter 𝔪} (hχ : χ ≠ 1) {s : ℂ} (hs : 1 ≤ s.re) :
    meromorphicOrderAt (heckeLFunctionC χ) s = 0 :=
  ((differentiable_heckeLFunctionC_rat hχ).analyticAt s).meromorphicNFAt
    |>.meromorphicOrderAt_eq_zero_iff.mpr (heckeLFunctionC_ne_zero_of_one_le_re_rat hχ hs)

end Rat

end TauCeti.LFunctions
