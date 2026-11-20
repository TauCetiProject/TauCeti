/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Ostrowski
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.NumberTheory.NumberField.ProductFormula
import TauCeti.Analysis.AbsoluteValue.Equivalence
import TauCeti.RingTheory.DedekindDomain.AdicValuation.Transport

/-!
# Finite places of the rational numbers

Every finite place of `ℚ` is exactly a `p`-adic absolute value, and every prime gives such a
place. The equalities use Mathlib's `Rat.HeightOneSpectrum.primesEquiv` to identify the prime
of a place and preserve normalization, not just equivalence of absolute values. This is
needed to translate products over finite places into the products of `padicNorm` occurring in
Ridout's theorem.

Ostrowski's theorem supplies equivalence with a `p`-adic absolute value. The known value at
the rational prime generating the place's maximal ideal then fixes the prime and exponent.
The inverse dictionary uses `primesEquiv.symm` to supply the corresponding finite place.
The local-value formulas `Rat.HeightOneSpectrum.finitePlace_mk_natGenerator` and
`Rat.HeightOneSpectrum.finitePlace_mk_inv_natGenerator` evaluate a place at its generating prime
and its inverse.

This file also identifies the height-one primes of `ℤ` with `NumberField.FinitePlace ℚ`
(`NumberField.HeightOneSpectrum.finitePlaceRatEquiv`), shows that
`NumberField.HeightOneSpectrum.adicAbv ℚ v` agrees with the corresponding finite place
(`NumberField.HeightOneSpectrum.adicAbv_eq_finitePlaceRatEquiv`), and transfers finite
multiplicative support (`NumberField.HeightOneSpectrum.hasFiniteMulSupport_adicAbv_rat`) and the
product formula `|q| · ∏ᶠ v : HeightOneSpectrum ℤ, |q|_v = 1`
(`NumberField.HeightOneSpectrum.abs_mul_finprod_adicAbv_rat`) to `HeightOneSpectrum ℤ`.

## References

* E. Bombieri and W. Gubler, *Heights in Diophantine Geometry*, §6.2.
* The original height-based normalization argument followed Ralf Stephan's
  `DiophantineApproximation/RationalPlaces.lean` in `rwst/Subspace-Theorems`, revision
  `09835cb23557ae5ae0cf55a9c4ab9055f5d60338` (Apache 2.0). Here the existing local-value
  formulas replace that height computation.
-/

public section

open IsDedekindDomain NumberField Rat.HeightOneSpectrum

namespace Rat.HeightOneSpectrum

variable (v : HeightOneSpectrum (𝓞 ℚ))

/-- The absolute value of the rational prime of `v` at the finite place `v` is its inverse. -/
theorem finitePlace_mk_natGenerator :
    FinitePlace.mk v (natGenerator v) = ((natGenerator v : ℕ) : ℝ)⁻¹ := by
  rw [FinitePlace.mk_apply, FinitePlace.norm_embedding', valuation_natGenerator,
    WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero, WithZero.log_exp]
  simp

/-- The absolute value of the inverse of the rational prime of `v` at the finite place `v` is
the prime. -/
theorem finitePlace_mk_inv_natGenerator :
    FinitePlace.mk v ((natGenerator v : ℚ)⁻¹) = natGenerator v := by
  rw [map_inv₀, finitePlace_mk_natGenerator, inv_inv]

end Rat.HeightOneSpectrum

namespace NumberField.FinitePlace

/-- A finite place of `ℚ` is the usual `p`-adic absolute value at its canonical prime under
`Rat.HeightOneSpectrum.primesEquiv`, not merely a positive power of that absolute value. -/
theorem val_eq_padic (v : FinitePlace ℚ) :
    letI : Fact (primesEquiv v.maximalIdeal : ℕ).Prime := ⟨(primesEquiv v.maximalIdeal).property⟩
    v.val = Rat.AbsoluteValue.padic (primesEquiv v.maximalIdeal) := by
  let p : Nat.Primes := primesEquiv v.maximalIdeal
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  -- Mathlib defines the value of `primesEquiv` to be `natGenerator`.
  have hpval : (p : ℕ) = natGenerator v.maximalIdeal := rfl
  have hvp : v.val (p : ℚ) = (p : ℝ)⁻¹ := by
    rw [← coe_apply, ← v.mk_maximalIdeal, hpval]
    exact finitePlace_mk_natGenerator v.maximalIdeal
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hsmall : v.val (p : ℚ) < 1 := by
    rw [hvp]
    exact inv_lt_one_of_one_lt₀ hp1
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hnt : v.val.IsNontrivial := ⟨(p : ℚ), hp0, hsmall.ne⟩
  have hbdd (n : ℕ) : v.val (n : ℚ) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one (f := v.val) (by simp) v.val.map_one v.add_le
  obtain ⟨q, ⟨hq, hv⟩, -⟩ := Rat.AbsoluteValue.equiv_padic_of_bounded hnt hbdd
  have hqp : q = (p : ℕ) := by
    have hlt := hv.lt_one_iff.mp hsmall
    rw [Rat.AbsoluteValue.padic_eq_padicNorm] at hlt
    have hdiv := (padicNorm.nat_lt_one_iff (p : ℕ)).mp (by exact_mod_cast hlt)
    exact (Nat.prime_dvd_prime_iff_eq hq.out p.property).mp hdiv
  subst q
  apply hv.eq_of_apply_eq hp0 hsmall.ne
  rw [hvp, Rat.AbsoluteValue.padic_eq_padicNorm, padicNorm.padicNorm_p_of_prime]
  simp only [Rat.cast_inv, Rat.cast_natCast]

/-- A finite place of `ℚ`, evaluated at a rational number, is `padicNorm` at its canonical
prime under `Rat.HeightOneSpectrum.primesEquiv`. -/
theorem apply_eq_padicNorm (v : FinitePlace ℚ) (x : ℚ) :
    v x = (padicNorm (primesEquiv v.maximalIdeal) x : ℝ) := by
  let : Fact (primesEquiv v.maximalIdeal : ℕ).Prime :=
    ⟨(primesEquiv v.maximalIdeal).property⟩
  rw [coe_apply, v.val_eq_padic, Rat.AbsoluteValue.padic_eq_padicNorm]

end NumberField.FinitePlace

namespace Nat.Primes

/-- The finite place corresponding to a prime under `Rat.HeightOneSpectrum.primesEquiv.symm`
has exactly the usual `p`-adic absolute value. -/
theorem finitePlace_mk_val_eq_padic (p : Nat.Primes) :
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).val = Rat.AbsoluteValue.padic p := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).val_eq_padic

/-- The finite place constructed from a prime evaluates to the usual `padicNorm`. -/
theorem finitePlace_mk_apply (p : Nat.Primes) (x : ℚ) :
    FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p) x = (padicNorm p x : ℝ) := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).apply_eq_padicNorm x

end Nat.Primes

namespace NumberField.HeightOneSpectrum

/-- Equivalence between height-one primes of `ℤ` and `NumberField.FinitePlace ℚ`, transporting
along `Rat.ringOfIntegersEquiv : 𝓞 ℚ ≃+* ℤ`. -/
noncomputable def finitePlaceRatEquiv :
    IsDedekindDomain.HeightOneSpectrum ℤ ≃ FinitePlace ℚ :=
  (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm.trans
    FinitePlace.equivHeightOneSpectrum.symm

/-- `finitePlaceRatEquiv` sends a height-one prime of `ℤ` to the finite place of `ℚ` associated
to its transported prime in `𝓞 ℚ`. -/
theorem finitePlaceRatEquiv_apply (v : IsDedekindDomain.HeightOneSpectrum ℤ) :
    finitePlaceRatEquiv v =
      FinitePlace.mk
        ((IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm v) :=
  (rfl)

/-- The inverse of `finitePlaceRatEquiv` transports `w.maximalIdeal` from `𝓞 ℚ` to `ℤ` along
`Rat.ringOfIntegersEquiv`. -/
theorem finitePlaceRatEquiv_symm_apply (w : FinitePlace ℚ) :
    finitePlaceRatEquiv.symm w =
      IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv
        w.maximalIdeal :=
  (rfl)

/-- At every height-one prime `v` of `ℤ`, `adicAbv ℚ v` agrees with `finitePlaceRatEquiv v`. -/
theorem adicAbv_eq_finitePlaceRatEquiv (v : IsDedekindDomain.HeightOneSpectrum ℤ) (q : ℚ) :
    adicAbv ℚ v q = finitePlaceRatEquiv v q := by
  let w : IsDedekindDomain.HeightOneSpectrum (𝓞 ℚ) :=
    (IsDedekindDomain.HeightOneSpectrum.equivOfRingEquiv Rat.ringOfIntegersEquiv).symm v
  have hvw : v.asIdeal = Ideal.map Rat.ringOfIntegersEquiv w.asIdeal := by
    rw [← IsDedekindDomain.HeightOneSpectrum.asIdeal_equivOfRingEquiv Rat.ringOfIntegersEquiv w,
      Equiv.apply_symm_apply]
  have hnorm : Ideal.absNorm w.asIdeal = Ideal.absNorm v.asIdeal := by
    rw [Ideal.absNorm_of_ne_bot w.ne_bot, Ideal.absNorm_of_ne_bot v.ne_bot,
      Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact Nat.card_congr
      (Ideal.quotientEquiv w.asIdeal v.asIdeal Rat.ringOfIntegersEquiv hvw).toEquiv
  have hσ : IsFractionRing.ringEquivOfRingEquiv Rat.ringOfIntegersEquiv q = q :=
    RingHom.congr_fun (Subsingleton.elim
      (IsFractionRing.ringEquivOfRingEquiv Rat.ringOfIntegersEquiv).toRingHom (RingHom.id ℚ)) q
  have hval : v.valuation ℚ q = w.valuation ℚ q := by
    have hv := IsDedekindDomain.HeightOneSpectrum.valuation_ringEquivOfRingEquiv
      (K := ℚ) (K' := ℚ) Rat.ringOfIntegersEquiv hvw q
    rwa [hσ] at hv
  simp only [finitePlaceRatEquiv_apply, FinitePlace.mk_apply,
    FinitePlace.norm_embedding, adicAbv_def]
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  · rw [WithZeroMulInt.toNNReal_neg_apply _ ((v.valuation ℚ).ne_zero_iff.mpr hq),
      WithZeroMulInt.toNNReal_neg_apply _ ((w.valuation ℚ).ne_zero_iff.mpr hq)]
    push_cast
    rw [hnorm, hval]

/-- A nonzero rational number has nontrivial `v`-adic absolute value at only finitely many
height-one primes of `ℤ`. -/
theorem hasFiniteMulSupport_adicAbv_rat {q : ℚ} (hq : q ≠ 0) :
    (fun v : IsDedekindDomain.HeightOneSpectrum ℤ ↦ adicAbv ℚ v q).HasFiniteMulSupport := by
  simp_rw [adicAbv_eq_finitePlaceRatEquiv]
  exact (FinitePlace.hasFiniteMulSupport hq).comp_of_injective finitePlaceRatEquiv.injective

/-- The product formula over `ℚ` indexed by `HeightOneSpectrum ℤ`: for any nonzero `q ∈ ℚ`,
`|q| · ∏ᶠ v : HeightOneSpectrum ℤ, |q|_v = 1`. -/
theorem abs_mul_finprod_adicAbv_rat {q : ℚ} (hq : q ≠ 0) :
    |(q : ℝ)| * ∏ᶠ v : IsDedekindDomain.HeightOneSpectrum ℤ, adicAbv ℚ v q = 1 := by
  simp_rw [adicAbv_eq_finitePlaceRatEquiv]
  rw [finprod_comp_equiv finitePlaceRatEquiv (f := fun w ↦ w q),
    FinitePlace.prod_eq_inv_abs_norm hq, Algebra.norm_self, MonoidHom.id_apply,
    Rat.cast_inv, Rat.cast_abs, mul_inv_cancel₀ (abs_ne_zero.mpr (Rat.cast_ne_zero.mpr hq))]

end NumberField.HeightOneSpectrum

/-- At the prime `2`, the finite place takes the values `1/2` at `2` and `2` at `1/2`.
In particular, the dictionary uses neither the reciprocal normalization nor another power. -/
example : ∃ v : FinitePlace ℚ, v (2 : ℚ) = 1 / 2 ∧ v ((2 : ℚ)⁻¹) = 2 := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  let v := FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)
  have htwo : v (2 : ℚ) = 1 / 2 := by
    rw [Nat.Primes.finitePlace_mk_apply]
    have h := congrArg ((↑) : ℚ → ℝ) (padicNorm.padicNorm_p_of_prime (p := 2))
    norm_num at h ⊢
    exact h
  refine ⟨v, htwo, ?_⟩
  rw [map_inv₀, htwo]
  norm_num
