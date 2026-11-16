/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
public import Mathlib.NumberTheory.Ostrowski
public import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import TauCeti.Analysis.AbsoluteValue.Equivalence
import TauCeti.NumberTheory.NumberField.FinitePlace.Basic
import TauCeti.NumberTheory.NumberField.Global.Places.Basic
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
and its inverse. For any Dedekind domain `R` integrally closed in `ℚ` with fraction field `ℚ`
(such as `ℤ` or `𝓞 ℚ`), transporting the product formula for `ℚ` along `R ≃+* 𝓞 ℚ` gives
`|x| · ∏ᶠ v, (#(R ⧸ v)) ^ log (v x) = 1` in `ℚ`
(`Rat.HeightOneSpectrum.abs_mul_finprod_zpow_log_valuation`).

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

section ProductFormula

variable {R : Type*} [CommRing R] [IsDedekindDomain R] [Algebra R ℚ] [IsFractionRing R ℚ]
  [IsIntegralClosure R ℤ ℚ]

/-- At a height-one prime `v` of an integral closure `R` of `ℤ` in `ℚ`, the rational factor
`#(R ⧸ v) ^ log (v x)` casts to the normalized absolute value of `x` at the corresponding finite
place of `ℚ`. -/
private theorem ratCast_zpow_log_valuation_eq_normalizedAbsValue
    (v : HeightOneSpectrum R) {x : ℚ} (hx : x ≠ 0) :
    (((Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ x) : ℚ) : ℝ) =
      TauCeti.GlobalNumberFields.normalizedAbsValue
        (Sum.inl (HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.equiv R).symm v))
        x := by
  let e : R ≃+* 𝓞 ℚ := (NumberField.RingOfIntegers.equiv R).symm
  let w : HeightOneSpectrum (𝓞 ℚ) := HeightOneSpectrum.equivOfRingEquiv e v
  have hvw : w.asIdeal = Ideal.map e v.asIdeal := HeightOneSpectrum.asIdeal_equivOfRingEquiv e v
  have hcard : Nat.card (R ⧸ v.asIdeal) = w.asIdeal.absNorm := by
    rw [Ideal.absNorm_of_ne_bot w.ne_bot, Submodule.cardQuot_apply]
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal w.asIdeal e hvw).toEquiv
  have hval : w.valuation ℚ x = v.valuation ℚ x := by
    have hσ : (IsFractionRing.ringEquivOfRingEquiv (K := ℚ) (L := ℚ) e).toRingHom =
        RingHom.id ℚ := Subsingleton.elim _ _
    have h := HeightOneSpectrum.valuation_ringEquivOfRingEquiv (K := ℚ) (K' := ℚ) e hvw x
    simpa [RingHom.ext_iff.mp hσ x] using h
  rw [TauCeti.GlobalNumberFields.normalizedAbsValue_inl, ← FinitePlace.norm_embedding,
    ← FinitePlace.mk_apply, FinitePlace.apply_eq_absNorm_zpow _ hx, FinitePlace.maximalIdeal_mk,
    hcard, hval]
  push_cast
  rfl

/-- For a nonzero rational number `x`, the local normalized absolute value
`#(R ⧸ v) ^ log (v x)` is `1` at all but finitely many height-one primes `v` of `R`. -/
theorem hasFiniteMulSupport_zpow_log_valuation {x : ℚ} (hx : x ≠ 0) :
    Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ x)) := by
  let f := HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.equiv (K := ℚ) R).symm
  have hsupp : Function.HasFiniteMulSupport (fun v : HeightOneSpectrum R ↦
      TauCeti.GlobalNumberFields.normalizedAbsValue (Sum.inl (f v)) x) := by
    have h := (TauCeti.GlobalNumberFields.hasFiniteMulSupport_adicAbv (K := ℚ) hx).preimage
      f.injective.injOn
    simpa [Function.HasFiniteMulSupport, TauCeti.GlobalNumberFields.normalizedAbsValue_inl,
      Set.preimage, Function.mulSupport] using h
  refine hsupp.subset fun v hv ↦ ?_
  simp only [Function.mem_mulSupport, ne_eq] at hv ⊢
  rw [← ratCast_zpow_log_valuation_eq_normalizedAbsValue v hx]
  exact_mod_cast hv

/-- **The product formula for `ℚ` over any integral closure `R` of `ℤ` in `ℚ`**: for every
nonzero `x : ℚ`, `|x| · ∏ᶠ v : HeightOneSpectrum R, (#(R ⧸ v)) ^ log (v x) = 1`. -/
theorem abs_mul_finprod_zpow_log_valuation {x : ℚ} (hx : x ≠ 0) :
    |x| * ∏ᶠ v : HeightOneSpectrum R,
        (Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ x) = 1 := by
  let f := HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.equiv (K := ℚ) R).symm
  apply Rat.cast_injective (α := ℝ)
  rw [Rat.cast_mul, Rat.cast_abs, Rat.cast_one,
    ← Rat.coe_castHom, map_finprod (Rat.castHom ℝ)
      (hasFiniteMulSupport_zpow_log_valuation (R := R) hx)]
  have hcongr : (∏ᶠ v : HeightOneSpectrum R,
      (Rat.castHom ℝ) ((Nat.card (R ⧸ v.asIdeal) : ℚ) ^ WithZero.log (v.valuation ℚ x))) =
      ∏ᶠ v : HeightOneSpectrum R,
        TauCeti.GlobalNumberFields.normalizedAbsValue (Sum.inl (f v)) x :=
    finprod_congr fun v ↦ ratCast_zpow_log_valuation_eq_normalizedAbsValue v hx
  rw [hcongr, finprod_comp_equiv (e := f) (f := fun w ↦
      TauCeti.GlobalNumberFields.normalizedAbsValue (Sum.inl w) x),
    TauCeti.GlobalNumberFields.finprod_normalizedAbsValue_inl (K := ℚ) hx,
    Algebra.norm_self, MonoidHom.id_apply, Rat.coe_castHom, Rat.cast_inv, Rat.cast_abs]
  exact mul_inv_cancel₀ (abs_ne_zero.mpr (by exact_mod_cast hx))

end ProductFormula

end Rat.HeightOneSpectrum

namespace NumberField.FinitePlace

/-- A finite place of `ℚ` is the usual `p`-adic absolute value at its canonical prime under
`Rat.HeightOneSpectrum.primesEquiv`, not merely a positive power of that absolute value. -/
theorem val_eq_padic (v : FinitePlace ℚ) :
    letI : Fact (primesEquiv v.maximalIdeal : ℕ).Prime := ⟨(primesEquiv v.maximalIdeal).property⟩
    v.1 = Rat.AbsoluteValue.padic (primesEquiv v.maximalIdeal) := by
  let p : Nat.Primes := primesEquiv v.maximalIdeal
  let : Fact (p : ℕ).Prime := ⟨p.property⟩
  -- Mathlib defines the value of `primesEquiv` to be `natGenerator`.
  have hpval : (p : ℕ) = natGenerator v.maximalIdeal := rfl
  have hvp : v.1 (p : ℚ) = (p : ℝ)⁻¹ := by
    rw [← coe_apply, ← v.mk_maximalIdeal, hpval]
    exact finitePlace_mk_natGenerator v.maximalIdeal
  have hp1 : (1 : ℝ) < p := by exact_mod_cast p.property.one_lt
  have hsmall : v.1 (p : ℚ) < 1 := by
    rw [hvp]
    exact inv_lt_one_of_one_lt₀ hp1
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr p.property.ne_zero
  have hnt : v.1.IsNontrivial := ⟨(p : ℚ), hp0, hsmall.ne⟩
  have hbdd (n : ℕ) : v.1 (n : ℚ) ≤ 1 :=
    IsNonarchimedean.apply_natCast_le_one (f := v.1) (by simp) v.1.map_one v.add_le
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
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).1 = Rat.AbsoluteValue.padic p := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).val_eq_padic

/-- The finite place constructed from a prime evaluates to the usual `padicNorm`. -/
theorem finitePlace_mk_apply (p : Nat.Primes) (x : ℚ) :
    FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p) x = (padicNorm p x : ℝ) := by
  simpa only [FinitePlace.maximalIdeal_mk, Equiv.apply_symm_apply] using
    (FinitePlace.mk ((primesEquiv (R := 𝓞 ℚ)).symm p)).apply_eq_padicNorm x

end Nat.Primes

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
