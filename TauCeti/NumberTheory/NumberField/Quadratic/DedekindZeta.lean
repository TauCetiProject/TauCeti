/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
public import TauCeti.NumberTheory.NumberField.Discriminant.Basic
import Mathlib.Tactic.NormNum.RealSqrt
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import TauCeti.NumberTheory.EffectiveBounds.Regulator
import TauCeti.NumberTheory.LSeries.ZetaMul
import TauCeti.NumberTheory.NumberField.PrimeIdeal
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification
import TauCeti.NumberTheory.NumberField.Quadratic.Units
import TauCeti.NumberTheory.NumberField.SplitsCompletely.Basic

/-!
# The Dedekind zeta function of a quadratic field and the class number formula

Let `K` be a quadratic number field with discriminant `D` and let `χ_D` be the primitive quadratic
Dirichlet character of conductor `|D|` (`TauCeti.Multiquadratic.fundamentalDiscriminantChar`),
regarded as a complex character. This file proves the factorization

`ζ_K(s) = ζ(s) L(s, χ_D)` for `Re s > 1`

and deduces the analytic class number formula of an imaginary quadratic field,

`h(D) = w_D √|D| L(1, χ_D) / (2π)`,

where `w_D` is the number of units of `𝓞 K`.

The factorization is an identity of Dirichlet coefficients: the number of integral ideals of `𝓞 K`
of norm `n` is `∑_{d ∣ n} χ_D(d)`. Both sides are multiplicative in `n`, so it suffices to compare
them at a prime power `p ^ k`. An ideal of norm `p ^ k` only has prime factors above `p`, so its
count is the coefficient at `p ^ k` of the product of the local Euler factors at the primes above
`p`. The decomposition law of `χ_D` describes those primes: one prime of norm `p` if `p` ramifies
(`χ_D(p) = 0`), two primes of norm `p` if `p` splits (`χ_D(p) = 1`), and one prime of norm `p ^ 2`
if `p` is inert (`χ_D(p) = -1`). In each case the count is `∑_{i ≤ k} χ_D(p) ^ i`.

Multiplying by `s - 1` and letting `s → 1⁺`, the residue of `ζ_K` at `1` is `L(1, χ_D)`, since
`ζ` has residue `1` and `L(s, χ_D)` is entire. Mathlib's `NumberField.dedekindZeta_residue`
expresses the residue as `2 ^ r₁ (2π) ^ r₂ R h / (w √|D|)`. For an imaginary quadratic field the
signature is `(r₁, r₂) = (0, 1)` and the regulator is `1`, which gives the class number formula.
The number of units is `6` for `D = -3`, `4` for `D = -4` and `2` otherwise
(`TauCeti.NumberField.Units.card_units_of_isTotallyComplex_of_discr`), and the formula is also
stated in each of these three cases.

## Main results

* `TauCeti.NumberField.normCoeff_one_eq_zetaMul`: the ideal-counting coefficients of `ζ_K` are
  the Dirichlet convolution `ζ * χ_D` (Mathlib's `DirichletCharacter.zetaMul`).
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`: `ζ_K(s) = ζ(s) L(s, χ_D)`
  on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_residue_eq_LFunction_one`: the residue of `ζ_K` at `1` is
  `L(1, χ_D)`.
* `TauCeti.NumberField.classNumber_eq_card_units_mul_LFunction_one`: the class number formula
  `h = w √|D| L(1, χ_D) / (2π)` for an imaginary quadratic field, with the specializations
  `TauCeti.NumberField.classNumber_eq_LFunction_one_of_discr_eq_neg_three`,
  `TauCeti.NumberField.classNumber_eq_LFunction_one_of_discr_eq_neg_four` and
  `TauCeti.NumberField.classNumber_eq_LFunction_one_of_discr_ne`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 6.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §5.
-/

public section

open Filter IsDedekindDomain Ideal Module NumberField NumberField.InfinitePlace
open TauCeti.IdealArithmeticFunction TauCeti.Multiquadratic
open scoped NumberField Real Topology

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### The local factor at a rational prime -/

section Local

variable {p : ℕ} [hp : Fact p.Prime]

/-- **The local Euler factor of `ζ_K` at `p`.** In a quadratic field of discriminant `D`, the
number of integral ideals of norm `p ^ k` is `∑_{i ≤ k} χ_D(p) ^ i`. -/
private theorem normCoeff_one_apply_prime_pow (hK : finrank ℚ K = 2) (k : ℕ) :
    normCoeff K 1 (p ^ k) = ∑ i ∈ Finset.range (k + 1),
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p : ℤ) : ℂ) ^ i := by
  classical
  rcases fundamentalDiscriminantChar_isQuadratic (isFundamentalDiscr_discr hK) p with h | h | h
  · -- `p` ramifies: a single prime above `p`, of norm `p`.
    have hram := (fundamentalDiscriminantChar_discr_eq_zero_iff hK p).mp h
    obtain ⟨𝔭, _, _⟩ := (inferInstance : Nonempty ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)))
    have hT := primesOver_eq_singleton_of_mem_ramifiedPrimes hK hram 𝔭
    have hN := absNorm_eq_of_mem_ramifiedPrimes hK hram 𝔭
    rw [← heightOneSpectrumOfLiesOver_asIdeal p 𝔭] at hN
    rw [normCoeff_apply_prime_pow_eq_localArithmeticFactor isMultiplicative_one hp.out _
      (eq_heightOneSpectrumOfLiesOver_of_primesOver_eq_singleton 𝔭 hT),
      localArithmeticFactor_one_apply_pow hN, h]
    simp [Finset.sum_range_succ']
  · -- `p` splits: two primes above `p`, each of norm `p`.
    obtain ⟨𝔭, 𝔮, hne, hT⟩ := Set.ncard_eq_two.mp
      ((fundamentalDiscriminantChar_discr_eq_one_iff hK p).mp h)
    have h𝔭 : 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := hT ▸ Set.mem_insert _ _
    have h𝔮 : 𝔮 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := hT ▸ by simp
    have := h𝔭.1; have := h𝔭.2; have := h𝔮.1; have := h𝔮.2
    have hsplit : ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K)).ncard = finrank ℚ K := by
      rw [hT, Set.ncard_pair hne, hK]
    have hN𝔭 := absNorm_eq_of_ncard_primesOver_eq_finrank 𝔭 hsplit
    have hN𝔮 := absNorm_eq_of_ncard_primesOver_eq_finrank 𝔮 hsplit
    rw [← heightOneSpectrumOfLiesOver_asIdeal p 𝔭] at hN𝔭
    rw [← heightOneSpectrumOfLiesOver_asIdeal p 𝔮] at hN𝔮
    have hne' : heightOneSpectrumOfLiesOver p 𝔭 ≠ heightOneSpectrumOfLiesOver p 𝔮 :=
      fun h ↦ hne (by simpa using congrArg HeightOneSpectrum.asIdeal h)
    rw [normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor isMultiplicative_one hp.out
      {heightOneSpectrumOfLiesOver p 𝔭, heightOneSpectrumOfLiesOver p 𝔮}
      (mem_of_natCast_mem_asIdeal fun P hP ↦ by
        rw [hT] at hP
        rcases hP with hP | hP
        · exact Finset.mem_insert.mpr (Or.inl (HeightOneSpectrum.ext
            (hP.trans (heightOneSpectrumOfLiesOver_asIdeal p 𝔭).symm)))
        · exact Finset.mem_insert_of_mem (Finset.mem_singleton.mpr (HeightOneSpectrum.ext
            ((Set.mem_singleton_iff.mp hP).trans (heightOneSpectrumOfLiesOver_asIdeal p 𝔮).symm)))),
      Finset.prod_pair hne', localArithmeticFactor_one_mul_apply_pow hp.out hN𝔭 hN𝔮, h]
    simp
  · -- `p` is inert: a single prime above `p`, of norm `p ^ 2`.
    obtain ⟨hunram, hone⟩ := (fundamentalDiscriminantChar_discr_eq_neg_one_iff hK p).mp h
    obtain ⟨𝔭, hT⟩ := Set.ncard_eq_one.mp hone
    have h𝔭 : 𝔭 ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) := hT ▸ rfl
    have := h𝔭.1; have := h𝔭.2
    have he : 𝔭.ramificationIdx ℤ = 1 :=
      (Algebra.isUnramifiedIn_iff_forall_ramificationIdx_eq_one.mp
        (by simpa [hp.out] using hunram)) 𝔭 inferInstance
    have hN : absNorm 𝔭 = p ^ 2 := by
      rw [absNorm_eq_pow_finrank_of_primesOver_eq_singleton 𝔭 hT he, hK]
    rw [normCoeff_apply_prime_pow_eq_localArithmeticFactor isMultiplicative_one hp.out _
      (eq_heightOneSpectrumOfLiesOver_of_primesOver_eq_singleton 𝔭 hT), h, Int.cast_neg,
      Int.cast_one, neg_one_geom_sum]
    -- The local factor is `1` at even powers of `p` and `0` at odd ones.
    rcases Nat.even_or_odd k with ⟨m, rfl⟩ | hodd
    · rw [← two_mul, pow_mul, localArithmeticFactor_one_apply_pow
        (by rwa [heightOneSpectrumOfLiesOver_asIdeal])]
      simp
    · rw [localArithmeticFactor_apply_eq_zero_of_not_exists_pow_eq _ _ ?_]
      · simp [Nat.even_add_one, Nat.not_even_iff_odd.mpr hodd]
      rintro ⟨n, hn⟩
      rw [heightOneSpectrumOfLiesOver_asIdeal, hN, ← pow_mul,
        (Nat.pow_right_injective hp.out.two_le).eq_iff] at hn
      exact Nat.not_even_iff_odd.mpr hodd ⟨n, by omega⟩

end Local

/-! ### The factorization of `ζ_K` and its residue -/

variable (hK : finrank ℚ K = 2)
include hK

/-- **The Dirichlet coefficients of `ζ_K` for a quadratic field.** The number of integral ideals
of `𝓞 K` of norm `n` is `∑_{d ∣ n} χ_D(d)`: the regrouped trivial ideal function is Mathlib's
convolution `DirichletCharacter.zetaMul` of the constant function `1` with the complex character
`χ_D` of the discriminant `D` of `K`. -/
theorem normCoeff_one_eq_zetaMul :
    normCoeff K 1 = DirichletCharacter.zetaMul
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) := by
  have hmul : (normCoeff K (1 : IdealArithmeticFunction K)).IsMultiplicative := by
    rw [normCoeff_eq_eulerProduct isMultiplicative_one]
    exact isMultiplicative_eulerProduct rfl
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ hmul _
    (DirichletCharacter.isMultiplicative_zetaMul _)).mpr fun p k hp ↦ ?_
  have := Fact.mk hp
  rw [normCoeff_one_apply_prime_pow hK, DirichletCharacter.zetaMul,
    ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [toArithmeticFunction, hp.ne_zero]

/-- **The Dedekind zeta function of a quadratic field factors as `ζ(s) L(s, χ_D)`** on the
half-plane `Re s > 1`, where `χ_D` is the complex quadratic character of the discriminant `D`
of `K`. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) s := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, normCoeff_one_eq_zetaMul hK,
    DirichletCharacter.LSeries_zetaMul _ hs]

/-- **The residue of the Dedekind zeta function of a quadratic field is `L(1, χ_D)`.** Mathlib's
`dedekindZeta_residue K`, the limit of `(s - 1) ζ_K(s)` as `s → 1⁺`, is the value at `1` of the
`L`-function of the complex quadratic character `χ_D` of the discriminant `D` of `K`. -/
theorem dedekindZeta_residue_eq_LFunction_one :
    (dedekindZeta_residue K : ℂ) = DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) 1 := by
  set χ : DirichletCharacter ℂ (discr K).natAbs :=
    (fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
      (Int.castRingHom ℂ)
  -- As `s → 1⁺`, `(s - 1) ζ(s) → 1` and `L(s, χ) → L(1, χ)`, while `(s - 1) ζ_K(s) → ρ`.
  have hζ : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by simpa using (Set.mem_Ioi.mp hs).ne')
  have hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) :=
    (((DirichletCharacter.differentiable_LFunction (χ := χ)
      (ringHomComp_fundamentalDiscriminantChar_discr_ne_one hK)).continuous.comp
      Complex.continuous_ofReal).tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (χ.LFunction 1)) := by
    refine (one_mul (χ.LFunction 1) ▸ hζ.mul hL).congr'
      (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
    dsimp only
    rw [dedekindZeta_eq_riemannZeta_mul_LFunction hK (s := s) (by simpa using hs), mul_assoc]
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hF

/-! ### The class number formula of an imaginary quadratic field -/

variable [IsTotallyComplex K]

/-- **The analytic class number formula of an imaginary quadratic field.** If `K` is imaginary
quadratic of discriminant `D`, then `h = w √|D| L(1, χ_D) / (2π)`, where `h` is the class number
of `K`, `w` is the number of units of `𝓞 K` and `χ_D` is the complex quadratic character of
`D`. -/
theorem classNumber_eq_card_units_mul_LFunction_one :
    (classNumber K : ℂ) = Nat.card (𝓞 K)ˣ * √|(discr K : ℝ)| * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) 1 / (2 * π) := by
  -- The signature is `(0, 1)`, the regulator is `1` and every unit is a root of unity.
  have hc : nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have hw : Nat.card (𝓞 K)ˣ = Units.torsionOrder K := by
    rw [Units.torsionOrder, Units.torsion_eq_top_of_isTotallyComplex hK, Subgroup.card_top]
  have hD : ((√|(discr K : ℝ)| : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (Real.sqrt_pos.mpr (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))).ne'
  have hw0 : (Units.torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Units.torsionOrder_pos K).ne'
  rw [← dedekindZeta_residue_eq_LFunction_one hK, dedekindZeta_residue_def,
    IsTotallyComplex.nrRealPlaces_eq_zero, hc,
    Units.regulator_eq_one_of_isTotallyComplex_of_finrank_eq_two K hK, hw]
  push_cast
  field_simp

/-- **The class number formula for `D = -3`.** The field of discriminant `-3` has six units, so
`h = 3 √3 L(1, χ_{-3}) / π`. -/
theorem classNumber_eq_LFunction_one_of_discr_eq_neg_three (h3 : discr K = -3) :
    (classNumber K : ℂ) = 3 * √3 * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) 1 / π := by
  rw [classNumber_eq_card_units_mul_LFunction_one hK,
    Units.card_units_of_isTotallyComplex_of_discr hK]
  simp only [h3]
  norm_num
  field_simp
  ring

/-- **The class number formula for `D = -4`.** The field of discriminant `-4` has four units, so
`h = 4 L(1, χ_{-4}) / π`. -/
theorem classNumber_eq_LFunction_one_of_discr_eq_neg_four (h4 : discr K = -4) :
    (classNumber K : ℂ) = 4 * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) 1 / π := by
  have hs : √|((-4 : ℤ) : ℝ)| = 2 := by norm_num
  rw [classNumber_eq_card_units_mul_LFunction_one hK,
    Units.card_units_of_isTotallyComplex_of_discr hK]
  simp only [h4, hs, ↓reduceIte]
  push_cast
  field_simp

/-- **The class number formula away from `D = -3, -4`.** An imaginary quadratic field of any
other discriminant `D` has two units, so `h = √|D| L(1, χ_D) / π`. -/
theorem classNumber_eq_LFunction_one_of_discr_ne (h3 : discr K ≠ -3) (h4 : discr K ≠ -4) :
    (classNumber K : ℂ) = √|(discr K : ℝ)| * DirichletCharacter.LFunction
      ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)).ringHomComp
        (Int.castRingHom ℂ)) 1 / π := by
  rw [classNumber_eq_card_units_mul_LFunction_one hK,
    Units.card_units_of_isTotallyComplex_of_discr hK]
  simp only [h3, h4, ↓reduceIte]
  push_cast
  field_simp

end TauCeti.NumberField
