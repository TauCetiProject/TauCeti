/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.Nonvanishing
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.Multiquadratic.FundamentalDiscriminant.Realization
public import TauCeti.NumberTheory.Multiquadratic.Quadratic.Discriminant
import Mathlib.RingTheory.Ideal.Int
import Mathlib.RingTheory.PowerSeries.Substitution
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import TauCeti.NumberTheory.EffectiveBounds.Regulator
import TauCeti.NumberTheory.Multiquadratic.Quadratic.Character
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification

/-!
# The Dedekind zeta function of a quadratic field and the class number formula

Let `K` be a quadratic number field of discriminant `D`, and let `χ_D` be the primitive quadratic
Dirichlet character of conductor `|D|` attached to `D` (`fundamentalDiscriminantCharCast`). This
file proves the factorization

```text
ζ_K(s) = ζ(s) L(s, χ_D)        (Re s > 1)
```

of the Dedekind zeta function, and deduces the analytic class number formula of an imaginary
quadratic field,

```text
h_K = w_K √|D| L(1, χ_D) / (2π),
```

where `h_K` is the class number, `w_K` the number of roots of unity in `K`, and `L(1, χ_D)` the
value at `1` of the continued Dirichlet `L`-function. This is the ordinary class number of the
maximal order. The number `w_K` is `6` for `D = -3`, `4` for `D = -4` and `2` otherwise
(`TauCeti.NumberField.Units.torsionOrder_eq_of_finrank_eq_two`).

The factorization is an identity of Dirichlet coefficients: the number of ideals of `𝓞 K` of norm
`n` is `∑ d ∣ n, χ_D(d)`. Both sides are multiplicative, so it suffices to compare them at a prime
power `p ^ k`. In a Galois number field the ideals of norm `p ^ k` are products of the `g` primes
above `p`, each of residue degree `f`, so their number is the coefficient of `X ^ k` in
`(1 - X ^ f) ^ (-g)` (`normCoeff_one_apply_prime_pow`). In a quadratic field `(g, f)` is `(1, 1)`,
`(2, 1)` or `(1, 2)` according as `p` ramifies, splits or is inert, that is, as `χ_D(p)` is `0`, `1`
or `-1`; in each case the coefficient is `∑ i ≤ k, χ_D(p) ^ i`.

Multiplying by `s - 1` and letting `s → 1⁺` identifies the residue of `ζ_K` at `1` with
`L(1, χ_D)`, since `ζ` has residue `1` there and `L(s, χ_D)` is continuous at `1` for `D ≠ 1`.
Mathlib's formula `NumberField.dedekindZeta_residue_def` for the residue involves the signature,
the regulator, the class number, the number of roots of unity and the discriminant; for an
imaginary quadratic field the signature is `(0, 1)` and the unit rank is `0`, so the regulator is
`1`, giving the class number formula.

## Main results

* `TauCeti.NumberField.normCoeff_one_apply_prime_pow`: in a Galois number field, the number of
  ideals of norm `p ^ k` is the coefficient of `X ^ k` in `(1 + X ^ f + X ^ (2 f) + ⋯) ^ g`.
* `TauCeti.NumberField.normCoeff_one_eq_zetaMul`: for a quadratic field, the Dirichlet
  coefficients of `ζ_K` are the convolution of `1` with `χ_D`.
* `TauCeti.NumberField.dedekindZetaCoeff_eq_sum_divisors`: the number of ideals of norm `n ≠ 0` is
  `∑ d ∣ n, χ_D(d)`.
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_LFunction`: `ζ_K(s) = ζ(s) L(s, χ_D)` for
  `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_residue_eq_LFunction_one`: the residue of `ζ_K` at `1` is
  `L(1, χ_D)`.
* `TauCeti.NumberField.classNumber_eq_torsionOrder_mul_sqrt_mul_LFunction_one_div`: the class
  number formula `h_K = w_K √|D| L(1, χ_D) / (2π)` for imaginary quadratic `K`.

## References

* H. Davenport, *Multiplicative Number Theory*, Chapter 6 (Dirichlet's class number formula).
* J. Neukirch, *Algebraic Number Theory*, Chapter I, §9 (decomposition of primes in quadratic
  fields) and Chapter VII, §5 (the Dedekind zeta function).
* The passage from the coefficient identity to `ζ(s) L(s, χ_D)` follows the private lemma
  `F_eq_LSeries` of `Mathlib/NumberTheory/LSeries/Nonvanishing.lean`, which uses Mathlib's
  `DirichletCharacter.zetaMul`.
-/

public section

open scoped NumberField Real Topology
open Filter Ideal Module NumberField NumberField.InfinitePlace NumberField.Units
open IsDedekindDomain (HeightOneSpectrum)
open TauCeti.Multiquadratic

namespace NumberField

/-- The discriminant of a number field is nonzero, so its absolute value is an admissible level for
Dirichlet characters and their `L`-functions, such as the character of a quadratic field. -/
instance neZero_natAbs_discr (K : Type*) [Field K] [NumberField K] : NeZero (discr K).natAbs :=
  ⟨Int.natAbs_ne_zero.mpr (discr_ne_zero K)⟩

end NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Ideals of prime-power norm -/

/-- **Ideals of prime-power norm in a Galois number field.** Let `p` be a prime, `g` the number of
primes of `𝓞 K` above `p` and `f` their common residue degree. The number of ideals of norm `p ^ k`,
which is the norm coefficient of the trivial ideal weight, is the coefficient of `X ^ k` in
`(1 + X ^ f + X ^ (2 f) + ⋯) ^ g`: each prime above `p` contributes the local factor
`(1 - X ^ f)⁻¹`. -/
theorem normCoeff_one_apply_prime_pow [IsGalois ℚ K] {p : ℕ} (hp : p.Prime) (k : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) (p ^ k) =
      PowerSeries.coeff k
        ((PowerSeries.mk fun n ↦ if (span {(p : ℤ)}).inertiaDegIn (𝓞 K) ∣ n then 1 else 0) ^
          (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard) := by
  have : Fact p.Prime := ⟨hp⟩
  set f := (span {(p : ℤ)}).inertiaDegIn (𝓞 K)
  have hspan : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by simpa using hp.ne_zero
  have hmax : (span {(p : ℤ)} : Ideal ℤ).IsMaximal := Int.ideal_span_isMaximal_of_prime p
  have hf : f ≠ 0 := inertiaDegIn_ne_zero (K ≃ₐ[ℚ] K)
  -- The height-one primes above `p`, as a finite set `S` with exactly `g` elements.
  have hfin :
      {P : HeightOneSpectrum (𝓞 K) | P.asIdeal ∈ primesOver (span {(p : ℤ)}) (𝓞 K)}.Finite :=
    (Algebra.QuasiFinite.finite_primesOver _).preimage
      HeightOneSpectrum.asIdeal_injective.injOn
  set S := hfin.toFinset
  have hcard : S.card = (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard := by
    rw [← Set.ncard_eq_toFinset_card _ hfin]
    refine Set.ncard_preimage_of_injective_subset_range HeightOneSpectrum.asIdeal_injective
      fun Q hQ ↦ ?_
    have := hQ.1
    have := hQ.2
    exact ⟨⟨Q, hQ.1, ne_bot_of_liesOver_of_ne_bot hspan Q⟩, rfl⟩
  -- Every prime containing `p ^ k` lies above `p`.
  have hS : ∀ P : HeightOneSpectrum (𝓞 K), ((p ^ k : ℕ) : 𝓞 K) ∈ P.asIdeal → P ∈ S := by
    intro P hP
    rw [Nat.cast_pow] at hP
    have hpP : (p : 𝓞 K) ∈ P.asIdeal := P.isPrime.mem_of_pow_mem k hP
    refine hfin.mem_toFinset.mpr ⟨P.isPrime, ⟨hmax.eq_of_le (IsPrime.under ℤ P.asIdeal).ne_top ?_⟩⟩
    rw [span_singleton_le_iff_mem, Ideal.under, Ideal.mem_comap]
    simpa using hpP
  -- Each prime above `p` has norm `p ^ f`, so its local factor is a power series in `X ^ f`.
  have hloc : ∀ P ∈ S, IdealArithmeticFunction.localArithmeticFactor 1 P =
      ArithmeticFunction.ofPowerSeries p (PowerSeries.mk fun n ↦ if f ∣ n then 1 else 0) := by
    intro P hP
    obtain ⟨_, _⟩ := hfin.mem_toFinset.mp hP
    rw [IdealArithmeticFunction.localArithmeticFactor_def, ← pow_inertiaDeg p P.asIdeal,
      ← inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P.asIdeal (K ≃ₐ[ℚ] K),
      ArithmeticFunction.ofPowerSeries_pow p hf]
    congr 1
    ext n
    simp [PowerSeries.coeff_subst_X_pow hf]
  rw [IdealArithmeticFunction.normCoeff_apply_eq_prod_localArithmeticFactor_apply
      IdealArithmeticFunction.isMultiplicative_one S hS,
    Finset.prod_congr rfl hloc, Finset.prod_const, hcard, ← map_pow,
    ArithmeticFunction.ofPowerSeries_apply_pow hp.one_lt]

/-- The prime-power norm coefficients of a quadratic field are the partial geometric sums of the
value of `χ_D` at the prime. -/
private theorem normCoeff_one_apply_prime_pow_eq_sum (hK : finrank ℚ K = 2) {p : ℕ}
    (hp : p.Prime) (k : ℕ) :
    normCoeff K (1 : IdealArithmeticFunction K) (p ^ k) =
      ∑ i ∈ Finset.range (k + 1),
        ((fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) p : ℤ) : ℂ) ^ i := by
  have : Fact p.Prime := ⟨hp⟩
  have : Algebra.IsQuadraticExtension ℚ K := ⟨hK⟩
  obtain ⟨𝔮, h𝔮, h𝔮p⟩ := (inferInstance : Nonempty (primesOver (span {(p : ℤ)}) (𝓞 K)))
  rw [normCoeff_one_apply_prime_pow hp]
  set χ := fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK)
  set g := (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard
  set e := (span {(p : ℤ)}).ramificationIdxIn (𝓞 K)
  set f := (span {(p : ℤ)}).inertiaDegIn (𝓞 K)
  -- The fundamental identity `g e f = 2` leaves three possible decompositions of `p`.
  have hgef : g * (e * f) = 2 := by
    have h := ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn (span {(p : ℤ)}) (𝓞 K)
      (K ≃ₐ[ℚ] K)
    rwa [IsGalois.card_aut_eq_finrank, hK] at h
  have hcases : (g = 1 ∧ e = 1 ∧ f = 2) ∨ (g = 1 ∧ e = 2 ∧ f = 1) ∨ (g = 2 ∧ e = 1 ∧ f = 1) := by
    have hg : g ∣ 2 := Dvd.intro _ hgef
    have he : e ∣ 2 := Dvd.intro (g * f) (by rw [← hgef]; ring)
    have hf : f ∣ 2 := Dvd.intro (g * e) (by rw [← hgef]; ring)
    rcases (Nat.dvd_prime Nat.prime_two).mp hg with hg | hg <;>
    rcases (Nat.dvd_prime Nat.prime_two).mp he with he | he <;>
    rcases (Nat.dvd_prime Nat.prime_two).mp hf with hf | hf <;>
    simp_all
  -- `χ_D(p)` is `0` exactly when `p` ramifies, that is `e = 2`, and `1` exactly when `g = 2`.
  have hram : p ∈ ramifiedPrimes K ↔ e = 2 := by
    rw [show e = 𝔮.ramificationIdx ℤ from
      ramificationIdxIn_eq_ramificationIdx (span {(p : ℤ)}) 𝔮 (K ≃ₐ[ℚ] K)]
    exact NumberField.mem_ramifiedPrimes_iff_ramificationIdx_eq_two hK hp 𝔮
  have h0 : χ p = 0 ↔ e = 2 := (fundamentalDiscriminantChar_discr_eq_zero_iff hK p).trans hram
  have h1 : χ p = 1 ↔ g = 2 := fundamentalDiscriminantChar_discr_eq_one_iff hK p
  rcases hcases with ⟨hg, he, hf⟩ | ⟨hg, he, hf⟩ | ⟨hg, he, hf⟩
  · -- `p` is inert: one prime of residue degree `2`, and `χ_D(p) = -1`.
    have hχ : χ p = -1 :=
      ((fundamentalDiscriminantChar_isQuadratic _ p).resolve_left fun h ↦ by
        have := h0.mp h; omega).resolve_left fun h ↦ by have := h1.mp h; omega
    rw [hg, hf, pow_one, PowerSeries.coeff_mk, hχ, Int.cast_neg, Int.cast_one, neg_one_geom_sum]
    by_cases hk : 2 ∣ k <;> simp [hk, even_iff_two_dvd, show 2 ∣ k + 1 ↔ ¬ 2 ∣ k by omega]
  · -- `p` ramifies: one prime of residue degree `1`, and `χ_D(p) = 0`.
    rw [hg, hf, h0.mpr he, pow_one, PowerSeries.coeff_mk]
    simp [zero_geom_sum]
  · -- `p` splits: two primes of residue degree `1`, and `χ_D(p) = 1`.
    rw [hg, hf, h1.mpr hg, pow_two, PowerSeries.coeff_mul]
    simp

/-! ### The factorization of the Dedekind zeta function -/

/-- **Ideal counts of a quadratic field.** For a quadratic field `K` of discriminant `D`, the
Dirichlet coefficients of `ζ_K`, which count the ideals of `𝓞 K` of each norm, are the Dirichlet
convolution of the constant function `1` with the character `χ_D`. -/
theorem normCoeff_one_eq_zetaMul (hK : finrank ℚ K = 2) :
    normCoeff K (1 : IdealArithmeticFunction K) =
      (fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)).zetaMul := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    IdealArithmeticFunction.isMultiplicative_one.normCoeff _
    (DirichletCharacter.isMultiplicative_zetaMul _)).mpr fun p k hp ↦ ?_
  rw [normCoeff_one_apply_prime_pow_eq_sum hK hp, DirichletCharacter.zetaMul,
    ArithmeticFunction.coe_zeta_mul_apply, Nat.sum_divisors_prime_pow hp]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp [toArithmeticFunction, hp.ne_zero]

/-- **The number of ideals of a given norm in a quadratic field.** If `K` is a quadratic field of
discriminant `D`, the number `dedekindZetaCoeff K n` of ideals of `𝓞 K` of norm `n ≠ 0` is
`∑ d ∣ n, χ_D(d)`. -/
theorem dedekindZetaCoeff_eq_sum_divisors (hK : finrank ℚ K = 2) {n : ℕ} (hn : n ≠ 0) :
    (dedekindZetaCoeff K n : ℤ) =
      ∑ d ∈ n.divisors, fundamentalDiscriminantChar (discr K) (isFundamentalDiscr_discr hK) d := by
  have h := congr($(normCoeff_one_eq_zetaMul hK) n)
  simp only [normCoeff_one_apply, hn, ↓reduceIte] at h
  apply Int.cast_injective (α := ℂ)
  rw [Int.cast_natCast, h]
  simp only [DirichletCharacter.zetaMul, ArithmeticFunction.coe_zeta_mul_apply, Int.cast_sum]
  refine Finset.sum_congr rfl fun d hd ↦ ?_
  simp [toArithmeticFunction, Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)]

/-- **`ζ_K = ζ · L(χ_D)`.** The Dedekind zeta function of a quadratic field `K` of discriminant
`D` is the product of the Riemann zeta function and the Dirichlet `L`-function of `χ_D`, on the
half-plane `Re s > 1` of absolute convergence. -/
theorem dedekindZeta_eq_riemannZeta_mul_LFunction (hK : finrank ℚ K = 2) {s : ℂ}
    (hs : 1 < s.re) :
    dedekindZeta K s = riemannZeta s *
      (fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)).LFunction s := by
  set χ := fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)
  rw [dedekindZeta_eq_LSeries_normCoeff_one K, normCoeff_one_eq_zetaMul hK,
    DirichletCharacter.zetaMul, ← ArithmeticFunction.coe_mul, LSeries_convolution',
    χ.LFunction_eq_LSeries hs, ← ArithmeticFunction.LSeries_zeta_eq_riemannZeta hs,
    LSeries_congr χ.apply_eq_toArithmeticFunction_apply s]
  · -- The two sides now agree up to η-reduction of the coefficients of `ζ`.
    simp_rw [← ArithmeticFunction.natCoe_apply]
    rfl
  · exact (LSeriesSummable_congr _ fun h ↦ by simp).mpr
      (ArithmeticFunction.LSeriesSummable_zeta_iff.mpr hs)
  · exact (LSeriesSummable_congr _ fun h ↦ (χ.apply_eq_toArithmeticFunction_apply h).symm).mpr
      (ZMod.LSeriesSummable_of_one_lt_re χ hs)

/-! ### The residue at `s = 1` and the class number formula -/

/-- **The residue of `ζ_K` at `1` is `L(1, χ_D)`.** For a quadratic field `K` of discriminant
`D`, the residue `NumberField.dedekindZeta_residue K` of the Dedekind zeta function at `s = 1` is
the value at `1` of the continued Dirichlet `L`-function of `χ_D`. -/
theorem dedekindZeta_residue_eq_LFunction_one (hK : finrank ℚ K = 2) :
    (dedekindZeta_residue K : ℂ) =
      (fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)).LFunction 1 := by
  set χ := fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)
  have hχ : χ ≠ 1 := by
    rw [Ne, fundamentalDiscriminantCharCast_eq_one_iff]
    intro h
    have := abs_discr_gt_two (K := K) (by omega)
    simp [h] at this
  -- On real `s > 1`, `(s - 1) ζ_K(s) = ((s - 1) ζ(s)) L(s, χ_D) → 1 · L(1, χ_D)`.
  have hofReal : Tendsto (fun s : ℝ ↦ (s : ℂ)) (𝓝[>] 1) (𝓝[≠] 1) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · simpa using (Complex.continuous_ofReal.tendsto (1 : ℝ)).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
      exact Set.mem_compl_singleton_iff.mpr (by exact_mod_cast hs.ne')
  have hL : Tendsto (fun s : ℝ ↦ χ.LFunction s) (𝓝[>] 1) (𝓝 (χ.LFunction 1)) :=
    (DirichletCharacter.differentiableAt_LFunction χ 1 (.inr hχ)).continuousAt.tendsto.comp
      (hofReal.mono_right nhdsWithin_le_nhds)
  have hprod := (riemannZeta_residue_one.comp hofReal).mul hL
  rw [one_mul] at hprod
  refine tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) (hprod.congr' ?_)
  filter_upwards [self_mem_nhdsWithin] with s (hs : 1 < s)
  rw [Function.comp_apply, dedekindZeta_eq_riemannZeta_mul_LFunction hK (by simpa using hs),
    mul_assoc]

/-- **The analytic class number formula for an imaginary quadratic field.** If `K` is an imaginary
quadratic field of discriminant `D`, with class number `h_K` and `w_K` roots of unity, then
`h_K = w_K √|D| L(1, χ_D) / (2π)`. -/
theorem classNumber_eq_torsionOrder_mul_sqrt_mul_LFunction_one_div [IsTotallyComplex K]
    (hK : finrank ℚ K = 2) :
    (classNumber K : ℂ) = torsionOrder K * Real.sqrt |(discr K : ℝ)| *
      (fundamentalDiscriminantCharCast ℂ (discr K) (isFundamentalDiscr_discr hK)).LFunction 1 /
        (2 * π) := by
  have hr₂ : nrComplexPlaces K = 1 := by
    have := IsTotallyComplex.finrank (K := K)
    omega
  have hres := dedekindZeta_residue_eq_LFunction_one hK
  rw [dedekindZeta_residue_def, IsTotallyComplex.nrRealPlaces_eq_zero, hr₂,
    regulator_eq_one_of_rank_eq_zero K
      (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K hK)] at hres
  rw [← hres]
  have hw : (torsionOrder K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (torsionOrder_pos K).ne'
  have hD : (Real.sqrt |(discr K : ℝ)| : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr
      (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K))))
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  push_cast
  field_simp

end TauCeti.NumberField
