/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.DirichletCharacter.Polynomial
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction
import TauCeti.NumberTheory.DirichletCharacter.Conductor
import TauCeti.NumberTheory.LSeries.Convolution
import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The Dedekind zeta function of a cyclotomic field

Let `K` be an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`). This file proves the
Dirichlet-coefficient, local Euler-factor, convergent `Re s > 1`, and residue-at-`1` identities
factoring the Dedekind zeta function `ζ_K` into Dirichlet `L`-functions attached to the primitive
characters `χ.primitiveCharacter` of the characters `χ : DirichletCharacter ℂ n`:

* **Local Euler factors** (`prod_primesOverFinset_one_sub_absNorm_cpow_neg`): at every rational
  prime `p` (including ramified primes dividing `n`),
  `∏ P | p, (1 - N(P) ^ (-s)) = ∏ χ, (1 - χ.primitiveCharacter p * p ^ (-s))`.
* **Dirichlet coefficients** (`normCoeff_one_eq_prod_primitiveCharacter`,
  `dedekindZetaCoeff_eq_prod_primitiveCharacter`): the ideal-counting arithmetic function
  `normCoeff K 1` is the Dirichlet convolution
  `∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)`.
* **Convergent factorization** (`dedekindZeta_eq_prod_LFunction_primitiveCharacter`,
  `dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`): on `Re s > 1`,
  `ζ_K(s) = ∏ χ, L(s, χ.primitiveCharacter) = ζ(s) ∏_{χ ≠ 1} L(s, χ.primitiveCharacter)`.
* **Level-`n` imprimitive comparison** (`dedekindZeta_mul_prod_eq_prod_LFunction`): multiplying
  `ζ_K(s)` by `∏ χ, ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * p ^ (-s))` recovers the
  product `∏ χ : DirichletCharacter ℂ n, L(s, χ)` of level-`n` `L`-functions.
* **Residue at `s = 1`** (`dedekindZeta_residue_eq_prod_LFunction_one`): the residue of `ζ_K` at
  `1` is `∏_{χ ≠ 1} L(1, χ.primitiveCharacter)`.

## Main results

* `TauCeti.NumberField.absNorm_eq_pow_orderOf`: for `n = p ^ k * m` with `¬ p ∣ m`, every prime `P`
  of `𝓞 K` above `p` has norm `p ^ orderOf (p : ZMod m)`.
* `TauCeti.NumberField.card_primesOverFinset_eq_totient_div_orderOf`: there are
  `m.totient / orderOf (p : ZMod m)` primes of `𝓞 K` above `p`.
* `TauCeti.NumberField.prod_primesOverFinset_one_sub_absNorm_cpow_neg`,
  `TauCeti.NumberField.prod_primesOverFinset_inv_one_sub_absNorm_cpow_neg`: local Euler-factor
  identity at every rational prime `p`.
* `TauCeti.NumberField.normCoeff_one_eq_prod_primitiveCharacter`,
  `TauCeti.NumberField.dedekindZetaCoeff_eq_prod_primitiveCharacter`: Dirichlet-coefficient
  factorization of `ζ_K`.
* `TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`,
  `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`,
  `TauCeti.NumberField.dedekindZeta_mul_prod_eq_prod_LFunction`: factorization of `dedekindZeta K s`
  for `1 < s.re`.
* `TauCeti.NumberField.dedekindZeta_residue_eq_prod_LFunction_one`: residue of `ζ_K` at `s = 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Corollary 5.11.
-/

public section

open Filter Ideal IsDedekindDomain NumberField
open TauCeti.IdealArithmeticFunction
open scoped NumberField Topology

namespace DirichletCharacter

/-- The primitive character associated to `χ` is principal if and only if `χ` is principal. -/
@[simp]
theorem primitiveCharacter_eq_one_iff {R : Type*} [CommMonoidWithZero R] {n : ℕ} [NeZero n]
    (χ : DirichletCharacter R n) :
    χ.primitiveCharacter = 1 ↔ χ = 1 :=
  χ.primitiveCharacter_isPrimitive.eq_one_iff.trans χ.eq_one_iff_conductor_eq_one.symm

private theorem LFunction_eq_riemannZeta_of_eq_one {m : ℕ} [NeZero m] (hm : m = 1)
    (ψ : DirichletCharacter ℂ m) : ψ.LFunction = riemannZeta := by
  subst hm
  exact LFunction_modOne_eq

/-- The continued `L`-function of the primitive character of the principal character modulo `n` is
the Riemann zeta function. -/
@[simp]
theorem LFunction_primitiveCharacter_one (n : ℕ) [NeZero n] :
    (1 : DirichletCharacter ℂ n).primitiveCharacter.LFunction = riemannZeta :=
  LFunction_eq_riemannZeta_of_eq_one conductor_one _

open scoped Classical in
/-- Splitting off the principal character `χ = 1` separates `riemannZeta s` from the product of
`χ.primitiveCharacter.LFunction s` over all `χ : DirichletCharacter ℂ n`. -/
theorem prod_LFunction_primitiveCharacter_eq_riemannZeta_mul (n : ℕ) [NeZero n] (s : ℂ) :
    (∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s) =
      riemannZeta s *
        ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction s := by
  rw [Finset.filter_ne', ← Finset.mul_prod_erase Finset.univ
    (fun χ : DirichletCharacter ℂ n ↦ χ.primitiveCharacter.LFunction s) (Finset.mem_univ 1),
    LFunction_primitiveCharacter_one]

end DirichletCharacter

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-! ### Prime-ideal norms and local Euler factors -/

section Local

variable {n p k m : ℕ} [hp : Fact p.Prime] [IsCyclotomicExtension {n} ℚ K]

/-- **Norm of a prime ideal in a cyclotomic field.** If `n = p ^ k * m` with `¬ p ∣ m`, every prime
ideal `P` of `𝓞 K` lying over `p` has absolute norm `p ^ orderOf (p : ZMod m)`. -/
theorem absNorm_eq_pow_orderOf (hn : n = p ^ k * m) (hm : ¬ p ∣ m) (P : Ideal (𝓞 K))
    [P.IsPrime] [P.LiesOver (span {(p : ℤ)})] :
    absNorm P = p ^ orderOf (p : ZMod m) := by
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  rw [← pow_inertiaDeg p P, ← inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) P Gal(K/ℚ),
    inertiaDegIn_eq_orderOf hn hm]

/-- **Cardinality of `primesOverFinset` in a cyclotomic field.** If `n = p ^ k * m` with `¬ p ∣ m`,
the number of primes of `𝓞 K` above `p` is `m.totient / orderOf (p : ZMod m)`. -/
theorem card_primesOverFinset_eq_totient_div_orderOf (hn : n = p ^ k * m) (hm : ¬ p ∣ m) :
    (primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card = m.totient / orderOf (p : ZMod m) := by
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.out.ne_zero
  have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_prime_iff_not_dvd hp.out).mpr hm
  have hf0 : 0 < orderOf (p : ZMod m) := by
    rw [← hu.unit_spec, orderOf_units]
    exact (isOfFinOrder_of_finite hu.unit).orderOf_pos
  rw [← Set.ncard_coe_finset, coe_primesOverFinset hp0,
    ← ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := K) hn hm,
    Nat.mul_div_cancel _ hf0]

/-- **Local polynomial Euler-factor identity at a rational prime.** In an `n`-th cyclotomic field
over `ℚ` (`n ≠ 0`), at any rational prime `p` and any `s : ℂ`, the product of `1 - N(P) ^ (-s)` over
the primes `P` of `𝓞 K` above `p` equals the product of `1 - χ.primitiveCharacter p * p ^ (-s)` over
all Dirichlet characters `χ` modulo `n`. -/
theorem prod_primesOverFinset_one_sub_absNorm_cpow_neg [NeZero n] (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K), (1 - (absNorm P : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s)) := by
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.out.ne_one
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have : NeZero (Monoid.exponent (ZMod m)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.out.ne_zero
  rw [DirichletCharacter.prod_one_sub_primitiveCharacter_prime_mul hp.out hn hm ((p : ℂ) ^ (-s)),
    ← card_primesOverFinset_eq_totient_div_orderOf (K := K) hn hm, ← Finset.prod_const]
  refine Finset.prod_congr rfl fun P hP ↦ ?_
  obtain ⟨_, _⟩ := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp hP
  rw [absNorm_eq_pow_orderOf hn hm P, Nat.cast_pow,
    ← Complex.natCast_cpow_natCast_mul p (orderOf (p : ZMod m)) (-s),
    Complex.cpow_nat_mul (p : ℂ) (orderOf (p : ZMod m)) (-s)]

/-- **Local Euler-factor identity at a rational prime.** Inverted form of
`prod_primesOverFinset_one_sub_absNorm_cpow_neg`. -/
theorem prod_primesOverFinset_inv_one_sub_absNorm_cpow_neg [NeZero n] (s : ℂ) :
    ∏ P ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K), (1 - (absNorm P : ℂ) ^ (-s))⁻¹ =
      ∏ χ : DirichletCharacter ℂ n, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))⁻¹ := by
  rw [Finset.prod_inv_distrib, Finset.prod_inv_distrib,
    prod_primesOverFinset_one_sub_absNorm_cpow_neg (n := n)]

/-- Prime-power evaluation of `normCoeff K 1` in a cyclotomic field: the `g` primes of `𝓞 K` above
`p` each contribute `ArithmeticFunction.ofPowerSeries (p ^ f) (PowerSeries.mk 1)`. -/
private theorem normCoeff_one_apply_prime_pow (hn : n = p ^ k * m) (hm : ¬ p ∣ m) (r : ℕ) :
    normCoeff K 1 (p ^ r) =
      ((ArithmeticFunction.ofPowerSeries (p ^ orderOf (p : ZMod m))
          (PowerSeries.mk 1 : PowerSeries ℂ)) ^
        (m.totient / orderOf (p : ZMod m))) (p ^ r) := by
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.out.ne_zero
  let Pset := primesOverFinset (span {(p : ℤ)}) (𝓞 K)
  let toH : {P // P ∈ Pset} ↪ HeightOneSpectrum (𝓞 K) :=
    { toFun := fun P ↦
        @heightOneSpectrumOfLiesOver K _ _ p hp P.1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P.2).1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P.2).2
      inj' := fun P₁ P₂ h ↦ Subtype.ext <| by
        have h₁ := @heightOneSpectrumOfLiesOver_asIdeal K _ _ p hp P₁.1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P₁.2).1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P₁.2).2
        have h₂ := @heightOneSpectrumOfLiesOver_asIdeal K _ _ p hp P₂.1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P₂.2).1
          ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P₂.2).2
        exact h₁.symm.trans ((congrArg HeightOneSpectrum.asIdeal h).trans h₂) }
  have hasIdeal (P : {P // P ∈ Pset}) : (toH P).asIdeal = P.1 :=
    @heightOneSpectrumOfLiesOver_asIdeal K _ _ p hp P.1
      ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P.2).1
      ((mem_primesOverFinset_iff hp0 (𝓞 K)).mp P.2).2
  have hmem : ∀ Q : HeightOneSpectrum (𝓞 K),
      Q.asIdeal ∈ (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K) → Q ∈ Pset.attach.map toH :=
    fun Q hQ ↦ Finset.mem_map.mpr ⟨⟨Q.asIdeal, (mem_primesOverFinset_iff hp0 (𝓞 K)).mpr hQ⟩,
      Finset.mem_attach _ _, HeightOneSpectrum.ext (hasIdeal _)⟩
  rw [normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor isMultiplicative_one hp.out
    (Pset.attach.map toH) (mem_of_natCast_mem_asIdeal hmem) r, Finset.prod_map]
  have hloc : ∀ P ∈ Pset.attach,
      (1 : IdealArithmeticFunction K).localArithmeticFactor (toH P) =
        ArithmeticFunction.ofPowerSeries (p ^ orderOf (p : ZMod m))
          (PowerSeries.mk 1 : PowerSeries ℂ) := by
    intro P _
    obtain ⟨_, _⟩ := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp P.2
    have hps : (1 : IdealArithmeticFunction K).localPowerSeries (toH P) = PowerSeries.mk 1 := by
      ext i; simp
    rw [localArithmeticFactor_def, hps, hasIdeal P, absNorm_eq_pow_orderOf hn hm P.1]
  rw [Finset.prod_congr rfl hloc, Finset.prod_const, Finset.card_attach,
    card_primesOverFinset_eq_totient_div_orderOf (K := K) hn hm]

end Local

/-! ### Global Dirichlet-coefficient, `L`-series, and residue factorizations -/

section Global

variable {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- **Dirichlet-coefficient factorization of `ζ_K` for a cyclotomic field.** In an `n`-th cyclotomic
field over `ℚ` (`n ≠ 0`), the ideal-counting arithmetic function `normCoeff K 1` equals the
Dirichlet convolution of `toArithmeticFunction (χ.primitiveCharacter ·)` over all characters
`χ : DirichletCharacter ℂ n`. -/
theorem normCoeff_one_eq_prod_primitiveCharacter :
    normCoeff K 1 =
      ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·) := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    isMultiplicative_one.normCoeff _
    (ArithmeticFunction.isMultiplicative_finsetProd _ _ fun χ _ ↦
      χ.primitiveCharacter.isMultiplicative_toArithmeticFunction)).mpr fun p r hp ↦ ?_
  have := Fact.mk hp
  obtain ⟨k, m, hm, hn⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  have : NeZero m := ⟨fun h ↦ hm (h ▸ dvd_zero p)⟩
  have : NeZero (Monoid.exponent (ZMod m)ˣ) := ⟨Monoid.exponent_ne_zero_of_finite⟩
  rw [normCoeff_one_apply_prime_pow (K := K) hn hm r,
    DirichletCharacter.prod_toArithmeticFunction_primitiveCharacter_apply_prime_pow hp hn hm r]

/-- **Ideal-counting coefficients of `ζ_K` for a cyclotomic field.** For every `k ≠ 0`, the number
`dedekindZetaCoeff K k` of integral ideals of `𝓞 K` of norm `k` equals the `k`-th coefficient of
`∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)`. -/
theorem dedekindZetaCoeff_eq_prod_primitiveCharacter {k : ℕ} (hk : k ≠ 0) :
    (dedekindZetaCoeff K k : ℂ) =
      (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) k := by
  have h := congr($(normCoeff_one_eq_prod_primitiveCharacter (K := K) (n := n)) k)
  simpa [normCoeff_one_apply, hk] using h

/-- **Factorization of `ζ_K` on `Re s > 1` into primitive Dirichlet `L`-functions.** For an `n`-th
cyclotomic field `K` over `ℚ` (`n ≠ 0`) and `1 < s.re`,
`dedekindZeta K s = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZeta_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, normCoeff_one_eq_prod_primitiveCharacter (n := n)]
  exact (ArithmeticFunction.LSeriesHasSum_prod
    (fun χ _ ↦ χ.primitiveCharacter.LSeriesHasSum_toArithmeticFunction hs)).LSeries_eq

open scoped Classical in
/-- **Factorization of `ζ_K` on `Re s > 1` with `riemannZeta` separated.** For an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`) and `1 < s.re`,
`dedekindZeta K s = riemannZeta s * ∏ χ ≠ 1, χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      riemannZeta s *
        ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) hs,
    DirichletCharacter.prod_LFunction_primitiveCharacter_eq_riemannZeta_mul]

/-- **Imprimitive level-`n` comparison for `ζ_K` on `Re s > 1`.** Multiplying `dedekindZeta K s` by
the Euler factors missing at primes dividing `n` gives the product of the level-`n` Dirichlet
`L`-functions `χ.LFunction s`. -/
theorem dedekindZeta_mul_prod_eq_prod_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s *
        (∏ χ : DirichletCharacter ℂ n,
          ∏ p ∈ n.primeFactors, (1 - χ.primitiveCharacter p * (p : ℂ) ^ (-s))) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter (n := n) hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (.inr hs1), χ.changeLevel_primitiveCharacter]

open scoped Classical in
/-- **Residue of `ζ_K` at `s = 1` for a cyclotomic field.** The residue `dedekindZeta_residue K` of
the Dedekind zeta function of an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`) equals the product of
`χ.primitiveCharacter.LFunction 1` over all nonprincipal characters `χ` modulo `n`. -/
theorem dedekindZeta_residue_eq_prod_LFunction_one :
    (dedekindZeta_residue K : ℂ) =
      ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction 1 := by
  have hζ : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by simpa using (Set.mem_Ioi.mp hs).ne')
  have hcont : Continuous (fun z : ℂ ↦
      ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction z) :=
    continuous_finsetProd _ fun χ hχ ↦
      (DirichletCharacter.differentiable_LFunction
        (mt χ.primitiveCharacter_eq_one_iff.mp (Finset.mem_filter.mp hχ).2)).continuous
  have hL : Tendsto
      (fun s : ℝ ↦ ∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction s)
      (𝓝[>] 1)
      (𝓝 (∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction 1)) :=
    ((hcont.comp Complex.continuous_ofReal).tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction 1)) := by
    refine (one_mul
      (∏ χ : DirichletCharacter ℂ n with χ ≠ 1, χ.primitiveCharacter.LFunction 1) ▸
      hζ.mul hL).congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)
    dsimp only
    rw [dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter (n := n) (s := s)
      (by simpa using hs), mul_assoc]
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hF

end Global

end TauCeti.NumberField
