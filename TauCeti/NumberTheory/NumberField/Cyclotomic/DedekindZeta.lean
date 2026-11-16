/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.NumberTheory.LSeries.Convolution
public import Mathlib.NumberTheory.LSeries.DirichletContinuation
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.DedekindZeta
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Trivial
public import TauCeti.NumberTheory.DirichletCharacter.Conductor
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Basic
import TauCeti.NumberTheory.ArithmeticFunction.BellSeries
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.DirichletCharacter.Primitive
import TauCeti.NumberTheory.LSeries.Convolution
import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.PrimeIdeal

/-!
# The Dedekind zeta function of a cyclotomic field

Let `K` be an `n`-th cyclotomic field over `ℚ` (`n ≠ 0`). This file proves the cyclotomic
factorization of the Dedekind zeta function of `K` at the coefficient level, on the half-plane
`Re s > 1` of absolute convergence (in both primitive and imprimitive level-`n` forms), and for
the residue at `s = 1`:

* `normCoeff K 1 = ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)`,
* `ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, L(s, χ*)` for `Re s > 1`, where
  `χ* = χ.primitiveCharacter`,
* `ζ_K(s) = ζ(s) ∏_{χ ≠ 1} L(s, χ*)` for `Re s > 1`,
* `ζ_K(s) ∏_χ ∏_{p ∣ n} (1 - χ*(p) p^(-s)) = ∏_χ L(s, χ)` for `Re s > 1`,
* `dedekindZeta_residue K = ∏_{χ ≠ 1} L(1, χ*)`.

At the coefficient level both sides are multiplicative arithmetic functions, so by
`ArithmeticFunction.IsMultiplicative.eq_iff_forall_bellSeries_eq` it suffices to equate their Bell
series at every rational prime `p`. Write `n = p ^ k * m` with `m = ordCompl[p] n`,
`f = orderOf (p : ZMod m)`, and `g = φ(m) / f`. By the cyclotomic splitting law
(`TauCeti.NumberField.inertiaDegIn_eq_orderOf`,
`TauCeti.NumberField.ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul`), there are `g` primes
of `𝓞 K` above `p`, each of norm `p ^ f`, so the Bell series of `normCoeff K 1` at `p` is the
formal inverse of `(1 - X ^ f) ^ g`. On the character side,
`DirichletCharacter.prod_one_sub_C_mul_X_primitiveCharacter` shows that the product of the
reciprocal local Euler polynomials `1 - χ*(p) X` over all `χ : DirichletCharacter ℂ n` is also
`(1 - X ^ f) ^ g`. Since both Bell series multiply with `(1 - X ^ f) ^ g` to `1`, they coincide.
This proof handles all levels `n ≠ 0` uniformly, including ramified primes and levels `n ≡ 2 mod 4`.

## Main results

* `TauCeti.NumberField.normCoeff_one_eq_prod_primitiveCharacter`: the ideal-counting coefficients
  of `ζ_K` equal the Dirichlet convolution of the primitive characters inducing the characters
  modulo `n`.
* `TauCeti.NumberField.dedekindZetaCoeff_eq_prod_primitiveCharacter`: pointwise form for
  `dedekindZetaCoeff K k` (`k ≠ 0`).
* `TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`:
  `ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s` for `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`:
  the same with the principal factor `riemannZeta s` separated.
* `TauCeti.NumberField.dedekindZeta_mul_prod_eulerFactor_eq_prod_LFunction`: the imprimitive
  level-`n` form on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one`:
  `(dedekindZeta_residue K : ℂ) = ∏ χ ≠ 1, χ.primitiveCharacter.LFunction 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, Corollary 5.11.
-/

public section

open Filter Ideal IsDedekindDomain NumberField TauCeti.IdealArithmeticFunction
open scoped NumberField Topology

namespace TauCeti.NumberField

variable (K : Type*) [Field K] [NumberField K]

/-! ### Local Bell-series comparison at a rational prime -/

section Local

variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- For every rational prime `p`, the Bell series of `normCoeff K 1` at `p` equals the Bell series
of the Dirichlet convolution of the primitive characters inducing the characters modulo `n`. -/
private theorem bellSeries_normCoeff_one_eq_bellSeries_prod_primitiveCharacter {p : ℕ}
    (hp : p.Prime) :
    ArithmeticFunction.bellSeries p hp (normCoeff K 1) =
      ArithmeticFunction.bellSeries p hp
        (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  set k := n.factorization p
  set m := ordCompl[p] n
  have hn_eq : n = p ^ k * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
  have hm_ndvd : ¬ p ∣ m := Nat.not_dvd_ordCompl hp (NeZero.ne n)
  have : NeZero m := ⟨(Nat.ordCompl_pos p (NeZero.ne n)).ne'⟩
  have hcop : p.Coprime m := Nat.coprime_ordCompl hp (NeZero.ne n)
  set f := orderOf (p : ZMod m)
  set g := m.totient / f
  have hf_pos : 0 < f := by
    have hord : orderOf (ZMod.unitOfCoprime p hcop) = f := by
      rw [← orderOf_units, ZMod.coe_unitOfCoprime]
    rw [← hord]
    exact orderOf_pos _
  -- Package the primes of `𝓞 K` lying over `p` as a `Finset (HeightOneSpectrum (𝓞 K))`.
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  set T : Finset (Ideal (𝓞 K)) := primesOverFinset (span {(p : ℤ)}) (𝓞 K)
  let toH1 : {𝔭 // 𝔭 ∈ T} → HeightOneSpectrum (𝓞 K) := fun ⟨𝔭, h𝔭⟩ ↦
    have hmem : 𝔭 ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
      rwa [← coe_primesOverFinset hp0, Finset.mem_coe]
    have : 𝔭.LiesOver (span {(p : ℤ)}) := hmem.2
    ⟨𝔭, hmem.1, ne_bot_of_liesOver_of_ne_bot hp0 𝔭⟩
  let S : Finset (HeightOneSpectrum (𝓞 K)) := T.attach.image toH1
  have hS_cover : ∀ P : HeightOneSpectrum (𝓞 K), (p : 𝓞 K) ∈ P.asIdeal → P ∈ S := by
    refine mem_of_natCast_mem_asIdeal fun P hP ↦ ?_
    have hPT : P.asIdeal ∈ T := by
      rw [← Finset.mem_coe, coe_primesOverFinset hp0]
      exact hP
    exact Finset.mem_image.mpr ⟨⟨P.asIdeal, hPT⟩, Finset.mem_attach T _, HeightOneSpectrum.ext rfl⟩
  have hS_card : S.card = g := by
    have hinj : Function.Injective toH1 := fun ⟨𝔭₁, _⟩ ⟨𝔭₂, _⟩ h ↦
      Subtype.ext (congrArg HeightOneSpectrum.asIdeal h)
    have hcardT : T.card = (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard := by
      rw [← coe_primesOverFinset hp0, Set.ncard_coe_finset]
    have hmul : T.card * f = m.totient := by
      rw [hcardT]
      exact ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := K) hn_eq hm_ndvd
    rw [Finset.card_image_of_injective _ hinj, Finset.card_attach]
    exact Nat.eq_div_of_mul_eq_left hf_pos.ne' hmul
  -- Every height-one prime in `S` has norm `p ^ f`, hence local factor `ofPowerSeries (p ^ f) 1`.
  have hlocal : ∀ P ∈ S, localArithmeticFactor (1 : IdealArithmeticFunction K) P =
      ArithmeticFunction.ofPowerSeries (p ^ f) (PowerSeries.mk 1) := by
    intro P hP
    obtain ⟨⟨𝔭, h𝔭⟩, -, rfl⟩ := Finset.mem_image.mp hP
    have hmem : 𝔭 ∈ primesOver (span {(p : ℤ)}) (𝓞 K) := by
      rwa [← coe_primesOverFinset hp0, Finset.mem_coe]
    have : 𝔭.IsPrime := hmem.1
    have : 𝔭.LiesOver (span {(p : ℤ)}) := hmem.2
    have hnorm : absNorm 𝔭 = p ^ f := by
      rw [← pow_inertiaDeg p 𝔭,
        ← Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) 𝔭 (K ≃ₐ[ℚ] K),
        inertiaDegIn_eq_orderOf (K := K) hn_eq hm_ndvd]
    rw [localArithmeticFactor_def, show (toH1 ⟨𝔭, h𝔭⟩).asIdeal = 𝔭 from rfl, hnorm]
    congr 1
    exact PowerSeries.ext fun j ↦ by simp
  -- Step 1: `bellSeries p hp (normCoeff K 1)` is the formal inverse of `(1 - X ^ f) ^ g`.
  have hzeta_inv :
      ArithmeticFunction.bellSeries p hp (normCoeff K 1) * (1 - PowerSeries.X ^ f) ^ g = 1 := by
    have hbell : ArithmeticFunction.bellSeries p hp (normCoeff K 1) =
        ArithmeticFunction.bellSeries p hp
          (∏ P ∈ S, localArithmeticFactor (1 : IdealArithmeticFunction K) P) :=
      PowerSeries.ext fun j ↦ by
        rw [ArithmeticFunction.coeff_bellSeries, ArithmeticFunction.coeff_bellSeries,
          normCoeff_apply_prime_pow_eq_prod_localArithmeticFactor
            isMultiplicative_one hp S hS_cover j]
    rw [hbell, map_prod, Finset.prod_congr rfl fun P hP ↦ congrArg _ (hlocal P hP),
      Finset.prod_const, hS_card, ← mul_pow,
      ArithmeticFunction.bellSeries_ofPowerSeries_mk_one_mul_one_sub_X_pow hp hf_pos.ne', one_pow]
  -- Step 2: the character-product Bell series is also the formal inverse of `(1 - X ^ f) ^ g`.
  have hchar_inv :
      ArithmeticFunction.bellSeries p hp
        (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) *
        (1 - PowerSeries.X ^ f) ^ g = 1 := by
    have hpoly :
        (∏ χ : DirichletCharacter ℂ n,
          (1 - PowerSeries.C (χ.primitiveCharacter (p : ZMod χ.conductor)) * PowerSeries.X)) =
          (1 - PowerSeries.X ^ f) ^ g := by
      have h := congrArg (Polynomial.coeToPowerSeries.ringHom (R := ℂ))
        (DirichletCharacter.prod_one_sub_C_mul_X_primitiveCharacter (R := ℂ) (N := n) hp)
      simpa [map_prod, map_pow, _root_.map_sub, _root_.map_one, _root_.map_mul] using h
    rw [map_prod, ← hpoly, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun χ _ ↦ ?_
    exact ArithmeticFunction.bellSeries_mul_one_sub_C_mul_X hp fun j ↦
      DirichletCharacter.toArithmeticFunction_apply_pow χ.primitiveCharacter hp.ne_zero j
  -- Two left inverses of the same element in a commutative monoid coincide.
  calc
    ArithmeticFunction.bellSeries p hp (normCoeff K 1)
      = ArithmeticFunction.bellSeries p hp (normCoeff K 1) *
          (ArithmeticFunction.bellSeries p hp
            (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) *
            (1 - PowerSeries.X ^ f) ^ g) := by rw [hchar_inv, mul_one]
    _ = ArithmeticFunction.bellSeries p hp
          (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) *
          (ArithmeticFunction.bellSeries p hp (normCoeff K 1) *
            (1 - PowerSeries.X ^ f) ^ g) := by ring
    _ = ArithmeticFunction.bellSeries p hp
          (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) := by
        rw [hzeta_inv, mul_one]

end Local

/-! ### Cyclotomic factorization of `ζ_K` and its residue -/

variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- **Dirichlet-coefficient factorization of `ζ_K` for a cyclotomic field.** If `K` is an `n`-th
cyclotomic field over `ℚ` (`n ≠ 0`), the ideal-counting function `normCoeff K 1` equals the
Dirichlet convolution of the primitive characters inducing the characters modulo `n`. -/
theorem normCoeff_one_eq_prod_primitiveCharacter :
    normCoeff K 1 =
      ∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·) := by
  have hmult : (∏ χ : DirichletCharacter ℂ n,
      toArithmeticFunction (χ.primitiveCharacter ·)).IsMultiplicative :=
    ArithmeticFunction.isMultiplicative_finsetProd _ _ fun χ _ ↦
      DirichletCharacter.isMultiplicative_toArithmeticFunction χ.primitiveCharacter
  exact (isMultiplicative_one.normCoeff.eq_iff_forall_bellSeries_eq hmult).mpr fun _ hp ↦
    bellSeries_normCoeff_one_eq_bellSeries_prod_primitiveCharacter K n hp

/-- **Pointwise coefficient factorization of `ζ_K` for a cyclotomic field.** For `k ≠ 0`, the
number `dedekindZetaCoeff K k` of integral ideals of `𝓞 K` of norm `k` equals the `k`-th
coefficient of the Dirichlet convolution of the primitive characters inducing the characters
modulo `n`. -/
theorem dedekindZetaCoeff_eq_prod_primitiveCharacter {k : ℕ} (hk : k ≠ 0) :
    (dedekindZetaCoeff K k : ℂ) =
      (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) k := by
  have h := congr($(normCoeff_one_eq_prod_primitiveCharacter K n) k)
  simpa [normCoeff_one_apply, hk] using h

/-- **Cyclotomic factorization of `ζ_K` on `Re s > 1` (primitive form).** If `K` is an `n`-th
cyclotomic field over `ℚ` (`n ≠ 0`), then for `Re s > 1`,
`ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZeta_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one, normCoeff_one_eq_prod_primitiveCharacter K n]
  exact (ArithmeticFunction.LSeriesHasSum_finsetProd
    (f := fun χ : DirichletCharacter ℂ n ↦ toArithmeticFunction (χ.primitiveCharacter ·))
    fun χ _ ↦ DirichletCharacter.LSeriesHasSum_toArithmeticFunction
      χ.primitiveCharacter hs).LSeries_eq

/-- **Cyclotomic factorization of `ζ_K` on `Re s > 1` with `ζ(s)` separated.** Separating the
principal character from the primitive-character factorization gives
`ζ_K(s) = ζ(s) * ∏ χ ≠ 1, χ.primitiveCharacter.LFunction s` on `Re s > 1`. -/
theorem dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter
    [DecidableEq (DirichletCharacter ℂ n)] {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      riemannZeta s *
        ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter K n hs,
    ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ (1 : DirichletCharacter ℂ n)),
    DirichletCharacter.LFunction_primitiveCharacter_one]

/-- **Cyclotomic factorization of `ζ_K` on `Re s > 1` (imprimitive level-`n` form).** Passing from
primitive characters to level-`n` characters introduces the missing Euler factors at primes
dividing `n` on the `ζ_K` side. -/
theorem dedekindZeta_mul_prod_eulerFactor_eq_prod_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter K n hs, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun χ _ ↦ ?_
  rw [← DirichletCharacter.LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter
    (.inr hs1), χ.changeLevel_primitiveCharacter]

/-- **The residue of the Dedekind zeta function of a cyclotomic field.** For an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`), Mathlib's `dedekindZeta_residue K` equals the product of
`L(1, χ.primitiveCharacter)` over all nonprincipal characters `χ` modulo `n`. -/
theorem dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one
    [DecidableEq (DirichletCharacter ℂ n)] :
    (dedekindZeta_residue K : ℂ) =
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1 := by
  have hζ : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * riemannZeta s) (𝓝[>] 1) (𝓝 1) :=
    riemannZeta_residue_one.comp <| tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      ((Complex.continuous_ofReal.tendsto' 1 1 Complex.ofReal_one).mono_left nhdsWithin_le_nhds)
      (eventually_nhdsWithin_of_forall fun s hs ↦ by simpa using (Set.mem_Ioi.mp hs).ne')
  have hL : Tendsto (fun s : ℝ ↦
        ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
          χ.primitiveCharacter.LFunction s)
      (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1)) := by
    refine tendsto_finsetProd _ fun χ hχ ↦ ?_
    have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    exact (((DirichletCharacter.differentiable_LFunction_primitiveCharacter hne).continuous.comp
      Complex.continuous_ofReal).tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds
  have hF : Tendsto (fun s : ℝ ↦ ((s : ℂ) - 1) * dedekindZeta K s) (𝓝[>] 1)
      (𝓝 (∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1)) := by
    refine ((hζ.mul hL).congr' (eventually_nhdsWithin_of_forall fun s hs ↦ ?_)).trans
      (by simp only [one_mul]; exact le_rfl)
    rw [dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter K n (s := s)
      (by simpa using hs), mul_assoc]
  exact tendsto_nhds_unique (tendsto_sub_one_mul_dedekindZeta_nhdsGT K) hF

end TauCeti.NumberField
