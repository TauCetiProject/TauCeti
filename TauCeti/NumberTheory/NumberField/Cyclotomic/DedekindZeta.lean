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
import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.BellSeries
import TauCeti.NumberTheory.DirichletCharacter.ArithmeticFunction
import TauCeti.NumberTheory.DirichletCharacter.BellSeries
import TauCeti.NumberTheory.DirichletCharacter.LFunction.ChangeLevel
import TauCeti.NumberTheory.LSeries.Convolution
import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import TauCeti.NumberTheory.NumberField.DedekindZeta.Residue

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
of `𝓞 K` above `p`, each of inertia degree `f`, so by
`TauCeti.IdealArithmeticFunction.bellSeries_normCoeff_one_mul_prod_one_sub_X_pow` the Bell series of
`normCoeff K 1` at `p` is the formal inverse of `(1 - X ^ f) ^ g`. On the character side,
`DirichletCharacter.bellSeries_prod_toArithmeticFunction_primitiveCharacter_mul_pow_one_sub` shows
that the character-product Bell series is also the formal inverse of `(1 - X ^ f) ^ g`. Since both
Bell series multiply with `(1 - X ^ f) ^ g` to `1`, they coincide. This proof handles all levels
`n ≠ 0` uniformly, including ramified primes and levels `n ≡ 2 mod 4`.

## Main results

* `TauCeti.NumberField.normCoeff_one_eq_prod_toArithmeticFunction_primitiveCharacter`: the
  ideal-counting coefficients of `ζ_K` equal the Dirichlet convolution of the primitive characters
  inducing the characters modulo `n`.
* `TauCeti.NumberField.dedekindZetaCoeff_eq_prod_toArithmeticFunction_primitiveCharacter_apply`:
  pointwise form for `dedekindZetaCoeff K k` (`k ≠ 0`).
* `TauCeti.NumberField.dedekindZeta_eq_prod_LFunction_primitiveCharacter`:
  `ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s` for `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter`:
  the same with the principal factor `riemannZeta s` separated.
* `TauCeti.NumberField.dedekindZeta_mul_prod_one_sub_eq_prod_LFunction`: the imprimitive level-`n`
  form on `Re s > 1`.
* `TauCeti.NumberField.dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one`:
  `(dedekindZeta_residue K : ℂ) = ∏ χ ≠ 1, χ.primitiveCharacter.LFunction 1`.

## References

* L. C. Washington, *Introduction to Cyclotomic Fields*, Theorem 4.3.
* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §10.
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
  have : Fact p.Prime := ⟨hp⟩
  have : IsGalois ℚ K := IsCyclotomicExtension.isGalois {n} ℚ K
  set m := ordCompl[p] n
  have hn_eq : n = p ^ n.factorization p * m := (Nat.ordProj_mul_ordCompl_eq_self n p).symm
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
  have hp0 : (span {(p : ℤ)} : Ideal ℤ) ≠ ⊥ := by
    simpa [Ideal.span_singleton_eq_bot] using hp.ne_zero
  -- Every prime `𝔭` above `p` in `𝓞 K` has inertia degree `f`, and there are `g` such primes.
  have hprod :
      ∏ 𝔭 ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K),
          (1 - (PowerSeries.X : PowerSeries ℂ) ^ 𝔭.inertiaDeg ℤ) =
        (1 - PowerSeries.X ^ f) ^ g := by
    have hinert : ∀ 𝔭 ∈ primesOverFinset (span {(p : ℤ)}) (𝓞 K), 𝔭.inertiaDeg ℤ = f := by
      intro 𝔭 h𝔭
      have hmem := (mem_primesOverFinset_iff hp0 (𝓞 K)).mp h𝔭
      have : 𝔭.IsPrime := hmem.1
      have : 𝔭.LiesOver (span {(p : ℤ)}) := hmem.2
      rw [← Ideal.inertiaDegIn_eq_inertiaDeg (span {(p : ℤ)}) 𝔭 (K ≃ₐ[ℚ] K)]
      exact inertiaDegIn_eq_orderOf (K := K) hn_eq hm_ndvd
    rw [Finset.prod_congr rfl fun 𝔭 h𝔭 ↦ by rw [hinert 𝔭 h𝔭], Finset.prod_const]
    congr 1
    have hmul : (primesOverFinset (span {(p : ℤ)}) (𝓞 K)).card * f = m.totient := by
      rw [← Set.ncard_coe_finset, coe_primesOverFinset hp0]
      exact ncard_primesOver_mul_orderOf_eq_totient_of_eq_pow_mul (K := K) hn_eq hm_ndvd
    exact Nat.eq_div_of_mul_eq_left hf_pos.ne' hmul
  have hzeta_inv :
      ArithmeticFunction.bellSeries p hp (normCoeff K 1) * (1 - PowerSeries.X ^ f) ^ g = 1 := by
    simpa only [hprod] using bellSeries_normCoeff_one_mul_prod_one_sub_X_pow K hp
  have hchar_inv :
      ArithmeticFunction.bellSeries p hp
        (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) *
        (1 - PowerSeries.X ^ f) ^ g = 1 :=
    DirichletCharacter.bellSeries_prod_toArithmeticFunction_primitiveCharacter_mul_pow_one_sub hp
  exact inv_unique ((mul_comm _ _).trans hzeta_inv) ((mul_comm _ _).trans hchar_inv)

end Local

/-! ### Cyclotomic factorization of `ζ_K` and its residue -/

variable (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K]

/-- **Dirichlet-coefficient factorization of `ζ_K` for a cyclotomic field.** If `K` is an `n`-th
cyclotomic field over `ℚ` (`n ≠ 0`), the ideal-counting function `normCoeff K 1` equals the
Dirichlet convolution of the primitive characters inducing the characters modulo `n`. -/
theorem normCoeff_one_eq_prod_toArithmeticFunction_primitiveCharacter :
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
theorem dedekindZetaCoeff_eq_prod_toArithmeticFunction_primitiveCharacter_apply
    {k : ℕ} (hk : k ≠ 0) :
    (dedekindZetaCoeff K k : ℂ) =
      (∏ χ : DirichletCharacter ℂ n, toArithmeticFunction (χ.primitiveCharacter ·)) k := by
  have h := congr($(normCoeff_one_eq_prod_toArithmeticFunction_primitiveCharacter K n) k)
  simpa [normCoeff_one_apply, hk] using h

/-- **Cyclotomic factorization of `ζ_K` on `Re s > 1` (primitive form).** If `K` is an `n`-th
cyclotomic field over `ℚ` (`n ≠ 0`), then for `Re s > 1`,
`ζ_K(s) = ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s`. -/
theorem dedekindZeta_eq_prod_LFunction_primitiveCharacter {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s =
      ∏ χ : DirichletCharacter ℂ n, χ.primitiveCharacter.LFunction s := by
  rw [dedekindZeta_eq_LSeries_normCoeff_one,
    normCoeff_one_eq_prod_toArithmeticFunction_primitiveCharacter K n]
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
primitive characters to level-`n` characters introduces the factors `1 - χ*(p) p^(-s)` at primes
dividing `n` on the `ζ_K` side. -/
theorem dedekindZeta_mul_prod_one_sub_eq_prod_LFunction {s : ℂ} (hs : 1 < s.re) :
    dedekindZeta K s *
        ∏ χ : DirichletCharacter ℂ n, ∏ p ∈ n.primeFactors,
          (1 - χ.primitiveCharacter (p : ZMod χ.conductor) * (p : ℂ) ^ (-s)) =
      ∏ χ : DirichletCharacter ℂ n, χ.LFunction s := by
  have hs1 : s ≠ 1 := fun h ↦ by simp [h] at hs
  rw [dedekindZeta_eq_prod_LFunction_primitiveCharacter K n hs, ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun χ _ ↦
    (DirichletCharacter.LFunction_eq_LFunction_primitiveCharacter_mul χ (.inr hs1)).symm

/-- **The residue of the Dedekind zeta function of a cyclotomic field.** For an `n`-th cyclotomic
field `K` over `ℚ` (`n ≠ 0`), Mathlib's `dedekindZeta_residue K` equals the product of
`L(1, χ.primitiveCharacter)` over all nonprincipal characters `χ` modulo `n`. -/
theorem dedekindZeta_residue_eq_prod_LFunction_primitiveCharacter_one
    [DecidableEq (DirichletCharacter ℂ n)] :
    (dedekindZeta_residue K : ℂ) =
      ∏ χ ∈ Finset.univ.erase (1 : DirichletCharacter ℂ n),
        χ.primitiveCharacter.LFunction 1 := by
  refine dedekindZeta_residue_eq_of_eventuallyEq_riemannZeta_mul K
    (eventually_nhdsWithin_of_forall fun s hs ↦
      dedekindZeta_eq_riemannZeta_mul_prod_LFunction_primitiveCharacter K n (s := s)
        (by simpa using hs)) ?_
  refine tendsto_finsetProd _ fun χ hχ ↦ ?_
  have hne : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
  exact (((DirichletCharacter.differentiable_LFunction_primitiveCharacter hne).continuous.comp
    Complex.continuous_ofReal).tendsto' 1 _ (by simp)).mono_left nhdsWithin_le_nhds

end TauCeti.NumberField
