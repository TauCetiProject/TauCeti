/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Estimates
public import TauCeti.NumberTheory.ArithmeticDirichletSeries.EulerProduct.Logarithm.VonMangoldtCoeff
public import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Orthogonality
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# The Frobenius von Mangoldt series as a character sum of logarithmic derivatives

Let `L / K` be a finite **abelian** Galois extension of number fields with group `G`, and fix
`σ ∈ G`. For each character `χ : G →* ℂˣ` let `L_χ` be the `L`-series of the Galois character
weight `MonoidHom.galoisCharacterWeight χ`, whose Euler product omits the primes ramified in `L`.
This file proves, for `Re s > 1`,

```text
∑_{𝔭 unramified, m ≥ 1, Frob(𝔭)^m = σ} log N𝔭 · N𝔭^{-ms}
  = (1 / #G) ∑_χ χ(σ)⁻¹ · (-L_χ'(s) / L_χ(s)).
```

The left-hand side is the `LSeries` of the canonical coefficient
`NumberField.Chebotarev.frobeniusVonMangoldtCoeff`, so the identity is a theorem about that
coefficient rather than a hypothesis on an arbitrary sequence. It reduces the
Frobenius-restricted von Mangoldt series to the logarithmic derivatives of the one-dimensional
character series, which is the form the Tauberian step of the Chebotarev argument consumes.

The proof is termwise. By
`TauCeti.MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform` each
`-L_χ'/L_χ` is the ideal-indexed series of `χ(A) Λ(A)`. At a prime power `A = 𝔭 ^ m` the
weight is `χ(Frob 𝔭) ^ m = χ(Frob(𝔭) ^ m)` when `𝔭` is unramified and `0` otherwise, and
character orthogonality
(`AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified`) collapses the character
sum at `A` to `#G` times the indicator of `Frob(𝔭) ^ m = σ`. That indicator is exactly the powered
filter of `frobeniusVonMangoldtWeight`, since in an abelian group the class of `Frob(𝔭) ^ m` is
`{σ}` precisely when `Frob(𝔭) ^ m = σ`.

## Main results

* `NumberField.Chebotarev.sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply`: the
  character sum of the von Mangoldt transforms at one nonzero ideal is `#G` times the Frobenius
  von Mangoldt weight of `σ` there.
* `NumberField.Chebotarev.LSeriesSummable_frobeniusVonMangoldtCoeff`: the Frobenius von Mangoldt
  series converges absolutely on `Re s > 1`, for an arbitrary conjugacy class.
* `NumberField.Chebotarev.LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv`: the character
  expansion of the Frobenius von Mangoldt series.

## Implementation notes

The inverse sits on the tag `σ`, never on the Frobenius argument. Writing `χ σ` for `(χ σ)⁻¹`, or
`χ (Frob 𝔭)⁻¹` for `χ (Frob 𝔭)`, replaces the fibre of `σ` by the fibre of `σ⁻¹`.

The prime-power filter uses the power of the Frobenius, not the Frobenius itself: the term at
`𝔭 ^ m` is counted when `Frob(𝔭) ^ m = σ`, even if `Frob 𝔭 ≠ σ`. This is what
`frobeniusVonMangoldtWeight` records and what the orthogonality at the `m`-th power of the weight
produces, so no separate bookkeeping of the higher prime powers is needed here.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
-/

public section

namespace NumberField.Chebotarev

open TauCeti
open scoped nonZeroDivisors NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

open scoped Classical IsMulCommutative in
/-- **Character orthogonality for the von Mangoldt transforms.** For `L / K` abelian and `σ` in its
Galois group, summing `(χ σ)⁻¹` against the von Mangoldt transform of the Galois character weight
at a nonzero ideal `I` gives `#Gal(L/K)` times the Frobenius von Mangoldt weight of `σ` at `I`.

At `I = 𝔭 ^ m` with `𝔭` unramified this is `#Gal(L/K) · log N𝔭` when `Frob(𝔭) ^ m = σ` and `0`
otherwise; at a ramified prime power, and away from the prime powers, both sides vanish. -/
theorem sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply
    [IsMulCommutative (L ≃ₐ[K] L)] (σ : L ≃ₐ[K] L) (I : (Ideal (𝓞 K))⁰) :
    ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
        (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
          I =
      (Nat.card (L ≃ₐ[K] L) : ℂ) * (frobeniusVonMangoldtWeight K L (ConjClasses.mk σ) I : ℂ) := by
  by_cases hI : IsPrimePow (I : Ideal (𝓞 K))
  swap
  · simp only [IdealArithmeticFunction.vonMangoldtTransform_apply,
      IdealArithmeticFunction.vonMangoldt_eq_zero_of_not_isPrimePow hI, mul_zero,
      Finset.sum_const_zero, frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow _ hI,
      Complex.ofReal_zero]
  set A : IdealPrimePower K := ⟨I, hI⟩
  have hA : (A : (Ideal (𝓞 K))⁰) = I := rfl
  have hpow := primePowerBase_pow_primePowerExponent A
  have hm := primePowerExponent_pos A
  have hterm : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ,
      (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
          I =
        MonoidHom.galoisCharacterWeight (L := L) χ (primePowerBase A).asIdeal ^
            primePowerExponent A * (primePowerWeight A : ℂ) := fun χ ↦ by
    rw [IdealArithmeticFunction.vonMangoldtTransform_apply, ← hA, vonMangoldt_eq_primePowerWeight,
      MultiplicativeIdealWeight.toIdealArithmeticFunction_apply, ← hpow, map_pow]
  simp only [hterm, ← mul_assoc, ← Finset.sum_mul]
  rw [← hA, frobeniusVonMangoldtWeight_idealPrimePower]
  by_cases hur : ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver (primePowerBase A).asIdeal],
      Algebra.IsUnramifiedAt (𝓞 K) Q
  · have : (primePowerBase A).asIdeal.IsMaximal := (primePowerBase A).isMaximal
    rw [AlgEquiv.sum_inv_mul_galoisCharacterWeight_pow_apply_of_unramified σ _ hur]
    have hmem : A ∈ frobeniusPrimePowerSet K L (ConjClasses.mk σ) ↔
        (artinSymbol (L := L) (primePowerBase A).asIdeal hur).out ^ primePowerExponent A = σ := by
      have hout : ConjClasses.mk (artinSymbol (L := L) (primePowerBase A).asIdeal hur).out =
          artinSymbol (L := L) (primePowerBase A).asIdeal hur := Quotient.out_eq' _
      rw [mem_frobeniusPrimePowerSet_iff_artinSymbol_pow_eq hur, ← hout, ConjClasses.mk_pow,
        ConjClasses.mk_eq_mk_iff_isConj, isConj_iff_eq, hout]
    split_ifs with h
    · rw [frobeniusPrimePowerWeight_of_mem (hmem.mpr h)]
    · rw [frobeniusPrimePowerWeight_of_notMem (mt hmem.mp h), zero_mul, Complex.ofReal_zero,
        mul_zero]
  · have hram : primePowerBase A ∈ ramifiedPrimes K L :=
      (mem_ramifiedPrimes_iff (L := L) _).mpr hur
    have hnot : A ∉ frobeniusPrimePowerSet K L (ConjClasses.mk σ) := fun h ↦
      hur (mem_frobeniusPrimePowerSet_iff.mp h).1
    simp only [(MonoidHom.galoisCharacterWeight_apply_eq_zero_iff _ _).mpr hram,
      zero_pow hm.ne', mul_zero, Finset.sum_const_zero, zero_mul,
      frobeniusPrimePowerWeight_of_notMem hnot, Complex.ofReal_zero]

/-- The regrouped coefficients of the Frobenius von Mangoldt ideal weight are the Frobenius von
Mangoldt coefficients. -/
private theorem normCoeff_frobeniusVonMangoldtWeight (C : ConjClasses (L ≃ₐ[K] L)) (n : ℕ) :
    normCoeff K (fun I ↦ (frobeniusVonMangoldtWeight K L C I : ℂ)) n =
      (frobeniusVonMangoldtCoeff K L C n : ℂ) := by
  rw [normCoeff_eq_sum_normFiber, frobeniusVonMangoldtCoeff_apply, Complex.ofReal_sum]

/-- The Frobenius von Mangoldt ideal weight is bounded by the logarithm of the absolute norm. -/
private theorem norm_frobeniusVonMangoldtWeight_le (C : ConjClasses (L ≃ₐ[K] L))
    (I : (Ideal (𝓞 K))⁰) :
    ‖(frobeniusVonMangoldtWeight K L C I : ℂ)‖ ≤
      ‖(IdealArithmeticFunction.vonMangoldt : IdealArithmeticFunction K) I‖ := by
  by_cases hI : IsPrimePow (I : Ideal (𝓞 K))
  · set A : IdealPrimePower K := ⟨I, hI⟩
    have hA : (A : (Ideal (𝓞 K))⁰) = I := rfl
    rw [← hA, vonMangoldt_eq_primePowerWeight, frobeniusVonMangoldtWeight_idealPrimePower,
      Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg (frobeniusPrimePowerWeight_nonneg C A),
      Real.norm_of_nonneg (primePowerWeight_nonneg A)]
    exact frobeniusPrimePowerWeight_le C A
  · rw [frobeniusVonMangoldtWeight_eq_zero_of_not_isPrimePow C hI, Complex.ofReal_zero,
      norm_zero]
    exact norm_nonneg _

/-- The ideal-indexed Dirichlet series of the Frobenius von Mangoldt weight converges absolutely
on `Re s > 1`. -/
private theorem summable_idealTerm_frobeniusVonMangoldtWeight (C : ConjClasses (L ≃ₐ[K] L))
    {s : ℂ} (hs : 1 < s.re) :
    Summable (idealTerm K (fun I ↦ (frobeniusVonMangoldtWeight K L C I : ℂ)) s) := by
  have hΛ := IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform
    (idealAbscissaOfAbsConv_lt_re_of_bounded (f := (1 : IdealArithmeticFunction K)) (C := 1)
      (fun I ↦ by simp) hs)
  rw [IdealArithmeticFunction.vonMangoldtTransform_one] at hΛ
  refine hΛ.norm.of_norm_bounded fun I ↦ ?_
  rw [norm_idealTerm, norm_idealTerm]
  gcongr
  exact norm_frobeniusVonMangoldtWeight_le C I

/-- **The Frobenius von Mangoldt series converges absolutely on `Re s > 1`.** Its coefficients are
dominated termwise, ideal by ideal, by the von Mangoldt function of `K`. -/
theorem LSeriesSummable_frobeniusVonMangoldtCoeff (C : ConjClasses (L ≃ₐ[K] L)) {s : ℂ}
    (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ (frobeniusVonMangoldtCoeff K L C n : ℂ)) s := by
  have h := LSeriesSummable_normCoeff K (summable_idealTerm_frobeniusVonMangoldtWeight C hs)
  rwa [funext (normCoeff_frobeniusVonMangoldtWeight C)] at h

open scoped IsMulCommutative in
/-- **The character expansion of the Frobenius von Mangoldt series.** For `L / K` abelian with
group `G`, `σ ∈ G` and `Re s > 1`,

```text
∑ n, Λ_σ(n) n^{-s} = (1 / #G) ∑_χ χ(σ)⁻¹ · (-L_χ'(s) / L_χ(s)),
```

where `Λ_σ` is `frobeniusVonMangoldtCoeff K L (ConjClasses.mk σ)` and `L_χ` is the `L`-series of
`MonoidHom.galoisCharacterWeight χ`, whose Euler product omits the ramified primes.

The inverse sits on the tag `σ`: with `χ σ` in its place the left-hand side would be the series of
the fibre of `σ⁻¹`. -/
theorem LSeries_frobeniusVonMangoldtCoeff_eq_sum_logDeriv [IsMulCommutative (L ≃ₐ[K] L)]
    (σ : L ≃ₐ[K] L) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun n ↦ (frobeniusVonMangoldtCoeff K L (ConjClasses.mk σ) n : ℂ)) s =
      (Nat.card (L ≃ₐ[K] L) : ℂ)⁻¹ * ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
        -logDeriv (LSeries (normCoeff K
          (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction)) s := by
  have hcard : (Nat.card (L ≃ₐ[K] L) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have habs : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, idealAbscissaOfAbsConv K
      (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction < s.re := fun χ ↦
    idealAbscissaOfAbsConv_lt_re_of_bounded (C := 1) (fun I ↦ by
      simpa using (MonoidHom.galoisCharacterUnitaryWeight (L := L) χ).norm_le_one I) hs
  have hsum : ∀ χ : (L ≃ₐ[K] L) →* ℂˣ, Summable (idealTerm K
      (MonoidHom.galoisCharacterWeight (L := L) χ).toIdealArithmeticFunction.vonMangoldtTransform
        s) :=
    fun χ ↦ IdealArithmeticFunction.summable_idealTerm_vonMangoldtTransform (habs χ)
  have hterm : ∀ I : (Ideal (𝓞 K))⁰,
      idealTerm K (fun I ↦ (frobeniusVonMangoldtWeight K L (ConjClasses.mk σ) I : ℂ)) s I =
        (Nat.card (L ≃ₐ[K] L) : ℂ)⁻¹ * ∑ χ : (L ≃ₐ[K] L) →* ℂˣ, (((χ σ)⁻¹ : ℂˣ) : ℂ) *
          idealTerm K (MonoidHom.galoisCharacterWeight (L := L)
            χ).toIdealArithmeticFunction.vonMangoldtTransform s I := fun I ↦ by
    simp only [idealTerm_def, ← mul_div_assoc, ← Finset.sum_div,
      sum_inv_mul_vonMangoldtTransform_galoisCharacterWeight_apply, inv_mul_cancel_left₀ hcard]
  rw [← funext (normCoeff_frobeniusVonMangoldtWeight (ConjClasses.mk σ)),
    LSeries_normCoeff K (summable_idealTerm_frobeniusVonMangoldtWeight _ hs), tsum_congr hterm,
    tsum_mul_left, Summable.tsum_finsetSum fun χ _ ↦ (hsum χ).mul_left _]
  congr 1
  refine Finset.sum_congr rfl fun χ _ ↦ ?_
  rw [tsum_mul_left, MultiplicativeIdealWeight.logDeriv_LSeries_eq_neg_tsum_vonMangoldtTransform _
    (habs χ), neg_neg]

end NumberField.Chebotarev
