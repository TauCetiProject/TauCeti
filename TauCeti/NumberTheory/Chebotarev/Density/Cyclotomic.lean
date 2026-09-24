/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.DirichletDensity
public import TauCeti.NumberTheory.Chebotarev.FrobeniusPrimeSet
import TauCeti.Analysis.SpecialFunctions.Log.OneDivSub
import TauCeti.NumberTheory.ArithmeticDirichletSeries.Prime.IdealZetaSum
import TauCeti.NumberTheory.Chebotarev.Density.Ramification
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.PrimeSum
import TauCeti.NumberTheory.Chebotarev.GaloisCharacter.Series

/-!
# Chebotarev density for cyclotomic extensions

Let `F = K(μ_m)` be a cyclotomic extension of the number field `K`. For every `σ ∈ Gal(F/K)`,
the primes of `𝓞 K` whose Frobenius is `σ` have Dirichlet density `1 / #Gal(F/K)`.

## Main results

* `NumberField.Chebotarev.hasDirichletDensity_cyclotomicFrobenius`: the Frobenius fibre of any
  `σ ∈ Gal(K(μ_m)/K)` has Dirichlet density `1 / #Gal(K(μ_m)/K)`.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* The same character-orthogonality argument is formalized as `Chebotarev.chebotarev_cyclotomic`
  in AINTLIB, <https://github.com/CBirkbeck/aintlib> (Apache-2.0), commit
  `8102fa09bbf570f3e991adfdb2d6d70b48cb5b5e`, file
  `projects/Chebotarev/CebotarevDensity/Cyclotomic.lean`.
-/

open Filter IsDedekindDomain NumberField TauCeti
open scoped NumberField nonZeroDivisors Topology

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

open scoped Classical in
-- The normalized prime sum of a character tends to `1` for the trivial character, whose primes are
-- the unramified ones, and to `0` for the others, whose prime sums stay bounded.
private theorem tendsto_primeSum_galoisCharacterWeight_div_log (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (χ : (F ≃ₐ[K] F) →* ℂˣ) :
    Tendsto (fun t : ℝ ↦ (MonoidHom.galoisCharacterWeight (L := F) χ).primeSum t /
      (Real.log (1 / (t - 1)) : ℂ)) (𝓝[>] 1) (𝓝 (if χ = 1 then 1 else 0)) := by
  split_ifs with hχ
  · subst hχ
    refine ((Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one _ _).mp
      (hasDirichletDensity_compl_ramifiedPrimes K F)).ofReal.congr fun t ↦ ?_
    rw [MonoidHom.primeSum_galoisCharacterWeight_one, Complex.ofReal_div]
  · have hℓ := Real.tendsto_log_one_div_sub_atTop 1
    obtain ⟨B, hB⟩ := MultiplicativeIdealWeight.exists_norm_primeSum_le
      (MonoidHom.norm_galoisCharacterWeight_le_one χ)
      (cyclotomicCharacterSeriesC_analyticAt_one K F m χ hχ)
      (cyclotomicCharacterSeriesC_ne_zero_at_one K F m χ hχ)
      fun _ ↦ cyclotomicCharacterSeriesC_eq_LSeries K F χ
    refine squeeze_zero_norm' ?_ ((tendsto_const_nhds (x := B)).div_atTop hℓ)
    filter_upwards [hB, hℓ.eventually_gt_atTop 0] with t hBt hℓt
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg hℓt.le]
    gcongr

end NumberField.Chebotarev

public section

namespace NumberField.Chebotarev

variable (K F : Type*) [Field K] [NumberField K] [Field F] [NumberField F] [Algebra K F]
  [IsGalois K F]

/-- **Chebotarev density for cyclotomic extensions.** For `F = K(μ_m)` and any `σ ∈ Gal(F/K)`,
the primes of `𝓞 K` whose Frobenius in `F` is `σ` have Dirichlet density `1 / #Gal(F/K)`. -/
theorem hasDirichletDensity_cyclotomicFrobenius (m : ℕ) [NeZero m]
    [IsCyclotomicExtension {m} K F] (σ : F ≃ₐ[K] F) :
    NumberField.Set.HasDirichletDensity (frobeniusPrimeSet K F (ConjClasses.mk σ))
      (1 / (Nat.card (F ≃ₐ[K] F) : ℝ)) := by
  classical
  have := IsCyclotomicExtension.isMulCommutative {m} K F
  rw [Set.hasDirichletDensity_iff_tendsto_div_log_one_div_sub_one, ← tendsto_ofReal_iff]
  -- Summed against `(χ σ)⁻¹`, only the trivial character's normalized prime sum survives.
  convert ((tendsto_finsetSum Finset.univ fun χ _ ↦
    (tendsto_primeSum_galoisCharacterWeight_div_log K F m χ).const_mul
      (((χ σ)⁻¹ : ℂˣ) : ℂ)).const_mul (1 / (Nat.card (F ≃ₐ[K] F) : ℂ))).congr' ?_ using 2
  · simp
  filter_upwards [self_mem_nhdsWithin] with t (ht : 1 < t)
  simp only [mul_div_assoc', ← Finset.sum_div,
    ← σ.natCard_mul_primeIdealZetaSum_frobeniusPrimeSet ht]
  simp

end NumberField.Chebotarev
