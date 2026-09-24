/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.Localization.AtPrime

/-!
# A local ring inside the completed integer ring

Let `R` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `R`.
The canonical map from `R` to the ring of integers `𝒪_v` of `K_v` sends every element outside
`v` to a unit. It therefore extends uniquely to a map

```text
R_v → 𝒪_v.
```

This file names that map, records its compatibility with the map from `R`, and proves that it is
injective with dense range. Thus the local ring `R_v` is the canonical dense
subring of the completed discrete valuation ring `𝒪_v`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.localizationToCompletionIntegers`: the canonical map
  `R_v → 𝒪_v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.localizationToCompletionIntegers_injective`: the map is an
  embedding.
* `IsDedekindDomain.HeightOneSpectrum.denseRange_localizationToCompletionIntegers`: its range is
  dense in `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.maximalIdeal_map_completion`: its maximal ideal generates
  the maximal ideal of `𝒪_v`.
* `IsDedekindDomain.HeightOneSpectrum.maximalIdeal_pow_map_completion`: the same is true for
  every power of the maximal ideal.

## References

* [J. Neukirch, *Algebraic Number Theory*][Neukirch1992], Chapter II, §4.
-/

public section
noncomputable section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

/-- The canonical map from the localization `R_v` into the ring of integers of the completion
`K_v`. Its construction uses that every denominator in `R \ v` maps to a unit of `𝒪_v`. -/
noncomputable def localizationToCompletionIntegers (v : HeightOneSpectrum R) :
    Localization.AtPrime v.asIdeal →+* v.adicCompletionIntegers K :=
  IsLocalization.lift (M := v.asIdeal.primeCompl)
    (g := algebraMap R (v.adicCompletionIntegers K)) fun y ↦
    IsLocalRing.notMem_maximalIdeal.mp fun hy ↦
    (Ideal.mem_primeCompl_iff.mp y.2) <| by
      have hunder : (y : R) ∈
          (IsLocalRing.maximalIdeal (v.adicCompletionIntegers K)).under R := hy
      rw [v.under_maximalIdeal_adicCompletionIntegers (K := K)] at hunder
      exact hunder

/-- The map `R_v → 𝒪_v` extends the canonical map from `R`. -/
@[simp]
theorem localizationToCompletionIntegers_algebraMap (v : HeightOneSpectrum R) (x : R) :
    v.localizationToCompletionIntegers (K := K)
        (algebraMap R (Localization.AtPrime v.asIdeal) x) =
      algebraMap R (v.adicCompletionIntegers K) x :=
  by simp [localizationToCompletionIntegers]

/-- The map `R_v → 𝒪_v` sends a fraction to its numerator times the inverse of its denominator. -/
@[simp]
theorem localizationToCompletionIntegers_mk' (v : HeightOneSpectrum R) (x : R)
    (y : v.asIdeal.primeCompl) :
    (v.localizationToCompletionIntegers (K := K)
        (IsLocalization.mk' (Localization.AtPrime v.asIdeal) x y) : v.adicCompletion K) =
      (algebraMap R (v.adicCompletionIntegers K) x : v.adicCompletion K) *
        (algebraMap R (v.adicCompletionIntegers K) y : v.adicCompletion K)⁻¹ := by
  have hy : (algebraMap R (v.adicCompletionIntegers K) y : v.adicCompletion K) ≠ 0 := by
    intro hy
    have hy' : algebraMap R (v.adicCompletionIntegers K) y = 0 := Subtype.ext hy
    have : (y : R) = 0 :=
      (FaithfulSMul.algebraMap_injective R (v.adicCompletionIntegers K)) (by simpa using hy')
    exact (Ideal.mem_primeCompl_iff.mp y.2) (this ▸ v.asIdeal.zero_mem)
  apply (eq_mul_inv_iff_mul_eq₀ hy).2
  have h := congrArg (v.localizationToCompletionIntegers (K := K))
    (IsLocalization.mk'_spec (Localization.AtPrime v.asIdeal) x y)
  simp only [map_mul, localizationToCompletionIntegers_algebraMap] at h
  exact congrArg Subtype.val h

/-- The canonical map `R_v → 𝒪_v` is injective. -/
theorem localizationToCompletionIntegers_injective (v : HeightOneSpectrum R) :
    Function.Injective (v.localizationToCompletionIntegers (K := K)) := by
  rw [localizationToCompletionIntegers, IsLocalization.lift_injective_iff]
  intro x y
  constructor
  · intro hxy
    exact congrArg (algebraMap R (v.adicCompletionIntegers K))
      (IsLocalization.injective (Localization.AtPrime v.asIdeal)
        v.asIdeal.primeCompl_le_nonZeroDivisors hxy)
  · intro hxy
    exact congrArg (algebraMap R (Localization.AtPrime v.asIdeal))
      (FaithfulSMul.algebraMap_injective R (v.adicCompletionIntegers K) hxy)

/-- The maximal ideal of `R_v` generates the maximal ideal of `𝒪_v`. -/
@[simp]
theorem maximalIdeal_map_completion (v : HeightOneSpectrum R) :
    Ideal.map (v.localizationToCompletionIntegers (K := K))
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal)) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) := by
  rw [← IsLocalization.AtPrime.map_eq_maximalIdeal v.asIdeal,
    Ideal.map_map]
  have hcomp :
      (v.localizationToCompletionIntegers (K := K)).comp
          (algebraMap R (Localization.AtPrime v.asIdeal)) =
        algebraMap R (v.adicCompletionIntegers K) := by
    ext x : 1
    exact v.localizationToCompletionIntegers_algebraMap (K := K) x
  rw [hcomp]
  exact v.map_asIdeal_adicCompletionIntegers (K := K)

/-- Every power of the maximal ideal of `R_v` generates the corresponding power of the maximal
ideal of `𝒪_v`. -/
@[simp]
theorem maximalIdeal_pow_map_completion (v : HeightOneSpectrum R) (n : ℕ) :
    Ideal.map (v.localizationToCompletionIntegers (K := K))
        (IsLocalRing.maximalIdeal (Localization.AtPrime v.asIdeal) ^ n) =
      IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ^ n := by
  rw [Ideal.map_pow, v.maximalIdeal_map_completion]

/-- The localization `R_v` is dense in the completed integer ring `𝒪_v`. -/
theorem denseRange_localizationToCompletionIntegers (v : HeightOneSpectrum R) :
    DenseRange (v.localizationToCompletionIntegers (K := K)) := by
  apply DenseRange.of_comp
    (g := algebraMap R (Localization.AtPrime v.asIdeal))
  have hcomp :
      (v.localizationToCompletionIntegers (K := K) : _ → _) ∘
          (algebraMap R (Localization.AtPrime v.asIdeal) : R → _) =
        (algebraMap R (v.adicCompletionIntegers K) : R → _) := by
    funext x
    exact v.localizationToCompletionIntegers_algebraMap (K := K) x
  rw [hcomp]
  exact v.denseRange_algebraMap_adicCompletionIntegers (K := K)

end IsDedekindDomain.HeightOneSpectrum

end

end
