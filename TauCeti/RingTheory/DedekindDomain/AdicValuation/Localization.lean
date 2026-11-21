/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Completion
public import TauCeti.RingTheory.DedekindDomain.LocalizationAtPrime

/-!
# A local ring inside the completed integer ring

Let `R` be a Dedekind domain with fraction field `K`, and let `v` be a height-one prime of `R`.
The canonical map from `R` to the ring of integers `𝒪_v` of `K_v` sends every element outside
`v` to a unit. It therefore extends uniquely to a map

```text
R_v → 𝒪_v.
```

This file names that map, records its compatibility with the map from `R` and the embeddings into
`K_v`, and proves that it is injective with dense range, reflects integrality from `K_v` to `K`,
and preserves and reflects divisibility and uniformizers. Thus the local ring `R_v` is the canonical
dense subring of the completed discrete valuation ring `𝒪_v`.

## Main definitions

* `IsDedekindDomain.HeightOneSpectrum.localizationToCompletionIntegers`: the canonical map
  `R_v → 𝒪_v`.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.localizationToCompletionIntegers_injective`: the map is an
  embedding.
* `IsDedekindDomain.HeightOneSpectrum.algebraMap_comp_localizationToCompletionIntegers`: `R_v → 𝒪_v`
  commutes with the embeddings into `K_v`.
* `IsDedekindDomain.HeightOneSpectrum.isInteger_adicCompletionIntegers_algebraMap_iff`: an element
  of `K` lies in `𝒪_v` inside `K_v` if and only if it lies in `R_v` inside `K`.
* `IsDedekindDomain.HeightOneSpectrum.localizationToCompletionIntegers_dvd_iff` and
  `IsDedekindDomain.HeightOneSpectrum.irreducible_localizationToCompletionIntegers_iff`: `R_v → 𝒪_v`
  preserves and reflects divisibility and irreducibility.
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
    (Ideal.mem_primeCompl_iff.mp y.property) <| by
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

/-- The canonical map `R_v → 𝒪_v` commutes with the embeddings of `R_v` and `𝒪_v` into `K_v`. -/
theorem algebraMap_comp_localizationToCompletionIntegers (v : HeightOneSpectrum R) :
    (algebraMap (v.adicCompletionIntegers K) (v.adicCompletion K)).comp
        (v.localizationToCompletionIntegers (K := K)) =
      (algebraMap K (v.adicCompletion K)).comp
        (algebraMap (Localization.AtPrime v.asIdeal) K) := by
  refine IsLocalization.ringHom_ext v.asIdeal.primeCompl (RingHom.ext fun x ↦ ?_)
  simp only [RingHom.comp_apply, localizationToCompletionIntegers_algebraMap,
    ← IsScalarTower.algebraMap_apply R (Localization.AtPrime v.asIdeal) K]
  exact IsScalarTower.algebraMap_apply R (v.adicCompletionIntegers K) (v.adicCompletion K) x

/-- An element of `K` lies in `𝒪_v` inside `K_v` if and only if it lies in `R_v` inside `K`. -/
theorem isInteger_adicCompletionIntegers_algebraMap_iff (v : HeightOneSpectrum R) (a : K) :
    IsLocalization.IsInteger (v.adicCompletionIntegers K)
        (algebraMap K (v.adicCompletion K) a) ↔
      IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) a := by
  have hv₁ := adicCompletionIntegers.integers K v
  have hv₂ := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := K)
  have h₁ : IsLocalization.IsInteger (v.adicCompletionIntegers K)
        (algebraMap K (v.adicCompletion K) a) ↔
      Valued.v (algebraMap K (v.adicCompletion K) a) ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hv₁.map_le_one r, fun h ↦ hv₁.exists_of_le_one h⟩
  have h₂ : IsLocalization.IsInteger (Localization.AtPrime v.asIdeal) a ↔
      v.valuation K a ≤ 1 :=
    ⟨fun ⟨r, hr⟩ ↦ hr ▸ hv₂.map_le_one r, fun h ↦ hv₂.exists_of_le_one h⟩
  rw [h₁, h₂, algebraMap_adicCompletion, Function.comp_apply,
    valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply]

/-- The canonical map `R_v → 𝒪_v` preserves and reflects divisibility. -/
@[simp]
theorem localizationToCompletionIntegers_dvd_iff (v : HeightOneSpectrum R)
    {x y : Localization.AtPrime v.asIdeal} :
    v.localizationToCompletionIntegers (K := K) x ∣
        v.localizationToCompletionIntegers (K := K) y ↔
      x ∣ y := by
  have hv₁ := adicCompletionIntegers.integers K v
  have hv₂ := v.integers_valuation_of_isLocalizationAtPrime
    (Localization.AtPrime v.asIdeal) (K := K)
  have hx := RingHom.congr_fun (v.algebraMap_comp_localizationToCompletionIntegers (K := K)) x
  have hy := RingHom.congr_fun (v.algebraMap_comp_localizationToCompletionIntegers (K := K)) y
  simp only [RingHom.comp_apply] at hx hy
  rw [hv₁.dvd_iff_le, hv₂.dvd_iff_le, hx, hy, algebraMap_adicCompletion,
    Function.comp_apply, Function.comp_apply, valuedAdicCompletion_eq_valuation',
    valuedAdicCompletion_eq_valuation', Algebra.algebraMap_self_apply,
    Algebra.algebraMap_self_apply]

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
    exact (Ideal.mem_primeCompl_iff.mp y.property) (this ▸ v.asIdeal.zero_mem)
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

/-- The canonical map `R_v → 𝒪_v` preserves and reflects irreducibility (uniformizers). -/
@[simp]
theorem irreducible_localizationToCompletionIntegers_iff (v : HeightOneSpectrum R)
    {ϖ : Localization.AtPrime v.asIdeal} :
    Irreducible (v.localizationToCompletionIntegers (K := K) ϖ) ↔ Irreducible ϖ := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible (Localization.AtPrime v.asIdeal)
  have hπ' : Irreducible (v.localizationToCompletionIntegers (K := K) π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, ← Set.image_singleton,
      ← Ideal.map_span, ← hπ.maximalIdeal_eq, v.maximalIdeal_map_completion]
  rw [IsDiscreteValuationRing.irreducible_iff_uniformizer, hπ'.maximalIdeal_eq,
    IsDiscreteValuationRing.irreducible_iff_uniformizer, hπ.maximalIdeal_eq,
    eq_comm, Ideal.span_singleton_eq_span_singleton,
    eq_comm, Ideal.span_singleton_eq_span_singleton,
    ← dvd_dvd_iff_associated, ← dvd_dvd_iff_associated,
    v.localizationToCompletionIntegers_dvd_iff, v.localizationToCompletionIntegers_dvd_iff]

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
