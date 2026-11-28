/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.MeasureTheory.Function.LpSeminorm.ContinuousOn
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Formal moment, free cumulant, and R-series of scalar laws and compactly supported measures

This file bridges `TauCeti.momentSeries`, `TauCeti.freeCumulantSeries`, and `TauCeti.rSeries` with
scalar laws `PositiveLinearMap.law` and compactly supported Borel probability measures on `ℝ`.

Mapping the real formal moment, free cumulant, and R-series of `id : ℝ → ℝ` under `φ.law a` into `ℂ`
recovers the series of a selfadjoint element `a`. For compactly supported probability measures on
`ℝ`, the formal R-series (equivalently, all positive-order free cumulants) uniquely determines the
measure, and for any square-integrable real random variable the linear coefficient of its formal
R-series equals its variance.

## Main definitions

* `MeasureTheory.Measure.freeCumulant`: the `n`-th free cumulant `κₙ(μ)` of a real Borel
  measure `μ`.
* `MeasureTheory.Measure.rSeries`: the formal R-series `∑_{n ≥ 0} κ_{n+1}(μ) z ^ n` of a real
  Borel measure `μ`.

## Main results

* `PositiveLinearMap.map_ofReal_momentSeries_integral_law`,
  `PositiveLinearMap.map_ofReal_freeCumulantSeries_integral_law`,
  `PositiveLinearMap.ofReal_freeCumulant_integral_law`,
  `PositiveLinearMap.ofReal_freeCumulant_law`,
  `PositiveLinearMap.map_ofReal_rSeries_law`: agreement of scalar-measure formal series and free
  cumulants of `φ.law a` with those of a selfadjoint element `a`.
* `MeasureTheory.Measure.rSeries_def`,
  `MeasureTheory.Measure.coeff_rSeries`,
  `MeasureTheory.Measure.constantCoeff_rSeries`,
  `MeasureTheory.Measure.freeCumulant_eq_coeff_freeCumulantSeries`,
  `MeasureTheory.Measure.freeCumulant_succ_eq_coeff_rSeries`,
  `MeasureTheory.Measure.freeCumulant_zero`,
  `MeasureTheory.Measure.zero_freeCumulant_succ`,
  `MeasureTheory.Measure.freeCumulant_one`,
  `MeasureTheory.Measure.freeCumulant_two_eq_variance`,
  `MeasureTheory.Measure.freeCumulant_integral_const_eq`,
  `MeasureTheory.Measure.rSeries_zero`,
  `MeasureTheory.Measure.rSeries_dirac`,
  `MeasureTheory.Measure.freeCumulant_dirac`,
  `MeasureTheory.Measure.rSeries_map_affine`,
  `MeasureTheory.Measure.freeCumulant_one_map_affine`,
  `MeasureTheory.Measure.freeCumulant_map_affine`: characterization, coefficient, special-value,
  zero-measure, Dirac, constant-word, and affine transport formulas for
  `MeasureTheory.Measure.freeCumulant` and `MeasureTheory.Measure.rSeries`.
* `MeasureTheory.Measure.ext_of_rSeries_eq`,
  `MeasureTheory.Measure.eq_iff_rSeries_eq`,
  `MeasureTheory.Measure.eq_iff_forall_freeCumulant_eq`,
  `MeasureTheory.Measure.coeff_zero_rSeries_integral`,
  `MeasureTheory.Measure.coeff_zero_rSeries`,
  `MeasureTheory.Measure.coeff_one_rSeries_integral_eq_variance`,
  `MeasureTheory.Measure.coeff_one_rSeries_eq_variance`: R-series/cumulant determinacy, mean, and
  variance.

## References

* D. Voiculescu, *Addition of certain noncommuting random variables*, J. Funct. Anal. 66 (1986),
  323–346.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Cambridge University
  Press (2006), Lectures 12 and 16.
-/

public section

noncomputable section

open Finset MeasureTheory PowerSeries ProbabilityTheory
open scoped ComplexOrder

namespace MeasureTheory.Measure

/-- The `n`-th **free cumulant** `κₙ(μ)` of a real Borel measure `μ` (`κ₀(μ) = 1`,
`κ₁(μ) = ∫ x, x ∂μ`, and `κ₂(μ) = variance id μ` for probability measures with finite second
moment). -/
def freeCumulant (μ : Measure ℝ) (n : ℕ) : ℝ :=
  TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : Fin n => (id : ℝ → ℝ)) univ

/-- The **formal R-series** `R_μ(z) = ∑_{n ≥ 0} κ_{n+1}(μ) z ^ n` of a real Borel measure `μ`. -/
def rSeries (μ : Measure ℝ) : ℝ⟦X⟧ :=
  TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id

/-- Characterization of `μ.rSeries` as the formal R-series of `id : ℝ → ℝ` under integration
against `μ`. -/
theorem rSeries_def (μ : Measure ℝ) :
    μ.rSeries = TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id := by rfl

/-- `μ.freeCumulant n` is the `n`-th coefficient of the formal free cumulant series of `μ`. -/
theorem freeCumulant_eq_coeff_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    μ.freeCumulant n =
      PowerSeries.coeff n (TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id) :=
  (TauCeti.coeff_freeCumulantSeries _ _ n).symm

/-- The `n`-th coefficient of `μ.rSeries` is `μ.freeCumulant (n + 1)`. -/
@[simp] theorem coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    PowerSeries.coeff n μ.rSeries = μ.freeCumulant (n + 1) := by
  rw [rSeries_def, TauCeti.coeff_rSeries]; rfl

/-- `μ.freeCumulant (n + 1)` is the `n`-th coefficient of the formal R-series of `μ`. -/
theorem freeCumulant_succ_eq_coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    μ.freeCumulant (n + 1) = PowerSeries.coeff n μ.rSeries :=
  (coeff_rSeries μ n).symm

/-- The zeroth free cumulant of any real Borel measure is `1`. -/
@[simp] theorem freeCumulant_zero (μ : Measure ℝ) : μ.freeCumulant 0 = 1 := by
  rw [freeCumulant_eq_coeff_freeCumulantSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    TauCeti.constantCoeff_freeCumulantSeries]

/-- Every positive-order free cumulant of the zero measure is `0`. -/
@[simp] theorem zero_freeCumulant_succ (n : ℕ) : (0 : Measure ℝ).freeCumulant (n + 1) = 0 := by
  rw [freeCumulant, TauCeti.freeCumulant_eq_sum_mu_mul_partitionMoment]
  refine Finset.sum_eq_zero fun π _ => ?_
  obtain ⟨B, hB, -⟩ := π.val.exists_mem (mem_univ (0 : Fin (n + 1)))
  simp [TauCeti.partitionMoment_def, prod_eq_zero hB]

/-- The formal R-series of the zero measure is `0`. -/
@[simp] theorem rSeries_zero : (0 : Measure ℝ).rSeries = 0 := by
  ext n
  simp

/-- The first free cumulant of any real Borel measure is its mean `∫ x, x ∂μ`. -/
@[simp] theorem freeCumulant_one (μ : Measure ℝ) : μ.freeCumulant 1 = ∫ x, x ∂μ := by
  rw [freeCumulant_eq_coeff_freeCumulantSeries, TauCeti.coeff_one_freeCumulantSeries]; rfl

/-- The constant coefficient of `μ.rSeries` is its mean `∫ x, x ∂μ`. -/
@[simp] theorem constantCoeff_rSeries (μ : Measure ℝ) :
    PowerSeries.constantCoeff μ.rSeries = ∫ x, x ∂μ := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_rSeries, Nat.zero_add,
    freeCumulant_one]

/-- The linear coefficient of the formal R-series of a square-integrable real random variable `X`
equals its variance. -/
theorem coeff_one_rSeries_integral_eq_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    PowerSeries.coeff 1 (TauCeti.rSeries (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) X) = variance X μ := by
  rw [← TauCeti.coeff_succ_freeCumulantSeries, TauCeti.coeff_two_freeCumulantSeries]
  exact (variance_eq_sub hX).symm

/-- The second free cumulant of a probability measure with finite second moment is its variance. -/
theorem freeCumulant_two_eq_variance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) : μ.freeCumulant 2 = variance id μ := by
  rw [freeCumulant_succ_eq_coeff_rSeries, rSeries_def]
  exact coeff_one_rSeries_integral_eq_variance hμ

/-- Any constant-`id` integral free cumulant along a finite linear order reduces to
`μ.freeCumulant #s`. -/
theorem freeCumulant_integral_const_eq (μ : Measure ℝ) {α : Type*} [LinearOrder α]
    (s : Finset α) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s =
      μ.freeCumulant #s := by
  rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    freeCumulant_eq_coeff_freeCumulantSeries]

/-- The formal R-series of a Dirac point mass `Measure.dirac c` is the constant series
`PowerSeries.C c`. -/
@[simp] theorem rSeries_dirac (c : ℝ) : (Measure.dirac c).rSeries = PowerSeries.C c := by
  simp [rSeries_def]

/-- All free cumulants of order `n ≥ 2` of a Dirac point mass `Measure.dirac c` vanish. -/
@[simp] theorem freeCumulant_dirac (c : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (Measure.dirac c).freeCumulant n = 0 := by
  rcases n with _ | _ | k
  · omega
  · omega
  · simp [freeCumulant_succ_eq_coeff_rSeries, PowerSeries.coeff_succ_C]

end MeasureTheory.Measure

namespace PositiveLinearMap

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A] (φ : A →ₚ[ℂ] ℂ)

/-- Mapping the real moment series of `φ.law a` into `ℂ` recovers the moment series of `a`. -/
theorem map_ofReal_momentSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.momentSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) =
      TauCeti.momentSeries φ a := by
  rw [TauCeti.map_momentSeries]; ext n
  simpa [TauCeti.coeff_momentSeries, Pi.pow_def] using φ.ofReal_integral_pow_law ha n

/-- Mapping the real free cumulant series of `φ.law a` into `ℂ` gives that of `a`. -/
theorem map_ofReal_freeCumulantSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) =
      TauCeti.freeCumulantSeries φ a := by
  rw [TauCeti.map_freeCumulantSeries]
  exact TauCeti.freeCumulantSeries_congr _ _
    ((TauCeti.map_momentSeries _ _ _).symm.trans (φ.map_ofReal_momentSeries_integral_law ha))

/-- For selfadjoint `a`, the real free cumulants of `id` under `φ.law a` match the complex free
cumulants of `a` under `φ`. -/
theorem ofReal_freeCumulant_integral_law {a : A} (ha : IsSelfAdjoint a) {α : Type*}
    [LinearOrder α] (s : Finset α) :
    ((TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a)
        (fun _ : α => (id : ℝ → ℝ)) s : ℝ) : ℂ) = TauCeti.freeCumulant φ (fun _ : α => a) s := by
  rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    ← φ.map_ofReal_freeCumulantSeries_integral_law ha, coeff_map, Complex.ofRealHom_eq_coe]

/-- For selfadjoint `a`, the `n`-th free cumulant of `φ.law a` matches `κₙ(a, …, a)` under `φ`. -/
theorem ofReal_freeCumulant_law {a : A} (ha : IsSelfAdjoint a) (n : ℕ) :
    ((φ.law a).freeCumulant n : ℂ) = TauCeti.freeCumulant φ (fun _ : Fin n => a) univ :=
  φ.ofReal_freeCumulant_integral_law ha univ

/-- Mapping the real formal R-series of `φ.law a` into `ℂ` gives the formal R-series of `a`. -/
theorem map_ofReal_rSeries_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ) (φ.law a).rSeries = TauCeti.rSeries φ a := by
  ext n
  rw [coeff_map, Measure.coeff_rSeries, TauCeti.coeff_rSeries, Complex.ofRealHom_eq_coe]
  exact φ.ofReal_freeCumulant_law ha (n + 1)

end PositiveLinearMap

namespace MeasureTheory.Measure

/-- Two compactly supported probability measures on `ℝ` with equal formal R-series coincide. -/
theorem ext_of_rSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (hr : μ.rSeries = ν.rSeries) : μ = ν := by
  have hc : TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id =
      TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
    rw [TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries,
      TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries, ← rSeries_def, ← rSeries_def, hr]
  have hm := (TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq (a := (id : ℝ → ℝ)) (by simp)
    (b := (id : ℝ → ℝ)) (by simp)).mp hc
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (hμ.union hν)
    (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left)
      (Measure.measure_compl_support (μ := μ)))
    (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_right)
      (Measure.measure_compl_support (μ := ν))) fun n => ?_
  simpa [TauCeti.coeff_momentSeries, Pi.pow_def] using congrArg (PowerSeries.coeff n) hm

/-- **R-series determinacy of compactly supported probability measures.** -/
theorem eq_iff_rSeries_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ μ.rSeries = ν.rSeries :=
  ⟨fun h => h ▸ rfl, ext_of_rSeries_eq hμ hν⟩

/-- **Free cumulant determinacy of compactly supported probability measures.** -/
theorem eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ ∀ n : ℕ, n ≠ 0 → μ.freeCumulant n = ν.freeCumulant n := by
  rw [eq_iff_rSeries_eq hμ hν, PowerSeries.ext_iff]
  refine ⟨fun h n hn => ?_, fun h n => ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa [coeff_rSeries] using h k
  · simpa [coeff_rSeries] using h (n + 1) n.succ_ne_zero

/-- The constant coefficient of the formal R-series of a real random variable `X` equals its mean
`∫ ω, X ω ∂μ`. -/
theorem coeff_zero_rSeries_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (X : Ω → ℝ) :
    PowerSeries.coeff 0 (TauCeti.rSeries (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) X) = ∫ ω, X ω ∂μ := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, TauCeti.constantCoeff_rSeries]

/-- The constant coefficient of `μ.rSeries` equals its mean `∫ x, x ∂μ`. -/
theorem coeff_zero_rSeries (μ : Measure ℝ) :
    PowerSeries.coeff 0 μ.rSeries = ∫ x, x ∂μ := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_rSeries]

/-- The linear coefficient of the formal R-series of a compactly supported probability measure
equals its variance. -/
theorem coeff_one_rSeries_eq_variance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) :
    PowerSeries.coeff 1 μ.rSeries = variance id μ := by
  rw [coeff_rSeries, freeCumulant_two_eq_variance
    (continuousOn_id.memLp_of_isCompact_support hμ support_mem_ae)]

/-- **Affine equivariance of the formal R-series of a compactly supported probability measure.**
Under `x ↦ a + b * x`, `R_{μ.map (a + b * ·)}(z) = b • rescale b R_μ(z) + C a`. -/
theorem rSeries_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) :
    (μ.map fun x => a + b * x).rSeries = b • PowerSeries.rescale b μ.rSeries + PowerSeries.C a := by
  have : CompactSpace μ.support := isCompact_iff_compactSpace.mp hμ
  let φ : C(μ.support, ℂ) →ₚ[ℂ] ℂ :=
    ContinuousMap.integralPositiveLinearMap (μ.comap ((↑) : μ.support → ℝ))
  let x : C(μ.support, ℂ) := (ContinuousMap.restrict μ.support (ContinuousMap.id ℝ)).realToRCLike ℂ
  have hφ : φ 1 = 1 :=
    ContinuousMap.integralPositiveLinearMap_comap_subtypeVal_one (Measure.measure_compl_support)
  have hx : IsSelfAdjoint x := ContinuousMap.isSelfAdjoint_realToRCLike ℂ
  have hlaw : φ.law x = μ :=
    PositiveLinearMap.law_integralPositiveLinearMap_comap_restrict_id
      (Measure.measure_compl_support)
  have haff : φ.law ((b : ℂ) • x + algebraMap ℂ _ (a : ℂ)) = μ.map fun t => a + b * t := by
    have h1 := φ.law_smul_add_algebraMap hx b a
    rw [hlaw] at h1
    refine h1.trans ?_
    congr 1; funext t; ring
  have hsa : IsSelfAdjoint ((b : ℂ) • x + algebraMap ℂ _ (a : ℂ)) := by
    simpa [Complex.coe_smul, IsScalarTower.algebraMap_apply ℝ ℂ C(μ.support, ℂ)] using
      ((IsSelfAdjoint.all b).smul hx).add (IsSelfAdjoint.algebraMap _ (.all a))
  have hr_aff :
      PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ) (μ.map fun x => a + b * x).rSeries =
        TauCeti.rSeries φ ((b : ℂ) • x + algebraMap ℂ _ (a : ℂ)) := by
    rw [← haff, φ.map_ofReal_rSeries_law hsa]
  have hr_alg :
      TauCeti.rSeries φ ((b : ℂ) • x + algebraMap ℂ _ (a : ℂ)) =
        (b : ℂ) • PowerSeries.rescale (b : ℂ) (TauCeti.rSeries φ x) + PowerSeries.C (a : ℂ) := by
    rw [← PositiveLinearMap.coe_toLinearMap, TauCeti.rSeries_add_algebraMap hφ _ (a : ℂ),
      TauCeti.rSeries_smul φ.toLinearMap (b : ℂ) x, PositiveLinearMap.coe_toLinearMap]
  have hRx :
      PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ) μ.rSeries = TauCeti.rSeries φ x := by
    simpa [hlaw] using φ.map_ofReal_rSeries_law hx
  have hr_map :
      PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
          (b • PowerSeries.rescale b μ.rSeries + PowerSeries.C a) =
        (b : ℂ) • PowerSeries.rescale (b : ℂ) (TauCeti.rSeries φ x) + PowerSeries.C (a : ℂ) := by
    simp only [PowerSeries.smul_eq_C_mul, map_add, map_mul, PowerSeries.map_C,
      ← PowerSeries.rescale_map, Complex.ofRealHom_eq_coe, hRx]
  exact PowerSeries.map_injective (Complex.ofRealHom : ℝ →+* ℂ) Complex.ofReal_injective
    (hr_aff.trans (hr_alg.trans hr_map.symm))

/-- Under `x ↦ a + b * x`, the first free cumulant (mean) transforms by
`κ₁(μ.map (a + b * ·)) = a + b * κ₁(μ)`. -/
theorem freeCumulant_one_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : Integrable (id : ℝ → ℝ) μ) (a b : ℝ) :
    (μ.map fun x => a + b * x).freeCumulant 1 = a + b * μ.freeCumulant 1 := by
  have hm : Integrable (fun x => b * x) μ := hμ.const_mul b
  rw [freeCumulant_one, freeCumulant_one, integral_map (by fun_prop) (by fun_prop),
    integral_add (integrable_const a) hm]
  simp [MeasureTheory.integral_const_mul (μ := μ) b fun x => x]

/-- For `n ≥ 2`, pushing a compactly supported probability measure `μ` forward by `x ↦ a + b * x`
scales its `n`-th free cumulant by `b ^ n`. -/
theorem freeCumulant_map_affine {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : IsCompact μ.support) (a b : ℝ) {n : ℕ} (hn : 2 ≤ n) :
    (μ.map fun x => a + b * x).freeCumulant n = b ^ n * μ.freeCumulant n := by
  rcases n with _ | _ | k
  · omega
  · omega
  · rw [freeCumulant_succ_eq_coeff_rSeries, rSeries_map_affine hμ a b]
    simp [PowerSeries.coeff_succ_C, pow_succ', mul_assoc]

end MeasureTheory.Measure
