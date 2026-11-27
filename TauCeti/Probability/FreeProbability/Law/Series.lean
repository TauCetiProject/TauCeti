/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Law.Basic
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

## Main results

* `PositiveLinearMap.map_ofReal_momentSeries_integral_law`,
  `PositiveLinearMap.map_ofReal_freeCumulantSeries_integral_law`,
  `PositiveLinearMap.ofReal_freeCumulant_integral_law`,
  `PositiveLinearMap.ofReal_freeCumulant_law`,
  `PositiveLinearMap.map_ofReal_rSeries_integral_law`: agreement of scalar-measure formal series and
  free cumulants of `φ.law a` with those of a selfadjoint element `a`.
* `MeasureTheory.Measure.freeCumulant_eq_coeff_freeCumulantSeries`,
  `MeasureTheory.Measure.freeCumulant_succ_eq_coeff_rSeries`,
  `MeasureTheory.Measure.freeCumulant_zero`,
  `MeasureTheory.Measure.freeCumulant_one`,
  `MeasureTheory.Measure.freeCumulant_two_eq_variance`,
  `MeasureTheory.Measure.freeCumulant_integral_const_eq`: coefficient, special-value, and
  constant-word formulas for `MeasureTheory.Measure.freeCumulant`.
* `MeasureTheory.Measure.ext_of_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_iff_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_iff_forall_freeCumulant_eq`,
  `MeasureTheory.Measure.coeff_one_rSeries_integral_eq_variance`: R-series/cumulant determinacy and
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

/-- `μ.freeCumulant n` is the `n`-th coefficient of the formal free cumulant series of `μ`. -/
theorem freeCumulant_eq_coeff_freeCumulantSeries (μ : Measure ℝ) (n : ℕ) :
    μ.freeCumulant n =
      PowerSeries.coeff n (TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id) :=
  (TauCeti.coeff_freeCumulantSeries _ _ n).symm

/-- `μ.freeCumulant (n + 1)` is the `n`-th coefficient of the formal R-series of `μ`. -/
theorem freeCumulant_succ_eq_coeff_rSeries (μ : Measure ℝ) (n : ℕ) :
    μ.freeCumulant (n + 1) =
      PowerSeries.coeff n (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id) :=
  (TauCeti.coeff_rSeries _ _ n).symm

/-- The zeroth free cumulant of any real Borel measure is `1`. -/
@[simp] theorem freeCumulant_zero (μ : Measure ℝ) : μ.freeCumulant 0 = 1 := by
  rw [freeCumulant_eq_coeff_freeCumulantSeries, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    TauCeti.constantCoeff_freeCumulantSeries]

/-- The first free cumulant of any real Borel measure is its mean `∫ x, x ∂μ`. -/
@[simp] theorem freeCumulant_one (μ : Measure ℝ) : μ.freeCumulant 1 = ∫ x, x ∂μ := by
  rw [freeCumulant_eq_coeff_freeCumulantSeries, TauCeti.coeff_one_freeCumulantSeries]; rfl

/-- The second free cumulant of a probability measure with finite second moment is its variance. -/
theorem freeCumulant_two_eq_variance {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (hμ : MemLp (id : ℝ → ℝ) 2 μ) : μ.freeCumulant 2 = variance id μ := by
  rw [freeCumulant_eq_coeff_freeCumulantSeries, TauCeti.coeff_two_freeCumulantSeries]
  exact (variance_eq_sub hμ).symm

/-- Any constant-`id` integral free cumulant along a finite linear order reduces to
`μ.freeCumulant #s`. -/
theorem freeCumulant_integral_const_eq (μ : Measure ℝ) {α : Type*} [LinearOrder α]
    (s : Finset α) :
    TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : α => (id : ℝ → ℝ)) s =
      μ.freeCumulant #s := by
  rw [TauCeti.freeCumulant_const_eq_coeff_freeCumulantSeries,
    freeCumulant_eq_coeff_freeCumulantSeries]

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
theorem map_ofReal_rSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) = TauCeti.rSeries φ a := by
  ext n
  rw [coeff_map, TauCeti.coeff_rSeries, TauCeti.coeff_rSeries, Complex.ofRealHom_eq_coe]
  exact φ.ofReal_freeCumulant_law ha (n + 1)

end PositiveLinearMap

namespace MeasureTheory.Measure

/-- Two compactly supported probability measures on `ℝ` with equal formal R-series coincide. -/
theorem ext_of_rSeries_integral_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support)
    (hr : TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id) : μ = ν := by
  have hc : TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id =
      TauCeti.freeCumulantSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id := by
    rw [TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries,
      TauCeti.freeCumulantSeries_eq_one_add_X_mul_rSeries, hr]
  have hm := (TauCeti.freeCumulantSeries_eq_iff_momentSeries_eq (a := (id : ℝ → ℝ)) (by simp)
    (b := (id : ℝ → ℝ)) (by simp)).mp hc
  refine TauCeti.Measure.ext_of_forall_integral_pow_eq_of_support (hμ.union hν)
    (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_left)
      (Measure.measure_compl_support (μ := μ)))
    (measure_mono_null (Set.compl_subset_compl.mpr Set.subset_union_right)
      (Measure.measure_compl_support (μ := ν))) fun n => ?_
  simpa [TauCeti.coeff_momentSeries, Pi.pow_def] using congrArg (PowerSeries.coeff n) hm

/-- **R-series determinacy of compactly supported probability measures.** -/
theorem eq_iff_rSeries_integral_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂μ) id =
      TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ν) id :=
  ⟨fun h => h ▸ rfl, ext_of_rSeries_integral_eq hμ hν⟩

/-- **Free cumulant determinacy of compactly supported probability measures.** -/
theorem eq_iff_forall_freeCumulant_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ ∀ n : ℕ, n ≠ 0 → μ.freeCumulant n = ν.freeCumulant n := by
  rw [eq_iff_rSeries_integral_eq hμ hν, PowerSeries.ext_iff]
  refine ⟨fun h n hn => ?_, fun h n => ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
    simpa [freeCumulant_succ_eq_coeff_rSeries] using h k
  · simpa [freeCumulant_succ_eq_coeff_rSeries] using h (n + 1) n.succ_ne_zero

/-- The linear coefficient of the formal R-series of a square-integrable real random variable `X`
equals its variance. -/
theorem coeff_one_rSeries_integral_eq_variance {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : MemLp X 2 μ) :
    PowerSeries.coeff 1 (TauCeti.rSeries (fun f : Ω → ℝ => ∫ ω, f ω ∂μ) X) = variance X μ := by
  rw [← TauCeti.coeff_succ_freeCumulantSeries, TauCeti.coeff_two_freeCumulantSeries]
  exact (variance_eq_sub hX).symm

end MeasureTheory.Measure
