/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Moments.Variance
public import TauCeti.Probability.FreeProbability.Cumulant.Series
public import TauCeti.Probability.FreeProbability.Law.Basic
import TauCeti.MeasureTheory.Measure.Support
import TauCeti.Probability.Moments.CompactDeterminacy

/-!
# Formal moment, free cumulant, and R-series of scalar laws and compactly supported measures

This file bridges `TauCeti.momentSeries`, `TauCeti.freeCumulantSeries`, and `TauCeti.rSeries` with
scalar laws `PositiveLinearMap.law` and compactly supported Borel probability measures on `ℝ`.

Mapping the real formal moment, free cumulant, and R-series of `id : ℝ → ℝ` under `φ.law a` into `ℂ`
recovers the series of a selfadjoint element `a`. For compactly supported probability measures on
`ℝ`, the formal R-series (equivalently, all positive-order free cumulants) uniquely determines the
measure; its linear coefficient is the variance, and for `Measure.dirac a` it equals `C a`.

## Main results

* `PositiveLinearMap.map_ofReal_momentSeries_integral_law`,
  `PositiveLinearMap.map_ofReal_freeCumulantSeries_integral_law`,
  `PositiveLinearMap.ofReal_freeCumulant_integral_law`,
  `PositiveLinearMap.map_ofReal_rSeries_integral_law`: agreement of scalar-measure formal series and
  free cumulants of `φ.law a` with those of a selfadjoint element `a`.
* `MeasureTheory.Measure.rSeries_integral_dirac`,
  `MeasureTheory.Measure.rSeries_integral_dirac_zero`: formal R-series of Dirac masses on `ℝ`.
* `MeasureTheory.Measure.ext_of_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_iff_rSeries_integral_eq`,
  `MeasureTheory.Measure.eq_iff_forall_freeCumulant_integral_eq`,
  `MeasureTheory.Measure.coeff_one_rSeries_eq_variance`: R-series/cumulant determinacy and variance.

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

/-- Mapping the real formal R-series of `φ.law a` into `ℂ` gives the formal R-series of `a`. -/
theorem map_ofReal_rSeries_integral_law {a : A} (ha : IsSelfAdjoint a) :
    PowerSeries.map (Complex.ofRealHom : ℝ →+* ℂ)
        (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂φ.law a) id) = TauCeti.rSeries φ a := by
  ext n
  simpa [TauCeti.coeff_rSeries] using
    φ.ofReal_freeCumulant_integral_law ha (univ : Finset (Fin (n + 1)))

end PositiveLinearMap

namespace MeasureTheory.Measure

-- `simp` already reduces via `integral_dirac` and `TauCeti.rSeries_eval` (`simpNF`).
/-- The formal R-series of a Dirac mass `Measure.dirac a` on `ℝ` is `PowerSeries.C a`. -/
theorem rSeries_integral_dirac (a : ℝ) :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂Measure.dirac a) id = PowerSeries.C a := by simp

/-- The formal R-series of `Measure.dirac 0` on `ℝ` vanishes. -/
theorem rSeries_integral_dirac_zero :
    TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂Measure.dirac (0 : ℝ)) id = 0 := by simp

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
theorem eq_iff_forall_freeCumulant_integral_eq {μ ν : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] (hμ : IsCompact μ.support) (hν : IsCompact ν.support) :
    μ = ν ↔ ∀ n : ℕ, n ≠ 0 →
      TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂μ) (fun _ : Fin n => (id : ℝ → ℝ)) univ =
        TauCeti.freeCumulant (fun f : ℝ → ℝ => ∫ x, f x ∂ν)
          (fun _ : Fin n => (id : ℝ → ℝ)) univ := by
  rw [eq_iff_rSeries_integral_eq hμ hν, PowerSeries.ext_iff]
  refine ⟨fun h n hn => ?_, fun h n => ?_⟩
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn; simpa [TauCeti.coeff_rSeries] using h k
  · simpa [TauCeti.coeff_rSeries] using h (n + 1) n.succ_ne_zero

/-- The linear coefficient of the formal R-series of a compactly supported probability measure on
`ℝ` equals its variance. -/
theorem coeff_one_rSeries_eq_variance {ρ : Measure ℝ} [IsProbabilityMeasure ρ]
    (hρ : IsCompact ρ.support) :
    PowerSeries.coeff 1 (TauCeti.rSeries (fun f : ℝ → ℝ => ∫ x, f x ∂ρ) id) = variance id ρ := by
  obtain ⟨R, hR⟩ := hρ.isBounded.subset_closedBall 0
  have hae : ∀ᵐ x ∂ρ, x ∈ Set.Icc (-R) R := by
    filter_upwards [Measure.support_mem_ae (μ := ρ)] with x hx
    simpa [Real.closedBall_eq_Icc] using hR hx
  rw [← TauCeti.coeff_succ_freeCumulantSeries, TauCeti.coeff_two_freeCumulantSeries]
  exact (variance_eq_sub (memLp_of_bounded hae measurable_id.aestronglyMeasurable 2)).symm

end MeasureTheory.Measure
