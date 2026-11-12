/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.NormalizedIncrements
public import TauCeti.Probability.Distributions.Gaussian.Hermite.Pi.Pullback
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Hermite expansions of finite Brownian observations

On a strictly increasing grid starting at zero, the standardized Brownian increments carry
exactly the same information, modulo null sets, as the observations on that grid. Thus the
Gaussian `L²` pullback has as its range precisely the classes measurable from those observations.
Every such claim has an `L²` expansion in products of normalized Hermite polynomials of the
standardized increments, with coefficients computed on the original probability space.

This is a finite-grid completeness statement, not a representation by a stochastic integral.
It needs only pre-Brownian laws and measurable observations, not continuous paths or a filtration.
The empty grid is allowed: its initial observation is zero almost surely and only constant
classes remain. Measurability is explicitly up to null sets, so the result also applies to
claims measured in the completed observation sigma algebra.

The construction uses `IsPreBrownianReal.hasLaw_normalizedBrownianIncrements`, the existing
`HasLaw.gaussianVectorL2Isometry` and `HasLaw.hasSum_gaussianVectorHermite`, and the native
finite-sum telescoping identity. It does not reconstruct the Gaussian tensor basis.

## References

* I. Karatzas and S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.4.
-/

public section
noncomputable section

open MeasureTheory ProbabilityTheory TauCeti Finset
open scoped NNReal ENNReal

namespace ProbabilityTheory.IsPreBrownianReal

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}
  {n : ℕ} {t : Fin (n + 1) → ℝ≥0}

/-- The Gaussian pullback along standardized increments has range exactly the `L²` classes
measurable, up to null sets, from all observations on a grid starting at zero. -/
theorem mem_range_gaussianVectorL2Isometry_iff
    (hB : IsPreBrownianReal B P) (ht : StrictMono t) (ht₀ : t 0 = 0)
    (hm : ∀ i, Measurable (B (t i))) (u : Lp ℝ 2 P) :
    u ∈ LinearMap.range
      ((hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorL2Isometry
        (measurable_normalizedBrownianIncrements hm)).toLinearMap ↔
      AEStronglyMeasurable[MeasurableSpace.comap (fun ω i ↦ B (t i) ω) inferInstance] u P := by
  let X := normalizedBrownianIncrements B t
  let Y : Ω → Fin (n + 1) → ℝ := fun ω i ↦ B (t i) ω
  have hX := (hB.hasLaw_normalizedBrownianIncrements ht).measurePreserving
    (measurable_normalizedBrownianIncrements hm)
  have hiso : (hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorL2Isometry
      (measurable_normalizedBrownianIncrements hm) = Lp.compMeasurePreservingₗᵢ ℝ X hX := by
    ext v
    exact (HasLaw.coeFn_gaussianVectorL2Isometry _ _ v).trans
      (Lp.coeFn_compMeasurePreserving v hX).symm
  rw [hiso, Lp.mem_range_compMeasurePreservingₗᵢ_iff]
  have hXY : MeasurableSpace.comap X inferInstance ≤
      MeasurableSpace.comap Y inferInstance := by
    let : MeasurableSpace Ω := MeasurableSpace.comap Y inferInstance
    have hY : Measurable Y :=
      measurable_iff_comap_le.mpr le_rfl
    have hx : Measurable X := by
      apply Measurable.of_eval
      intro i
      simpa only [X, normalizedBrownianIncrements_apply, Y, Function.comp_apply,
        Pi.sub_apply] using
        (((measurable_pi_apply i.succ).comp hY).sub
          ((measurable_pi_apply i.castSucc).comp hY)).div_const
            (Real.sqrt ((t i.succ : ℝ) - t i.castSucc))
    exact hx.comap_le
  constructor
  · exact fun hu ↦ hu.mono hXY
  · intro hu
    obtain ⟨g, hg, hgu⟩ := hu.stronglyMeasurable_mk.exists_eq_measurable_comp
    -- Recover the observations by cumulative sums; the first observation is zero a.s.,
    -- rather than literally zero on an arbitrary version of the Brownian process.
    let R : (Fin n → ℝ) → Fin (n + 1) → ℝ := fun x ↦
      Fin.cases 0 (fun i ↦ ∑ j ∈ Iic i,
        Real.sqrt ((t j.succ : ℝ) - t j.castSucc) * x j)
    have hR : Measurable R := by
      apply Measurable.of_eval
      intro i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · exact measurable_const
      · exact Finset.measurable_sum _ fun j _ ↦ measurable_const.mul (measurable_pi_apply j)
    have hRY : (R ∘ X) =ᵐ[P] Y := by
      filter_upwards [hB.eval_zero_ae_eq_zero] with ω hω
      ext i
      refine Fin.cases ?_ (fun i ↦ ?_) i
      · simpa only [R, Y, Function.comp_apply, Fin.cases_zero, ht₀] using hω.symm
      · simp only [R, Function.comp_apply, Fin.cases_succ, X,
          normalizedBrownianIncrements_apply]
        have hterm (j : Fin n) :
            Real.sqrt ((t j.succ : ℝ) - t j.castSucc) *
                ((B (t j.succ) ω - B (t j.castSucc) ω) /
                  Real.sqrt ((t j.succ : ℝ) - t j.castSucc)) =
              B (t j.succ) ω - B (t j.castSucc) ω := by
          exact mul_div_cancel₀ _ (ne_of_gt (Real.sqrt_pos.2
            (sub_pos.2 (NNReal.coe_lt_coe.2 (ht Fin.castSucc_lt_succ)))))
        simp_rw [hterm]
        rw [Fin.sum_Iic_sub i (fun j ↦ B (t j) ω), ht₀, hω, sub_zero]
    refine ⟨g ∘ R ∘ X, ?_, ?_⟩
    · let : MeasurableSpace Ω := MeasurableSpace.comap X inferInstance
      exact (hg.comp_measurable hR).comp_measurable (measurable_iff_comap_le.mpr le_rfl)
    · filter_upwards [hu.ae_eq_mk, hRY] with ω h₁ h₂
      exact h₁.trans ((congrFun hgu ω).trans (congrArg g h₂).symm)

/-- Every square-integrable claim measurable from a finite grid of Brownian observations
has a convergent Hermite expansion in the standardized increments. The coefficients are
expectations on the original sample space. -/
theorem hasSum_gaussianVectorHermite_of_gridMeasurable
    (hB : IsPreBrownianReal B P) (ht : StrictMono t) (ht₀ : t 0 = 0)
    (hm : ∀ i, Measurable (B (t i))) (u : Lp ℝ 2 P)
    (hu : AEStronglyMeasurable[MeasurableSpace.comap
      (fun ω i ↦ B (t i) ω) inferInstance] u P) :
    HasSum (fun a : Fin n → ℕ ↦
      (∫ ω, (hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        (measurable_normalizedBrownianIncrements hm) a ω * u ω ∂P) •
      (hB.hasLaw_normalizedBrownianIncrements ht).gaussianVectorHermite
        (measurable_normalizedBrownianIncrements hm) a) u := by
  obtain ⟨v, hv⟩ := (hB.mem_range_gaussianVectorL2Isometry_iff ht ht₀ hm u).2 hu
  simp only [LinearIsometry.coe_toLinearMap] at hv
  simpa only [hv] using
    (hB.hasLaw_normalizedBrownianIncrements ht).hasSum_gaussianVectorHermite
      (measurable_normalizedBrownianIncrements hm) v

end ProbabilityTheory.IsPreBrownianReal
