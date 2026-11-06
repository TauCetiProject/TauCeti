/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Prod
public import TauCeti.Analysis.Contour.Cycle.Basic

/-!
# Fubini's theorem for integrals over cycles

For cycles `C` and `D` and a function `F z w` jointly continuous on the product of their traces,
the two iterated integrals agree:

`∫_C (∫_D F z w dw) dz = ∫_D (∫_C F z w dz) dw`.

Iterated cycle integrals arise in the holomorphic functional calculus, where the product of two
resolvent integrals over nested cycles is a double integral over both cycles.

## Main results

* `TauCeti.Contour.Cycle.integral_integral_swap`: the order of integration over two cycles can be
  exchanged for integrands continuous on the product of the traces.
-/

public section

noncomputable section

open MeasureTheory Set intervalIntegral Function

open scoped Interval

namespace TauCeti.Contour.Cycle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {F : ℂ → ℂ → E} {C D : Cycle}
  {γ η : PiecewiseC1ClosedCurve}

/-- For curves `γ` and `η` in the supports of `C` and `D`, the double contour integrand of a
function continuous on the product of the traces is integrable on the product of the parameter
intervals. -/
private theorem integrableOn_deriv_smul_deriv_smul
    (hF : ContinuousOn (uncurry F) (trace C ×ˢ trace D)) (hγ : γ ∈ FreeAbelianGroup.support C)
    (hη : η ∈ FreeAbelianGroup.support D) :
    IntegrableOn (fun p : ℝ × ℝ ↦ deriv γ p.1 • deriv η p.2 • F (γ p.1) (η p.2))
      (Ι γ.a γ.b ×ˢ Ι η.a η.b) := by
  have hmaps : MapsTo (fun p : ℝ × ℝ ↦ (γ p.1, η p.2)) (uIcc γ.a γ.b ×ˢ uIcc η.a η.b)
      (trace C ×ˢ trace D) := fun p hp ↦
    ⟨mem_trace_iff.mpr ⟨γ, hγ, p.1, hp.1, rfl⟩, mem_trace_iff.mpr ⟨η, hη, p.2, hp.2, rfl⟩⟩
  have hcont : ContinuousOn (fun p : ℝ × ℝ ↦ F (γ p.1) (η p.2)) (uIcc γ.a γ.b ×ˢ uIcc η.a η.b) :=
    hF.comp ((γ.continuousOn.comp continuousOn_fst fun _ hp ↦ (mem_prod.mp hp).1).prodMk
      (η.continuousOn.comp continuousOn_snd fun _ hp ↦ (mem_prod.mp hp).2)) hmaps
  have hderiv : IntegrableOn (fun p : ℝ × ℝ ↦ deriv γ p.1 * deriv η p.2)
      (Ι γ.a γ.b ×ˢ Ι η.a η.b) := by
    rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict]
    exact γ.intervalIntegrable_deriv.def'.mul_prod η.intervalIntegrable_deriv.def'
  simpa only [mul_smul] using hderiv.smul_continuousOn_of_subset hcont
    (measurableSet_uIoc.prod measurableSet_uIoc) (isCompact_uIcc.prod isCompact_uIcc)
    (prod_mono uIoc_subset_uIcc uIoc_subset_uIcc)

/-- For curves `γ` and `η` in the supports of `C` and `D`, the order of the two contour integrals
along `γ` and `η` can be exchanged. -/
private theorem integral_deriv_smul_integral_deriv_smul_comm
    (hF : ContinuousOn (uncurry F) (trace C ×ˢ trace D)) (hγ : γ ∈ FreeAbelianGroup.support C)
    (hη : η ∈ FreeAbelianGroup.support D) :
    ∫ s in γ.a..γ.b, deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t) =
      ∫ t in η.a..η.b, deriv η t • ∫ s in γ.a..γ.b, deriv γ s • F (γ s) (η t) := by
  simp_rw [← intervalIntegral.integral_smul]
  rw [intervalIntegral_intervalIntegral_swap (F := fun s t ↦ deriv γ s • deriv η t • F (γ s) (η t))
    (integrableOn_deriv_smul_deriv_smul hF hγ hη)]
  simp_rw [smul_comm (deriv γ _) (deriv η _)]

/-- For a curve `γ` in the support of `C`, the inner contour integral along a curve `η` in the
support of `D`, weighted by `γ'`, is interval-integrable along `γ`. -/
private theorem intervalIntegrable_deriv_smul_integral_deriv_smul
    (hF : ContinuousOn (uncurry F) (trace C ×ˢ trace D)) (hγ : γ ∈ FreeAbelianGroup.support C)
    (hη : η ∈ FreeAbelianGroup.support D) :
    IntervalIntegrable (fun s ↦ deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t))
      volume γ.a γ.b := by
  have h := integrableOn_deriv_smul_deriv_smul hF hγ hη
  rw [IntegrableOn, Measure.volume_eq_prod, ← Measure.prod_restrict] at h
  rw [intervalIntegrable_iff]
  refine (h.integral_prod_left.smul (if η.a ≤ η.b then (1 : ℝ) else -1)).congr
    (ae_of_all _ fun s ↦ ?_)
  dsimp only [Pi.smul_apply]
  rw [intervalIntegral.intervalIntegral_eq_integral_uIoc, MeasureTheory.integral_smul]
  exact smul_comm _ _ _

/-- Integrating the inner cycle integral `∫_D F (γ s) w dw` along a curve `γ` in the support of `C`
gives the sum of the double integrals along `γ` and the curves in the support of `D`. -/
private theorem integral_deriv_smul_integral_eq_sum
    (hF : ContinuousOn (uncurry F) (trace C ×ˢ trace D)) (hγ : γ ∈ FreeAbelianGroup.support C) :
    ∫ s in γ.a..γ.b, deriv γ s • integral (F (γ s)) D =
      ∑ η ∈ FreeAbelianGroup.support D, FreeAbelianGroup.coeff η D •
        ∫ s in γ.a..γ.b, deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t) := by
  calc ∫ s in γ.a..γ.b, deriv γ s • integral (F (γ s)) D
      = ∫ s in γ.a..γ.b, ∑ η ∈ FreeAbelianGroup.support D, (FreeAbelianGroup.coeff η D : ℂ) •
          (deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t)) :=
        intervalIntegral.integral_congr fun s _ ↦ by
          simp only [integral_eq_sum_support, Finset.smul_sum, Int.cast_smul_eq_zsmul]
          exact Finset.sum_congr rfl fun _ _ ↦ smul_comm _ _ _
    _ = _ := by
        rw [intervalIntegral.integral_finsetSum (f := fun η s ↦ (FreeAbelianGroup.coeff η D : ℂ) •
          (deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t))) fun η hη ↦
          (intervalIntegrable_deriv_smul_integral_deriv_smul hF hγ hη).smul _]
        simp only [intervalIntegral.integral_smul]
        simp only [Int.cast_smul_eq_zsmul]

/-- **Fubini's theorem for cycles.** For a function `F` continuous on the product of the traces of
two cycles `C` and `D`,

`∫_C (∫_D F z w dw) dz = ∫_D (∫_C F z w dz) dw`. -/
theorem integral_integral_swap (hF : ContinuousOn (uncurry F) (trace C ×ˢ trace D)) :
    integral (fun z ↦ integral (F z) D) C = integral (fun w ↦ integral (fun z ↦ F z w) C) D := by
  have hF' : ContinuousOn (uncurry fun w z ↦ F z w) (trace D ×ˢ trace C) :=
    hF.comp continuous_swap.continuousOn fun _ hp ↦ ⟨(mem_prod.mp hp).2, (mem_prod.mp hp).1⟩
  -- Expanding both cycles into their generators reduces this to Fubini's theorem on a product of
  -- two parameter intervals. There the integrand `γ' s • η' t • F (γ s) (η t)` is integrable
  -- because the derivatives of the curves are integrable and `F` is bounded on the compact product
  -- of the traces.
  rw [integral_eq_sum_support, integral_eq_sum_support]
  calc ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
        ∫ s in γ.a..γ.b, deriv γ s • integral (F (γ s)) D
      = ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
          ∑ η ∈ FreeAbelianGroup.support D, FreeAbelianGroup.coeff η D •
            ∫ s in γ.a..γ.b, deriv γ s • ∫ t in η.a..η.b, deriv η t • F (γ s) (η t) :=
        Finset.sum_congr rfl fun γ hγ ↦ by rw [integral_deriv_smul_integral_eq_sum hF hγ]
    _ = ∑ η ∈ FreeAbelianGroup.support D, FreeAbelianGroup.coeff η D •
          ∑ γ ∈ FreeAbelianGroup.support C, FreeAbelianGroup.coeff γ C •
            ∫ t in η.a..η.b, deriv η t • ∫ s in γ.a..γ.b, deriv γ s • F (γ s) (η t) := by
        simp only [Finset.smul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun η hη ↦ Finset.sum_congr rfl fun γ hγ ↦ ?_
        rw [smul_comm, integral_deriv_smul_integral_deriv_smul_comm hF hγ hη]
    _ = ∑ η ∈ FreeAbelianGroup.support D, FreeAbelianGroup.coeff η D •
          ∫ t in η.a..η.b, deriv η t • integral (fun z ↦ F z (η t)) C :=
        Finset.sum_congr rfl fun η hη ↦ by rw [integral_deriv_smul_integral_eq_sum hF' hη]

end TauCeti.Contour.Cycle
