/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.ODE.Propagator
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.LocallyConvex.SeparatingDual
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp
import TauCeti.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# The backward integral equation of a propagator

For a coefficient `P` integrable on `[a, b]` and `t ∈ [a, b]`, the propagator `s ↦ N_P(t, s)` is
absolutely continuous on `[a, b]` (`TauCeti.absolutelyContinuousOnInterval_propagator_right`):
it is `N_P(t, a) N_P(s, a)⁻¹`, and the inverse is smooth on the units. Its almost-everywhere
derivative `-N_P(t, s) P(s)` integrates to the backward integral
equation `N_P(t, s) = 1 + ∫ r in s..t, N_P(t, r) ∘L P r`
(`TauCeti.propagator_eq_one_add_integral_right`).
-/

public section

open MeasureTheory Set intervalIntegral

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {E : Type*}
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedSpace ℝ E] [IsScalarTower ℝ 𝕜 E]
  [CompleteSpace E] {P : ℝ → E →L[𝕜] E} {a b s t : ℝ}

/-- **Absolute continuity in the initial time.** If `P` is integrable on `[a, b]` and
`t ∈ [a, b]`, then `s ↦ N_P(t, s)` is absolutely continuous on `[a, b]`. -/
theorem absolutelyContinuousOnInterval_propagator_right (hP : IntegrableOn P (Icc a b))
    (ht : t ∈ Icc a b) : AbsolutelyContinuousOnInterval (fun s ↦ propagator P t s) a b := by
  have hab : a ≤ b := ht.1.trans ht.2
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hmem {r : ℝ} (hr : r ∈ uIcc a b) : r ∈ Icc a b := by rwa [uIcc_of_le hab] at hr
  -- `s ↦ N_P(a, s)` is the inverse of the absolutely continuous `s ↦ N_P(s, a)`.
  have hinv : AbsolutelyContinuousOnInterval (fun s ↦ propagator P a s) a b := by
    refine ((absolutelyContinuousOnInterval_propagator_left hP ha).comp_of_contDiffAt
      (φ := Ring.inverse) ?_).congr fun r hr ↦ ringInverse_propagator hP ha (hmem hr)
    rintro _ ⟨r, hr, rfl⟩
    obtain ⟨u, hu⟩ := isUnit_propagator hP ha (hmem hr)
    simp only [← hu]
    exact (contDiffAt_ringInverse 𝕜 u).restrict_scalars ℝ
  refine ((contDiffOn_const (c := propagator P t a)).absolutelyContinuousOnInterval.fun_mul'
    hinv).congr fun r hr ↦ ?_
  exact propagator_comp_propagator hP ha (hmem hr) ht

/-- **The backward integral equation.** If `P` is integrable on `[a, b]` and `s, t ∈ [a, b]`, then
`N_P(t, s) = 1 + ∫ r in s..t, N_P(t, r) ∘L P r`. -/
theorem propagator_eq_one_add_integral_right (hP : IntegrableOn P (Icc a b)) (hs : s ∈ Icc a b)
    (ht : t ∈ Icc a b) :
    propagator P t s = 1 + ∫ r in s..t, propagator P t r ∘L P r := by
  have hac := (absolutelyContinuousOnInterval_propagator_right hP ht).mono
    (uIcc_subset_uIcc (mem_uIcc_of_le hs.1 hs.2) (mem_uIcc_of_le ht.1 ht.2))
  have hI : IntervalIntegrable (fun r ↦ propagator P t r ∘L P r) volume s t :=
    ((IntegrableOn.continuousOn_mul (continuousOn_propagator_right hP ht) hP
      isCompact_Icc).mono_set (uIcc_subset_Icc hs ht)).intervalIntegrable
  have hV : ∀ᵐ r, r ∈ uIoc s t →
      HasDerivAt (fun r ↦ propagator P t r) (-(propagator P t r ∘L P r)) r := by
    filter_upwards [ae_hasDerivAt_propagator_right hP ht, Measure.ae_ne volume a,
      Measure.ae_ne volume b] with r hr hra hrb hmem
    have hr' := uIcc_subset_Icc hs ht (uIoc_subset_uIcc hmem)
    exact hr ⟨lt_of_le_of_ne hr'.1 (Ne.symm hra), lt_of_le_of_ne hr'.2 hrb⟩
  -- The fundamental theorem of calculus, tested against every continuous linear functional.
  have hint :
      ∫ r in s..t, -(propagator P t r ∘L P r) = propagator P t t - propagator P t s := by
    refine (SeparatingDual.eq_iff_forall_dual_eq (R := ℝ)).2 fun g ↦ ?_
    rw [← g.intervalIntegral_comp_comm (f := fun r ↦ -(propagator P t r ∘L P r)) hI.neg,
      map_sub]
    simpa [g.fderiv] using hac.integral_fderiv_apply_eq_sub hV g.contDiff
  rw [propagator_self, intervalIntegral.integral_neg] at hint
  rw [← neg_neg (∫ r in s..t, propagator P t r ∘L P r), hint]
  abel

end TauCeti
