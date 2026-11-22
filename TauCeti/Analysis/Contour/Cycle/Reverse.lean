/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
import TauCeti.Analysis.Contour.Cycle.Winding
import TauCeti.Analysis.Contour.Winding.Number.Reverse

/-!
# Orientation reversal of closed piecewise-`C¹` curves and cycle generators

Swapping the endpoints `(a, b)` of a `TauCeti.Contour.PiecewiseC1ClosedCurve` reverses its
orientation without changing its canonical extension to `ℝ` (`PiecewiseC1ClosedCurve.coe_symm`) or
its geometric trace (`PiecewiseC1ClosedCurve.image_symm`). Hence reversing a cycle generator
negates its contour integral (`Cycle.integral_of_symm`), negates its winding number off its trace
(`Cycle.windingNumber_of_symm`), and preserves domain containment and null-homology.

## Main definitions

* `TauCeti.Contour.PiecewiseC1ClosedCurve.symm`: reverse a bundled closed piecewise-`C¹` curve.

## Main results

* `TauCeti.Contour.PiecewiseC1ClosedCurve.coe_symm`, `symm_symm`, `of_symm`, `image_symm`
* `TauCeti.Contour.Cycle.trace_of_symm`, `isIn_of_symm_iff`, `integral_of_symm`,
  `windingNumber_of_symm`, `windingNumber_of_symm_eq_zero_iff`, `isNullHomologous_of_symm_iff`
-/

public section

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace TauCeti.Contour

namespace PiecewiseC1ClosedCurve

/-- Reverse the orientation of a bundled closed piecewise-`C¹` curve by swapping its initial and
terminal parameters. -/
def symm (γ : PiecewiseC1ClosedCurve) : PiecewiseC1ClosedCurve :=
  of γ γ.isPiecewiseC1On.symm γ.source_eq_target.symm

/-- Defining formula for `PiecewiseC1ClosedCurve.symm`. -/
theorem symm_def (γ : PiecewiseC1ClosedCurve) :
    γ.symm = of γ γ.isPiecewiseC1On.symm γ.source_eq_target.symm :=
  (rfl)

/-- Reversing a closed curve makes its old terminal parameter the new initial parameter. -/
@[simp]
theorem symm_a (γ : PiecewiseC1ClosedCurve) : γ.symm.a = γ.b := of_a _ _ _

/-- Reversing a closed curve makes its old initial parameter the new terminal parameter. -/
@[simp]
theorem symm_b (γ : PiecewiseC1ClosedCurve) : γ.symm.b = γ.a := of_b _ _ _

/-- Reversing a bundled closed curve leaves its canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_symm (γ : PiecewiseC1ClosedCurve) : (γ.symm : ℝ → ℂ) = γ := by
  ext t
  by_cases ht : t ∈ uIcc γ.b γ.a
  · exact of_apply _ _ _ ht
  · rw [coe_apply_of_notMem _ (by rwa [symm_a, symm_b]),
      coe_apply_of_notMem _ (by rwa [uIcc_comm] at ht)]

/-- Orientation reversal on bundled closed curves is an involution. -/
@[simp]
theorem symm_symm (γ : PiecewiseC1ClosedCurve) : γ.symm.symm = γ :=
  ext_of_eqOn (by simp) (by simp) fun _ _ ↦ by simp

/-- Reversing a curve bundled via `PiecewiseC1ClosedCurve.of` swaps the endpoints of `of`. -/
@[simp]
theorem of_symm {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) :
    (of γ hγ hclosed).symm = of γ hγ.symm hclosed.symm :=
  ext_of_eqOn (by simp) (by simp) fun t ht ↦ by
    rw [symm_a, symm_b, of_a, of_b] at ht
    rw [coe_symm, of_apply _ _ _ (uIcc_comm (a := a) (b := b) ▸ ht), of_apply _ _ _ ht]

/-- Reversing a closed curve preserves its geometric image on its parameter interval. -/
theorem image_symm (γ : PiecewiseC1ClosedCurve) :
    γ.symm '' uIcc γ.symm.a γ.symm.b = γ '' uIcc γ.a γ.b := by
  simp [uIcc_comm]

end PiecewiseC1ClosedCurve

namespace Cycle

/-- Reversing a generator does not change its cycle trace. -/
theorem trace_of_symm (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAddCommGroup.of γ.symm) = trace (FreeAddCommGroup.of γ) := by
  rw [trace_of, trace_of, PiecewiseC1ClosedCurve.image_symm]

/-- Reversing a generator preserves containment in any target set. -/
theorem isIn_of_symm_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAddCommGroup.of γ.symm) Ω ↔ IsIn (FreeAddCommGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_symm]

/-- Integrating over a reversed generator negates the contour integral. -/
theorem integral_of_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : PiecewiseC1ClosedCurve) (f : ℂ → E) :
    integral f (FreeAddCommGroup.of γ.symm) = -integral f (FreeAddCommGroup.of γ) := by
  simp only [integral_of, PiecewiseC1ClosedCurve.coe_symm, PiecewiseC1ClosedCurve.symm_a,
    PiecewiseC1ClosedCurve.symm_b]
  rw [intervalIntegral.integral_symm]

/-- At any point outside the image of `γ`, reversing `γ` negates its cycle winding number. -/
theorem windingNumber_of_symm (γ : PiecewiseC1ClosedCurve) {z : ℂ}
    (hz : z ∉ γ '' uIcc γ.a γ.b) :
    windingNumber z (FreeAddCommGroup.of γ.symm) =
      -windingNumber z (FreeAddCommGroup.of γ) := by
  have hz' : z ∉ trace (FreeAddCommGroup.of γ) := by rwa [trace_of]
  have hzsymm : z ∉ trace (FreeAddCommGroup.of γ.symm) := by rwa [trace_of_symm]
  rw [windingNumber_eq_integral_of_not_mem_trace _ hzsymm,
    windingNumber_eq_integral_of_not_mem_trace _ hz', integral_of_symm, mul_neg]

/-- Vanishing of the cycle winding number of a generator is preserved under orientation reversal,
even at points on the trace. -/
theorem windingNumber_of_symm_eq_zero_iff (γ : PiecewiseC1ClosedCurve) (z : ℂ) :
    windingNumber z (FreeAddCommGroup.of γ.symm) = 0 ↔
      windingNumber z (FreeAddCommGroup.of γ) = 0 := by
  simp only [windingNumber_of, PiecewiseC1ClosedCurve.coe_symm, PiecewiseC1ClosedCurve.symm_a,
    PiecewiseC1ClosedCurve.symm_b]
  exact ⟨TauCeti.Contour.windingNumber_eq_zero_symm, TauCeti.Contour.windingNumber_eq_zero_symm⟩

/-- Null-homology of a generator is preserved under orientation reversal. -/
theorem isNullHomologous_of_symm_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAddCommGroup.of γ.symm) Ω ↔
      IsNullHomologous (FreeAddCommGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_symm_eq_zero_iff]

end Cycle

end TauCeti.Contour

end
