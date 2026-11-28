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
# Orientation reversal of closed absolutely continuous curves and cycle generators

Swapping the endpoints `(a, b)` of a `TauCeti.Contour.AbsolutelyContinuousClosedCurve` reverses its
orientation without changing its canonical extension to `ℝ`
(`AbsolutelyContinuousClosedCurve.coe_symm`) or its geometric trace
(`AbsolutelyContinuousClosedCurve.image_symm`). Hence reversing a cycle generator negates its
contour integral (`Cycle.integral_of_symm`), negates its winding number off its trace
(`Cycle.windingNumber_of_symm`), and preserves domain containment and null-homology.

## Main definitions

* `TauCeti.Contour.AbsolutelyContinuousClosedCurve.symm`: reverse a bundled closed absolutely
  continuous curve.

## Main results

* `TauCeti.Contour.AbsolutelyContinuousClosedCurve.coe_symm`, `symm_symm`, `of_symm`, `image_symm`,
  `lt_and_injOn_or_symm_lt_and_injOn_of_ne`, `induction_on_lt`
* `TauCeti.Contour.Cycle.trace_of_symm`, `isIn_of_symm_iff`, `integral_of_symm`,
  `windingNumber_of_symm`, `windingNumber_of_symm_eq_zero_iff`, `isNullHomologous_of_symm_iff`
-/

public section

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace TauCeti.Contour

namespace AbsolutelyContinuousClosedCurve

/-- Reverse the orientation of a bundled closed absolutely continuous curve by swapping its initial
and terminal parameters. -/
def symm (γ : AbsolutelyContinuousClosedCurve) : AbsolutelyContinuousClosedCurve :=
  of γ γ.absolutelyContinuousOnInterval.symm γ.source_eq_target.symm

/-- Defining formula for `AbsolutelyContinuousClosedCurve.symm`. -/
theorem symm_def (γ : AbsolutelyContinuousClosedCurve) :
    γ.symm = of γ γ.absolutelyContinuousOnInterval.symm γ.source_eq_target.symm :=
  (rfl)

/-- Reversing a closed curve makes its old terminal parameter the new initial parameter. -/
@[simp]
theorem symm_a (γ : AbsolutelyContinuousClosedCurve) : γ.symm.a = γ.b := of_a _ _ _

/-- Reversing a closed curve makes its old initial parameter the new terminal parameter. -/
@[simp]
theorem symm_b (γ : AbsolutelyContinuousClosedCurve) : γ.symm.b = γ.a := of_b _ _ _

/-- Reversing a bundled closed curve leaves its canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_symm (γ : AbsolutelyContinuousClosedCurve) : (γ.symm : ℝ → ℂ) = γ := by
  ext t
  by_cases ht : t ∈ uIcc γ.b γ.a
  · exact of_apply _ _ _ ht
  · rw [coe_apply_of_notMem _ (by rwa [symm_a, symm_b]),
      coe_apply_of_notMem _ (by rwa [uIcc_comm] at ht)]

/-- Orientation reversal on bundled closed curves is an involution. -/
@[simp]
theorem symm_symm (γ : AbsolutelyContinuousClosedCurve) : γ.symm.symm = γ :=
  ext (by simp) (by simp) fun _ _ ↦ by simp

/-- Reversing a curve bundled via `AbsolutelyContinuousClosedCurve.of` swaps the endpoints of
`of`. -/
@[simp]
theorem of_symm {a b : ℝ} (γ : ℝ → ℂ) (hγ : AbsolutelyContinuousOnInterval γ a b)
    (hclosed : γ a = γ b) :
    (of γ hγ hclosed).symm = of γ hγ.symm hclosed.symm :=
  ext (by simp) (by simp) fun t ht ↦ by
    rw [symm_a, symm_b, of_a, of_b] at ht
    rw [coe_symm, of_apply _ _ _ (uIcc_comm (a := a) (b := b) ▸ ht), of_apply _ _ _ ht]

/-- Reversing a closed curve preserves its geometric image on its parameter interval. -/
theorem image_symm (γ : AbsolutelyContinuousClosedCurve) :
    γ.symm '' uIcc γ.symm.a γ.symm.b = γ '' uIcc γ.a γ.b := by
  simp [uIcc_comm]

/-- Every simple closed absolutely continuous curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) has either `γ` or `γ.symm` with increasing
endpoints `a < b` and `InjOn` on `Ico a b`. -/
theorem lt_and_injOn_or_symm_lt_and_injOn_of_ne {γ : AbsolutelyContinuousClosedCurve}
    (hab : γ.a ≠ γ.b) (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))) :
    (γ.a < γ.b ∧ InjOn γ (Ico γ.a γ.b)) ∨
      (γ.symm.a < γ.symm.b ∧ InjOn γ.symm (Ico γ.symm.a γ.symm.b)) := by
  rcases lt_or_gt_of_ne hab with hlt | hlt
  · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hinj
    exact Or.inl ⟨hlt, hinj⟩
  · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hinj
    exact Or.inr ⟨by simpa using hlt, by simpa using hinj⟩

/-- Reduce a property of a simple closed absolutely continuous curve (`γ.a ≠ γ.b`,
`InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b))`) to the increasing-endpoint case `η.a < η.b` with
`InjOn η (Ico η.a η.b)`, provided the property passes from `γ.symm` to `γ`. -/
theorem induction_on_lt {P : AbsolutelyContinuousClosedCurve → Prop}
    {γ : AbsolutelyContinuousClosedCurve} (hab : γ.a ≠ γ.b)
    (hinj : InjOn γ (Ico (min γ.a γ.b) (max γ.a γ.b)))
    (hlt : ∀ {η : AbsolutelyContinuousClosedCurve}, η.a < η.b → InjOn η (Ico η.a η.b) → P η)
    (hsymm : P γ.symm → P γ) : P γ := by
  rcases lt_and_injOn_or_symm_lt_and_injOn_of_ne hab hinj with ⟨h, h'⟩ | ⟨h, h'⟩
  · exact hlt h h'
  · exact hsymm (hlt h h')

end AbsolutelyContinuousClosedCurve

namespace Cycle

/-- Reversing a generator does not change its cycle trace. -/
theorem trace_of_symm (γ : AbsolutelyContinuousClosedCurve) :
    trace (FreeAddCommGroup.of γ.symm) = trace (FreeAddCommGroup.of γ) := by
  rw [trace_of, trace_of, AbsolutelyContinuousClosedCurve.image_symm]

/-- Reversing a generator preserves containment in any target set. -/
theorem isIn_of_symm_iff {γ : AbsolutelyContinuousClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAddCommGroup.of γ.symm) Ω ↔ IsIn (FreeAddCommGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_symm]

/-- Integrating over a reversed generator negates the contour integral. -/
theorem integral_of_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : AbsolutelyContinuousClosedCurve) (f : ℂ → E) :
    integral f (FreeAddCommGroup.of γ.symm) = -integral f (FreeAddCommGroup.of γ) := by
  simp only [integral_of, AbsolutelyContinuousClosedCurve.coe_symm,
    AbsolutelyContinuousClosedCurve.symm_a, AbsolutelyContinuousClosedCurve.symm_b]
  rw [intervalIntegral.integral_symm]

/-- At any point outside the image of `γ`, reversing `γ` negates its cycle winding number. -/
theorem windingNumber_of_symm (γ : AbsolutelyContinuousClosedCurve) {z : ℂ}
    (hz : z ∉ γ '' uIcc γ.a γ.b) :
    windingNumber z (FreeAddCommGroup.of γ.symm) =
      -windingNumber z (FreeAddCommGroup.of γ) := by
  have hz' : z ∉ trace (FreeAddCommGroup.of γ) := by rwa [trace_of]
  have hzsymm : z ∉ trace (FreeAddCommGroup.of γ.symm) := by rwa [trace_of_symm]
  rw [windingNumber_eq_integral_of_not_mem_trace _ hzsymm,
    windingNumber_eq_integral_of_not_mem_trace _ hz', integral_of_symm, mul_neg]

/-- Vanishing of the cycle winding number of a generator is preserved under orientation reversal,
even at points on the trace. -/
theorem windingNumber_of_symm_eq_zero_iff (γ : AbsolutelyContinuousClosedCurve) (z : ℂ) :
    windingNumber z (FreeAddCommGroup.of γ.symm) = 0 ↔
      windingNumber z (FreeAddCommGroup.of γ) = 0 := by
  simp only [windingNumber_of, AbsolutelyContinuousClosedCurve.coe_symm,
    AbsolutelyContinuousClosedCurve.symm_a, AbsolutelyContinuousClosedCurve.symm_b]
  exact ⟨TauCeti.Contour.windingNumber_eq_zero_symm, TauCeti.Contour.windingNumber_eq_zero_symm⟩

/-- Null-homology of a generator is preserved under orientation reversal. -/
theorem isNullHomologous_of_symm_iff {γ : AbsolutelyContinuousClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAddCommGroup.of γ.symm) Ω ↔
      IsNullHomologous (FreeAddCommGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_symm_eq_zero_iff]

end Cycle

end TauCeti.Contour

end
