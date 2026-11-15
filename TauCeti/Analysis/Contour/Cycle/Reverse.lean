/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Contour.Cycle.Basic
import TauCeti.Analysis.Contour.Winding.Number.Reverse

/-!
# Orientation reversal of closed piecewise-`C¹` curves and cycle generators

Every `TauCeti.Contour.PiecewiseC1ClosedCurve` carries an ordered parameter pair `(a, b)` together
with a parametrization on the unordered interval `uIcc a b`. Swapping `(a, b)` to `(b, a)` reverses
the curve's orientation without changing its canonical extension to `ℝ` or its geometric trace.

Because the canonical extension to `ℝ` is unchanged (`PiecewiseC1ClosedCurve.coe_symm`), reversing a
generator negates its contour integral unconditionally (`Cycle.integral_of_symm`), negates its
winding number at every point off its image (`Cycle.windingNumber_of_symm`), and preserves both
domain containment and null-homology (`Cycle.isIn_of_symm_iff`,
`Cycle.isNullHomologous_of_symm_iff`).

## Main definitions

* `TauCeti.Contour.PiecewiseC1ClosedCurve.symm`: reverse the orientation of a bundled closed
  piecewise-`C¹` curve by swapping its endpoints.

## Main results

* `TauCeti.Contour.PiecewiseC1ClosedCurve.ext_of_eqOn`: two bundled closed curves with the same
  endpoints that agree on their parameter interval are equal.
* `TauCeti.Contour.PiecewiseC1ClosedCurve.coe_symm`, `symm_symm`, `image_symm`: reversal leaves the
  canonical extension to `ℝ` and the interval image unchanged and is an involution.
* `TauCeti.Contour.Cycle.trace_of_symm`, `isIn_of_symm_iff`: reversal of a generator preserves its
  cycle trace and containment.
* `TauCeti.Contour.Cycle.integral_of_symm`: reversal of a generator negates its cycle integral.
* `TauCeti.Contour.Cycle.windingNumber_of_symm`, `windingNumber_of_symm_eq_zero_iff`,
  `isNullHomologous_of_symm_iff`: effect of generator reversal on cycle winding numbers and
  null-homology.
-/

public section

noncomputable section

open MeasureTheory Set intervalIntegral
open scoped Interval

namespace TauCeti.Contour

namespace PiecewiseC1ClosedCurve

/-- Outside its parameter interval `uIcc γ.a γ.b`, the canonical extension of a bundled closed curve
to `ℝ` vanishes. -/
theorem coe_apply_of_notMem (γ : PiecewiseC1ClosedCurve) {t : ℝ}
    (ht : t ∉ uIcc γ.a γ.b) : γ t = 0 :=
  Function.extend_apply' _ _ _ fun ⟨s, hs⟩ ↦ ht (hs ▸ s.2)

/-- Two bundled closed curves with equal initial and terminal parameters that agree on their
parameter interval are equal. -/
theorem ext_of_eqOn {γ₁ γ₂ : PiecewiseC1ClosedCurve} (ha : γ₁.a = γ₂.a) (hb : γ₁.b = γ₂.b)
    (h : EqOn (γ₁ : ℝ → ℂ) (γ₂ : ℝ → ℂ) (uIcc γ₁.a γ₁.b)) : γ₁ = γ₂ := by
  cases γ₁ with
  | mk a₁ b₁ toFun₁ hγ₁ hcl₁ =>
    cases γ₂ with
    | mk a₂ b₂ toFun₂ hγ₂ hcl₂ =>
      dsimp only at ha hb
      subst ha hb
      refine PiecewiseC1ClosedCurve.ext rfl rfl (heq_of_eq ?_)
      funext t
      have ht := h t.2
      rwa [coe_apply, coe_apply] at ht

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
theorem symm_a (γ : PiecewiseC1ClosedCurve) : γ.symm.a = γ.b := by
  rw [symm, of_a]

/-- Reversing a closed curve makes its old initial parameter the new terminal parameter. -/
@[simp]
theorem symm_b (γ : PiecewiseC1ClosedCurve) : γ.symm.b = γ.a := by
  rw [symm, of_b]

/-- Reversing a bundled closed curve leaves its canonical extension to `ℝ` unchanged. -/
@[simp]
theorem coe_symm (γ : PiecewiseC1ClosedCurve) : (γ.symm : ℝ → ℂ) = γ := by
  ext t
  by_cases ht : t ∈ uIcc γ.b γ.a
  · rw [symm, of_apply γ γ.isPiecewiseC1On.symm γ.source_eq_target.symm ht]
  · have ht₁ : t ∉ uIcc γ.symm.a γ.symm.b := by rwa [symm_a, symm_b]
    have ht₂ : t ∉ uIcc γ.a γ.b := by rwa [uIcc_comm] at ht
    rw [coe_apply_of_notMem γ.symm ht₁, coe_apply_of_notMem γ ht₂]

/-- Orientation reversal on bundled closed curves is an involution. -/
@[simp]
theorem symm_symm (γ : PiecewiseC1ClosedCurve) : γ.symm.symm = γ :=
  ext_of_eqOn (by simp) (by simp) fun t _ ↦ by simp

/-- Reversing a curve bundled via `PiecewiseC1ClosedCurve.of` swaps the endpoints of `of`. -/
@[simp]
theorem of_symm {a b : ℝ} (γ : ℝ → ℂ) (hγ : IsPiecewiseC1On γ a b) (hclosed : γ a = γ b) :
    (of γ hγ hclosed).symm = of γ hγ.symm hclosed.symm :=
  ext_of_eqOn (by simp) (by simp) fun t ht ↦ by
    rw [symm_a, symm_b, of_a, of_b] at ht
    have ht' : t ∈ uIcc a b := by rwa [uIcc_comm] at ht
    rw [coe_symm, of_apply γ hγ hclosed ht', of_apply γ hγ.symm hclosed.symm ht]

/-- Reversing a closed curve preserves its geometric image on its parameter interval. -/
theorem image_symm (γ : PiecewiseC1ClosedCurve) :
    γ.symm '' uIcc γ.symm.a γ.symm.b = γ '' uIcc γ.a γ.b := by
  have hu : uIcc γ.symm.a γ.symm.b = uIcc γ.a γ.b := by
    rw [symm_a, symm_b, uIcc_comm]
  exact (congrArg (· '' uIcc γ.symm.a γ.symm.b) (coe_symm γ)).trans
    (congrArg ((γ : ℝ → ℂ) '' ·) hu)

end PiecewiseC1ClosedCurve

namespace Cycle

/-- Reversing a generator does not change its cycle trace. -/
theorem trace_of_symm (γ : PiecewiseC1ClosedCurve) :
    trace (FreeAbelianGroup.of γ.symm) = trace (FreeAbelianGroup.of γ) := by
  rw [trace_of, trace_of]
  exact PiecewiseC1ClosedCurve.image_symm γ

/-- Reversing a generator preserves containment in any target set. -/
theorem isIn_of_symm_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsIn (FreeAbelianGroup.of γ.symm) Ω ↔ IsIn (FreeAbelianGroup.of γ) Ω := by
  rw [isIn_iff, isIn_iff, trace_of_symm]

/-- Integrating over a reversed generator negates the contour integral. -/
theorem integral_of_symm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    (γ : PiecewiseC1ClosedCurve) (f : ℂ → E) :
    integral f (FreeAbelianGroup.of γ.symm) = -integral f (FreeAbelianGroup.of γ) := by
  rw [integral_of, integral_of]
  have hfun : (fun t ↦ deriv (γ.symm : ℝ → ℂ) t • f (γ.symm t)) =
      fun t ↦ deriv (γ : ℝ → ℂ) t • f (γ t) := by
    rw [PiecewiseC1ClosedCurve.coe_symm]
  rw [hfun, PiecewiseC1ClosedCurve.symm_a, PiecewiseC1ClosedCurve.symm_b,
    intervalIntegral.integral_symm]

/-- At any point outside the image of `γ`, reversing `γ` negates its cycle winding number. -/
theorem windingNumber_of_symm (γ : PiecewiseC1ClosedCurve) {z : ℂ}
    (hz : z ∉ γ '' uIcc γ.a γ.b) :
    windingNumber z (FreeAbelianGroup.of γ.symm) =
      -windingNumber z (FreeAbelianGroup.of γ) := by
  have hoff : ∀ t ∈ uIcc γ.a γ.b, γ t ≠ z := fun t ht htz ↦ hz ⟨t, ht, htz⟩
  have hint := intervalIntegrable_inv_sub_mul_deriv γ.continuousOn hoff γ.intervalIntegrable_deriv
  rw [windingNumber_of, windingNumber_of]
  have hwn : TauCeti.Contour.windingNumber (γ.symm : ℝ → ℂ) γ.symm.a γ.symm.b z =
      TauCeti.Contour.windingNumber (γ : ℝ → ℂ) γ.b γ.a z := by
    rw [PiecewiseC1ClosedCurve.coe_symm, PiecewiseC1ClosedCurve.symm_a,
      PiecewiseC1ClosedCurve.symm_b]
  rw [hwn]
  exact TauCeti.Contour.windingNumber_symm
    (cauchyPVExistsAt_of_avoidance γ.continuousOn hoff hint)

/-- Vanishing of the cycle winding number of a generator is preserved under orientation reversal,
even at points on the trace. -/
theorem windingNumber_of_symm_eq_zero_iff (γ : PiecewiseC1ClosedCurve) (z : ℂ) :
    windingNumber z (FreeAbelianGroup.of γ.symm) = 0 ↔
      windingNumber z (FreeAbelianGroup.of γ) = 0 := by
  rw [windingNumber_of, windingNumber_of]
  have hwn : TauCeti.Contour.windingNumber (γ.symm : ℝ → ℂ) γ.symm.a γ.symm.b z =
      TauCeti.Contour.windingNumber (γ : ℝ → ℂ) γ.b γ.a z := by
    rw [PiecewiseC1ClosedCurve.coe_symm, PiecewiseC1ClosedCurve.symm_a,
      PiecewiseC1ClosedCurve.symm_b]
  rw [hwn]
  exact ⟨fun h ↦ TauCeti.Contour.windingNumber_eq_zero_symm h,
    fun h ↦ TauCeti.Contour.windingNumber_eq_zero_symm h⟩

/-- Null-homology of a generator is preserved under orientation reversal. -/
theorem isNullHomologous_of_symm_iff {γ : PiecewiseC1ClosedCurve} {Ω : Set ℂ} :
    IsNullHomologous (FreeAbelianGroup.of γ.symm) Ω ↔
      IsNullHomologous (FreeAbelianGroup.of γ) Ω := by
  simp only [isNullHomologous_iff, windingNumber_of_symm_eq_zero_iff]

end Cycle

end TauCeti.Contour

end
