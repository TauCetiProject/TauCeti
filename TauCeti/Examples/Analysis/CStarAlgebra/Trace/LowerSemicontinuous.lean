/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.ContinuousMap
public import Mathlib.Topology.ContinuousMap.ContinuousSqrt
public import TauCeti.Analysis.CStarAlgebra.Trace.LowerSemicontinuous

/-!
# Checks: a lower semicontinuous trace that is not semifinite

A lower semicontinuous trace that is not semifinite, on `C(X, ℂ)` for a compact space `X` and a
point `x₀ ∈ X`: the map `τ` equal to `0` on the positive functions vanishing at `x₀` and to `∞` on
the other positive functions (`TauCeti.TraceExamples.pointTrace`) is a trace. It is lower
semicontinuous, since `{f ≥ 0 : f(x₀) ≠ 0}` is open, and it is not semifinite: the constant
function `1` has `τ(1) = ∞`, while its minorants of finite trace have trace `0`.

We work on `C(X, ℂ)` with `X` compact so that the constant `1` is a witness; on `C₀(X, ℂ)` for
`X` locally compact one would use a Urysohn function positive at `x₀`.
-/

public section

open scoped ENNReal NNReal ComplexOrder

namespace TauCeti.TraceExamples

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- The trace on `C(X, ℂ)` that is `0` at functions vanishing at `x₀` and `∞` elsewhere. -/
noncomputable def pointTrace (x₀ : X) : C(X, ℂ) → ℝ≥0∞ :=
  open Classical in fun f ↦ if f x₀ = 0 then 0 else ∞

omit [CompactSpace X] in
/-- The value of `pointTrace`. -/
theorem pointTrace_apply (x₀ : X) (f : C(X, ℂ)) :
    pointTrace x₀ f = if f x₀ = 0 then 0 else ∞ := by
  simp only [pointTrace]

/-- `pointTrace x₀` is a trace. -/
theorem isTrace_pointTrace (x₀ : X) : IsTrace (pointTrace x₀) where
  map_add_of_nonneg f g hf hg := by
    have hf₀ : 0 ≤ f x₀ := hf x₀
    have hg₀ : 0 ≤ g x₀ := hg x₀
    simp only [pointTrace_apply, ContinuousMap.add_apply, add_eq_zero_iff_of_nonneg hf₀ hg₀]
    by_cases h₁ : f x₀ = 0 <;> by_cases h₂ : g x₀ = 0 <;> simp [h₁, h₂]
  map_nnreal_smul_of_nonneg c f _ := by
    rcases eq_or_ne c 0 with rfl | hc
    · simp [pointTrace_apply]
    · have hc' : ((c : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hc
      by_cases h : f x₀ = 0 <;>
        simp [pointTrace_apply, ← Complex.coe_smul, h, hc', ENNReal.mul_top, hc]
  map_star_mul_self f := by rw [mul_comm]

omit [CompactSpace X] in
/-- `pointTrace x₀` is lower semicontinuous on the positive cone. -/
theorem lowerSemicontinuousOn_pointTrace (x₀ : X) :
    LowerSemicontinuousOn (pointTrace x₀) {f | 0 ≤ f} := by
  intro f _ y hy
  have hf : f x₀ ≠ 0 := by
    intro h
    simp [pointTrace_apply, h] at hy
  have hopen : IsOpen {g : C(X, ℂ) | g x₀ ≠ 0} :=
    isOpen_ne_fun (continuous_eval_const x₀) continuous_const
  filter_upwards [nhdsWithin_le_nhds (hopen.mem_nhds hf)] with g hg
  simpa [pointTrace_apply, hg] using hy.trans_le le_top

/-- `pointTrace x₀` is not semifinite: `τ(1) = ∞`, but the minorants of `1` of finite trace have
trace `0`. -/
theorem not_isSemifinite_pointTrace (x₀ : X) : ¬ IsSemifinite (pointTrace x₀) := by
  intro h
  have h1 := isSemifinite_iff.1 h (zero_le_one : (0 : C(X, ℂ)) ≤ 1)
  have hsup : ⨆ (y : C(X, ℂ)) (_ : 0 ≤ y ∧ y ≤ 1 ∧ pointTrace x₀ y < ∞), pointTrace x₀ y = 0 :=
    by
    refine le_antisymm (iSup₂_le fun y hy ↦ ?_) zero_le
    have := hy.2.2
    rw [pointTrace_apply] at this ⊢
    split_ifs at this ⊢
    · exact le_rfl
    · simp at this
  rw [hsup, pointTrace_apply] at h1
  simp at h1

end TauCeti.TraceExamples
