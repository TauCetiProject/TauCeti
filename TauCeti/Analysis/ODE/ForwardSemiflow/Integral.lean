/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import TauCeti.Analysis.ODE.ForwardSemiflow.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integral equation for maximal forward semiflows

Proves `LocallyLipschitzOn.forwardSemiflow_eq_add_integral`: for a locally Lipschitz vector field
`X` on `S`, every trajectory `forwardSemiflow X S · x` satisfies the Volterra integral equation
`forwardSemiflow X S t x = x + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X S s x)` at every `t` in its
maximal forward interval `forwardSemiflowInterval X S x`.
-/

public section

open Set intervalIntegral

namespace LocallyLipschitzOn

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- For a locally Lipschitz vector field `X` on `S` in a Banach space, `forwardSemiflow X S · x`
satisfies the integral equation at every time `t` in its maximal forward interval. -/
theorem forwardSemiflow_eq_add_integral {S : Set E} {X : E → E} (hX : LocallyLipschitzOn S X)
    {x : E} {t : ℝ} (ht : t ∈ forwardSemiflowInterval X S x) :
    forwardSemiflow X S t x = x + ∫ s in (0 : ℝ)..t, X (forwardSemiflow X S s x) := by
  have ht0 : 0 ≤ t := nonneg_of_mem_forwardSemiflowInterval ht
  have hsub : Icc 0 t ⊆ forwardSemiflowInterval X S x :=
    Icc_subset_forwardSemiflowInterval_of_mem ht
  have hcont : ContinuousOn (fun s ↦ forwardSemiflow X S s x) (Icc 0 t) := fun s hs ↦
    ((hX.hasDerivWithinAt_forwardSemiflow (hsub hs)).continuousWithinAt).mono hsub
  have hderiv : ∀ s ∈ Ioo 0 t,
      HasDerivAt (fun r ↦ forwardSemiflow X S r x) (X (forwardSemiflow X S s x)) s :=
    fun s hs ↦ hX.hasDerivAt_forwardSemiflow (hsub (Ioo_subset_Icc_self hs)) hs.1
  have hint : IntervalIntegrable (fun s ↦ X (forwardSemiflow X S s x)) MeasureTheory.volume 0 t :=
    ((hX.continuousOn.comp hcont fun s hs ↦ forwardSemiflow_mem (hsub hs)).mono
      (uIcc_of_le ht0).subset).intervalIntegrable
  have hFTC := integral_eq_sub_of_hasDerivAt_of_le ht0 hcont hderiv hint
  rw [forwardSemiflow_zero] at hFTC
  exact eq_add_of_sub_eq' hFTC.symm

end LocallyLipschitzOn
