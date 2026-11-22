/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Exponential
public import TauCeti.Analysis.ODE.ForwardSemiflow.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Closed-form model checks for inward forward semiflows

Two explicit one-dimensional checks verifying `TauCeti.forwardSemiflowInterval` and
`TauCeti.forwardSemiflow` against closed-form solutions on `Ici (0 : ℝ)` and `Icc (0 : ℝ) 1`:

* `TauCeti.forwardSemiflowInterval_const_one_Ici`, `TauCeti.forwardSemiflow_const_one_Ici`:
  constant inward field `X = 1` on `[0, ∞)`.
* `TauCeti.forwardSemiflowInterval_half_sub_Icc`, `TauCeti.forwardSemiflow_half_sub_Icc`:
  affine inward field `X y = 1 / 2 - y` on `[0, 1]`.
-/

public section

open Set

namespace TauCeti

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the constant inward field `X = 1`
has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_const_one_Ici {x : ℝ} (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflowInterval (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦
    Ico_subset_forwardSemiflowInterval (b := t + 1) (by linarith [mem_Ici.mp ht]) (add_zero x)
      (fun _ hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
      (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt) ⟨ht, lt_add_one t⟩

/-- Closed-form check on the closed half-line `Ici (0 : ℝ)`: the forward semiflow of the constant
inward field `X = 1` is `forwardSemiflow (fun _ ↦ 1) (Ici 0) t x = x + t`. -/
theorem forwardSemiflow_const_one_Ici {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Ici (0 : ℝ)) :
    forwardSemiflow (fun _ : ℝ ↦ (1 : ℝ)) (Ici (0 : ℝ)) t x = x + t :=
  (((LipschitzWith.const (1 : ℝ)).locallyLipschitz.locallyLipschitzOn).eqOn_forwardSemiflow
    (γ := fun s ↦ x + s) (b := t + 1) (by linarith) (add_zero x)
    (fun _ hs ↦ mem_Ici.mpr (by linarith [mem_Ici.mp hx, hs.1]))
    (fun s _ ↦ ((hasDerivAt_id' s).const_add x).hasDerivWithinAt) ⟨ht, lt_add_one t⟩).symm

/-- Explicit trajectory for the affine inward field `y ↦ 1 / 2 - y` on `Icc 0 1`. -/
private theorem mapsTo_and_deriv_half_sub_Icc {x b : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    let γ : ℝ → ℝ := fun s ↦ 1 / 2 + (x - 1 / 2) * Real.exp (-s)
    MapsTo γ (Ico 0 b) (Icc (0 : ℝ) 1) ∧
      ∀ s ∈ Ico 0 b, HasDerivWithinAt γ (1 / 2 - γ s) (Ico 0 b) s :=
  ⟨fun s hs ↦ by
      have := Real.exp_pos (-s); have := Real.exp_le_one_iff.mpr (by linarith [hs.1] : -s ≤ 0)
      exact ⟨by nlinarith [hx.1, hx.2], by nlinarith [hx.1, hx.2]⟩,
    fun s _ ↦ ((((Real.hasDerivAt_exp (-s)).comp s (hasDerivAt_id' s).neg).const_mul
      (x - 1 / 2)).const_add (1 / 2 : ℝ) |>.congr_deriv (by simp)).hasDerivWithinAt⟩

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the affine inward field
`X y = 1 / 2 - y` has maximal forward interval `Ici 0`. -/
theorem forwardSemiflowInterval_half_sub_Icc {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflowInterval (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) x = Ici 0 :=
  Subset.antisymm (fun _ ht ↦ nonneg_of_mem_forwardSemiflowInterval ht) fun t ht ↦
    let h := mapsTo_and_deriv_half_sub_Icc (b := t + 1) hx
    Ico_subset_forwardSemiflowInterval (by linarith [mem_Ici.mp ht]) (by simp) h.1 h.2
      ⟨ht, lt_add_one t⟩

/-- Closed-form check on the unit interval `Icc (0 : ℝ) 1`: the forward semiflow of the affine
inward field `X y = 1 / 2 - y` is `1 / 2 + (x - 1 / 2) * exp (-t)`. -/
theorem forwardSemiflow_half_sub_Icc {t x : ℝ} (ht : 0 ≤ t) (hx : x ∈ Icc (0 : ℝ) 1) :
    forwardSemiflow (fun y : ℝ ↦ 1 / 2 - y) (Icc (0 : ℝ) 1) t x =
      1 / 2 + (x - 1 / 2) * Real.exp (-t) :=
  let h := mapsTo_and_deriv_half_sub_Icc (b := t + 1) hx
  ((((LipschitzWith.const (1 / 2 : ℝ)).sub
    LipschitzWith.id).locallyLipschitz.locallyLipschitzOn).eqOn_forwardSemiflow
    (γ := fun s ↦ 1 / 2 + (x - 1 / 2) * Real.exp (-s))
    (b := t + 1) (by linarith) (by simp) h.1 h.2 ⟨ht, lt_add_one t⟩).symm

end TauCeti
