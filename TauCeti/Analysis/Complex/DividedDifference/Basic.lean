/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DSlope
public import TauCeti.Analysis.Complex.PartialDslope
import Mathlib.Analysis.Calculus.FDeriv.Pi
import TauCeti.Analysis.Calculus.DSlope.Basic

/-!
# Coordinate divided differences of functions on `ℂⁿ`

This file supplements `TauCeti.Analysis.Complex.PartialDslope` with algebraic linearity lemmas,
`partialDslope_update_self`, and uniqueness of `TauCeti.partialDslope i f ζ` without global
differentiability assumptions (`TauCeti.eq_partialDslope_apply_of_sub_smul_eq`,
`TauCeti.eq_partialDslope_of_sub_smul_eq`).

## Main declarations

* `TauCeti.eq_update_add_sub_mul_partialDslope`: scalar form
  `f z = f (update z i ζ) + (z i - ζ) * partialDslope i f ζ z`.
* `TauCeti.eq_partialDslope_apply_of_sub_smul_eq`, `TauCeti.eq_partialDslope_of_sub_smul_eq`:
  uniqueness of continuous quotients satisfying the coordinate division identity.
-/

public section

open Function

namespace TauCeti

variable {ι E : Type*} [DecidableEq ι] [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The coordinate divided difference of a constant function is zero. -/
@[simp]
theorem partialDslope_const (i : ι) (c : E) (ζ : ℂ) :
    partialDslope i (fun _ : ι → ℂ ↦ c) ζ = 0 := by
  ext z
  simp [partialDslope_apply]

/-- The coordinate divided difference of the zero function is zero. -/
@[simp]
theorem partialDslope_zero_fun (i : ι) (ζ : ℂ) :
    partialDslope i (0 : (ι → ℂ) → E) ζ = 0 :=
  partialDslope_const i 0 ζ

/-- Evaluating `partialDslope i f ζ` at `update z i ζ` gives `partialDeriv i f (update z i ζ)`. -/
@[simp]
theorem partialDslope_update_self [Finite ι] {f : (ι → ℂ) → E} {z : ι → ℂ} {i : ι} {ζ : ℂ}
    (hf : DifferentiableAt ℂ f (update z i ζ)) :
    partialDslope i f ζ (update z i ζ) = partialDeriv i f (update z i ζ) :=
  partialDslope_of_eq hf (update_self i ζ z)

/-- Exact coordinate division identity for complex-valued functions:
`f z = f (update z i ζ) + (z i - ζ) * partialDslope i f ζ z`. -/
theorem eq_update_add_sub_mul_partialDslope (i : ι) (f : (ι → ℂ) → ℂ) (ζ : ℂ) (z : ι → ℂ) :
    f z = f (update z i ζ) + (z i - ζ) * partialDslope i f ζ z := by
  have h := sub_smul_partialDslope i f ζ z
  rw [smul_eq_mul] at h
  linear_combination -h

/-- Pointwise uniqueness of the coordinate divided difference: if `g : (ι → ℂ) → E` satisfies the
division identity `(y i - ζ) • g y = f y - f (update y i ζ)` everywhere and is continuous at `z`
whenever `z i = ζ`, then `g z = partialDslope i f ζ z`. -/
theorem eq_partialDslope_apply_of_sub_smul_eq {f g : (ι → ℂ) → E} {i : ι} {ζ : ℂ} {z : ι → ℂ}
    (hg : z i = ζ → ContinuousAt g z) (h : ∀ y, (y i - ζ) • g y = f y - f (update y i ζ)) :
    g z = partialDslope i f ζ z := by
  rcases ne_or_eq (z i) ζ with hz | rfl
  · rw [partialDslope_of_ne hz, ← h z, inv_smul_smul₀ (sub_ne_zero.mpr hz)]
  · have hcont : ContinuousAt (fun w ↦ g (update z i w)) (z i) := by
      have hupd : ContinuousAt (update z i) (z i) :=
        (continuous_const.update i continuous_id).continuousAt
      have hg' : ContinuousAt g (update z i (z i)) := by
        simpa only [update_eq_self] using hg rfl
      exact hg'.comp hupd
    have htend : Filter.Tendsto (slope (fun w ↦ f (update z i w)) (z i))
        (nhdsWithin (z i) {z i}ᶜ) (nhds (g z)) := by
      have heq : slope (fun w ↦ f (update z i w)) (z i) =ᶠ[nhdsWithin (z i) {z i}ᶜ]
          fun w ↦ g (update z i w) := by
        filter_upwards [self_mem_nhdsWithin] with w (hw : w ≠ z i)
        have hy := h (update z i w)
        simp only [update_self, update_idem] at hy
        rw [slope_def_module, ← hy, inv_smul_smul₀ (sub_ne_zero.mpr hw)]
      have hg_tend : Filter.Tendsto (fun w ↦ g (update z i w))
          (nhdsWithin (z i) {z i}ᶜ) (nhds (g z)) := by
        simpa [update_eq_self] using hcont.tendsto.mono_left nhdsWithin_le_nhds
      exact hg_tend.congr' heq.symm
    rw [partialDslope_apply, dslope_same, (hasDerivAt_iff_tendsto_slope.mpr htend).deriv]

/-- **Uniqueness of the coordinate divided difference.** Any continuous function
`g : (ι → ℂ) → E` satisfying `(z i - ζ) • g z = f z - f (update z i ζ)` everywhere equals
`partialDslope i f ζ`. -/
theorem eq_partialDslope_of_sub_smul_eq {f g : (ι → ℂ) → E} {i : ι} {ζ : ℂ}
    (hg : Continuous g) (h : ∀ z, (z i - ζ) • g z = f z - f (update z i ζ)) :
    g = partialDslope i f ζ :=
  funext fun _ ↦ eq_partialDslope_apply_of_sub_smul_eq (fun _ ↦ hg.continuousAt) h

/-- `partialDslope i · ζ` commutes with scalar multiplication by a constant. -/
@[simp]
theorem partialDslope_const_smul (c : ℂ) (i : ι) (f : (ι → ℂ) → E) (ζ : ℂ) :
    partialDslope i (c • f) ζ = c • partialDslope i f ζ := by
  ext z
  rw [Pi.smul_apply, partialDslope_apply, partialDslope_apply, ← Pi.smul_apply]
  exact congrFun (dslope_const_smul c (fun w ↦ f (update z i w)) ζ) (z i)

/-- `partialDslope i · ζ` commutes with left multiplication by a constant. -/
@[simp]
theorem partialDslope_const_mul (c : ℂ) (i : ι) (f : (ι → ℂ) → ℂ) (ζ : ℂ) :
    partialDslope i (fun z ↦ c * f z) ζ = fun z ↦ c * partialDslope i f ζ z := by
  simpa only [Pi.smul_def, smul_eq_mul] using partialDslope_const_smul c i f ζ

/-- `partialDslope i · ζ` is additive on entire functions. -/
theorem partialDslope_add [Finite ι] {f g : (ι → ℂ) → E} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (i : ι) (ζ : ℂ) :
    partialDslope i (f + g) ζ = partialDslope i f ζ + partialDslope i g ζ := by
  have := Fintype.ofFinite ι
  ext z
  have hfu : DifferentiableAt ℂ (fun w ↦ f (update z i w)) ζ :=
    (hf (update z i ζ)).comp ζ (hasFDerivAt_update z ζ).differentiableAt
  have hgu : DifferentiableAt ℂ (fun w ↦ g (update z i w)) ζ :=
    (hg (update z i ζ)).comp ζ (hasFDerivAt_update z ζ).differentiableAt
  rw [Pi.add_apply, partialDslope_apply, partialDslope_apply, partialDslope_apply]
  exact congrFun (dslope_add hfu hgu) (z i)

end TauCeti
