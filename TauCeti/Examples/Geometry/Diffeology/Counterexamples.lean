/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Diffeology.Induced

import Mathlib.Analysis.Calculus.Deriv.Abs
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Examples: non-plot and non-diffeomorphism counterexamples on `ℝ`

Concrete counterexamples on `ℝ` with its standard diffeology:

* `not_dSmooth_abs` and `not_isPlot_abs`: `abs : ℝ → ℝ` is continuous (`C⁰`) without being
  diffeologically smooth, and `u ↦ |u 0|` from `𝔼¹` to `ℝ` is not a plot.
* `cubeEquiv`, `dSmooth_cubeEquiv`, `not_dSmooth_cubeEquiv_symm`, `not_isInduction_cubeEquiv`, and
  `not_isSubduction_cubeEquiv`: the cubing map `x ↦ x ^ 3` on `ℝ` is a diffeologically smooth
  bijection whose inverse (the real cube root) is not diffeologically smooth, so `cubeEquiv` is
  neither an induction nor a subduction.

## References

* P. Iglesias-Zemmour, *Diffeology*, Mathematical Surveys and Monographs **185**, American
  Mathematical Society (2013), §1.15, §1.29, and §1.48.
-/

public noncomputable section

open Filter Function
open scoped ContDiff

namespace TauCeti.Diffeology

local macro:max "𝔼" noWs n:superscript(term) : term =>
  `(EuclideanSpace ℝ (Fin $(⟨n.raw[0]⟩)))

/-- The absolute value `abs : ℝ → ℝ` is continuous (`C⁰`) on `ℝ` without being diffeologically
smooth. -/
theorem not_dSmooth_abs : ¬ _root_.Diffeology.DSmooth (abs : ℝ → ℝ) := fun h ↦
  not_differentiableAt_abs_zero ((_root_.Diffeology.dSmooth_iff_contDiff.mp h).differentiable
    (by simp) 0)

/-- The `C⁰` curve `u ↦ |u 0|` from `𝔼¹` to `ℝ` is not a plot of `ℝ`. -/
theorem not_isPlot_abs : ¬ _root_.Diffeology.IsPlot (fun u : 𝔼¹ ↦ |u 0|) := fun hp ↦
  not_dSmooth_abs <|
    hp.dSmooth.comp
      ((ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans
        (EuclideanSpace.equiv (Fin 1) ℝ).symm).contDiff.dSmooth

/-- The cubing bijection `x ↦ x ^ 3` on `ℝ`, bundled as an equivalence `ℝ ≃ ℝ`. -/
def cubeEquiv : ℝ ≃ ℝ :=
  Equiv.ofBijective (fun x : ℝ ↦ x ^ 3) <| by
    have hodd : Odd 3 := by decide
    refine ⟨hodd.strictMono_pow.injective,
      (continuous_pow 3).surjective (tendsto_pow_atTop (by decide)) ?_⟩
    simpa only [Function.comp_def, hodd.neg_pow, neg_neg] using
      (tendsto_neg_atTop_atBot.comp (tendsto_pow_atTop (α := ℝ) (n := 3) (by decide))).comp
        tendsto_neg_atBot_atTop

/-- Evaluating `cubeEquiv` at `x` returns `x ^ 3`. -/
@[simp]
theorem cubeEquiv_apply (x : ℝ) : cubeEquiv x = x ^ 3 :=
  (rfl)

/-- `cubeEquiv` maps `0` to `0`. -/
theorem cubeEquiv_zero : cubeEquiv 0 = 0 := by
  simp

/-- `cubeEquiv.symm` maps `0` to `0`. -/
@[simp]
theorem cubeEquiv_symm_zero : cubeEquiv.symm 0 = 0 :=
  cubeEquiv.symm_apply_eq.mpr cubeEquiv_zero.symm

/-- `cubeEquiv : ℝ ≃ ℝ` is diffeologically smooth. -/
@[fun_prop]
theorem dSmooth_cubeEquiv : _root_.Diffeology.DSmooth cubeEquiv :=
  _root_.Diffeology.dSmooth_iff_contDiff.mpr (contDiff_id.pow 3)

/-- The real cube root `cubeEquiv.symm : ℝ → ℝ` is not diffeologically smooth, even though
`cubeEquiv` is a smooth bijection. -/
theorem not_dSmooth_cubeEquiv_symm : ¬ _root_.Diffeology.DSmooth cubeEquiv.symm := by
  intro h
  have hg : DifferentiableAt ℝ cubeEquiv.symm 0 :=
    (_root_.Diffeology.dSmooth_iff_contDiff.mp h).differentiable (by simp) 0
  have hf : HasDerivAt cubeEquiv (3 * (0 : ℝ) ^ (3 - 1)) 0 := hasDerivAt_pow 3 (0 : ℝ)
  have hcomp : HasDerivAt (cubeEquiv.symm ∘ cubeEquiv)
      (deriv cubeEquiv.symm 0 * (3 * (0 : ℝ) ^ (3 - 1))) 0 := by
    have hg0 : HasDerivAt cubeEquiv.symm (deriv cubeEquiv.symm 0) (cubeEquiv 0) := by
      simpa only [cubeEquiv_zero] using hg.hasDerivAt
    exact hg0.comp 0 hf
  have hid : HasDerivAt (cubeEquiv.symm ∘ cubeEquiv) 1 0 := by
    have heq : cubeEquiv.symm ∘ cubeEquiv = id := funext cubeEquiv.left_inv
    simpa only [heq] using hasDerivAt_id (0 : ℝ)
  have h10 : (1 : ℝ) = deriv cubeEquiv.symm 0 * (3 * (0 : ℝ) ^ (3 - 1)) := hid.unique hcomp
  norm_num at h10

/-- `cubeEquiv : ℝ → ℝ` is a smooth bijection that is not an induction. -/
theorem not_isInduction_cubeEquiv : ¬ IsInduction (cubeEquiv : ℝ → ℝ) := fun h ↦
  not_dSmooth_cubeEquiv_symm <| h.dSmooth_iff.mpr <| by
    have heq : (cubeEquiv : ℝ → ℝ) ∘ cubeEquiv.symm = id := funext cubeEquiv.right_inv
    simpa only [heq] using _root_.Diffeology.dSmooth_id

/-- `cubeEquiv : ℝ → ℝ` is a smooth bijection that is not a subduction. -/
theorem not_isSubduction_cubeEquiv : ¬ IsSubduction (cubeEquiv : ℝ → ℝ) := fun h ↦
  not_dSmooth_cubeEquiv_symm <| (h.dSmooth_iff cubeEquiv.symm).mpr <| by
    have heq : cubeEquiv.symm ∘ (cubeEquiv : ℝ → ℝ) = id := funext cubeEquiv.left_inv
    simpa only [heq] using _root_.Diffeology.dSmooth_id

end TauCeti.Diffeology
