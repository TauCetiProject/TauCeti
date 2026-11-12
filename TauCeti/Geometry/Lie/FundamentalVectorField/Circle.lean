/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Lie.FundamentalVectorField.Linear
public import Mathlib.Geometry.Manifold.Instances.Sphere
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# The circle acting on complex vector spaces

Mathlib's unit circle `Circle ⊆ ℂ` is a Lie group, and it acts on every complex normed space `V`
by scalar multiplication, `z • v = (z : ℂ) • v` (`Circle.smul_def`). This file shows that the
action is smooth (`Circle.instContMDiffSMul`) and computes its fundamental vector fields: an
element `ξ` of the Lie algebra of the circle acts on `V` by multiplication by the complex number
`ι_* ξ`, its image under the derivative at `1` of the inclusion `ι : Circle → ℂ`
(`TauCeti.fundamentalLinearMap_circle_apply`). The velocity of `Circle.exp` at `0`, the generator
of the rotations `t ↦ exp (t i)` of period `2π`, has image `i`
(`TauCeti.mvfderiv_coe_mfderiv_circleExp`),
so this generator acts by `v ↦ i • v`.

These are the inputs for the moment maps of circle actions on complex vector spaces, such as the
rotations of the phase space of a planar mechanical system.

## Main results

* `Circle.contMDiff_coe`: the inclusion `Circle → ℂ` is smooth.
* `Circle.instContMDiffSMul`: the circle acts smoothly on every complex normed space.
* `TauCeti.fundamentalLinearMap_circle_apply`: the fundamental vector field of `ξ` is
  `v ↦ (ι_* ξ) • v`.
* `TauCeti.hasDerivAt_coe_circleExp`: the velocity of `t ↦ exp (t i)` at `t` is `i exp (t i)`.
* `TauCeti.mvfderiv_coe_mfderiv_circleExp`: the generator of `t ↦ exp (t i)` has image `i`.
-/

public section

noncomputable section

open Complex
open scoped Manifold ContDiff

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

attribute [local instance] finrank_real_complex_fact'

namespace Circle

/-- The inclusion of the circle in `ℂ` is smooth: `contMDiff_coe_sphere`, stated for the coercion
`Circle → ℂ`. -/
theorem contMDiff_coe {n : ℕ∞ω} : ContMDiff (𝓡 1) 𝓘(ℝ, ℂ) n fun z : Circle ↦ (z : ℂ) :=
  contMDiff_coe_sphere

/-- The circle acts smoothly on every complex normed space by scalar multiplication. -/
instance instContMDiffSMul {n : ℕ∞ω} : ContMDiffSMul (𝓡 1) 𝓘(ℝ, V) n Circle V where
  contMDiff_smul := by
    have hsmul : ContMDiff (𝓘(ℝ, ℂ).prod 𝓘(ℝ, V)) 𝓘(ℝ, V) n fun p : ℂ × V ↦ p.1 • p.2 := by
      rw [contMDiff_iff]
      exact ⟨continuous_smul, fun _ _ ↦ (contDiff_fst.smul contDiff_snd).contDiffOn⟩
    exact hsmul.comp (contMDiff_coe.prodMap contMDiff_id)

end Circle

namespace TauCeti

/-- **The fundamental vector fields of the circle action.** An element `ξ` of the Lie algebra of
the circle acts on a complex normed space by multiplication by its image `ι_* ξ ∈ ℂ` under the
derivative at `1` of the inclusion `ι : Circle → ℂ`. -/
theorem fundamentalLinearMap_circle_apply (ξ : GroupLieAlgebra (𝓡 1) Circle) (v : V) :
    fundamentalLinearMap (𝓡 1) Circle V ξ v =
      mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1 ξ • v := by
  -- The orbit map of `v` is the inclusion followed by the real-linear map `c ↦ c • v`.
  let L : ℂ →L[ℝ] V := (ContinuousLinearMap.id ℝ ℂ).smulRight v
  have horbit : (fun g : Circle ↦ g • v) = L ∘ (fun z : Circle ↦ (z : ℂ)) := by
    ext g
    simp [L, Circle.smul_def]
  rw [fundamentalLinearMap_apply, horbit,
    mvfderiv_comp_apply_of_differentiableAt L.differentiableAt
      ((Circle.contMDiff_coe (n := 1)).mdifferentiableAt one_ne_zero), L.fderiv,
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.id_apply]

/-- Read in `ℂ`, the circle exponential `t ↦ exp (t i)` has velocity `i exp (t i)`. -/
theorem hasDerivAt_coe_circleExp (t : ℝ) :
    HasDerivAt (fun s : ℝ ↦ ((Circle.exp s : Circle) : ℂ)) (I * Circle.exp t) t := by
  simp only [Circle.coe_exp]
  simpa [mul_comm] using ((ofRealCLM.hasDerivAt (x := t)).mul_const I).cexp

/-- **The generator of the circle exponential.** Read in `ℂ`, the velocity of `Circle.exp` at `0`,
the generator of the rotations `t ↦ exp (t i)`, is `i`. -/
theorem mvfderiv_coe_mfderiv_circleExp :
    mvfderiv (𝓡 1) (fun z : Circle ↦ (z : ℂ)) 1 (mfderiv 𝓘(ℝ) (𝓡 1) Circle.exp 0 (1 : ℝ)) = I := by
  have hcomp := mvfderiv_comp_apply_of_eq (g := fun z : Circle ↦ (z : ℂ))
    (f := Circle.exp) 0
    ((Circle.contMDiff_coe (n := 1)).mdifferentiableAt one_ne_zero)
    ((contMDiff_circleExp (m := 1)).mdifferentiableAt one_ne_zero) Circle.exp_zero (1 : ℝ)
  -- The coercion `Circle → ℂ` is `Subtype.val` through the definition `Circle`, which blocks
  -- rewriting inside `hcomp`; the composite is read off by transitivity instead.
  refine hcomp.symm.trans ((mvfderiv_eq_fderiv_apply
    (fun s : ℝ ↦ ((Circle.exp s : Circle) : ℂ)) 0 (1 : ℝ)).trans ?_)
  rw [(hasDerivAt_coe_circleExp 0).hasFDerivAt.fderiv]
  refine (ContinuousLinearMap.toSpanSingleton_apply ℝ _ 1).trans ?_
  simp

end TauCeti
