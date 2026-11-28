/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence.Linear
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.TwoDim
import TauCeti.Analysis.Sobolev.WeakDeriv.Hyperplane
import TauCeti.MeasureTheory.Measure.Haar.Disintegration

/-!
# Solenoidal fields in the plane

This file checks the weak divergence of `TauCeti.HasWeakDivergenceOn` on explicit vector fields
on `ℝ² = EuclideanSpace ℝ (Fin 2)`, with coordinates `x = (x 0, x 1)`.

* **Stream functions.** For `ψ` of class `C²`, the field `∇^⊥ψ = (-∂₂ψ, ∂₁ψ)` is solenoidal
  (`isSolenoidalOn_perp_gradient`).
* **Linear fields.** The rotation `(-x₂, x₁)` and the strain `(-x₁, x₂)` are solenoidal
  (`isSolenoidalOn_rotation`, `isSolenoidalOn_strain`), being `∇^⊥` of `‖x‖² / 2` and of
  `x₁ x₂`, while the identity field `x ↦ x` has divergence `2`, an instance of
  `TauCeti.hasWeakDivergenceOn_id`.
* **Shears.** The shear `(g(x₂), 0)` is solenoidal for every locally integrable `g`
  (`isSolenoidalOn_shear`). For the Heaviside function `g = 1_{(0, ∞)}` the shear has no weak
  derivative at all (`not_hasWeakFDerivOn_heavisideShear`): its first component jumps across the
  line `x₂ = 0`. So solenoidality, a condition on the single scalar `div u`, is strictly weaker
  than weak differentiability of `u`.

## References

* A. J. Majda and A. L. Bertozzi, *Vorticity and Incompressible Flow*, Cambridge University
  Press, 2002, §1.2 (the elementary planar flows) and §2.1 (stream functions).
-/

public section

namespace TauCeti

open MeasureTheory Set TopologicalSpace
open scoped EuclideanSpace Gradient InnerProductSpace

/-- **Stream functions.** For a `C²` function `ψ` on the plane, the field
`∇^⊥ψ = (-∂₂ψ, ∂₁ψ)` is solenoidal. -/
theorem isSolenoidalOn_perp_gradient {ψ : EuclideanSpace ℝ (Fin 2) → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    IsSolenoidalOn volume ⊤ (fun x ↦ !₂[-(∇ ψ x) 1, (∇ ψ x) 0]) := by
  let b := EuclideanSpace.basisFun (Fin 2) ℝ
  -- In the standard orientation, the rotation by a right angle is `(a, b) ↦ (-b, a)`.
  have hJ (z : EuclideanSpace ℝ (Fin 2)) :
      b.toBasis.orientation.rightAngleRotation z = !₂[-z 1, z 0] := by
    rw [Orientation.rightAngleRotation_eq_inner_smul_sub_inner_smul _ rfl]
    ext i
    fin_cases i <;> simp [b, EuclideanSpace.inner_single_right]
  simpa only [hJ] using hψ.contDiffOn.isSolenoidalOn_rightAngleRotation_gradient (μ := volume)
    (Ω := ⊤) b.toBasis.orientation

/-- The rotation `(-x₂, x₁)` is solenoidal: it is `∇^⊥` of `‖x‖² / 2`. -/
theorem isSolenoidalOn_rotation :
    IsSolenoidalOn volume ⊤ (fun x : EuclideanSpace ℝ (Fin 2) ↦ !₂[-x 1, x 0]) := by
  have hψ : ContDiff ℝ 2 (fun y : EuclideanSpace ℝ (Fin 2) ↦ 1 / 2 * ‖y‖ ^ 2 + 0) :=
    (contDiff_const.mul (contDiff_norm_sq ℝ)).add contDiff_const
  simpa only [gradient_mul_norm_sq_add, one_smul] using isSolenoidalOn_perp_gradient hψ

/-- The strain `(-x₁, x₂)` is solenoidal: it is `∇^⊥` of `x₁ x₂`. -/
theorem isSolenoidalOn_strain :
    IsSolenoidalOn volume ⊤ (fun x : EuclideanSpace ℝ (Fin 2) ↦ !₂[-x 0, x 1]) := by
  have hcoord (i : Fin 2) {n : WithTop ℕ∞} :
      ContDiff ℝ n (fun y : EuclideanSpace ℝ (Fin 2) ↦ y i) :=
    contDiff_piLp_apply 2
  have hgrad (x : EuclideanSpace ℝ (Fin 2)) :
      ∇ (fun y : EuclideanSpace ℝ (Fin 2) ↦ y 0 * y 1) x = !₂[x 1, x 0] := by
    rw [gradient_fun_mul ((hcoord 0 (n := 1)).differentiable one_ne_zero x)
      ((hcoord 1 (n := 1)).differentiable one_ne_zero x)]
    ext i
    fin_cases i <;> simp
  convert isSolenoidalOn_perp_gradient ((hcoord 0).mul (hcoord 1)) using 2 with x
  rw [hgrad]
  ext i
  fin_cases i <;> simp

/-- The identity field `x ↦ x` of the plane has weak divergence `2`. -/
example :
    HasWeakDivergenceOn volume ⊤ (id : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2))
      (fun _ ↦ 2) := by
  simpa using hasWeakDivergenceOn_id (μ := (volume : Measure (EuclideanSpace ℝ (Fin 2))))
    (Ω := ⊤)

/-- **Shears.** For every locally integrable `g : ℝ → ℝ`, the shear `(g(x₂), 0)` is solenoidal,
with no regularity of `g`. -/
theorem isSolenoidalOn_shear {g : ℝ → ℝ} (hg : LocallyIntegrable g) :
    IsSolenoidalOn volume ⊤ (fun x : EuclideanSpace ℝ (Fin 2) ↦ !₂[g (x 1), 0]) := by
  have hsurj : Function.Surjective (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) :=
    fun t ↦ ⟨EuclideanSpace.single 1 t, by simp⟩
  have hgA : LocallyIntegrableOn (fun x : EuclideanSpace ℝ (Fin 2) ↦ g (x 1))
      ((⊤ : Opens (EuclideanSpace ℝ (Fin 2))) : Set (EuclideanSpace ℝ (Fin 2))) volume := by
    simpa [Function.comp_def] using
      (locallyIntegrableOn_univ.2 hg).comp_surjective (μ := volume) isOpen_univ hsurj
  have hfield : (fun x : EuclideanSpace ℝ (Fin 2) ↦ !₂[g (x 1), 0]) =
      fun x ↦ g (x 1) • EuclideanSpace.single 0 1 := by
    funext x
    ext i
    fin_cases i <;> simp
  rw [hfield]
  exact isSolenoidalOn_smul_const_of_forall_add_smul_eq hgA fun x t ↦ by simp

/-- The Heaviside shear `(1_{(0, ∞)}(x₂), 0)`, solenoidal by `isSolenoidalOn_shear`, has no weak
derivative: its first component jumps across the line `x₂ = 0`. -/
theorem not_hasWeakFDerivOn_heavisideShear
    (U : EuclideanSpace ℝ (Fin 2) → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2)) :
    ¬ HasWeakFDerivOn volume ⊤
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ !₂[(Ioi 0).indicator 1 (x 1), 0]) U := by
  intro hU
  have hℓ : (EuclideanSpace.proj 1 : EuclideanSpace ℝ (Fin 2) →L[ℝ] ℝ) ≠ 0 := fun h ↦ by
    simpa using DFunLike.congr_fun h (EuclideanSpace.single 1 1)
  refine not_hasWeakFDerivOn_indicator_pos (μ := volume) hℓ (x₀ := 0) (Opens.mem_top _)
    (by simp) (fun x ↦ (EuclideanSpace.proj 0).comp (U x)) ?_
  convert hU.clm_comp (EuclideanSpace.proj 0) using 1
  funext x
  by_cases hx : 0 < x 1 <;> simp [indicator, hx]

end TauCeti
