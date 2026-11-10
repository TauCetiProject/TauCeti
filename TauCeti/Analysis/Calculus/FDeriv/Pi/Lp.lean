/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Calculus.Gradient
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.WithLp

/-!
# Derivatives of coordinates on finite `L^p` products

The derivative of a coordinate of a function into a finite `L^p` product is the corresponding
coordinate of its derivative (`DifferentiableAt.fderiv_piLp_apply`).

Freezing all but one coordinate of a scalar function on `PiLp 2 E` gives a function on
that factor. At a differentiability point, its derivative norm equals the norm of the
corresponding coordinate of the full gradient. The squared coordinate norms therefore add
up to the squared norm of the full derivative, as required in product energy estimates.
-/

public section

noncomputable section

open InnerProductSpace

section Coordinate

variable {𝕜 ι H : Type*} {E : ι → Type*} [NontriviallyNormedField 𝕜] [Finite ι]
  [NormedAddCommGroup H] [NormedSpace 𝕜 H] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] {p : ENNReal} [Fact (1 ≤ p)] {f : H → PiLp p E} {y : H}

/-- The partial derivatives of a coordinate of a function into a finite `L^p` product, at a
point where the function is differentiable, are the coordinates of its partial derivatives. -/
theorem DifferentiableAt.fderiv_piLp_apply (hf : DifferentiableAt 𝕜 f y) (i : ι) (v : H) :
    fderiv 𝕜 (fun x ↦ f x i) y v = fderiv 𝕜 f y v i := by
  rw [(hasFDerivWithinAt_univ.1 ((hasFDerivWithinAt_piLp p).1
    hf.hasFDerivAt.hasFDerivWithinAt i)).fderiv]
  rfl

end Coordinate

namespace PiLp

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, CompleteSpace (E i)]

/-- The derivative norm of a coordinate slice equals the norm of that coordinate of the
gradient of the original function, at any point where the original function is differentiable. -/
theorem norm_fderiv_update (f : PiLp 2 E → ℝ) (x : ∀ i, E i) (i : ι) (y : E i)
    (hf : DifferentiableAt ℝ f (WithLp.toLp 2 (Function.update x i y))) :
    ‖fderiv ℝ (fun z ↦ f (WithLp.toLp 2 (Function.update x i z))) y‖ =
      ‖gradient f (WithLp.toLp 2 (Function.update x i y)) i‖ := by
  have hcomp := hf.hasFDerivAt.comp y
    ((PiLp.hasFDerivAt_toLp (𝕜 := ℝ) 2 (Function.update x i y)).comp y
      (hasFDerivAt_update (𝕜 := ℝ) x y))
  simp only [Function.comp_def] at hcomp
  have heq : fderiv ℝ (fun z ↦ f (WithLp.toLp 2 (Function.update x i z))) y =
      toDual ℝ (E i) (gradient f (WithLp.toLp 2 (Function.update x i y)) i) := by
    rw [hcomp.fderiv]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      PiLp.coe_symm_continuousLinearEquiv]
    have hsingle : (ContinuousLinearMap.pi
        (Pi.single i (ContinuousLinearMap.id ℝ (E i))) :
        E i →L[ℝ] (∀ j, E j)) v = Pi.single i v := by
      ext j
      by_cases hj : j = i
      · subst j; simp
      · simp [ContinuousLinearMap.pi_apply, Pi.single_eq_of_ne hj]
    rw [hsingle, PiLp.toLp_single, ← inner_gradient_left]
    rw [PiLp.inner_apply, Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [PiLp.single_eq_of_ne 2 hj, inner_zero_right]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [heq, LinearIsometryEquiv.norm_map]

end PiLp
