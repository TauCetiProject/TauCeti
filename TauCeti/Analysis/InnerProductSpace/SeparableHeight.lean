/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.InnerProductSpace.Laplacian
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# Calculus of separated heights on the Euclidean plane

For a height `f (x 0) + g (x 1)` on `EuclideanSpace ℝ (Fin 2)`, the gradient consists
of the profile derivatives, the Hessian is diagonal, and the Laplacian is the sum
of the profile second derivatives. These formulas reduce planar differential operators
to one-variable calculus.
-/

public noncomputable section

open scoped Gradient Laplacian

namespace TauCeti

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- A height obtained by adding one-variable profiles in the two Cartesian directions. -/
def separableHeight (f g : ℝ → ℝ) (x : Plane) : ℝ := f (x 0) + g (x 1)

@[simp] theorem separableHeight_apply (f g : ℝ → ℝ) (x : Plane) :
    separableHeight f g x = f (x 0) + g (x 1) := (rfl)

/-- The gradient of a separated height consists of the two profile derivatives. -/
theorem gradient_separableHeight (f g : ℝ → ℝ) (x : Plane)
    (hf : DifferentiableAt ℝ f (x 0)) (hg : DifferentiableAt ℝ g (x 1)) :
    ∇ (separableHeight f g) x =
      WithLp.toLp 2 ![deriv f (x 0), deriv g (x 1)] := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  rw [toDual_gradient]
  have h0 := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).differentiableAt
  have h1 := (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 1).differentiableAt
  have hd0 := fderiv_comp x hf h0
  have hd1 := fderiv_comp x hg h1
  have hd := fderiv_fun_add (hf.comp x h0) (hg.comp x h1)
  simp only [Function.comp_def] at hd hd0 hd1
  unfold separableHeight
  rw [hd, hd0, hd1]
  ext v
  simp [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).fderiv,
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 1).fderiv, InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

/-- The Hessian of a separated height is diagonal in Cartesian coordinates. -/
theorem fderiv_fderiv_separableHeight_apply (f g : ℝ → ℝ) (x v w : Plane)
    (hf : ContDiffAt ℝ 2 f (x 0)) (hg : ContDiffAt ℝ 2 g (x 1)) :
    fderiv ℝ (fderiv ℝ (separableHeight f g)) x v w =
      iteratedDeriv 2 f (x 0) * v 0 * w 0 +
        iteratedDeriv 2 g (x 1) * v 1 * w 1 := by
  have heq : separableHeight f g =
      (fun z : Fin 2 → ℝ ↦ ∑ i : Fin 2, ![f, g] i (z i)) ∘
        EuclideanSpace.equiv (Fin 2) ℝ := by
    funext y
    simp [separableHeight, Fin.sum_univ_two]
  rw [heq, ContinuousLinearEquiv.fderiv_fderiv_comp_right_apply_apply]
  rw [TauCeti.fderiv_fderiv_sum_comp_eval_apply (Fin.forall_fin_two.2 ⟨hf, hg⟩)]
  simp [Fin.sum_univ_two, iteratedDeriv_succ]

/-- The flat Laplacian of a separated height is the sum of its one-variable second derivatives. -/
theorem laplacian_separableHeight (f g : ℝ → ℝ) (x : Plane)
    (hf : ContDiffAt ℝ 2 f (x 0)) (hg : ContDiffAt ℝ 2 g (x 1)) :
    Δ (separableHeight f g) x =
      iteratedDeriv 2 f (x 0) + iteratedDeriv 2 g (x 1) := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (separableHeight f g) (EuclideanSpace.basisFun (Fin 2) ℝ)) x]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [fderiv_fderiv_separableHeight_apply f g x _ _ hf hg,
    fderiv_fderiv_separableHeight_apply f g x _ _ hf hg]
  simp [EuclideanSpace.basisFun_apply]

end TauCeti
