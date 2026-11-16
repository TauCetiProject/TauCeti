/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.InnerProductSpace.PiL2
import TauCeti.Analysis.InnerProductSpace.Laplacian.Trace
import Mathlib.Analysis.InnerProductSpace.Trace
import TauCeti.Analysis.Calculus.IteratedFDeriv.CompContinuousLinearEquiv
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Calculus.SecondDerivative
import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.InnerProductSpace.SquaredDistance

/-!
# Model checks for the Euclidean minimal graph equation

Affine height functions solve the minimal graph equation. On the Euclidean plane, squared norm
has strictly positive nondivergence operator, while the harmonic saddle `xy` has operator `-2xy`.
Scherk's graph solves both forms of the equation on its natural open square.

## References

* T. H. Colding and W. P. Minicozzi II, *A course in minimal surfaces*, Section 1.1.
-/

public noncomputable section

open scoped Gradient Laplacian Topology

namespace TauCeti.MinimalGraph

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- An affine Euclidean height function. -/
def affineHeight (a : E) (c : ℝ) (x : E) : ℝ := c + inner ℝ a x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineHeight_apply (a : E) (c : ℝ) (x : E) :
    affineHeight a c x = c + inner ℝ a x := (rfl)

omit [FiniteDimensional ℝ E] in
/-- The gradient of an affine height function is constant. -/
@[simp]
theorem gradient_affineHeight [CompleteSpace E] (a : E) (c : ℝ) (x : E) :
    ∇ (affineHeight a c) x = a := by
  apply (InnerProductSpace.toDual ℝ E).injective
  rw [toDual_gradient, funext (affineHeight_apply a c)]
  simp_rw [← InnerProductSpace.toDual_apply_apply]
  rw [fderiv_const_add, ContinuousLinearMap.fderiv]

/-- Every affine graph solves the nondivergence minimal graph equation. -/
@[simp]
theorem nondivergenceOperator_affineHeight (a : E) (c : ℝ) (x : E) :
    nondivergenceOperator (affineHeight a c) x = 0 := by
  rw [nondivergenceOperator_def, funext (gradient_affineHeight a c)]
  simp

/-- Every affine graph solves the divergence minimal graph equation. -/
@[simp]
theorem fluxDivergence_affineHeight (a : E) (c : ℝ) (x : E) :
    fluxDivergence (affineHeight a c) x = 0 := by
  rw [fluxDivergence_eq_rpow_mul_nondivergenceOperator (by
    rw [funext (gradient_affineHeight a c)]
    exact differentiableAt_const _)]
  simp [nondivergenceOperator_affineHeight]

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The squared norm graph operator in any finite-dimensional Euclidean space. -/
theorem nondivergenceOperator_norm_sq (x : E) :
    nondivergenceOperator (fun y : E ↦ ‖y‖ ^ 2) x =
      2 * (Module.finrank ℝ E : ℝ) + 8 * ((Module.finrank ℝ E : ℝ) - 1) * ‖x‖ ^ 2 := by
  have hgrad : ∇ (fun y : E ↦ ‖y‖ ^ 2) x = (2 : ℝ) • x := by
    simpa only [sub_zero] using TauCeti.gradient_norm_sq_sub (0 : E) x
  rw [nondivergenceOperator_eq, hgrad, TauCeti.laplacian_norm_sq,
    TauCeti.fderiv_fderiv_norm_sq_apply]
  simp [norm_smul]
  ring

/-- In positive dimension the squared norm does not solve the minimal graph equation. -/
theorem nondivergenceOperator_norm_sq_pos [Nontrivial E] (x : E) :
    0 < nondivergenceOperator (fun y : E ↦ ‖y‖ ^ 2) x := by
  rw [nondivergenceOperator_norm_sq]
  have hn : (1 : ℝ) ≤ Module.finrank ℝ E := by
    exact_mod_cast Module.finrank_pos (R := ℝ) (M := E)
  positivity

/-- The saddle height `xy` in Cartesian coordinates. -/
def saddleHeight (x : Plane) : ℝ := x 0 * x 1

@[simp] theorem saddleHeight_apply (x : Plane) : saddleHeight x = x 0 * x 1 := (rfl)

/-- The saddle height has gradient `(y,x)`. -/
theorem gradient_saddleHeight (x : Plane) :
    ∇ saddleHeight x = WithLp.toLp 2 ![x 1, x 0] := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  rw [toDual_gradient]
  unfold saddleHeight
  rw [fderiv_fun_mul (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).differentiableAt
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 1).differentiableAt]
  ext v
  simp [(PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 0).fderiv,
    (PiLp.hasFDerivAt_apply (𝕜 := ℝ) 2 x 1).fderiv, InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm, add_comm]

private theorem gradient_saddleHeight_eq :
    ∇ saddleHeight =
      (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ
        (Equiv.swap (0 : Fin 2) 1)).toContinuousLinearMap := by
  funext x
  rw [gradient_saddleHeight]
  ext i
  fin_cases i <;> simp [LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']

/-- The saddle height `xy` is harmonic. -/
@[simp]
theorem laplacian_saddleHeight (x : Plane) : Δ saddleHeight x = 0 := by
  rw [TauCeti.laplacian_eq_trace_iteratedGradientChain_one,
    TauCeti.iteratedGradientChain_succ, TauCeti.iteratedGradientChain_zero,
    gradient_saddleHeight_eq, ContinuousLinearMap.fderiv]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp [EuclideanSpace.inner_single_left]

/-- The nondivergence graph operator of `xy` is `-2xy`, despite its harmonicity. -/
theorem nondivergenceOperator_saddleHeight (x : Plane) :
    nondivergenceOperator saddleHeight x = -2 * x 0 * x 1 := by
  have htrace := laplacian_saddleHeight x
  rw [TauCeti.laplacian_eq_trace_iteratedGradientChain_one,
    TauCeti.iteratedGradientChain_succ, TauCeti.iteratedGradientChain_zero] at htrace
  rw [nondivergenceOperator_def, htrace, gradient_saddleHeight_eq,
    ContinuousLinearMap.fderiv]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two,
    LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft']
  ring

/-- Away from the axes, the harmonic saddle height does not solve the nondivergence
minimal graph equation. -/
theorem nondivergenceOperator_saddleHeight_ne_zero (x : Plane) (h : x 0 * x 1 ≠ 0) :
    nondivergenceOperator saddleHeight x ≠ 0 := by
  rw [nondivergenceOperator_saddleHeight]
  simpa only [mul_assoc] using (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) h)

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

/-- The minimal graph operator on a separated height has the standard diagonal form. -/
theorem nondivergenceOperator_separableHeight (f g : ℝ → ℝ) (x : Plane)
    (hf : ContDiffAt ℝ 2 f (x 0)) (hg : ContDiffAt ℝ 2 g (x 1)) :
    nondivergenceOperator (separableHeight f g) x =
      (1 + (deriv g (x 1)) ^ 2) * iteratedDeriv 2 f (x 0) +
        (1 + (deriv f (x 0)) ^ 2) * iteratedDeriv 2 g (x 1) := by
  rw [nondivergenceOperator_eq,
    gradient_separableHeight f g x (hf.differentiableAt (by norm_num))
      (hg.differentiableAt (by norm_num)),
    laplacian_separableHeight f g x hf hg,
    fderiv_fderiv_separableHeight_apply f g x _ _ hf hg,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The one-dimensional profile of Scherk's graph. -/
private def logCos (t : ℝ) : ℝ := Real.log (Real.cos t)

@[simp] private theorem logCos_apply (t : ℝ) : logCos t = Real.log (Real.cos t) := (rfl)

/-- The Scherk profile is smooth wherever the cosine is nonzero. -/
private theorem contDiffAt_logCos {n : WithTop ℕ∞} {t : ℝ} (hc : Real.cos t ≠ 0) :
    ContDiffAt ℝ n logCos t := by
  exact (Real.contDiff_cos.contDiffAt.log hc)

/-- The derivative of the Scherk profile is the negative tangent. -/
private theorem deriv_logCos {t : ℝ} (hc : Real.cos t ≠ 0) :
    deriv logCos t = -Real.tan t := by
  have h := ((Real.hasDerivAt_cos t).log hc).deriv
  unfold logCos
  simpa [Real.tan_eq_sin_div_cos, neg_div] using h

/-- The second derivative of the Scherk profile is the negative squared secant. -/
private theorem iteratedDeriv_logCos {t : ℝ} (hc : Real.cos t ≠ 0) :
    iteratedDeriv 2 logCos t = -(1 / Real.cos t ^ 2) := by
  rw [iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero]
  have hne : ∀ᶠ s in 𝓝 t, Real.cos s ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hc
  have heq : deriv logCos =ᶠ[𝓝 t] fun s ↦ -Real.tan s :=
    hne.mono fun s hs ↦ deriv_logCos hs
  rw [heq.deriv_eq]
  exact (Real.hasDerivAt_tan hc).neg.deriv

/-- Scherk's minimal graph on the open square where both cosines are positive. -/
def scherkHeight (x : Plane) : ℝ :=
  Real.log (Real.cos (x 0)) - Real.log (Real.cos (x 1))

@[simp] theorem scherkHeight_apply (x : Plane) :
    scherkHeight x = Real.log (Real.cos (x 0)) - Real.log (Real.cos (x 1)) := (rfl)

/-- Scherk's graph solves the Euclidean minimal graph equation where both cosines are nonzero. -/
theorem nondivergenceOperator_scherkHeight (x : Plane)
    (hcx : Real.cos (x 0) ≠ 0) (hcy : Real.cos (x 1) ≠ 0) :
    nondivergenceOperator scherkHeight x = 0 := by
  have hfx : ContDiffAt ℝ 2 logCos (x 0) := contDiffAt_logCos hcx
  have hgy : ContDiffAt ℝ 2 (fun t ↦ -logCos t) (x 1) :=
    (contDiffAt_logCos hcy).neg
  have heq : scherkHeight = separableHeight logCos (fun t ↦ -logCos t) := by
    funext z
    simp only [scherkHeight_apply, separableHeight_apply, logCos_apply, sub_eq_add_neg]
  rw [heq, nondivergenceOperator_separableHeight _ _ x hfx hgy]
  simp only [deriv.fun_neg, iteratedDeriv_fun_neg, neg_sq,
    deriv_logCos hcx, deriv_logCos hcy,
    iteratedDeriv_logCos hcx, iteratedDeriv_logCos hcy]
  rw [← Real.inv_one_add_tan_sq hcx, ← Real.inv_one_add_tan_sq hcy]
  simp only [one_div, inv_inv]
  ring

/-- Scherk's height also solves the divergence form where both cosines are nonzero. -/
theorem fluxDivergence_scherkHeight (x : Plane)
    (hcx : Real.cos (x 0) ≠ 0) (hcy : Real.cos (x 1) ≠ 0) :
    fluxDivergence scherkHeight x = 0 := by
  have hu : ContDiffAt ℝ 2 scherkHeight x := by
    unfold scherkHeight
    exact ((contDiffAt_logCos hcx).comp x (contDiffAt_piLp_apply 2)).sub
      ((contDiffAt_logCos hcy).comp x (contDiffAt_piLp_apply 2))
  have hgrad : DifferentiableAt ℝ (∇ scherkHeight) x :=
    (hu.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (fluxDivergence_eq_zero_iff hgrad).2 (nondivergenceOperator_scherkHeight x hcx hcy)

end TauCeti.MinimalGraph
