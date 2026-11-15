/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.SpecialFunctions.Log.Deriv
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Analysis.Calculus.SecondDerivative
public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
public import TauCeti.Analysis.InnerProductSpace.SquaredDistance

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
@[expose]
def affineHeight (a : E) (c : ℝ) (x : E) : ℝ := c + inner ℝ a x

omit [FiniteDimensional ℝ E] in
@[simp]
theorem affineHeight_apply (a : E) (c : ℝ) (x : E) :
    affineHeight a c x = c + inner ℝ a x := rfl

/-- The gradient of an affine height function is constant. -/
theorem gradient_affineHeight (a : E) (c : ℝ) (x : E) : ∇ (affineHeight a c) x = a := by
  unfold gradient
  change (InnerProductSpace.toDual ℝ E).symm
    (fderiv ℝ (fun y : E ↦ c + (InnerProductSpace.toDual ℝ E a) y) x) = a
  rw [fderiv_const_add, ContinuousLinearMap.fderiv]
  exact (InnerProductSpace.toDual ℝ E).symm_apply_apply a

/-- Every affine graph solves the nondivergence minimal graph equation. -/
theorem nondivergenceOperator_affineHeight (a : E) (c : ℝ) (x : E) :
    nondivergenceOperator (affineHeight a c) x = 0 := by
  have hgrad : (∇ (affineHeight a c)) = fun _ ↦ a := funext (gradient_affineHeight a c)
  have hF : fderiv ℝ (affineHeight a c) = fun _ ↦ InnerProductSpace.toDual ℝ E a := by
    funext y
    change fderiv ℝ (fun z : E ↦ c + (InnerProductSpace.toDual ℝ E a) z) y = _
    rw [fderiv_const_add, ContinuousLinearMap.fderiv]
  rw [nondivergenceOperator_eq, ← trace_fderiv_gradient_eq_laplacian]
  rw [hgrad, hF]
  simp

/-- Every affine graph solves the divergence minimal graph equation. -/
theorem fluxDivergence_affineHeight (a : E) (c : ℝ) (x : E) :
    fluxDivergence (affineHeight a c) x = 0 := by
  rw [fluxDivergence_eq_nondivergence (by
    rw [funext (gradient_affineHeight a c)]
    exact differentiableAt_const _)]
  simp [nondivergenceOperator_affineHeight]

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- On the Euclidean plane, the squared norm gives `4 + 8‖x‖²` in the graph operator. -/
theorem nondivergenceOperator_norm_sq (x : Plane) :
    nondivergenceOperator (fun y : Plane ↦ ‖y‖ ^ 2) x = 4 + 8 * ‖x‖ ^ 2 := by
  have hgrad : ∇ (fun y : Plane ↦ ‖y‖ ^ 2) x = (2 : ℝ) • x := by
    have h := TauCeti.gradient_mul_norm_sq_add (E := Plane) 2 0 x
    have hfun : (fun y : Plane ↦ (2 : ℝ) / 2 * ‖y‖ ^ 2 + 0) =
        (fun y : Plane ↦ ‖y‖ ^ 2) := by
      funext y
      norm_num
    rw [hfun] at h
    exact h
  rw [nondivergenceOperator_eq, hgrad, TauCeti.laplacian_norm_sq,
    TauCeti.fderiv_fderiv_norm_sq_apply]
  simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]
  rw [real_inner_self_eq_norm_sq, norm_smul]
  norm_num
  ring

/-- The squared norm is a strict negative control for the minimal graph equation. -/
theorem nondivergenceOperator_norm_sq_pos (x : Plane) :
    0 < nondivergenceOperator (fun y : Plane ↦ ‖y‖ ^ 2) x := by
  rw [nondivergenceOperator_norm_sq]
  positivity

/-- Exchange the two Cartesian coordinates of the Euclidean plane. -/
@[expose] def coordinateSwap : Plane →L[ℝ] Plane where
  toFun x := WithLp.toLp 2 ![x 1, x 0]
  map_add' x y := by
    ext i
    fin_cases i <;> simp
  map_smul' r x := by
    ext i
    fin_cases i <;> simp

@[simp] theorem coordinateSwap_zero (x : Plane) : (coordinateSwap x) 0 = x 1 := rfl
@[simp] theorem coordinateSwap_one (x : Plane) : (coordinateSwap x) 1 = x 0 := rfl

/-- The saddle height `xy` in Cartesian coordinates. -/
def saddleHeight (x : Plane) : ℝ := x 0 * x 1

/-- The saddle height has gradient `(y,x)`. -/
theorem gradient_saddleHeight (x : Plane) : ∇ saddleHeight x = coordinateSwap x := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  rw [toDual_gradient]
  change fderiv ℝ (fun y : Plane ↦ y 0 * y 1) x =
    InnerProductSpace.toDual ℝ Plane (coordinateSwap x)
  have h0 : DifferentiableAt ℝ (fun y : Plane ↦ y 0) x :=
    by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).differentiableAt (x := x)
  have h1 : DifferentiableAt ℝ (fun y : Plane ↦ y 1) x :=
    by simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).differentiableAt (x := x)
  have hd := fderiv_fun_mul h0 h1
  change fderiv ℝ (fun y : Plane ↦ y 0 * y 1) x = _ at hd
  rw [hd]
  have hd0 : fderiv ℝ (fun y : Plane ↦ y 0) x = EuclideanSpace.proj 0 := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).fderiv (x := x)
  have hd1 : fderiv ℝ (fun y : Plane ↦ y 1) x = EuclideanSpace.proj 1 := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).fderiv (x := x)
  ext v
  simp [hd0, hd1, InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two, mul_comm]
  ring

/-- The saddle height `xy` is harmonic. -/
theorem laplacian_saddleHeight (x : Plane) : Δ saddleHeight x = 0 := by
  rw [← trace_fderiv_gradient_eq_laplacian]
  have hgrad : (∇ saddleHeight) = coordinateSwap := funext gradient_saddleHeight
  rw [hgrad, ContinuousLinearMap.fderiv]
  rw [LinearMap.trace_eq_sum_inner _ (EuclideanSpace.basisFun (Fin 2) ℝ)]
  simp [Fin.sum_univ_two, EuclideanSpace.inner_single_left]

/-- The second derivative of `xy` is the coordinate exchange map under the Riesz pairing. -/
private theorem fderiv_saddleHeight_eq :
    fderiv ℝ saddleHeight =
      (InnerProductSpace.toDual ℝ Plane).toContinuousLinearMap.comp coordinateSwap := by
  funext x
  rw [← toDual_gradient, gradient_saddleHeight]
  rfl

/-- The nondivergence graph operator of `xy` is `-2xy`, despite its harmonicity. -/
theorem nondivergenceOperator_saddleHeight (x : Plane) :
    nondivergenceOperator saddleHeight x = -2 * x 0 * x 1 := by
  rw [nondivergenceOperator_eq, laplacian_saddleHeight, gradient_saddleHeight,
    fderiv_saddleHeight_eq, ContinuousLinearMap.fderiv]
  simp only [mul_zero, zero_sub, ContinuousLinearMap.comp_apply]
  simp [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]
  ring

/-- Away from the coordinate axes, the harmonic saddle graph is not minimal. -/
theorem nondivergenceOperator_saddleHeight_ne_zero (x : Plane) (h : x 0 * x 1 ≠ 0) :
    nondivergenceOperator saddleHeight x ≠ 0 := by
  rw [nondivergenceOperator_saddleHeight]
  simpa only [mul_assoc] using (mul_ne_zero (by norm_num : (-2 : ℝ) ≠ 0) h)

/-- A height obtained by adding one-variable profiles in the two Cartesian directions. -/
def separableHeight (f g : ℝ → ℝ) (x : Plane) : ℝ := f (x 0) + g (x 1)

private theorem gradient_separableHeight (f g : ℝ → ℝ) (x : Plane)
    (hf : DifferentiableAt ℝ f (x 0)) (hg : DifferentiableAt ℝ g (x 1)) :
    ∇ (separableHeight f g) x =
      WithLp.toLp 2 ![deriv f (x 0), deriv g (x 1)] := by
  apply (InnerProductSpace.toDual ℝ Plane).injective
  rw [toDual_gradient]
  have h0 : DifferentiableAt ℝ (fun y : Plane ↦ y 0) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).differentiableAt (x := x)
  have h1 : DifferentiableAt ℝ (fun y : Plane ↦ y 1) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).differentiableAt (x := x)
  have hd0 := fderiv_comp x hf h0
  have hd1 := fderiv_comp x hg h1
  have hd := fderiv_fun_add (hf.comp x h0) (hg.comp x h1)
  change fderiv ℝ (separableHeight f g) x = _ at hd
  rw [hd, hd0, hd1]
  have hp0 : fderiv ℝ (fun y : Plane ↦ y 0) x = EuclideanSpace.proj 0 := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).fderiv (x := x)
  have hp1 : fderiv ℝ (fun y : Plane ↦ y 1) x = EuclideanSpace.proj 1 := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).fderiv (x := x)
  ext v
  simp [hp0, hp1, InnerProductSpace.toDual_apply_apply,
    EuclideanSpace.inner_eq_star_dotProduct, dotProduct, Fin.sum_univ_two]

private theorem secondDerivative_separableHeight (f g : ℝ → ℝ) (x v w : Plane)
    (hf : ContDiffAt ℝ 2 f (x 0)) (hg : ContDiffAt ℝ 2 g (x 1)) :
    fderiv ℝ (fderiv ℝ (separableHeight f g)) x v w =
      iteratedDeriv 2 f (x 0) * v 0 * w 0 +
        iteratedDeriv 2 g (x 1) * v 1 * w 1 := by
  have hp0 : ContDiffAt ℝ 2 (fun y : Plane ↦ y 0) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.contDiffAt (x := x)
  have hp1 : ContDiffAt ℝ 2 (fun y : Plane ↦ y 1) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.contDiffAt (x := x)
  have hd0 : fderiv ℝ (fun y : Plane ↦ y 0) = fun _ ↦ EuclideanSpace.proj 0 := by
    funext y
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).fderiv (x := y)
  have hd1 : fderiv ℝ (fun y : Plane ↦ y 1) = fun _ ↦ EuclideanSpace.proj 1 := by
    funext y
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).fderiv (x := y)
  have hdd0 : fderiv ℝ (fderiv ℝ (fun y : Plane ↦ y 0)) x = 0 := by
    rw [hd0]
    simp
  have hdd1 : fderiv ℝ (fderiv ℝ (fun y : Plane ↦ y 1)) x = 0 := by
    rw [hd1]
    simp
  have hfcomp := TauCeti.fderiv_fderiv_comp_apply
    (f := f) (φ := fun y : Plane ↦ y 0) hf hp0 v w
  have hgcomp := TauCeti.fderiv_fderiv_comp_apply
    (f := g) (φ := fun y : Plane ↦ y 1) hg hp1 v w
  have hsum := iteratedFDeriv_add_apply (hf.comp x hp0) (hg.comp x hp1)
    (i := 2)
  have hsum' := congrArg (fun L ↦ L ![v, w]) hsum
  simp only [add_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one] at hsum'
  change fderiv ℝ (fderiv ℝ (separableHeight f g)) x v w =
    fderiv ℝ (fderiv ℝ (f ∘ fun y : Plane ↦ y 0)) x v w +
      fderiv ℝ (fderiv ℝ (g ∘ fun y : Plane ↦ y 1)) x v w at hsum'
  rw [hsum', hfcomp, hgcomp]
  rw [hdd0, hdd1]
  simp only [zero_apply, map_zero, add_zero, hd0, hd1]
  rw [TauCeti.fderiv_fderiv_apply_eq_smul_iteratedDeriv,
    TauCeti.fderiv_fderiv_apply_eq_smul_iteratedDeriv]
  simp only [smul_eq_mul]
  simp
  ring

/-- The flat Laplacian of a separated height is the sum of its one-variable second derivatives. -/
private theorem laplacian_separableHeight (f g : ℝ → ℝ) (x : Plane)
    (hf : ContDiffAt ℝ 2 f (x 0)) (hg : ContDiffAt ℝ 2 g (x 1)) :
    Δ (separableHeight f g) x =
      iteratedDeriv 2 f (x 0) + iteratedDeriv 2 g (x 1) := by
  rw [congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (separableHeight f g) (EuclideanSpace.basisFun (Fin 2) ℝ)) x]
  simp only [Fin.sum_univ_two, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [secondDerivative_separableHeight f g x _ _ hf hg,
    secondDerivative_separableHeight f g x _ _ hf hg]
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
    secondDerivative_separableHeight f g x _ _ hf hg,
    EuclideanSpace.real_norm_sq_eq]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one]
  ring

/-- The one-dimensional profile of Scherk's graph. -/
def logCos (t : ℝ) : ℝ := Real.log (Real.cos t)

private theorem contDiffAt_logCos {t : ℝ} (hc : Real.cos t ≠ 0) :
    ContDiffAt ℝ 2 logCos t := by
  exact (Real.contDiff_cos.contDiffAt.log hc)

private theorem deriv_logCos {t : ℝ} (hc : Real.cos t ≠ 0) :
    deriv logCos t = -Real.tan t := by
  have h := ((Real.hasDerivAt_cos t).log hc).deriv
  change deriv (fun y ↦ Real.log (Real.cos y)) t = -Real.tan t
  simpa [Real.tan_eq_sin_div_cos, neg_div] using h

private theorem iteratedDeriv_logCos {t : ℝ} (hc : Real.cos t ≠ 0) :
    iteratedDeriv 2 logCos t = -(1 / Real.cos t ^ 2) := by
  rw [show iteratedDeriv 2 logCos = deriv (deriv logCos) by
    simp [iteratedDeriv_succ]]
  have hne : ∀ᶠ s in 𝓝 t, Real.cos s ≠ 0 :=
    Real.continuous_cos.continuousAt.eventually_ne hc
  have heq : deriv logCos =ᶠ[𝓝 t] fun s ↦ -Real.tan s :=
    hne.mono fun s hs ↦ deriv_logCos hs
  rw [heq.deriv_eq]
  exact (Real.hasDerivAt_tan hc).neg.deriv

private theorem one_add_tan_sq (t : ℝ) (hc : Real.cos t ≠ 0) :
    1 + Real.tan t ^ 2 = 1 / Real.cos t ^ 2 := by
  rw [Real.tan_eq_sin_div_cos]
  have h := Real.sin_sq_add_cos_sq t
  field_simp
  nlinarith

/-- Scherk's minimal graph on the open square where both cosines are positive. -/
def scherkHeight (x : Plane) : ℝ :=
  Real.log (Real.cos (x 0)) - Real.log (Real.cos (x 1))

/-- Scherk's graph solves the Euclidean minimal graph equation on its natural square domain. -/
theorem nondivergenceOperator_scherkHeight (x : Plane)
    (hx : x 0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hy : x 1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    nondivergenceOperator scherkHeight x = 0 := by
  have hcx : Real.cos (x 0) ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
  have hcy : Real.cos (x 1) ≠ 0 := (Real.cos_pos_of_mem_Ioo hy).ne'
  have hfx := contDiffAt_logCos hcx
  have hgy : ContDiffAt ℝ 2 (fun t ↦ -logCos t) (x 1) :=
    (contDiffAt_logCos hcy).neg
  have heq : scherkHeight = separableHeight logCos (fun t ↦ -logCos t) := by
    funext z
    rfl
  rw [heq, nondivergenceOperator_separableHeight _ _ x hfx hgy]
  simp only [deriv.fun_neg, iteratedDeriv_fun_neg, neg_sq,
    deriv_logCos hcx, deriv_logCos hcy,
    iteratedDeriv_logCos hcx, iteratedDeriv_logCos hcy]
  rw [one_add_tan_sq (x 0) hcx, one_add_tan_sq (x 1) hcy]
  ring

/-- Scherk's height also solves the divergence form on the open square. -/
theorem fluxDivergence_scherkHeight (x : Plane)
    (hx : x 0 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hy : x 1 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    fluxDivergence scherkHeight x = 0 := by
  have hcx : Real.cos (x 0) ≠ 0 := (Real.cos_pos_of_mem_Ioo hx).ne'
  have hcy : Real.cos (x 1) ≠ 0 := (Real.cos_pos_of_mem_Ioo hy).ne'
  have h0 : ContDiffAt ℝ 2 (fun y : Plane ↦ y 0) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 0 : Plane →L[ℝ] ℝ).contDiff.contDiffAt (x := x)
  have h1 : ContDiffAt ℝ 2 (fun y : Plane ↦ y 1) x := by
    simpa only [EuclideanSpace.coe_proj] using
      (EuclideanSpace.proj 1 : Plane →L[ℝ] ℝ).contDiff.contDiffAt (x := x)
  have hu : ContDiffAt ℝ 2 scherkHeight x := by
    change ContDiffAt ℝ 2 (fun y : Plane ↦ logCos (y 0) - logCos (y 1)) x
    exact ((contDiffAt_logCos hcx).comp x h0).sub
      ((contDiffAt_logCos hcy).comp x h1)
  have hgrad : DifferentiableAt ℝ (∇ scherkHeight) x :=
    (hu.gradient_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  exact (fluxDivergence_eq_zero_iff hgrad).2 (nondivergenceOperator_scherkHeight x hx hy)

end TauCeti.MinimalGraph
