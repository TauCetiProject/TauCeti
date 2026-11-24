/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# A local logarithmic angle branch for the helicoid

The logarithm is taken after rotating the chosen polar basepoint to the positive real axis.
This gives a smooth Cartesian angle germ at every point of the polar cover, agreeing with
the unrestricted polar angle on a sector of angular width less than a full turn.

We compute the first derivative, Hessian, Cartesian coordinate entries and gradient throughout
the rotated slit plane. The Laplacian and the Hessian on two copies of the gradient vanish
there. Consequently `nondivergenceOperator_const_mul_angleBranch` shows that every real multiple
of the branch satisfies the minimal graph equation, giving the helicoid height for any pitch.
-/

public noncomputable section

open scoped Gradient Laplacian Topology

namespace TauCeti.PolarGraph

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The local Cartesian angle centered at a polar point. -/
def angleBranch (p : PolarPoint) (x : Plane) : ℝ :=
  angle p + (Complex.log
    (Complex.orthonormalBasisOneI.repr.symm x / projection p)).im

theorem angleBranch_def (p : PolarPoint) (x : Plane) :
    angleBranch p x = angle p + (Complex.log
      (Complex.orthonormalBasisOneI.repr.symm x / projection p)).im := (rfl)

@[simp] theorem angleBranch_repr_projection (p : PolarPoint) :
    angleBranch p (Complex.orthonormalBasisOneI.repr (projection p)) = angle p := by
  simp [angleBranch, projection_ne_zero]

/-- Translating the basepoint by a deck transformation adds the corresponding full turns. -/
@[simp, grind =] theorem angleBranch_deckShift (k : ℤ) (p : PolarPoint) :
    angleBranch (deckShift k p) = fun x ↦ angleBranch p x + (k : ℝ) * (2 * Real.pi) := by
  funext x
  simp only [angleBranch_def, projection_deckShift, angle_deckShift]
  ring

/-- On the sector centered at `p`, the Cartesian branch recovers the unrestricted polar angle. -/
@[grind =] theorem angleBranch_repr_projection_of_abs_lt (p q : PolarPoint)
    (h : |angle q - angle p| < Real.pi) :
    angleBranch p (Complex.orthonormalBasisOneI.repr (projection q)) = angle q := by
  have hquot : projection q / projection p =
      ((radius q / radius p : ℝ) : ℂ) * (Circle.exp (angle q - angle p) : ℂ) := by
    simp only [projection_def, Circle.exp_sub, Circle.coe_div, Complex.ofReal_div]
    ring
  rw [angleBranch_def, LinearIsometryEquiv.symm_apply_apply, hquot, Complex.log_im,
    Complex.arg_ofReal_mul (div_pos (radius_pos q) (radius_pos p)),
    Circle.arg_exp (neg_lt_of_abs_lt h) (le_of_lt (lt_of_abs_lt h))]
  ring

/-- The rotated logarithmic angle is smooth to every order on its slit domain. -/
theorem contDiffAt_angleBranch (p : PolarPoint) (x : Plane) {n : WithTop ℕ∞}
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    ContDiffAt ℝ n (angleBranch p) x := by
  let L := Complex.orthonormalBasisOneI.repr.symm
  have hdiv : AnalyticAt ℂ (fun z : ℂ ↦ z / projection p) (L x) := by fun_prop
  have h := ((hdiv.clog hx).contDiffAt (n := n)).restrict_scalars ℝ
  exact contDiffAt_const.add
    (Complex.imCLM.contDiff.contDiffAt.comp _ (h.comp _ L.contDiff.contDiffAt))

/-- The derivative of the angle branch is differentiable on its slit domain. -/
theorem differentiableAt_fderiv_angleBranch (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    DifferentiableAt ℝ (fderiv ℝ (angleBranch p)) x :=
  ((contDiffAt_angleBranch p x (n := 2) hx).fderiv_right (m := 1)
    (by norm_num)).differentiableAt (by norm_num)

private theorem hasDerivAt_rotatedLog (p : PolarPoint) (z : ℂ)
    (hz : z / projection p ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ ↦ Complex.log (w / projection p)) z⁻¹ z := by
  have h : HasDerivAt (fun w : ℂ ↦ w / projection p)
      (1 / projection p) z :=
    (hasDerivAt_id z).div_const (projection p)
  have hs : z ≠ 0 := by
    intro hz0
    simp [hz0] at hz
  convert h.clog hz using 1
  field_simp [projection_ne_zero p, hs]

/-- The Cartesian first derivative of the angle is the imaginary part of division by the
point, throughout the rotated slit plane. -/
theorem fderiv_angleBranch_apply (p : PolarPoint) (x v : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (angleBranch p) x v =
      (Complex.orthonormalBasisOneI.repr.symm v /
        Complex.orthonormalBasisOneI.repr.symm x).im := by
  have hcomplex := (hasDerivAt_rotatedLog p _ hx).complexToReal_fderiv
  have hplane := hcomplex.comp x
    Complex.orthonormalBasisOneI.repr.symm.hasFDerivAt
  have him := Complex.imCLM.hasFDerivAt.comp _ hplane
  have htotal : HasFDerivAt (angleBranch p) _ x :=
    (hasFDerivAt_const (angle p) x).add him
  rw [htotal.fderiv]
  simp only [zero_add,
    ContinuousLinearMap.comp_apply, Complex.imCLM_apply, smul_apply,
    one_apply_eq_self, smul_eq_mul, div_eq_mul_inv]
  congr 1
  simp
  ring

/-- The Cartesian Hessian of the angle on its slit domain is the imaginary part of the complex
second derivative of logarithm. -/
theorem fderiv_fderiv_angleBranch_apply (p : PolarPoint) (x : Plane) (v w : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      x v w =
      -((Complex.orthonormalBasisOneI.repr.symm v *
        Complex.orthonormalBasisOneI.repr.symm w) /
        (Complex.orthonormalBasisOneI.repr.symm x) ^ 2).im := by
  let a := Complex.orthonormalBasisOneI.repr.symm x
  let L := Complex.orthonormalBasisOneI.repr.symm
  let x₀ := x
  have ha : a ≠ 0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hx)).1
  have hcenter : L x₀ = a := rfl
  have hslit : ∀ᶠ y in 𝓝 x₀, L y / projection p ∈ Complex.slitPlane := by
    have hcont : ContinuousAt (fun y : Plane ↦ L y / projection p) x₀ := by fun_prop
    apply hcont.preimage_mem_nhds
    exact Complex.isOpen_slitPlane.mem_nhds hx
  have heq : (fun y : Plane ↦ fderiv ℝ (angleBranch p) y w) =ᶠ[𝓝 x₀]
      (fun y : Plane ↦ (L w / L y).im) := by
    filter_upwards [hslit] with y hy
    exact fderiv_angleBranch_apply p y w hy
  have hdiv : HasDerivAt (fun z : ℂ ↦ L w / z) (-(L w / a ^ 2)) a := by
    convert (hasDerivAt_const (x := a) (c := L w)).fun_div (hasDerivAt_id a) ha
      using 1 <;> simp [div_eq_mul_inv]
  have hr : HasFDerivAt (fun y : Plane ↦ (L w / L y).im)
      (Complex.imCLM.comp
        (((-(L w / a ^ 2)) • (1 : ℂ →L[ℝ] ℂ)).comp L.toContinuousLinearMap)) x₀ := by
    have hreal := hdiv.complexToReal_fderiv
    have hreal' : HasFDerivAt (fun z : ℂ ↦ L w / z)
        (-(L w / a ^ 2) • (1 : ℂ →L[ℝ] ℂ)) (L x₀) := by
      simpa only [hcenter] using hreal
    exact Complex.imCLM.hasFDerivAt.comp _
      (hreal'.comp x₀ L.hasFDerivAt)
  have hgrad := differentiableAt_fderiv_angleBranch p x hx
  have hscalar : fderiv ℝ
      (fun y : Plane ↦ fderiv ℝ (angleBranch p) y w) x₀ v =
      -((L v * L w) / a ^ 2).im := by
    rw [heq.fderiv_eq, hr.fderiv]
    simp only [ContinuousLinearMap.comp_apply, Complex.imCLM_apply,
      smul_apply, one_apply_eq_self, smul_eq_mul]
    rw [← Complex.neg_im]
    congr 1
    simp
    ring
  have hderiv := congrArg (fun M : Plane →L[ℝ] ℝ ↦ M v)
    (fderiv_clm_apply hgrad (differentiableAt_const w))
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero] at hderiv
  rw [hscalar] at hderiv
  simpa [L, x₀, a] using hderiv.symm

/-- The `x` partial derivative of the angle on its slit domain. -/
theorem fderiv_angleBranch_x (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (angleBranch p)
      x
      (EuclideanSpace.single 0 1) =
      -(Complex.orthonormalBasisOneI.repr.symm x).im /
        Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) := by
  simpa [Complex.div_im] using
    fderiv_angleBranch_apply p x (EuclideanSpace.single 0 1) hx

/-- The `y` partial derivative of the angle on its slit domain. -/
theorem fderiv_angleBranch_y (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (angleBranch p)
      x
      (EuclideanSpace.single 1 1) =
      (Complex.orthonormalBasisOneI.repr.symm x).re /
        Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) := by
  simpa [Complex.div_im] using
    fderiv_angleBranch_apply p x (EuclideanSpace.single 1 1) hx

private theorem angleHessian_complex_xx (z : ℂ) :
    -((1 : ℂ) / z ^ 2).im = 2 * z.re * z.im / Complex.normSq z ^ 2 := by
  simp [pow_two, Complex.mul_im]
  ring

private theorem angleHessian_complex_xy (z : ℂ) :
    -(Complex.I / z ^ 2).im = (z.im ^ 2 - z.re ^ 2) / Complex.normSq z ^ 2 := by
  simp [Complex.div_im, pow_two, Complex.normSq_mul, Complex.mul_re]
  ring

private theorem angleHessian_complex_yy (z : ℂ) :
    -((-1 : ℂ) / z ^ 2).im = -(2 * z.re * z.im) / Complex.normSq z ^ 2 := by
  simpa only [neg_div, Complex.neg_im, neg_neg] using
    congrArg Neg.neg (angleHessian_complex_xx z)

/-- The `xx` Hessian entry of the angle on its slit domain. -/
theorem fderiv_fderiv_angleBranch_xx (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      x
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) =
      2 * (Complex.orthonormalBasisOneI.repr.symm x).re *
        (Complex.orthonormalBasisOneI.repr.symm x).im /
        Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p x
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) hx
  calc
    _ = -((1 : ℂ) / (Complex.orthonormalBasisOneI.repr.symm x) ^ 2).im := by
      simpa using h
    _ = _ := angleHessian_complex_xx (Complex.orthonormalBasisOneI.repr.symm x)

/-- The `xy` Hessian entry of the angle on its slit domain. -/
theorem fderiv_fderiv_angleBranch_xy (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      x
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) =
      ((Complex.orthonormalBasisOneI.repr.symm x).im ^ 2 -
        (Complex.orthonormalBasisOneI.repr.symm x).re ^ 2) /
        Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p x
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) hx
  calc
    _ = -(Complex.I / (Complex.orthonormalBasisOneI.repr.symm x) ^ 2).im := by
      simpa using h
    _ = _ := angleHessian_complex_xy (Complex.orthonormalBasisOneI.repr.symm x)

/-- The `yy` Hessian entry of the angle on its slit domain. -/
theorem fderiv_fderiv_angleBranch_yy (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      x
      (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) =
      -(2 * (Complex.orthonormalBasisOneI.repr.symm x).re *
        (Complex.orthonormalBasisOneI.repr.symm x).im) /
        Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p x
    (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) hx
  calc
    _ = -((-1 : ℂ) / (Complex.orthonormalBasisOneI.repr.symm x) ^ 2).im := by
      simpa using h
    _ = _ := angleHessian_complex_yy (Complex.orthonormalBasisOneI.repr.symm x)

/-- The Cartesian gradient of the angle is the ninety-degree rotation of the radial
vector, divided by squared radius. -/
theorem repr_symm_gradient_angleBranch (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    Complex.orthonormalBasisOneI.repr.symm
      (∇ (angleBranch p) x) =
      Complex.I * Complex.orthonormalBasisOneI.repr.symm x /
        (Complex.normSq (Complex.orthonormalBasisOneI.repr.symm x) : ℂ) := by
  let a := Complex.orthonormalBasisOneI.repr.symm x
  let x₀ := x
  let g := ∇ (angleBranch p) x₀
  have hg (i : Fin 2) : g i =
      (Complex.orthonormalBasisOneI.repr.symm (EuclideanSpace.single i 1) / a).im := by
    calc
      g i = inner ℝ g (EuclideanSpace.basisFun (Fin 2) ℝ i) :=
        (EuclideanSpace.inner_basisFun_real (Fin 2) g i).symm
      _ = fderiv ℝ (angleBranch p) x₀ (EuclideanSpace.single i 1) := by
        simpa only [g, EuclideanSpace.basisFun_apply] using
          (inner_gradient_left (f := angleBranch p) (x := x₀)
            (y := EuclideanSpace.single i 1))
      _ = _ := by simpa only [x₀, a] using
        fderiv_angleBranch_apply p x (EuclideanSpace.single i 1) hx
  have hg0 : g 0 = -a.im / Complex.normSq a := by
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.div_im]
      using hg 0
  have hg1 : g 1 = a.re / Complex.normSq a := by
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.div_im]
      using hg 1
  have hd : Complex.normSq a ≠ 0 :=
    (Complex.normSq_pos.mpr (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hx)).1).ne'
  calc
    _ = (g 0 : ℂ) + g 1 * Complex.I :=
      Complex.orthonormalBasisOneI_repr_symm_apply g
    _ = Complex.I * a / (Complex.normSq a : ℂ) := by
      apply Complex.ext
      · rw [Complex.add_re, Complex.mul_re, Complex.div_re, hg0, hg1]
        simp [Complex.mul_re, Complex.normSq_ofReal]
        field_simp [hd]
      · rw [Complex.add_im, Complex.mul_im, Complex.div_im, hg0, hg1]
        simp [Complex.mul_im, Complex.normSq_ofReal]
        field_simp [hd]

/-- The Laplacian of the logarithmic angle vanishes on its slit domain. -/
theorem laplacian_angleBranch (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    Δ (angleBranch p) x = 0 := by
  have hlap := congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
    (angleBranch p) (EuclideanSpace.basisFun (Fin 2) ℝ)) x
  simp only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Fin.sum_univ_two] at hlap
  rw [hlap, fderiv_fderiv_angleBranch_xx p x hx, fderiv_fderiv_angleBranch_yy p x hx]
  ring

/-- The Hessian of the angle annihilates two copies of its own gradient. -/
theorem fderiv_fderiv_angleBranch_gradient_gradient_eq_zero (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      x
      (∇ (angleBranch p) x)
      (∇ (angleBranch p) x) = 0 := by
  let a := Complex.orthonormalBasisOneI.repr.symm x
  let d := Complex.normSq a
  have ha : a ≠ 0 := (div_ne_zero_iff.mp (Complex.slitPlane_ne_zero hx)).1
  have hd : d ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [fderiv_fderiv_angleBranch_apply p x _ _ hx, repr_symm_gradient_angleBranch p x hx]
  have h : (Complex.I * a / (d : ℂ)) * (Complex.I * a / (d : ℂ)) / a ^ 2 =
      -(1 / (d : ℂ) ^ 2) := by
    field_simp [ha, hd]
    simp [Complex.I_sq]
  rw [h]
  simp [pow_two, Complex.mul_im]

/-- Every pitched logarithmic angle branch solves the native minimal graph equation on its
slit domain. The pitch may vanish. -/
theorem nondivergenceOperator_const_mul_angleBranch (c : ℝ) (p : PolarPoint) (x : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    MinimalGraph.nondivergenceOperator
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ c * angleBranch p x)
      x = 0 := by
  let x₀ := x
  have hsmul : (fun y : Plane ↦ c * angleBranch p y) = c • angleBranch p :=
    funext fun _ ↦ (smul_eq_mul ..).symm
  rw [hsmul]
  rw [MinimalGraph.nondivergenceOperator_eq]
  rw [InnerProductSpace.laplacian_smul c (contDiffAt_angleBranch p x hx)]
  rw [laplacian_angleBranch p x hx]
  simp only [smul_zero, mul_zero, zero_sub]
  have hg : ∇ (c • angleBranch p) x₀ = c • ∇ (angleBranch p) x₀ := by
    simpa using (TauCeti.gradient_const_smul (f := angleBranch p) (x := x₀) c)
  rw [hg]
  rw [fderiv_const_smul_field]
  rw [fderiv_const_smul (differentiableAt_fderiv_angleBranch p x hx) c]
  simp only [smul_apply, map_smul]
  rw [fderiv_fderiv_angleBranch_gradient_gradient_eq_zero p x hx]
  ring

/-- At every polar point, the centered branch gives a minimal graph for every real pitch. -/
theorem nondivergenceOperator_const_mul_angleBranch_repr_projection (c : ℝ) (p : PolarPoint) :
    MinimalGraph.nondivergenceOperator (fun x : Plane ↦ c * angleBranch p x)
      (Complex.orthonormalBasisOneI.repr (projection p)) = 0 := by
  apply nondivergenceOperator_const_mul_angleBranch
  simp [projection_ne_zero]

end TauCeti.PolarGraph
