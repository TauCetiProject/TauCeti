/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Euclidean.MinimalGraph.Equation.Operator
public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
public import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import TauCeti.Analysis.Calculus.Gradient
public import TauCeti.Geometry.Euclidean.PolarGraph.Basic

/-!
# A local logarithmic angle branch for the helicoid

The logarithm is taken after rotating the chosen polar basepoint to the positive real axis.
This gives a smooth Cartesian angle germ at every point of the polar cover.
-/

public noncomputable section

open scoped Gradient Laplacian Topology

namespace TauCeti.PolarGraph

local notation "Plane" => EuclideanSpace ℝ (Fin 2)

/-- The local Cartesian angle centered at a polar point. -/
@[expose] def angleBranch (p : PolarPoint) (x : Plane) : ℝ :=
  angle p + (Complex.log
    (Complex.orthonormalBasisOneI.repr.symm x / projection p)).im

theorem angleBranch_def (p : PolarPoint) (x : Plane) :
    angleBranch p x = angle p + (Complex.log
      (Complex.orthonormalBasisOneI.repr.symm x / projection p)).im := rfl

@[simp] theorem angleBranch_at_projection (p : PolarPoint) :
    angleBranch p (Complex.orthonormalBasisOneI.repr (projection p)) = angle p := by
  simp [angleBranch, projection_ne_zero]

private theorem analyticAt_rotatedLog (p : PolarPoint) :
    AnalyticAt ℂ (fun z : ℂ ↦ Complex.log (z / projection p)) (projection p) := by
  have h : AnalyticAt ℂ (fun z : ℂ ↦ z / projection p) (projection p) := by
    fun_prop
  apply h.clog
  simp [projection_ne_zero]

/-- The rotated logarithmic angle is smooth to every order at its center. -/
theorem contDiffAt_angleBranch (p : PolarPoint) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (angleBranch p)
      (Complex.orthonormalBasisOneI.repr (projection p)) := by
  let L := Complex.orthonormalBasisOneI.repr
  have h : ContDiffAt ℝ n (fun z : ℂ ↦ Complex.log (z / projection p))
      (L.symm (L (projection p))) := by
    simpa [L] using ((analyticAt_rotatedLog p).contDiffAt (n := n)).restrict_scalars ℝ
  exact contDiffAt_const.add
    (Complex.imCLM.contDiff.contDiffAt.comp _ (h.comp _ L.symm.contDiff.contDiffAt))

private theorem hasDerivAt_rotatedLog (p : PolarPoint) (z : ℂ)
    (hz : z / projection p ∈ Complex.slitPlane) :
    HasDerivAt (fun w : ℂ ↦ Complex.log (w / projection p)) z⁻¹ z := by
  have h : HasDerivAt (fun w : ℂ ↦ w / projection p)
      (1 / projection p) z :=
    (hasDerivAt_id z).div_const (projection p)
  have hs : z ≠ 0 := by
    intro hz0
    simp [hz0] at hz
  have hlog := h.clog hz
  simpa [projection_ne_zero p, hs, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
    using hlog

private theorem fderiv_angleBranch_apply_of_slit (p : PolarPoint) (x v : Plane)
    (hx : Complex.orthonormalBasisOneI.repr.symm x / projection p ∈ Complex.slitPlane) :
    fderiv ℝ (angleBranch p) x v =
      (Complex.orthonormalBasisOneI.repr.symm v /
        Complex.orthonormalBasisOneI.repr.symm x).im := by
  have hcomplex := (hasDerivAt_rotatedLog p _ hx).complexToReal_fderiv
  have hplane := hcomplex.comp x
    Complex.orthonormalBasisOneI.repr.symm.hasFDerivAt
  have him := Complex.imCLM.hasFDerivAt.comp _ hplane
  have htotal := (hasFDerivAt_const (angle p) x).add him
  have hd := congrArg (fun L : Plane →L[ℝ] ℝ ↦ L v) htotal.fderiv
  change fderiv ℝ (angleBranch p) x v = _ at hd
  simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hd

/-- The Cartesian first derivative of the centered angle is the imaginary part of division
by the basepoint. -/
theorem fderiv_angleBranch_apply (p : PolarPoint) (v : Plane) :
    fderiv ℝ (angleBranch p)
      (Complex.orthonormalBasisOneI.repr (projection p)) v =
      (Complex.orthonormalBasisOneI.repr.symm v / projection p).im := by
  have h : Complex.orthonormalBasisOneI.repr.symm
      (Complex.orthonormalBasisOneI.repr (projection p)) / projection p ∈
      Complex.slitPlane := by simp [projection_ne_zero p]
  simpa using fderiv_angleBranch_apply_of_slit p _ v h

/-- The Cartesian Hessian of the centered angle is the imaginary part of the complex
second derivative of logarithm. -/
theorem fderiv_fderiv_angleBranch_apply (p : PolarPoint) (v w : Plane) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      (Complex.orthonormalBasisOneI.repr (projection p)) v w =
      -((Complex.orthonormalBasisOneI.repr.symm v *
        Complex.orthonormalBasisOneI.repr.symm w) / (projection p) ^ 2).im := by
  let a := projection p
  let L := Complex.orthonormalBasisOneI.repr.symm
  let x₀ := Complex.orthonormalBasisOneI.repr a
  have ha : a ≠ 0 := projection_ne_zero p
  have hcenter : L x₀ = a := by simp [L, x₀]
  have hslit : ∀ᶠ y in 𝓝 x₀, L y / a ∈ Complex.slitPlane := by
    have hcont : ContinuousAt (fun y : Plane ↦ L y / a) x₀ := by fun_prop
    apply hcont.preimage_mem_nhds
    simpa [hcenter, ha] using Complex.isOpen_slitPlane.mem_nhds
      (show a / a ∈ Complex.slitPlane by simp [ha])
  have heq : (fun y : Plane ↦ fderiv ℝ (angleBranch p) y w) =ᶠ[𝓝 x₀]
      (fun y : Plane ↦ (L w / L y).im) := by
    filter_upwards [hslit] with y hy
    exact fderiv_angleBranch_apply_of_slit p y w hy
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
  have hgrad : DifferentiableAt ℝ (fderiv ℝ (angleBranch p)) x₀ := by
    simpa [x₀, a] using
      ((contDiffAt_angleBranch p (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
        (by norm_num)
  have hscalar : fderiv ℝ
      (fun y : Plane ↦ fderiv ℝ (angleBranch p) y w) x₀ v =
      -((L v * L w) / a ^ 2).im := by
    rw [heq.fderiv_eq, hr.fderiv]
    simp [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]
  have hderiv := congrArg (fun M : Plane →L[ℝ] ℝ ↦ M v)
    (fderiv_clm_apply hgrad (differentiableAt_const w))
  simp only [fderiv_const_apply, ContinuousLinearMap.comp_zero] at hderiv
  rw [hscalar] at hderiv
  simpa [L, x₀, a] using hderiv.symm

/-- The `x` partial derivative of the centered angle. -/
theorem fderiv_angleBranch_x (p : PolarPoint) :
    fderiv ℝ (angleBranch p)
      (Complex.orthonormalBasisOneI.repr (projection p))
      (EuclideanSpace.single 0 1) =
      -(projection p).im / Complex.normSq (projection p) := by
  simpa [Complex.div_im] using
    fderiv_angleBranch_apply p (EuclideanSpace.single 0 1)

/-- The `y` partial derivative of the centered angle. -/
theorem fderiv_angleBranch_y (p : PolarPoint) :
    fderiv ℝ (angleBranch p)
      (Complex.orthonormalBasisOneI.repr (projection p))
      (EuclideanSpace.single 1 1) =
      (projection p).re / Complex.normSq (projection p) := by
  simpa [Complex.div_im] using
    fderiv_angleBranch_apply p (EuclideanSpace.single 1 1)

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

/-- The `xx` Hessian entry of the centered angle. -/
theorem fderiv_fderiv_angleBranch_xx (p : PolarPoint) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      (Complex.orthonormalBasisOneI.repr (projection p))
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1) =
      2 * (projection p).re * (projection p).im /
        Complex.normSq (projection p) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  have hs : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 0 1) = 1 := by simp
  calc
    _ = -((1 : ℂ) / (projection p) ^ 2).im := by
      simpa only [hs, one_mul] using h
    _ = _ := angleHessian_complex_xx (projection p)

/-- The `xy` Hessian entry of the centered angle. -/
theorem fderiv_fderiv_angleBranch_xy (p : PolarPoint) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      (Complex.orthonormalBasisOneI.repr (projection p))
      (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1) =
      ((projection p).im ^ 2 - (projection p).re ^ 2) /
        Complex.normSq (projection p) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 1 1)
  have hs0 : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 0 1) = 1 := by simp
  have hs1 : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 1 1) = Complex.I := by simp
  calc
    _ = -(Complex.I / (projection p) ^ 2).im := by
      simpa only [hs0, hs1, one_mul] using h
    _ = _ := angleHessian_complex_xy (projection p)

/-- The `yy` Hessian entry of the centered angle. -/
theorem fderiv_fderiv_angleBranch_yy (p : PolarPoint) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      (Complex.orthonormalBasisOneI.repr (projection p))
      (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1) =
      -(2 * (projection p).re * (projection p).im) /
        Complex.normSq (projection p) ^ 2 := by
  have h := fderiv_fderiv_angleBranch_apply p
    (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
  have hs : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 1 1) = Complex.I := by simp
  calc
    _ = -((-1 : ℂ) / (projection p) ^ 2).im := by
      simpa only [hs, Complex.I_mul_I] using h
    _ = _ := angleHessian_complex_yy (projection p)

/-- The Cartesian gradient of the angle is the ninety-degree rotation of the radial
vector, divided by squared radius. -/
theorem gradient_angleBranch_repr (p : PolarPoint) :
    Complex.orthonormalBasisOneI.repr.symm
      (∇ (angleBranch p) (Complex.orthonormalBasisOneI.repr (projection p))) =
      Complex.I * projection p / (Complex.normSq (projection p) : ℂ) := by
  let a := projection p
  let x₀ := Complex.orthonormalBasisOneI.repr a
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
        fderiv_angleBranch_apply p (EuclideanSpace.single i 1)
  have hg0 : g 0 = -a.im / Complex.normSq a := by
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.div_im]
      using hg 0
  have hg1 : g 1 = a.re / Complex.normSq a := by
    simpa [Complex.orthonormalBasisOneI_repr_symm_apply, Complex.div_im]
      using hg 1
  have hd : Complex.normSq a ≠ 0 := (Complex.normSq_pos.mpr (projection_ne_zero p)).ne'
  apply Complex.ext
  · change (g 0 + g 1 * Complex.I).re =
        (Complex.I * a / (Complex.normSq a : ℂ)).re
    rw [Complex.add_re, Complex.mul_re, Complex.div_re, hg0, hg1]
    simp [Complex.mul_re, Complex.normSq_ofReal]
    field_simp [hd]
  · change (g 0 + g 1 * Complex.I).im =
        (Complex.I * a / (Complex.normSq a : ℂ)).im
    rw [Complex.add_im, Complex.mul_im, Complex.div_im, hg0, hg1]
    simp [Complex.mul_im, Complex.normSq_ofReal]
    field_simp [hd]

/-- The logarithmic angle is harmonic at its Cartesian center. -/
theorem laplacian_angleBranch (p : PolarPoint) :
    Δ (angleBranch p) (Complex.orthonormalBasisOneI.repr (projection p)) = 0 := by
  let x₀ := Complex.orthonormalBasisOneI.repr (projection p)
  have h0 := fderiv_fderiv_angleBranch_apply p
    (EuclideanSpace.single 0 1) (EuclideanSpace.single 0 1)
  have h1 := fderiv_fderiv_angleBranch_apply p
    (EuclideanSpace.single 1 1) (EuclideanSpace.single 1 1)
  have hs0 : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 0 1) = 1 := by simp
  have hs1 : Complex.orthonormalBasisOneI.repr.symm
      (EuclideanSpace.single 1 1) = Complex.I := by simp
  rw [show Δ (angleBranch p) x₀ =
      ∑ i : Fin 2, fderiv ℝ (fderiv ℝ (angleBranch p)) x₀
        (EuclideanSpace.single i 1) (EuclideanSpace.single i 1) by
      simpa only [EuclideanSpace.basisFun_apply, iteratedFDeriv_two_apply,
        Matrix.cons_val_zero, Matrix.cons_val_one] using
        congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_orthonormalBasis
          (angleBranch p) (EuclideanSpace.basisFun (Fin 2) ℝ)) x₀]
  simp only [Fin.sum_univ_two]
  rw [h0, h1]
  simp only [hs0, hs1, one_mul, Complex.I_mul_I, neg_div,
    Complex.neg_im]
  ring

/-- The Hessian of the angle annihilates two copies of its own gradient. -/
theorem hessian_angleBranch_gradient (p : PolarPoint) :
    fderiv ℝ (fderiv ℝ (angleBranch p))
      (Complex.orthonormalBasisOneI.repr (projection p))
      (∇ (angleBranch p) (Complex.orthonormalBasisOneI.repr (projection p)))
      (∇ (angleBranch p) (Complex.orthonormalBasisOneI.repr (projection p))) = 0 := by
  let a := projection p
  let d := Complex.normSq a
  have ha : a ≠ 0 := projection_ne_zero p
  have hd : d ≠ 0 := (Complex.normSq_pos.mpr ha).ne'
  rw [fderiv_fderiv_angleBranch_apply, gradient_angleBranch_repr]
  have h : (Complex.I * a / (d : ℂ)) * (Complex.I * a / (d : ℂ)) / a ^ 2 =
      -(1 / (d : ℂ) ^ 2) := by
    field_simp [ha, hd]
    simp [Complex.I_sq]
  rw [h]
  simp [pow_two, Complex.mul_im]

/-- Every pitched logarithmic angle germ solves the native minimal graph equation at its
center. The pitch may vanish. -/
theorem nondivergenceOperator_const_mul_angleBranch (c : ℝ) (p : PolarPoint) :
    MinimalGraph.nondivergenceOperator
      (fun x : EuclideanSpace ℝ (Fin 2) ↦ c * angleBranch p x)
      (Complex.orthonormalBasisOneI.repr (projection p)) = 0 := by
  let x₀ := Complex.orthonormalBasisOneI.repr (projection p)
  change MinimalGraph.nondivergenceOperator (c • angleBranch p) x₀ = 0
  rw [MinimalGraph.nondivergenceOperator_eq]
  rw [InnerProductSpace.laplacian_smul c (contDiffAt_angleBranch p)]
  rw [laplacian_angleBranch]
  simp only [smul_zero, mul_zero, zero_sub]
  have hg : ∇ (c • angleBranch p) x₀ = c • ∇ (angleBranch p) x₀ := by
    simpa using (TauCeti.gradient_const_smul (f := angleBranch p) (x := x₀) c)
  rw [hg]
  rw [fderiv_const_smul_field]
  change -((fderiv ℝ (fun y : Plane ↦ c • fderiv ℝ (angleBranch p) y) x₀)
    (c • ∇ (angleBranch p) x₀)) (c • ∇ (angleBranch p) x₀) = 0
  have hgrad : DifferentiableAt ℝ (fderiv ℝ (angleBranch p)) x₀ :=
    ((contDiffAt_angleBranch p (n := 2)).fderiv_right (m := 1) (by norm_num)).differentiableAt
      (by norm_num)
  rw [fderiv_fun_const_smul hgrad c]
  simp only [smul_apply, map_smul]
  rw [hessian_angleBranch_gradient]
  ring

end TauCeti.PolarGraph
