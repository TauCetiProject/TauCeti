/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.Calculus.Morse.Linearization
public import TauCeti.Geometry.Calibrated.SpecialLagrangian
import Mathlib.Algebra.Order.Star.Real
import TauCeti.Analysis.Calculus.FDeriv.Det.Basic
import TauCeti.Analysis.Matrix.Cayley
import TauCeti.LinearAlgebra.Matrix.OfReal

/-!
# Gradient graphs and the special Lagrangian equation

For a real `n × n` matrix `A`, the graph `{v + i A v | v ∈ ℝⁿ}` of `A` in `ℂⁿ` is the image of
the real-linear map `Matrix.realGraphMap A`, `v ↦ v + i A v`, whose values `eⱼ + i A eⱼ` on the
standard basis are the columns of the complex matrix `1 + i A`. The gradient graph
`x ↦ x + i ∇u(x)` of a function `u : ℝⁿ → ℝ` (`TauCeti.gradientGraph`) is the graph `y = ∇u(x)` in
the coordinates `z = x + i y` of `ℂⁿ`; when `u` is `C²` at `x`, its derivative there is
`realGraphMap` of the Hessian matrix `D²u(x)` (`TauCeti.hasFDerivAt_gradientGraph`), the matrix
of `TauCeti.hessianOperator u x` in the standard basis. This file computes the special Lagrangian
data of these graphs.

* **The Lagrangian condition.** `Im ⟪v + i A v, w + i A w⟫_ℂ = v ⬝ A w - A v ⬝ w`, so the graph of
  `A` is Lagrangian exactly when `A` is symmetric
  (`Matrix.forall_im_inner_realGraphMap_eq_zero_iff`). Hessians of `C²` functions are symmetric,
  so gradient graphs are Lagrangian (`TauCeti.im_inner_fderiv_gradientGraph_eq_zero`).
* **The holomorphic volume form.** The pullback of `Ω = dz₁ ∧ ⋯ ∧ dzₙ` along `v ↦ v + i A v` is
  `det (1 + i A) dx₁ ∧ ⋯ ∧ dxₙ` (`TauCeti.standardComplexVolume_realGraphMap`); along a gradient
  graph it is `det (1 + i D²u) dx₁ ∧ ⋯ ∧ dxₙ`
  (`TauCeti.standardComplexVolume_fderiv_gradientGraph`).
* **The special Lagrangian equation.** Oriented by the coordinates of `ℝⁿ`, the graph of `A` is
  calibrated by the special Lagrangian form `φ_θ = Re (e^(-iθ) Ω)` exactly when `A` is symmetric
  and `e^(-iθ) det (1 + i A)` is real and positive
  (`TauCeti.standardSpecialLagrangianForm_realGraphMap_single_eq_norm_ιMulti_iff`). For a gradient
  graph this is the equation `Im (e^(-iθ) det (1 + i D²u)) = 0` with
  `Re (e^(-iθ) det (1 + i D²u)) > 0`
  (`TauCeti.standardSpecialLagrangianForm_fderiv_gradientGraph_eq_norm_ιMulti_iff`).
* **The phase-lift equation.** For symmetric `A` with eigenvalues `λⱼ`,
  `det (1 + i A) = (∏ⱼ √(1 + λⱼ²)) e^(i ∑ⱼ arctan λⱼ)`
  (`Matrix.IsHermitian.det_one_add_I_smul_map_ofReal_eq_mul_exp`), so `e^(-iθ) det (1 + i A)` is
  real and positive exactly when `∑ⱼ arctan λⱼ = θ + 2πk` for some integer `k`
  (`Matrix.IsHermitian.im_exp_mul_det_one_add_I_smul_map_ofReal_eq_zero_and_re_pos_iff`). The
  integer `k` records the branch; nothing here selects one.
* **The linearized equation.** At a symmetric solution `A` of `Im (e^(-iθ) det (1 + i A)) = 0`,
  the derivative of the residual in a real direction `B` is
  `Re (e^(-iθ) det (1 + i A)) tr ((1 + A²)⁻¹ B)`
  (`Matrix.IsSymm.hasDerivAt_im_exp_mul_det_one_add_I_smul`), and `B ↦ tr ((1 + A²)⁻¹ B)` has
  positive principal symbol (`Matrix.IsSymm.trace_inv_one_add_mul_self_mul_vecMulVec_pos`). On the
  positive branch `Re (e^(-iθ) det (1 + i A)) > 0`, so the linearization is elliptic there.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Section III.2.
-/

public section

noncomputable section

open Complex Matrix
open scoped InnerProductSpace Gradient

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

namespace Matrix

omit [DecidableEq ι] in
/-- The real-linear map `v ↦ v + i A v` from `ℝⁿ` to `ℂⁿ`, whose image is the graph of the real
matrix `A` over the real points `ℝⁿ ⊆ ℂⁿ`. -/
def realGraphMap (A : Matrix ι ι ℝ) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℂ ι :=
  LinearMap.toContinuousLinearMap
    { toFun v := WithLp.toLp 2 fun k ↦ (v k : ℂ) + ((A *ᵥ v.ofLp) k : ℂ) * I
      map_add' v w := by
        ext k
        simp [mulVec_add]
        ring
      map_smul' c v := by
        ext k
        simp [mulVec_smul]
        ring }

omit [DecidableEq ι] in
/-- The coordinates of `v + i A v`. -/
@[simp]
theorem realGraphMap_apply (A : Matrix ι ι ℝ) (v : EuclideanSpace ℝ ι)
    (k : ι) : realGraphMap A v k = (v k : ℂ) + ((A *ᵥ v.ofLp) k : ℂ) * I :=
  (rfl)

/-- On the standard basis vector `eⱼ`, the map `v ↦ v + i A v` gives the `j`-th column of the
complex matrix `1 + i A`. -/
theorem realGraphMap_single_apply (A : Matrix ι ι ℝ) (j k : ι) :
    realGraphMap A (EuclideanSpace.single j 1) k =
      (1 + I • A.map ((↑) : ℝ → ℂ) : Matrix ι ι ℂ) k j := by
  by_cases h : k = j
  · subst h; simp [mul_comm]
  · simp [h, mul_comm]

omit [DecidableEq ι] in
/-- The symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ` on the graph of `A`:
`Im ⟪v + i A v, w + i A w⟫_ℂ = v ⬝ A w - A v ⬝ w`. -/
theorem im_inner_realGraphMap (A : Matrix ι ι ℝ) (v w : EuclideanSpace ℝ ι) :
    (⟪realGraphMap A v, realGraphMap A w⟫_ℂ).im =
      v.ofLp ⬝ᵥ (A *ᵥ w.ofLp) - (A *ᵥ v.ofLp) ⬝ᵥ w.ofLp := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, realGraphMap_apply, Complex.im_sum,
    dotProduct, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  simp [Complex.mul_im]
  ring

omit [DecidableEq ι] in
/-- The graph `{v + i A v}` of a real symmetric matrix `A` is isotropic for `Im ⟪·, ·⟫_ℂ`. -/
theorem IsSymm.im_inner_realGraphMap_eq_zero {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (v w : EuclideanSpace ℝ ι) : (⟪realGraphMap A v, realGraphMap A w⟫_ℂ).im = 0 := by
  rw [im_inner_realGraphMap, dotProduct_comm (A *ᵥ v.ofLp), hA.dotProduct_mulVec_comm, sub_self]

/-- The tangent frame `eⱼ + i A eⱼ` of the graph of `A` is Lagrangian exactly when `A` is
symmetric. -/
theorem forall_im_inner_realGraphMap_single_eq_zero_iff (A : Matrix ι ι ℝ) :
    (∀ i j, (⟪realGraphMap A (EuclideanSpace.single i 1),
      realGraphMap A (EuclideanSpace.single j 1)⟫_ℂ).im = 0) ↔ A.IsSymm := by
  refine ⟨fun h ↦ IsSymm.ext fun i j ↦ ?_, fun hA i j ↦ hA.im_inner_realGraphMap_eq_zero _ _⟩
  have := h j i
  simp only [im_inner_realGraphMap, sub_eq_zero] at this
  simpa using this

omit [DecidableEq ι] in
/-- The graph `{v + i A v}` of a real matrix `A` is Lagrangian for `Im ⟪·, ·⟫_ℂ` exactly when `A`
is symmetric. -/
theorem forall_im_inner_realGraphMap_eq_zero_iff (A : Matrix ι ι ℝ) :
    (∀ v w, (⟪realGraphMap A v, realGraphMap A w⟫_ℂ).im = 0) ↔ A.IsSymm := by
  classical
  exact ⟨fun h ↦ (forall_im_inner_realGraphMap_single_eq_zero_iff A).1 fun _ _ ↦ h _ _,
    IsSymm.im_inner_realGraphMap_eq_zero⟩

omit [DecidableEq ι] in
/-- The real parts of `v + i A v` recover `v`, so the map `v ↦ v + i A v` is injective. -/
theorem realGraphMap_injective (A : Matrix ι ι ℝ) :
    Function.Injective (realGraphMap A) := by
  intro v w h
  ext k
  simpa using congrArg Complex.re (congrFun (congrArg WithLp.ofLp h) k)

/-- The images `eⱼ + i A eⱼ` of the standard basis vectors are `ℝ`-linearly independent. -/
theorem linearIndependent_realGraphMap_single (A : Matrix ι ι ℝ) :
    LinearIndependent ℝ fun j ↦ realGraphMap A (EuclideanSpace.single j 1) := by
  have h := (EuclideanSpace.basisFun ι ℝ).toBasis.linearIndependent.map'
    (realGraphMap A).toLinearMap
    (LinearMap.ker_eq_bot.mpr (realGraphMap_injective A))
  simpa [Function.comp_def] using h

/-! ### The phase in terms of the eigenvalues -/

/-- **The phase-lift equation.** For a real symmetric matrix `A` with eigenvalues `λⱼ`,
`e^(-iθ) det (1 + i A)` is real and positive exactly when `∑ⱼ arctan λⱼ = θ` modulo `2π`. -/
theorem IsHermitian.im_exp_mul_det_one_add_I_smul_map_ofReal_eq_zero_and_re_pos_iff
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (θ : ℝ) :
    ((Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).im = 0 ∧
        0 < (Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).re) ↔
      ∃ k : ℤ, ∑ j, Real.arctan (hA.eigenvalues j) = θ + 2 * Real.pi * k := by
  set r : ℝ := ∏ j, √(1 + hA.eigenvalues j ^ 2)
  set s : ℝ := ∑ j, Real.arctan (hA.eigenvalues j)
  have hr : 0 < r := Finset.prod_pos fun j _ ↦ Real.sqrt_pos.2 (by positivity)
  have hz : Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det =
      (r : ℂ) * Complex.exp (((s - θ : ℝ) : ℂ) * I) := by
    rw [hA.det_one_add_I_smul_map_ofReal_eq_mul_exp, mul_left_comm, ← Complex.exp_add,
      Complex.ofReal_sub]
    congr 2
    ring
  rw [hz, Complex.im_ofReal_mul, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, mul_eq_zero, mul_pos_iff_of_pos_left hr, or_iff_right hr.ne']
  have hcos : (Real.sin (s - θ) = 0 ∧ 0 < Real.cos (s - θ)) ↔ Real.cos (s - θ) = 1 := by
    have h := Real.sin_sq_add_cos_sq (s - θ)
    refine ⟨fun ⟨h0, hpos⟩ ↦ ?_, fun h1 ↦ ⟨?_, by rw [h1]; exact one_pos⟩⟩
    · rw [h0] at h
      nlinarith [hpos]
    · rw [h1] at h
      nlinarith
  rw [hcos, Real.cos_eq_one_iff]
  exact exists_congr fun k ↦ ⟨fun h ↦ by linarith, fun h ↦ by linarith⟩

/-! ### The linearized equation -/

/-- **The linearized special Lagrangian equation.** Let `A` be a real symmetric matrix solving the
phase-`θ` equation `Im (e^(-iθ) det (1 + i A)) = 0`. Then the derivative of the imaginary residual
`Im (e^(-iθ) det (1 + i (A + t B)))` at `t = 0`, in any real direction `B`, is
`Re (e^(-iθ) det (1 + i A)) tr ((1 + A²)⁻¹ B)`: the linearized operator is the trace against
`(1 + A²)⁻¹`, times `Re (e^(-iθ) det (1 + i A))`. -/
theorem IsSymm.hasDerivAt_im_exp_mul_det_one_add_I_smul {A : Matrix ι ι ℝ} (hA : A.IsSymm)
    (B : Matrix ι ι ℝ) {θ : ℝ}
    (hθ : (Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).im = 0) :
    HasDerivAt
      (fun t : ℝ ↦
        (Complex.exp (-(θ : ℂ) * I) * (1 + I • (A + t • B).map ((↑) : ℝ → ℂ)).det).im)
      ((Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).re *
        trace ((1 + A * A)⁻¹ * B)) 0 := by
  set M : Matrix ι ι ℂ := 1 + I • A.map ((↑) : ℝ → ℂ) with hM_def
  set N : Matrix ι ι ℂ := I • B.map ((↑) : ℝ → ℂ) with hN_def
  set c : ℂ := Complex.exp (-(θ : ℂ) * I)
  have hM : IsUnit M.det := (isHermitian_iff_isSymm.2 hA).map_ofReal.isUnit_det_one_add_I_smul
  have hline (t : ℝ) :
      1 + I • (A + t • B).map ((↑) : ℝ → ℂ) = M * (1 + (t : ℂ) • (M⁻¹ * N)) := by
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul, mul_nonsing_inv_cancel_left _ _ hM]
    ext i j
    simp [M, N]
    ring
  have hC : HasDerivAt (fun t : ℂ ↦ c * (M.det * det (1 + t • (M⁻¹ * N))))
      (c * (M.det * trace (M⁻¹ * N))) ((0 : ℝ) : ℂ) := by
    simpa using ((hasDerivAt_det_one_add_smul (M⁻¹ * N)).const_mul M.det).const_mul c
  have hI := Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hC.comp_ofReal
  convert hI using 1
  · funext t
    simp [hline, det_mul]
  · -- On a solution `e^(-iθ) det M` is real, and `M⁻¹ N = i (1 - i A) (1 + A²)⁻¹ B`.
    have hMN : M⁻¹ * N = I • (((1 + A * A)⁻¹ * B).map ((↑) : ℝ → ℂ) -
        I • (A * (1 + A * A)⁻¹ * B).map ((↑) : ℝ → ℂ)) := by
      rw [hM_def, hA.inv_one_add_I_smul_map_ofReal, hN_def, map_ofReal_mul, map_ofReal_mul,
        map_ofReal_mul]
      simp [sub_mul, Matrix.mul_assoc]
    have hz : c * M.det = ((c * M.det).re : ℂ) := Complex.ext (by simp) (by simp [hθ])
    rw [Complex.imCLM_apply, ← mul_assoc, hz, hMN, trace_smul, trace_sub, trace_smul,
      trace_map_ofReal, trace_map_ofReal]
    simp

end Matrix

namespace TauCeti

/-! ### Gradient graphs -/

omit [DecidableEq ι] in
/-- The **gradient graph** of `u : ℝⁿ → ℝ`: the map `x ↦ x + i ∇u(x)` from `ℝⁿ` to `ℂⁿ`, whose
image is the graph `y = ∇u(x)` in `ℂⁿ`, with coordinates `z = x + i y`. -/
def gradientGraph (u : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    EuclideanSpace ℂ ι :=
  WithLp.toLp 2 fun k ↦ (x k : ℂ) + (∇ u x k : ℂ) * I

omit [DecidableEq ι] in
/-- The coordinates of `x + i ∇u(x)`. -/
@[simp]
theorem gradientGraph_apply (u : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι)
    (k : ι) : gradientGraph u x k = (x k : ℂ) + (∇ u x k : ℂ) * I :=
  (rfl)

/-- The **derivative of a gradient graph**: if `u` is `C²` at `x`, the gradient graph
`x ↦ x + i ∇u(x)` has derivative `v ↦ v + i D²u(x) v` at `x`, the map `realGraphMap` of the
Hessian matrix `(∂ᵢ∂ⱼu(x))`. -/
theorem hasFDerivAt_gradientGraph {u : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hu : ContDiffAt ℝ 2 u x) :
    HasFDerivAt (gradientGraph u)
      (realGraphMap (LinearMap.toMatrix (EuclideanSpace.basisFun ι ℝ).toBasis
        (EuclideanSpace.basisFun ι ℝ).toBasis (hessianOperator u x).toLinearMap)) x := by
  -- `realGraphMap 0` is the real inclusion `v ↦ v` of `ℝⁿ` into `ℂⁿ`.
  let L := realGraphMap (0 : Matrix ι ι ℝ)
  have h := L.hasFDerivAt.add ((L.hasFDerivAt.comp x hu.hasFDerivAt_gradient).const_smul I)
  convert h using 1
  · ext y k
    simp [L, mul_comm]
  · ext v k
    have hmul := congrFun (LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun ι ℝ).toBasis (EuclideanSpace.basisFun ι ℝ).toBasis
      (hessianOperator u x).toLinearMap v) k
    have hrepr : ⇑((EuclideanSpace.basisFun ι ℝ).toBasis.repr v) = v.ofLp := by
      ext j
      simp
    rw [hrepr] at hmul
    simp [L, hmul, mul_comm]

omit [DecidableEq ι] in
/-- **Gradient graphs are Lagrangian.** If `u` is `C²` at `x`, the tangent space of the gradient
graph at `x` is isotropic for the symplectic form `Im ⟪·, ·⟫_ℂ` of `ℂⁿ`, by the symmetry of the
Hessian. -/
theorem im_inner_fderiv_gradientGraph_eq_zero {u : EuclideanSpace ℝ ι → ℝ}
    {x : EuclideanSpace ℝ ι} (hu : ContDiffAt ℝ 2 u x) (v w : EuclideanSpace ℝ ι) :
    (⟪fderiv ℝ (gradientGraph u) x v, fderiv ℝ (gradientGraph u) x w⟫_ℂ).im = 0 := by
  classical
  rw [(hasFDerivAt_gradientGraph hu).fderiv]
  exact ((EuclideanSpace.basisFun ι ℝ).isSymm_toMatrix_hessianOperator
    hu).im_inner_realGraphMap_eq_zero v w

/-! ### The holomorphic volume form and the special Lagrangian equation -/

/-- **The holomorphic volume form on a graph**: pulled back along `v ↦ v + i A v`, the complex
volume form `Ω = dz₁ ∧ ⋯ ∧ dzₙ` is `det (1 + i A) dx₁ ∧ ⋯ ∧ dxₙ`. -/
theorem standardComplexVolume_realGraphMap (A : Matrix (Fin n) (Fin n) ℝ)
    (w : Fin n → EuclideanSpace ℝ (Fin n)) :
    standardComplexVolume n (fun i ↦ realGraphMap A (w i)) =
      (1 + I • A.map ((↑) : ℝ → ℂ)).det *
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det w : ℂ) := by
  have hrows : (Matrix.of fun i k ↦ realGraphMap A (w i) k) =
      (Matrix.of fun i j ↦ (w i j : ℂ)) * (1 + I • A.map ((↑) : ℝ → ℂ))ᵀ := by
    ext i k
    simp only [of_apply, realGraphMap_apply, Matrix.mul_apply, transpose_apply,
      Matrix.add_apply, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Matrix.one_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ite_true, mulVec, dotProduct, Complex.ofReal_sum, Finset.sum_mul]
    congr 1
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    push_cast
    ring
  have hdet : ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det w : ℂ) =
      (Matrix.of fun i j ↦ (w i j : ℂ)).det := by
    rw [Module.Basis.det_apply, ← det_transpose]
    rw [← det_map_ofReal]
    refine congrArg det ?_
    ext i j
    simp [Module.Basis.toMatrix_apply]
  rw [standardComplexVolume_apply, hrows, det_mul, det_transpose, hdet, mul_comm]

/-- On the tangent frame `eⱼ + i A eⱼ` of the graph of `A`, the complex volume form is
`det (1 + i A)`. -/
theorem standardComplexVolume_realGraphMap_single (A : Matrix (Fin n) (Fin n) ℝ) :
    standardComplexVolume n (fun j ↦ realGraphMap A (EuclideanSpace.single j 1)) =
      (1 + I • A.map ((↑) : ℝ → ℂ)).det := by
  have h := standardComplexVolume_realGraphMap A (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  rw [Module.Basis.det_self] at h
  simpa using h

/-- **The special Lagrangian equation for a graph.** The graph `{v + i A v}` of a real matrix `A`,
oriented by the frame `eⱼ + i A eⱼ`, is calibrated by the phase-`θ` special Lagrangian form,
`φ_θ (eⱼ + i A eⱼ) = ‖⋀ⱼ (eⱼ + i A eⱼ)‖`, exactly when `A` is symmetric (the graph is Lagrangian)
and `e^(-iθ) det (1 + i A)` is real and positive. -/
theorem standardSpecialLagrangianForm_realGraphMap_single_eq_norm_ιMulti_iff
    (A : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) :
    standardSpecialLagrangianForm n θ (fun j ↦ realGraphMap A (EuclideanSpace.single j 1)) =
        ‖exteriorPower.ιMulti ℝ n (fun j ↦ realGraphMap A (EuclideanSpace.single j 1))‖ ↔
      A.IsSymm ∧ (Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).im = 0 ∧
        0 < (Complex.exp (-(θ : ℂ) * I) * (1 + I • A.map ((↑) : ℝ → ℂ)).det).re := by
  rw [standardSpecialLagrangianForm_apply_eq_norm_ιMulti_iff n θ
      (linearIndependent_realGraphMap_single A),
    forall_im_inner_realGraphMap_single_eq_zero_iff, standardComplexVolume_realGraphMap_single]

/-- **The special Lagrangian equation for the graph of a symmetric matrix**, in phase-lift form:
for a real symmetric matrix `A` with eigenvalues `λⱼ`, the graph of `A` oriented by the frame
`eⱼ + i A eⱼ` is calibrated by the phase-`θ` special Lagrangian form exactly when
`∑ⱼ arctan λⱼ = θ + 2πk` for some integer `k`. -/
theorem standardSpecialLagrangianForm_realGraphMap_single_eq_norm_ιMulti_iff_exists_sum_arctan
    {A : Matrix (Fin n) (Fin n) ℝ} (hA : A.IsHermitian) (θ : ℝ) :
    standardSpecialLagrangianForm n θ (fun j ↦ realGraphMap A (EuclideanSpace.single j 1)) =
        ‖exteriorPower.ιMulti ℝ n (fun j ↦ realGraphMap A (EuclideanSpace.single j 1))‖ ↔
      ∃ k : ℤ, ∑ j, Real.arctan (hA.eigenvalues j) = θ + 2 * Real.pi * k := by
  rw [standardSpecialLagrangianForm_realGraphMap_single_eq_norm_ιMulti_iff,
    and_iff_right (isHermitian_iff_isSymm.1 hA),
    hA.im_exp_mul_det_one_add_I_smul_map_ofReal_eq_zero_and_re_pos_iff]

/-- **The holomorphic volume form on a gradient graph**: if `u` is `C²` at `x`, the pullback of
`Ω = dz₁ ∧ ⋯ ∧ dzₙ` along the gradient graph is `det (1 + i D²u(x)) dx₁ ∧ ⋯ ∧ dxₙ` at `x`. -/
theorem standardComplexVolume_fderiv_gradientGraph {u : EuclideanSpace ℝ (Fin n) → ℝ}
    {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x)
    (w : Fin n → EuclideanSpace ℝ (Fin n)) :
    standardComplexVolume n (fun i ↦ fderiv ℝ (gradientGraph u) x (w i)) =
      (1 + I • (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
          (hessianOperator u x).toLinearMap).map ((↑) : ℝ → ℂ)).det *
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det w : ℂ) := by
  rw [(hasFDerivAt_gradientGraph hu).fderiv, standardComplexVolume_realGraphMap]

/-- **The special Lagrangian equation for gradient graphs.** If `u` is `C²` at `x`, the gradient
graph, oriented by the coordinates of `ℝⁿ`, is calibrated at `x` by the phase-`θ` special Lagrangian
form exactly when `e^(-iθ) det (1 + i D²u(x))` is real and positive: the imaginary equation
`Im (e^(-iθ) det (1 + i D²u(x))) = 0` together with the positivity of the real part. -/
theorem standardSpecialLagrangianForm_fderiv_gradientGraph_eq_norm_ιMulti_iff
    {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)} (hu : ContDiffAt ℝ 2 u x)
    (θ : ℝ) :
    standardSpecialLagrangianForm n θ
          (fun j ↦ fderiv ℝ (gradientGraph u) x (EuclideanSpace.single j 1)) =
        ‖exteriorPower.ιMulti ℝ n
          (fun j ↦ fderiv ℝ (gradientGraph u) x (EuclideanSpace.single j 1))‖ ↔
      (Complex.exp (-(θ : ℂ) * I) *
          (1 + I • (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (hessianOperator u x).toLinearMap).map ((↑) : ℝ → ℂ)).det).im = 0 ∧
        0 < (Complex.exp (-(θ : ℂ) * I) *
          (1 + I • (LinearMap.toMatrix (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
            (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
              (hessianOperator u x).toLinearMap).map ((↑) : ℝ → ℂ)).det).re := by
  rw [(hasFDerivAt_gradientGraph hu).fderiv,
    standardSpecialLagrangianForm_realGraphMap_single_eq_norm_ιMulti_iff,
    and_iff_right ((EuclideanSpace.basisFun (Fin n) ℝ).isSymm_toMatrix_hessianOperator hu)]

end TauCeti
