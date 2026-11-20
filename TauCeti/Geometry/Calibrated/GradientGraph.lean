/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.CStarAlgebra.Matrix
public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Matrix.Spectrum
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Calibrated.SpecialLagrangian
import Mathlib.Analysis.Calculus.FDeriv.WithLp
import Mathlib.Analysis.Matrix.Hermitian
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.InnerProductSpace.Gram.Hadamard
import TauCeti.Analysis.Matrix.Cayley
import TauCeti.Analysis.SpecialFunctions.Complex.Arg

/-!
# Graphs and gradient graphs in complex Euclidean space

Write `ℂⁿ = ℝⁿ ⊕ i ℝⁿ`. A real linear operator `A` on `ℝⁿ` has the graph `{x + i A x}`,
parametrized by the real-linear graph map `x ↦ x + i A x` (`TauCeti.graphMap`), and a real
function `u` on `ℝⁿ` has the gradient graph `{x + i ∇u(x)}`, parametrized by
`TauCeti.gradientGraph u`. The derivative of the gradient graph at `x` is the graph map of the
derivative `H` of `∇u` at `x`, the Hessian of `u` (`TauCeti.hasFDerivAt_gradientGraph`).

This file proves the special Lagrangian equations for these graphs.

* The Hermitian product of two vectors of the graph of `A` has imaginary part
  `Im ⟪x + i A x, y + i A y⟫ = ⟪x, A y⟫ - ⟪A x, y⟫` (`TauCeti.im_inner_graphMap`), so the graph is
  Lagrangian exactly when `A` is symmetric (`TauCeti.forall_im_inner_graphMap_eq_zero_iff`). By
  the symmetry of second derivatives, the tangent planes of a gradient graph are Lagrangian
  (`TauCeti.im_inner_fderiv_gradientGraph_eq_zero`).
* On the graph of a real `n × n` matrix `M`, the holomorphic volume form is
  `Ω = det (1 + i M) dx₁ ∧ ⋯ ∧ dxₙ` (`TauCeti.standardComplexVolume_graphMap_comp`); on a gradient
  graph `M` is the Hessian matrix (`TauCeti.standardComplexVolume_fderiv_gradientGraph_comp`).
* The graph of `M`, oriented by `(x₁, …, xₙ)`, is calibrated by the special Lagrangian form
  `φ_θ = Re (e^{-iθ} Ω)` exactly when `M` is symmetric, `Im (e^{-iθ} det (1 + i M)) = 0` and
  `Re (e^{-iθ} det (1 + i M)) > 0`
  (`TauCeti.standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff`). For a gradient graph
  the symmetry is automatic, which leaves the phase equation for the Hessian
  (`TauCeti.standardSpecialLagrangianForm_fderiv_gradientGraph_eq_norm_ιMulti_iff`).
* For a symmetric `M` with eigenvalues `λⱼ`, `det (1 + i M) = (∏ⱼ √(1 + λⱼ²)) e^{i ∑ⱼ arctan λⱼ}`,
  so the phase equation is the real phase-lift equation `∑ⱼ arctan λⱼ = θ` modulo `2π`
  (`TauCeti.standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff_of_isHermitian`).

## Main declarations

* `TauCeti.graphMap`: the graph map `x ↦ x + i A x` of a real operator `A`.
* `TauCeti.gradientGraph`: the gradient graph `x ↦ x + i ∇u(x)` of a real function `u`.

## References

* R. Harvey and H. B. Lawson, *Calibrated geometries*, Acta Math. **148** (1982), 47–157,
  Section III.2, Theorem III.2.3.
-/

public section

noncomputable section

open Complex Matrix Module Filter
open scoped InnerProductSpace Gradient Topology

namespace TauCeti

/-! ### The graph of a real operator -/

section Graph

variable {ι : Type*} [Fintype ι]

/-- The graph map `x ↦ x + i A x : ℝ^ι → ℂ^ι` of a real linear operator `A` on `ℝ^ι`, whose image
is the graph of `A` in `ℂ^ι = ℝ^ι ⊕ i ℝ^ι`. -/
def graphMap (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι) :
    EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℂ ι :=
  EuclideanSpace.ofRealCLM ι + I • (EuclideanSpace.ofRealCLM ι).comp A

variable (A : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι)

/-- The graph map sends `x` to `x + i A x`. -/
theorem graphMap_apply (x : EuclideanSpace ℝ ι) :
    graphMap A x = EuclideanSpace.ofRealCLM ι x + I • EuclideanSpace.ofRealCLM ι (A x) :=
  (rfl)

/-- The coordinates of `x + i A x` are `xₖ + (A x)ₖ i`. -/
@[simp]
theorem graphMap_apply_apply (x : EuclideanSpace ℝ ι) (k : ι) :
    graphMap A x k = x k + A x k * I := by
  simp [graphMap_apply, mul_comm]

/-- The graph map is injective: the real part of `x + i A x` is `x`. -/
theorem graphMap_injective : Function.Injective (graphMap A) := fun x y h ↦ by
  ext k
  simpa using congrArg (fun z : EuclideanSpace ℂ ι ↦ (z k).re) h

/-- A family `v` of vectors of `ℝ^ι` is linearly independent exactly when its image
`v + i A v` in the graph of `A` is. -/
theorem linearIndependent_graphMap_comp_iff {κ : Type*} {v : κ → EuclideanSpace ℝ ι} :
    LinearIndependent ℝ (graphMap A ∘ v) ↔ LinearIndependent ℝ v :=
  LinearMap.linearIndependent_iff (graphMap A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℂ ι)
    (LinearMap.ker_eq_bot.mpr (graphMap_injective A))

/-- The real part of the Hermitian product on the graph of `A` is the metric
`⟪x, y⟫ + ⟪A x, A y⟫` induced on the graph. -/
@[simp]
theorem re_inner_graphMap (x y : EuclideanSpace ℝ ι) :
    (⟪graphMap A x, graphMap A y⟫_ℂ).re = ⟪x, y⟫_ℝ + ⟪A x, A y⟫_ℝ := by
  simp [graphMap_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_ofRealCLM]

/-- The imaginary part of the Hermitian product on the graph of `A` is
`Im ⟪x + i A x, y + i A y⟫ = ⟪x, A y⟫ - ⟪A x, y⟫`: the standard symplectic form restricted to the
graph. -/
@[simp]
theorem im_inner_graphMap (x y : EuclideanSpace ℝ ι) :
    (⟪graphMap A x, graphMap A y⟫_ℂ).im = ⟪x, A y⟫_ℝ - ⟪A x, y⟫_ℝ := by
  simp [graphMap_apply, inner_add_left, inner_add_right, inner_smul_left, inner_smul_right,
    EuclideanSpace.inner_ofRealCLM]
  ring

/-- **The graph of `A` is Lagrangian exactly when `A` is symmetric**: `Im ⟪x + i A x, y + i A y⟫`
vanishes for all `x, y` if and only if `⟪A x, y⟫ = ⟪x, A y⟫` for all `x, y`. -/
theorem forall_im_inner_graphMap_eq_zero_iff :
    (∀ x y, (⟪graphMap A x, graphMap A y⟫_ℂ).im = 0) ↔
      (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
  simp only [im_inner_graphMap, sub_eq_zero, LinearMap.IsSymmetric, ContinuousLinearMap.coe_coe]
  exact ⟨fun h x y ↦ (h x y).symm, fun h x y ↦ (h x y).symm⟩

/-- The Lagrangian condition for the graph of `A` may be tested on a basis `b`:
`Im ⟪b i + i A (b i), b j + i A (b j)⟫ = 0` for all `i, j` exactly when `A` is symmetric. -/
theorem forall_im_inner_graphMap_basis_eq_zero_iff {κ : Type*}
    (b : Basis κ ℝ (EuclideanSpace ℝ ι)) :
    (∀ i j, (⟪graphMap A (b i), graphMap A (b j)⟫_ℂ).im = 0) ↔
      (A : EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι).IsSymmetric := by
  rw [← forall_im_inner_graphMap_eq_zero_iff]
  refine ⟨fun h x y ↦ ?_, fun h i j ↦ h _ _⟩
  -- `(x, y) ↦ Im ⟪x + i A x, y + i A y⟫` is bilinear, and vanishes on pairs of basis vectors.
  have hB : (innerₗ (EuclideanSpace ℝ ι)).compl₂ (A : EuclideanSpace ℝ ι →ₗ[ℝ] _) -
      (innerₗ (EuclideanSpace ℝ ι)).comp (A : EuclideanSpace ℝ ι →ₗ[ℝ] _) = 0 :=
    b.ext fun i ↦ b.ext fun j ↦ by simpa [im_inner_graphMap] using h i j
  simpa [im_inner_graphMap] using LinearMap.congr_fun₂ hB x y

end Graph

/-! ### The holomorphic volume form on a graph -/

section Volume

variable {n : ℕ}

/-- **The holomorphic volume form on a graph.** On the graph of a real `n × n` matrix `M`,
`Ω = det (1 + i M) dx₁ ∧ ⋯ ∧ dxₙ`: for every `n`-tuple `v` of vectors of `ℝⁿ`,
`Ω (v₁ + i M v₁, …, vₙ + i M vₙ) = det (1 + i M) · det v`. -/
theorem standardComplexVolume_graphMap_comp (M : Matrix (Fin n) (Fin n) ℝ)
    (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    standardComplexVolume n (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ v) =
      det (1 + I • M.map ((↑) : ℝ → ℂ)) *
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v : ℂ) := by
  set V : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j ↦ v i j
  -- The coordinate matrix of the graph frame is `V (1 + i M)ᵀ`.
  have hW : (Matrix.of fun i j ↦ (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ v) i j) =
      V.map ((↑) : ℝ → ℂ) * (1 + I • M.map ((↑) : ℝ → ℂ))ᵀ := by
    ext i j
    simp [V, Matrix.mul_apply, Matrix.one_apply, mulVec, dotProduct, add_mul, ite_mul,
      Finset.sum_add_distrib, Finset.mul_sum, mul_assoc, mul_comm]
  have hV : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v = V.det := by
    rw [← Matrix.basisFun_toBasis_det_toLp]
    congr 1
  rw [standardComplexVolume_apply, hW, det_mul, det_transpose, hV, mul_comm]
  exact congrArg _ (RingHom.map_det Complex.ofRealHom V).symm

/-! ### Special Lagrangian graphs -/

/-- **The special Lagrangian equation for a graph** (Harvey–Lawson, Theorem III.2.3). The graph
of a real `n × n` matrix `M`, oriented by `(x₁, …, xₙ)`, is calibrated by the special Lagrangian
form `φ_θ = Re (e^{-iθ} Ω)`, that is `φ_θ` equals the volume `‖v₁ ∧ ⋯ ∧ vₙ‖` on the frame
`vⱼ = eⱼ + i M eⱼ`, exactly when `M` is symmetric (the graph is Lagrangian) and
`e^{-iθ} det (1 + i M)` is a positive real number. -/
theorem standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff
    (M : Matrix (Fin n) (Fin n) ℝ) (θ : ℝ) :
    standardSpecialLagrangianForm n θ
        (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ EuclideanSpace.basisFun (Fin n) ℝ) =
        ‖exteriorPower.ιMulti ℝ n
          (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ EuclideanSpace.basisFun (Fin n) ℝ)‖ ↔
      M.IsHermitian ∧ (exp (-(θ : ℂ) * I) * det (1 + I • M.map ((↑) : ℝ → ℂ))).im = 0 ∧
        0 < (exp (-(θ : ℂ) * I) * det (1 + I • M.map ((↑) : ℝ → ℂ))).re := by
  have hdet : (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det
      (EuclideanSpace.basisFun (Fin n) ℝ) = 1 := by
    simpa using (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det_self
  rw [standardSpecialLagrangianForm_apply_eq_norm_ιMulti_iff n θ
      (linearIndependent_graphMap_comp_iff _ |>.mpr
        (EuclideanSpace.basisFun (Fin n) ℝ).orthonormal.linearIndependent),
    standardComplexVolume_graphMap_comp, hdet, ofReal_one, mul_one,
    ← isSymmetric_toEuclideanLin_iff, ← coe_toEuclideanCLM_eq_toEuclideanLin,
    ← forall_im_inner_graphMap_basis_eq_zero_iff _ (EuclideanSpace.basisFun (Fin n) ℝ).toBasis]
  simp

open scoped ComplexOrder in
/-- **The phase-lift equation for a symmetric graph.** For a real symmetric `n × n` matrix `M`
with eigenvalues `λⱼ`, the graph of `M`, oriented by `(x₁, …, xₙ)`, is calibrated by the special
Lagrangian form of phase `θ` exactly when `∑ⱼ arctan λⱼ = θ` modulo `2π`. -/
theorem standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff_of_isHermitian
    {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.IsHermitian) (θ : ℝ) :
    standardSpecialLagrangianForm n θ
        (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ EuclideanSpace.basisFun (Fin n) ℝ) =
        ‖exteriorPower.ιMulti ℝ n
          (graphMap (toEuclideanCLM (𝕜 := ℝ) M) ∘ EuclideanSpace.basisFun (Fin n) ℝ)‖ ↔
      ((∑ j, Real.arctan (hM.eigenvalues j) : ℝ) : Real.Angle) = θ := by
  set r : ℝ := ∏ j, √(1 + hM.eigenvalues j ^ 2)
  set α : ℝ := ∑ j, Real.arctan (hM.eigenvalues j)
  have hr : 0 < r := Finset.prod_pos fun j _ ↦ Real.sqrt_pos.mpr (by positivity)
  have hrot : exp (-(θ : ℂ) * I) * det (1 + I • M.map ((↑) : ℝ → ℂ)) =
      (r : ℂ) * exp (((α - θ : ℝ) : ℂ) * I) := by
    rw [hM.det_one_add_I_smul_map_ofReal_eq_mul_exp, mul_left_comm, ← exp_add, ofReal_sub]
    congr 2
    ring
  rw [standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff, and_iff_right hM, hrot,
    and_comm, eq_comm, ← Complex.pos_iff, ofReal_mul_exp_mul_I_pos_iff hr, Real.Angle.coe_sub,
    sub_eq_zero]

end Volume

/-! ### Gradient graphs -/

section GradientGraph

variable {ι : Type*} [Fintype ι]

/-- The gradient graph `x ↦ x + i ∇u(x) : ℝ^ι → ℂ^ι` of a real function `u` on `ℝ^ι`, a
parametrization of the graph of `∇u` in `ℂ^ι = ℝ^ι ⊕ i ℝ^ι`. -/
def gradientGraph (u : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℂ ι :=
  EuclideanSpace.ofRealCLM ι x + I • EuclideanSpace.ofRealCLM ι (∇ u x)

/-- The gradient graph sends `x` to `x + i ∇u(x)`. -/
theorem gradientGraph_def (u : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) :
    gradientGraph u x = EuclideanSpace.ofRealCLM ι x + I • EuclideanSpace.ofRealCLM ι (∇ u x) :=
  (rfl)

/-- The coordinates of `x + i ∇u(x)` are `xₖ + (∇u(x))ₖ i`. -/
@[simp]
theorem gradientGraph_apply (u : EuclideanSpace ℝ ι → ℝ) (x : EuclideanSpace ℝ ι) (k : ι) :
    gradientGraph u x k = x k + ∇ u x k * I := by
  simp [gradientGraph_def, mul_comm]

variable {u : EuclideanSpace ℝ ι → ℝ} {x : EuclideanSpace ℝ ι}
  {H : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ ι}

/-- If `∇u` has derivative `H` at `x` (the Hessian of `u`), the gradient graph has derivative the
graph map `v ↦ v + i H v` of `H` at `x`. -/
theorem hasFDerivAt_gradientGraph (hH : HasFDerivAt (∇ u) H x) :
    HasFDerivAt (gradientGraph u) (graphMap H) x :=
  (EuclideanSpace.ofRealCLM ι).hasFDerivAt.add
    (((EuclideanSpace.ofRealCLM ι).hasFDerivAt.comp x hH).const_smul I)

/-- **Gradient graphs are Lagrangian.** If `u` is differentiable near `x`, the tangent plane of
the gradient graph at `x` is Lagrangian: `Im ⟪dΓ v, dΓ w⟫ = 0`. This is the symmetry of the
Hessian of `u`. -/
theorem im_inner_fderiv_gradientGraph_eq_zero (hu : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y)
    (v w : EuclideanSpace ℝ ι) :
    (⟪fderiv ℝ (gradientGraph u) x v, fderiv ℝ (gradientGraph u) x w⟫_ℂ).im = 0 := by
  by_cases hΓ : DifferentiableAt ℝ (gradientGraph u) x
  · -- `∇u` is differentiable at `x`, its coordinates being the imaginary parts of those of `Γ`.
    have hgrad : DifferentiableAt ℝ (∇ u) x := (differentiableAt_piLp _).mpr fun k ↦ by
      have hk : (fun y ↦ ∇ u y k) = fun y ↦ Complex.imCLM (gradientGraph u y k) :=
        funext fun y ↦ by simp
      rw [hk]
      exact Complex.imCLM.differentiableAt.comp x
        ((differentiableAt_piLp _).mp hΓ k)
    rw [(hasFDerivAt_gradientGraph hgrad.hasFDerivAt).fderiv]
    exact (forall_im_inner_graphMap_eq_zero_iff _).mpr
      (isSymmetric_of_hasFDerivAt_gradient hu hgrad.hasFDerivAt) v w
  · simp [fderiv_zero_of_not_differentiableAt hΓ]

end GradientGraph

section GradientGraphVolume

variable {n : ℕ} {u : EuclideanSpace ℝ (Fin n) → ℝ} {x : EuclideanSpace ℝ (Fin n)}
  {M : Matrix (Fin n) (Fin n) ℝ}

/-- **The holomorphic volume form on a gradient graph**: if `∇u` has derivative the Hessian matrix
`M` at `x`, then `Γ^* Ω = det (1 + i M) dx₁ ∧ ⋯ ∧ dxₙ` at `x` for the gradient graph `Γ`. -/
theorem standardComplexVolume_fderiv_gradientGraph_comp
    (hH : HasFDerivAt (∇ u) (toEuclideanCLM (𝕜 := ℝ) M) x) (v : Fin n → EuclideanSpace ℝ (Fin n)) :
    standardComplexVolume n (fderiv ℝ (gradientGraph u) x ∘ v) =
      det (1 + I • M.map ((↑) : ℝ → ℂ)) *
        ((EuclideanSpace.basisFun (Fin n) ℝ).toBasis.det v : ℂ) := by
  rw [(hasFDerivAt_gradientGraph hH).fderiv, standardComplexVolume_graphMap_comp]

/-- **The special Lagrangian equation for a gradient graph** (Harvey–Lawson, Theorem III.2.3). If
`u` is differentiable near `x` and `∇u` has derivative the Hessian matrix `M` at `x`, the tangent
plane of the gradient graph at `x`, oriented by `(x₁, …, xₙ)`, is calibrated by the special
Lagrangian form of phase `θ` exactly when `Im (e^{-iθ} det (1 + i M)) = 0` and
`Re (e^{-iθ} det (1 + i M)) > 0`. -/
theorem standardSpecialLagrangianForm_fderiv_gradientGraph_eq_norm_ιMulti_iff
    (hu : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ u y)
    (hH : HasFDerivAt (∇ u) (toEuclideanCLM (𝕜 := ℝ) M) x) (θ : ℝ) :
    standardSpecialLagrangianForm n θ
        (fderiv ℝ (gradientGraph u) x ∘ EuclideanSpace.basisFun (Fin n) ℝ) =
        ‖exteriorPower.ιMulti ℝ n
          (fderiv ℝ (gradientGraph u) x ∘ EuclideanSpace.basisFun (Fin n) ℝ)‖ ↔
      (exp (-(θ : ℂ) * I) * det (1 + I • M.map ((↑) : ℝ → ℂ))).im = 0 ∧
        0 < (exp (-(θ : ℂ) * I) * det (1 + I • M.map ((↑) : ℝ → ℂ))).re := by
  have hM : M.IsHermitian := by
    rw [← isSymmetric_toEuclideanLin_iff, ← coe_toEuclideanCLM_eq_toEuclideanLin]
    exact isSymmetric_of_hasFDerivAt_gradient hu hH
  rw [(hasFDerivAt_gradientGraph hH).fderiv,
    standardSpecialLagrangianForm_graphMap_eq_norm_ιMulti_iff, and_iff_right hM]

end GradientGraphVolume

end TauCeti
