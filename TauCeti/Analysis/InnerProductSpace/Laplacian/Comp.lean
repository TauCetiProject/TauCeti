/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic
import TauCeti.Analysis.Calculus.SecondDerivative

/-!
# The Laplacian of a composite with a nonlinear change of variables

For a map `φ : E → G` between real inner product spaces and a function `f : G → F`, both twice
differentiable at the relevant points, the second-order chain rule gives

`Δ (f ∘ φ) x = ∑ᵢ D²f (φ x) (Dφ bᵢ, Dφ bᵢ) + Df (φ x) (Δ φ x)`

for any orthonormal basis `b` of `E` (`ContDiffAt.laplacian_fun_comp`). Here `Δ φ` is Mathlib's
Laplacian of the vector-valued map `φ`. When `φ` is a linear equivalence the second term vanishes
and this is `TauCeti.laplacian_comp_continuousLinearEquiv_right_apply`.

When the derivative of `φ` at `x` is a scalar multiple `a • L` of a linear isometry equivalence
`L` (a conformal map), the vectors `L bᵢ` form an orthonormal basis of `G`, so the first term is
`a² Δ f (φ x)` (`ContDiffAt.laplacian_fun_comp_of_fderiv_eq_smul`). This is the computation
behind the transformation of the Laplacian under inversion in a sphere and the Kelvin transform.
-/

public section

namespace TauCeti

open Filter InnerProductSpace Laplacian Topology

variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **The chain rule for the Laplacian.** For maps `φ : E → G` and `f : G → F`, twice
differentiable at `x` and at `φ x` respectively, and an orthonormal basis `b` of `E`,
`Δ (f ∘ φ) x = ∑ᵢ D²f (φ x) (Dφ bᵢ, Dφ bᵢ) + Df (φ x) (Δ φ x)`. -/
theorem _root_.ContDiffAt.laplacian_fun_comp {f : G → F} {φ : E → G} {x : E}
    (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x) {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ E) :
    Δ (fun y ↦ f (φ y)) x =
      ∑ i, iteratedFDeriv ℝ 2 f (φ x) ![fderiv ℝ φ x (b i), fderiv ℝ φ x (b i)] +
        fderiv ℝ f (φ x) (Δ φ x) := by
  -- Each diagonal Hessian entry of the composite, by the second-order chain rule.
  have hterm : ∀ v, iteratedFDeriv ℝ 2 (fun y ↦ f (φ y)) x ![v, v] =
      iteratedFDeriv ℝ 2 f (φ x) ![fderiv ℝ φ x v, fderiv ℝ φ x v] +
        fderiv ℝ f (φ x) (iteratedFDeriv ℝ 2 φ x ![v, v]) := fun v ↦ by
    rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simpa [Function.comp_def] using fderiv_fderiv_comp_apply hf hφ v v
  rw [congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis _ b) x,
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis φ b) x, map_sum]
  simp_rw [hterm, Finset.sum_add_distrib]

/-- **The Laplacian after a conformal change of variables.** If `φ : E → G` and `f : G → F` are
twice differentiable at `x` and at `φ x`, and the derivative of `φ` at `x` is `a • L` for a linear
isometry equivalence `L : E ≃ₗᵢ[ℝ] G`, then `Δ (f ∘ φ) x = a² Δ f (φ x) + Df (φ x) (Δ φ x)`. -/
theorem _root_.ContDiffAt.laplacian_fun_comp_of_fderiv_eq_smul
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    {f : G → F} {φ : E → G} {x : E} (hf : ContDiffAt ℝ 2 f (φ x)) (hφ : ContDiffAt ℝ 2 φ x)
    {a : ℝ} {L : E ≃ₗᵢ[ℝ] G} (hφ' : fderiv ℝ φ x = a • (L : E →L[ℝ] G)) :
    Δ (fun y ↦ f (φ y)) x = a ^ 2 • Δ f (φ x) + fderiv ℝ f (φ x) (Δ φ x) := by
  set b := stdOrthonormalBasis ℝ E
  rw [hf.laplacian_fun_comp hφ b, hφ',
    congrFun (laplacian_eq_iteratedFDeriv_orthonormalBasis f (b.map L)) (φ x), Finset.smul_sum]
  congr 1
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  simp only [smul_apply, OrthonormalBasis.map_apply, LinearIsometryEquiv.coe_coe'',
    iteratedFDeriv_two_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Fin.isValue, map_smul,
    smul_smul, sq]

end TauCeti
