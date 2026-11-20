/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Laplacian.Basic

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
  have hφd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ φ y :=
    (hφ.eventually (by simp)).mono fun y hy ↦ hy.differentiableAt (by simp)
  have hfd : ∀ᶠ y in 𝓝 x, DifferentiableAt ℝ f (φ y) :=
    hφ.continuousAt.eventually <|
      (hf.eventually (by simp)).mono fun z hz ↦ hz.differentiableAt (by simp)
  have hD : fderiv ℝ (fun y ↦ f (φ y)) =ᶠ[𝓝 x]
      fun y ↦ (fderiv ℝ f (φ y)).comp (fderiv ℝ φ y) := by
    filter_upwards [hφd, hfd] with y hφy hfy
    exact fderiv_comp y hfy hφy
  have hf₂ : DifferentiableAt ℝ (fderiv ℝ f) (φ x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφ₂ : DifferentiableAt ℝ (fderiv ℝ φ) x :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : HasFDerivAt (fun y ↦ fderiv ℝ f (φ y))
      ((fderiv ℝ (fderiv ℝ f) (φ x)).comp (fderiv ℝ φ x)) x :=
    hf₂.hasFDerivAt.comp x hφd.self_of_nhds.hasFDerivAt
  -- Each diagonal Hessian entry of the composite, by differentiating the chain rule once more.
  have hterm : ∀ v, iteratedFDeriv ℝ 2 (fun y ↦ f (φ y)) x ![v, v] =
      iteratedFDeriv ℝ 2 f (φ x) ![fderiv ℝ φ x v, fderiv ℝ φ x v] +
        fderiv ℝ f (φ x) (iteratedFDeriv ℝ 2 φ x ![v, v]) := by
    intro v
    rw [iteratedFDeriv_two_apply, hD.fderiv_eq, fderiv_clm_comp hc.differentiableAt hφ₂,
      hc.fderiv, iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
    simp only [Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
      add_apply, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply]
    abel
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
