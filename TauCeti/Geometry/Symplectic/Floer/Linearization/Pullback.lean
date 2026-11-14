/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Linearization
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Analysis.Calculus.FDeriv.Mul
import TauCeti.Geometry.Symplectic.AlmostComplex.Topology

/-!
# The Floer operator and its linearization under holomorphic changes of domain coordinates

The inhomogeneous Floer equation on a punctured Riemann surface, such as the pair of pants, is
written in a global coordinate on the surface and in the cylinder coordinates `(s, t)` on each
end, and the two are related by holomorphic changes of coordinates `φ`. This file computes how the
coordinate Floer operator `F(u) = ∂s u - X_Ks + J(u)(∂t u - X_Kt)` and its linearization `D_u` of
`TauCeti.Geometry.Symplectic.Floer.Linearization` change under such a `φ`: for the reparametrized
map `u ∘ φ`, the reparametrized direction `ξ ∘ φ`, the reparametrized structures `J ∘ φ` and the
pulled-back perturbation `φ^*K` (`TauCeti.Floer.perturbationPullback`).

Write `dφ_w (1, 0) = (a, b)`; since `dφ_w` is complex linear, `dφ_w (0, 1) = (-b, a)`. The
perturbed derivative `du - X_K` pulls back to `(du - X_K) ∘ dφ`
(`TauCeti.SymplecticForm.perturbedFDeriv_perturbationPullback`), and `J² = -1` gives:

* the Floer operator is multiplied by `a - b J`, which acts as the complex number `a - b i`:
  `F_{φ^*K}(u ∘ φ)(w) = (a - b J) F_K(u)(φ w)`
  (`TauCeti.SymplecticForm.floerOperator_perturbationPullback`);
* the linearized operator is multiplied by the same factor, up to a term in `F_K(u)`:
  `D_{u ∘ φ}(ξ ∘ φ)(w) = (a - b J) D_u ξ(φ w) - b (dJ(u) ξ) F_K(u)(φ w)`
  (`TauCeti.SymplecticForm.floerLinearization_perturbationPullback`). The correction comes from
  the target derivative `dJ` of `J`, which anticommutes with `J` because `J² = -1`
  (`TauCeti.mul_fderiv_add_fderiv_mul_eq_zero`). Along a solution of the Floer equation it
  vanishes
  (`TauCeti.SymplecticForm.floerLinearization_perturbationPullback_of_floerOperator_eq_zero`).

The factor `a - b J` scales the metric `g_J = ω(·, J ·)` by `a² + b²`
(`TauCeti.SymplecticForm.associatedBilinForm_smul_sub_smul_apply_self`), which is the Jacobian
determinant of `φ` at `w` (`TauCeti.IsComplexLinearMap.det_eq_sq_add_sq`). So along a solution
the integral of `g_J(D_u ξ, D_u ξ)` over a region is the same computed in either coordinate
system, for an injective holomorphic `φ`
(`TauCeti.SymplecticForm.integral_associatedBilinForm_floerLinearization_image`). In this form,
`L²` estimates of the linearized operator proved in the cylinder coordinates of an end apply to
the linearized operator in the coordinates of the surface.

The target is a symplectic vector space, as in `TauCeti.Geometry.Symplectic.Floer.Linearization`.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Sections 3.1 and 8.1,
  on the linearized operator and on Hamiltonian perturbations as one-forms on the domain.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends.
-/

public section

open Filter Function MeasureTheory Set
open scoped Topology

namespace TauCeti.SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {φ : ℝ × ℝ → ℝ × ℝ} {J : ℝ × ℝ → V → V →L[ℝ] V} {Ks Kt : ℝ × ℝ → V → ℝ}
  {u ξ : ℝ × ℝ → V} {w : ℝ × ℝ}

/-- **Naturality of the Floer operator.** Let `dφ_w` be complex linear, with
`dφ_w (1, 0) = (a, b)`, and let `J² = -1` at `u (φ w)`. Then the Floer operator of `u ∘ φ`, for the
structures `J ∘ φ` and the pulled-back datum `φ^*K`, is `(a - b J) F_K(u)(φ w)`. -/
theorem floerOperator_perturbationPullback (ω : SymplecticForm V) (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w)))
    (hJ : J (φ w) (u (φ w)) * J (φ w) (u (φ w)) = -1) :
    ω.floerOperator (fun w' ↦ J (φ w')) (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerOperator J Ks Kt u (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          J (φ w) (u (φ w)) (ω.floerOperator J Ks Kt u (φ w)) := by
  have hA (v : V) : J (φ w) (u (φ w)) (J (φ w) (u (φ w)) v) = -v := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v) hJ
  -- The perturbed derivative `P` of `u` on the columns `(a, b)` and `(-b, a)` of `dφ_w`.
  have hreal := (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine
    (fderiv ℝ φ w stdComplexLineReal)
  have himag := hφJ.apply_apply_stdComplexLineImag
    (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V)
  simp only [ContinuousLinearMap.coe_coe] at hreal himag
  rw [floerOperator_eq_perturbedFDeriv, ω.perturbedFDeriv_perturbationPullback hφ hu hKs hKt,
    floerOperator_eq_perturbedFDeriv]
  simp only [ContinuousLinearMap.comp_apply, comp_apply, hreal, himag, map_add, map_smul, hA]
  module

/-- **Naturality of the linearized Floer operator.** Let `dφ_w` be complex linear, with
`dφ_w (1, 0) = (a, b)`, let `J² = -1` near `u (φ w)` and let the Hamiltonians be `C²` at
`u (φ w)`. Then the linearization along `u ∘ φ` in the direction `ξ ∘ φ`, for the structures `J ∘ φ`
and the pulled-back datum `φ^*K`, is

`D_{u ∘ φ}(ξ ∘ φ)(w) = (a - b J) D_u ξ(φ w) - b (dJ(u) ξ) F_K(u)(φ w)`,

where `J` and its target derivative `dJ` are taken at `(φ w, u (φ w))` and `ξ` at `φ w`. -/
theorem floerLinearization_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (Ks (φ w)) (u (φ w))) (hKt : ContDiffAt ℝ 2 (Kt (φ w)) (u (φ w)))
    (hJ : ∀ᶠ y in 𝓝 (u (φ w)), J (φ w) y * J (φ w) y = -1) :
    ω.floerLinearization (fun w' ↦ J (φ w')) (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerLinearization J Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          J (φ w) (u (φ w)) (ω.floerLinearization J Ks Kt u ξ (φ w)) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) (ω.floerOperator J Ks Kt u (φ w)) := by
  have hA (v : V) : J (φ w) (u (φ w)) (J (φ w) (u (φ w)) v) = -v := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v) hJ.self_of_nhds
  -- The target derivative of `J` anticommutes with `J`.
  have hanti (v : V) : J (φ w) (u (φ w)) (fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) v) +
      fderiv ℝ (J (φ w)) (u (φ w)) (ξ (φ w)) (J (φ w) (u (φ w)) v) = 0 := by
    simpa using congrArg (fun L : V →L[ℝ] V ↦ L v)
      (mul_fderiv_add_fderiv_mul_eq_zero (𝕜 := ℝ) hJ (ξ (φ w)))
  -- The slice defect `∂t (u ∘ φ) - X_{(φ^*K)_t}` is the perturbed derivative of `u` on `(-b, a)`.
  have hP := congrArg (fun L : ℝ × ℝ →L[ℝ] V ↦ L stdComplexLineImag)
    (ω.perturbedFDeriv_perturbationPullback hφ hu (hKs.differentiableAt (by norm_num))
      (hKt.differentiableAt (by norm_num)))
  simp only [perturbedFDeriv_apply_stdComplexLineImag, ContinuousLinearMap.comp_apply,
    comp_apply] at hP
  have himag := hφJ.apply_apply_stdComplexLineImag
    (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V)
  -- The derivative of `ξ` on `(a, b)`, and the column `(-b, a)` of `dφ_w`.
  have hξ' := (fderiv ℝ ξ (φ w) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine
    (fderiv ℝ φ w stdComplexLineReal)
  have hφ' := hφJ.apply_apply_stdComplexLineImag (LinearMap.id : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ)
  simp only [ContinuousLinearMap.coe_coe, LinearMap.id_apply] at himag hξ' hφ'
  rw [himag] at hP
  -- Expand both linearizations and the Floer operator in these coordinates.
  rw [floerLinearization_def]
  simp only [comp_apply]
  rw [hP, fderiv_comp w hξ hφ, ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt,
    ω.fderiv_hamiltonianVectorField_perturbationPullback hKs hKt, floerLinearization_def,
    floerOperator_eq_perturbedFDeriv]
  simp only [ContinuousLinearMap.comp_apply, hξ', hφ', _root_.add_apply, _root_.smul_apply,
    perturbedFDeriv_apply_stdComplexLineImag, perturbedFDeriv_apply_stdComplexLineReal, map_add,
    map_sub, map_smul, hA, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul,
    stdComplexLineReal_fst, stdComplexLineReal_snd, stdComplexLineImag_fst,
    stdComplexLineImag_snd]
  -- What remains is `b (J dJ + dJ J)` applied to the slice defect `∂t u - X_{K_t}(u)`.
  linear_combination (norm := module)
    (fderiv ℝ φ w stdComplexLineReal).2 • hanti (fderiv ℝ u (φ w) stdComplexLineImag) -
      (fderiv ℝ φ w stdComplexLineReal).2 •
        hanti (ω.hamiltonianVectorField (Kt (φ w)) (u (φ w)))

/-- **Naturality of the linearized Floer operator along a solution.** Under the hypotheses of
`floerLinearization_perturbationPullback`, if `u` solves the Floer equation at `φ w`, then
`D_{u ∘ φ}(ξ ∘ φ)(w) = (a - b J) D_u ξ(φ w)` for `dφ_w (1, 0) = (a, b)`. -/
theorem floerLinearization_perturbationPullback_of_floerOperator_eq_zero (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w)
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : DifferentiableAt ℝ u (φ w)) (hξ : DifferentiableAt ℝ ξ (φ w))
    (hKs : ContDiffAt ℝ 2 (Ks (φ w)) (u (φ w))) (hKt : ContDiffAt ℝ 2 (Kt (φ w)) (u (φ w)))
    (hJ : ∀ᶠ y in 𝓝 (u (φ w)), J (φ w) y * J (φ w) y = -1)
    (hF : ω.floerOperator J Ks Kt u (φ w) = 0) :
    ω.floerLinearization (fun w' ↦ J (φ w')) (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w =
      (fderiv ℝ φ w stdComplexLineReal).1 • ω.floerLinearization J Ks Kt u ξ (φ w) -
        (fderiv ℝ φ w stdComplexLineReal).2 •
          J (φ w) (u (φ w)) (ω.floerLinearization J Ks Kt u ξ (φ w)) := by
  rw [ω.floerLinearization_perturbationPullback hφ hφJ hu hξ hKs hKt hJ, hF, map_zero, smul_zero,
    sub_zero]

/-- **Invariance of the `L²` norm of the linearized operator under holomorphic changes of
coordinates.** Let `J` be a family of almost complex structures, let `φ` be injective on a
measurable set `s`, with complex-linear derivative at every point of `s`, and let `u` solve the
Floer equation on `φ '' s`. Then the integral of `g_J(D_u ξ, D_u ξ)` over `φ '' s`, with
`g_J = ω(·, J ·)` at `(z, u z)`, is the integral over `s` of the same quantity for `u ∘ φ`, `ξ ∘ φ`,
the structures `J ∘ φ` and the pulled-back datum `φ^*K`. -/
theorem integral_associatedBilinForm_floerLinearization_image (ω : SymplecticForm V)
    {J : ℝ × ℝ → V → AlmostComplexStructure V} {s : Set (ℝ × ℝ)} (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hφJ : ∀ w ∈ s, IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w)) (hξ : ∀ w ∈ s, DifferentiableAt ℝ ξ (φ w))
    (hKs : ∀ w ∈ s, ContDiffAt ℝ 2 (Ks (φ w)) (u (φ w)))
    (hKt : ∀ w ∈ s, ContDiffAt ℝ 2 (Kt (φ w)) (u (φ w)))
    (hF : ∀ w ∈ s, ω.floerOperator (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u
      (φ w) = 0) :
    ∫ z in φ '' s, ω.associatedBilinForm (J z (u z))
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z)
        (ω.floerLinearization (fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) Ks Kt u ξ z) =
      ∫ w in s, ω.associatedBilinForm (J (φ w) (u (φ w)))
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w)
        (ω.floerLinearization (fun w' y ↦ (J (φ w') y).toLinearMap.toContinuousLinearMap)
          (perturbationPullback φ Ks Kt stdComplexLineReal)
          (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) (ξ ∘ φ) w) := by
  refine integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ ?_
  rw [ω.floerLinearization_perturbationPullback_of_floerOperator_eq_zero
    (J := fun z y ↦ (J z y).toLinearMap.toContinuousLinearMap) (hφ w hw) (hφJ w hw) (hu w hw)
    (hξ w hw) (hKs w hw) (hKt w hw)
    (Eventually.of_forall fun y ↦ AlmostComplexStructure.toContinuousLinearMap_mul_self _)
    (hF w hw)]
  -- `a - b J` scales `g_J` by `a² + b²`, the Jacobian determinant of `φ` at `w`.
  simp only [LinearMap.coe_toContinuousLinearMap', ω.associatedBilinForm_smul_sub_smul_apply_self,
    ContinuousLinearMap.det, (hφJ w hw).det_eq_sq_add_sq, ContinuousLinearMap.coe_coe, smul_eq_mul]
  rw [abs_of_nonneg (by positivity)]

end TauCeti.SymplecticForm
