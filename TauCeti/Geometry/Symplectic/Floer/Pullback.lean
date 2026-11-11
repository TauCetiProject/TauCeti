/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import TauCeti.Analysis.Complex.RealChart
public import TauCeti.MeasureTheory.Function.Jacobian.Plane
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import TauCeti.LinearAlgebra.Complex.Module

/-!
# Pulling back Hamiltonian perturbation data along changes of domain coordinates

A Riemann surface with cylindrical ends, such as the pair of pants, carries no single global
coordinate: its perturbation datum `K = K_s ds + K_t dt` and the inhomogeneous Floer equation are
written in an affine chart on the compact part and in the cylinder coordinates `(s, t)` on each
end. This file records how the coordinate objects of `TauCeti.Geometry.Symplectic.Floer.Energy`
change under a change of domain coordinates `φ : ℝ × ℝ → ℝ × ℝ`.

The pullback `φ^*K` of the Hamiltonian-valued one-form `K` evaluates `K` at `φ w` on the pushed
tangent vector `dφ_w v`, so its components are
`(φ^*K)_s = (∂_s φ)₁ K_s ∘ φ + (∂_s φ)₂ K_t ∘ φ` and
`(φ^*K)_t = (∂_t φ)₁ K_s ∘ φ + (∂_t φ)₂ K_t ∘ φ` (`TauCeti.Floer.perturbationPullback`).
Then, for the reparametrized map `u ∘ φ`:

* the perturbed derivative `d(u ∘ φ) - X_{φ^*K}` is `(du - X_K) ∘ dφ`;
* the Floer energy density is multiplied by the Jacobian determinant `det dφ`;
* the curvature `R_{φ^*K}` is `det dφ` times `R_K ∘ φ`, so that `R_K ds ∧ dt` is a well-defined
  Hamiltonian-valued two-form; the second derivatives of `φ` cancel by the symmetry of `d²φ`;
* when `dφ` is complex linear (a holomorphic change of coordinates, such as the exponential
  cylinder coordinates on the ends of a punctured sphere), solutions of the Floer equation
  `(du - X_K)^{0,1} = 0` pull back to solutions.

With the change of variables formula, the energy and the integrated curvature over a region
are the same computed in either coordinate system, for an injective orientation-preserving `φ`.
These are the identities that let the rectangle energy identity
`TauCeti.SymplecticForm.integral_floerEnergyDensity` be applied chart by chart on a punctured
domain.

## Main definitions

* `TauCeti.Floer.perturbationPullback`: the pullback `φ^*K` of a perturbation datum, evaluated on
  a tangent vector.

## Main results

* `TauCeti.Floer.perturbationPullback_comp`: pullback is compatible with composition of
  coordinate changes.
* `TauCeti.Floer.fderiv_perturbationPullback_sub_fderiv_perturbationPullback`: the domain-derivative
  part `∂_s K_t - ∂_t K_s` of the curvature scales by `det dφ`, for any target.
* `TauCeti.Floer.perturbationPullback_realChart`: the pullback of a datum on `ℂ` along a
  holomorphic map `f` evaluates the datum at `f w` on `f'(w) v`.
* `TauCeti.Floer.differentiableAt_domain_of_differentiableAt`,
  `TauCeti.Floer.differentiableAt_target_of_differentiableAt`: a datum on `ℂ` that is
  differentiable jointly in the domain and target points is differentiable in each of them, in
  real coordinates.
* `TauCeti.SymplecticForm.perturbedFDeriv_perturbationPullback`: the perturbed derivative of the
  reparametrized map is the original one precomposed with `dφ`.
* `TauCeti.SymplecticForm.floerEnergyDensity_perturbationPullback`: the energy density scales by
  `det dφ`.
* `TauCeti.SymplecticForm.hamiltonianCurvature_perturbationPullback`: the curvature scales by
  `det dφ`.
* `TauCeti.SymplecticForm.isComplexLinearMap_perturbedFDeriv_perturbationPullback`: holomorphic
  changes of coordinates preserve the Floer equation.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_image`,
  `TauCeti.SymplecticForm.integral_hamiltonianCurvature_image` and
  `TauCeti.SymplecticForm.integral_abs_hamiltonianCurvature_image`: the integrated energy and
  curvature are invariant under injective orientation-preserving changes of coordinates, and the
  integrated absolute curvature under all injective ones.
* `TauCeti.SymplecticForm.lintegral_enorm_hamiltonianCurvature_image`: the same invariance of the
  integrated absolute curvature as a lower Lebesgue integral, along arbitrary maps.
* `TauCeti.SymplecticForm.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico`: the energy
  identity over the image of a rectangle `[α, β] × [-1/2, 1/2)` under a holomorphic map in whose
  coordinates the datum is `g(s) G(t) dt`, such as a band of a cylindrical end.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations as one-forms on the domain, their curvature two-form and the
  energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends.
-/

public section

open Function MeasureTheory Set
open TauCeti.Complex (realChart realChart_apply fderiv_realChart_apply)

namespace TauCeti

namespace Floer

variable {X : Type*}

/-- The pullback `φ^*K` of the perturbation one-form `K = K_s ds + K_t dt` along a change of
domain coordinates `φ`, evaluated on the tangent vector `v` at `w` and the target point `x`: it is
`K` at `φ w` evaluated on `dφ_w v`. Its `ds` and `dt` components are
`perturbationPullback φ Ks Kt stdComplexLineReal` and
`perturbationPullback φ Ks Kt stdComplexLineImag`. -/
noncomputable def perturbationPullback (φ : ℝ × ℝ → ℝ × ℝ) (Ks Kt : ℝ × ℝ → X → ℝ)
    (v w : ℝ × ℝ) (x : X) : ℝ :=
  (fderiv ℝ φ w v).1 * Ks (φ w) x + (fderiv ℝ φ w v).2 * Kt (φ w) x

theorem perturbationPullback_apply (φ : ℝ × ℝ → ℝ × ℝ) (Ks Kt : ℝ × ℝ → X → ℝ)
    (v w : ℝ × ℝ) (x : X) :
    perturbationPullback φ Ks Kt v w x =
      (fderiv ℝ φ w v).1 * Ks (φ w) x + (fderiv ℝ φ w v).2 * Kt (φ w) x :=
  (rfl)

/-- The `ds` component of the pullback along the identity is `K_s`. -/
@[simp]
theorem perturbationPullback_id_stdComplexLineReal (Ks Kt : ℝ × ℝ → X → ℝ) :
    perturbationPullback id Ks Kt stdComplexLineReal = Ks := by
  funext w x
  simp [perturbationPullback_apply]

/-- The `dt` component of the pullback along the identity is `K_t`. -/
@[simp]
theorem perturbationPullback_id_stdComplexLineImag (Ks Kt : ℝ × ℝ → X → ℝ) :
    perturbationPullback id Ks Kt stdComplexLineImag = Kt := by
  funext w x
  simp [perturbationPullback_apply]

/-- Pulling back along a composite `φ ∘ ψ` is pulling back along `φ` and then along `ψ`, at points
where both changes of coordinates are differentiable. -/
theorem perturbationPullback_comp {φ ψ : ℝ × ℝ → ℝ × ℝ} (Ks Kt : ℝ × ℝ → X → ℝ) {w : ℝ × ℝ}
    (hφ : DifferentiableAt ℝ φ (ψ w)) (hψ : DifferentiableAt ℝ ψ w) (v : ℝ × ℝ) :
    perturbationPullback (φ ∘ ψ) Ks Kt v w =
      perturbationPullback ψ (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) v w := by
  funext x
  have h := (fderiv ℝ φ (ψ w) : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ).apply_stdComplexLine (fderiv ℝ ψ w v)
  simp only [ContinuousLinearMap.coe_coe] at h
  simp only [perturbationPullback_apply, fderiv_comp w hφ hψ, ContinuousLinearMap.comp_apply,
    comp_apply, h, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
  ring

/-- The domain derivative of a component of the pullback `φ^*K`, by the product and chain rules:
the second derivative of `φ` falls on the coefficient and the first derivative of `φ` on `K`. -/
theorem fderiv_perturbationPullback_apply {φ : ℝ × ℝ → ℝ × ℝ} {Ks Kt : ℝ × ℝ → X → ℝ}
    {w : ℝ × ℝ} {x : X} (hφ : DifferentiableAt ℝ (fderiv ℝ φ) w)
    (hφ' : DifferentiableAt ℝ φ w) (hKs : DifferentiableAt ℝ (fun z ↦ Ks z x) (φ w))
    (hKt : DifferentiableAt ℝ (fun z ↦ Kt z x) (φ w)) (v e : ℝ × ℝ) :
    fderiv ℝ (fun w' ↦ perturbationPullback φ Ks Kt v w' x) w e =
      (fderiv ℝ (fderiv ℝ φ) w e v).1 * Ks (φ w) x +
        (fderiv ℝ φ w v).1 * fderiv ℝ (fun z ↦ Ks z x) (φ w) (fderiv ℝ φ w e) +
      ((fderiv ℝ (fderiv ℝ φ) w e v).2 * Kt (φ w) x +
        (fderiv ℝ φ w v).2 * fderiv ℝ (fun z ↦ Kt z x) (φ w) (fderiv ℝ φ w e)) := by
  have hA : HasFDerivAt (fun w' ↦ fderiv ℝ φ w' v)
      ((ContinuousLinearMap.apply ℝ (ℝ × ℝ) v).comp (fderiv ℝ (fderiv ℝ φ) w)) w :=
    (ContinuousLinearMap.apply ℝ (ℝ × ℝ) v).hasFDerivAt.comp w hφ.hasFDerivAt
  have hS : HasFDerivAt (fun w' ↦ Ks (φ w') x)
      ((fderiv ℝ (fun z ↦ Ks z x) (φ w)).comp (fderiv ℝ φ w)) w :=
    hKs.hasFDerivAt.comp w hφ'.hasFDerivAt
  have hT : HasFDerivAt (fun w' ↦ Kt (φ w') x)
      ((fderiv ℝ (fun z ↦ Kt z x) (φ w)).comp (fderiv ℝ φ w)) w :=
    hKt.hasFDerivAt.comp w hφ'.hasFDerivAt
  have h := (hA.fst.fun_mul hS).fun_add (hA.snd.fun_mul hT)
  simp only [perturbationPullback_apply]
  rw [h.fderiv]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply, smul_eq_mul,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd']
  ring

/-- **The domain part of the curvature is a two-form.** For a `C²` change of coordinates `φ`, the
exterior derivative `∂_s (φ^*K)_t - ∂_t (φ^*K)_s` of the pulled-back datum at a fixed target point
is the Jacobian determinant of `φ` times `∂_s K_t - ∂_t K_s` at `φ w`. The terms involving second
derivatives of `φ` cancel by the symmetry of `d²φ`. No structure on the target is involved. -/
theorem fderiv_perturbationPullback_sub_fderiv_perturbationPullback {φ : ℝ × ℝ → ℝ × ℝ}
    {Ks Kt : ℝ × ℝ → X → ℝ} {w : ℝ × ℝ} {x : X} (hφ : ContDiffAt ℝ 2 φ w)
    (hKs : DifferentiableAt ℝ (fun z ↦ Ks z x) (φ w))
    (hKt : DifferentiableAt ℝ (fun z ↦ Kt z x) (φ w)) :
    fderiv ℝ (fun w' ↦ perturbationPullback φ Ks Kt stdComplexLineImag w' x) w
        stdComplexLineReal -
      fderiv ℝ (fun w' ↦ perturbationPullback φ Ks Kt stdComplexLineReal w' x) w
        stdComplexLineImag =
      (fderiv ℝ φ w).det * (fderiv ℝ (fun z ↦ Kt z x) (φ w) stdComplexLineReal -
        fderiv ℝ (fun z ↦ Ks z x) (φ w) stdComplexLineImag) := by
  have hφ₁ : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have hφ₂ : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm : fderiv ℝ (fderiv ℝ φ) w stdComplexLineReal stdComplexLineImag =
      fderiv ℝ (fderiv ℝ φ) w stdComplexLineImag stdComplexLineReal :=
    hφ.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  -- Expand the derivatives of `K_s` and `K_t` on the columns of `dφ_w`.
  have hκ (κ : ℝ × ℝ →L[ℝ] ℝ) (e : ℝ × ℝ) : κ (fderiv ℝ φ w e) =
      (fderiv ℝ φ w e).1 * κ stdComplexLineReal + (fderiv ℝ φ w e).2 * κ stdComplexLineImag := by
    simpa using (κ : ℝ × ℝ →ₗ[ℝ] ℝ).apply_stdComplexLine (fderiv ℝ φ w e)
  simp only [fderiv_perturbationPullback_apply hφ₂ hφ₁ hKs hKt, hsymm, hκ]
  simp only [ContinuousLinearMap.det, LinearMap.det_finTwoProd, ContinuousLinearMap.coe_coe,
    stdComplexLineReal_eq, stdComplexLineImag_eq]
  ring

/-! ### Holomorphic changes of coordinates -/

/-- The pullback along a holomorphic map `f` of a datum `P` on `ℂ`, written in the real
coordinates through its values on `1` and `i`, evaluates `P` at the image point `f w` on the image
`f'(w) v` of the tangent vector. -/
theorem perturbationPullback_realChart (P : ℂ → X → ℂ →L[ℝ] ℝ) {f : ℂ → ℂ} {f' : ℂ}
    {w : ℝ × ℝ} (hf : HasDerivAt f f' (Complex.equivRealProdCLM.symm w)) (v : ℝ × ℝ) (x : X) :
    perturbationPullback (realChart f) (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) v w x =
      P (f (Complex.equivRealProdCLM.symm w)) x (f' * Complex.equivRealProdCLM.symm v) := by
  rw [perturbationPullback_apply, fderiv_realChart_apply hf, realChart_apply,
    ContinuousLinearEquiv.symm_apply_apply, Complex.equivRealProdCLM_apply]
  exact ((P _ x : ℂ →ₗ[ℝ] ℝ).apply_eq_re_smul_one_add_im_smul_I _).symm

section Differentiable

variable [NormedAddCommGroup X] [NormedSpace ℝ X] {P : ℂ → X → ℂ →L[ℝ] ℝ} {w : ℝ × ℝ} {x : X}

/-- If a datum `P` on `ℂ` is differentiable jointly in the domain and target points, then, in the
real coordinates, its value on a fixed tangent vector is differentiable in the domain point. -/
theorem differentiableAt_domain_of_differentiableAt
    (hP : DifferentiableAt ℝ (fun p : ℂ × X ↦ P p.1 p.2) (Complex.equivRealProdCLM.symm w, x))
    (v : ℂ) : DifferentiableAt ℝ (fun z ↦ P (Complex.equivRealProdCLM.symm z) x v) w :=
  (hP.comp (f := fun z ↦ (Complex.equivRealProdCLM.symm z, x)) w
    (Complex.equivRealProdCLM.symm.differentiableAt.prodMk (differentiableAt_const x))).clm_apply
    (differentiableAt_const v)

/-- If a datum `P` on `ℂ` is differentiable jointly in the domain and target points, then, in the
real coordinates, its value on a fixed tangent vector is differentiable in the target point. -/
theorem differentiableAt_target_of_differentiableAt
    (hP : DifferentiableAt ℝ (fun p : ℂ × X ↦ P p.1 p.2) (Complex.equivRealProdCLM.symm w, x))
    (v : ℂ) : DifferentiableAt ℝ (fun y ↦ P (Complex.equivRealProdCLM.symm w) y v) x :=
  (hP.comp (f := fun y ↦ (Complex.equivRealProdCLM.symm w, y)) x
    ((differentiableAt_const _).prodMk differentiableAt_id)).clm_apply (differentiableAt_const v)

end Differentiable

end Floer

namespace SymplecticForm

open Floer

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
variable {φ : ℝ × ℝ → ℝ × ℝ} {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {w : ℝ × ℝ} {x : V}

section Pointwise

/-- The Hamiltonian vector field of a component of the pullback `φ^*K` is the corresponding
combination of the Hamiltonian vector fields of `K_s` and `K_t` at `φ w`. -/
theorem hamiltonianVectorField_perturbationPullback (ω : SymplecticForm V)
    (hKs : DifferentiableAt ℝ (Ks (φ w)) x) (hKt : DifferentiableAt ℝ (Kt (φ w)) x)
    (v : ℝ × ℝ) :
    ω.hamiltonianVectorField (perturbationPullback φ Ks Kt v w) x =
      (fderiv ℝ φ w v).1 • ω.hamiltonianVectorField (Ks (φ w)) x +
        (fderiv ℝ φ w v).2 • ω.hamiltonianVectorField (Kt (φ w)) x := by
  have h : perturbationPullback φ Ks Kt v w = fun y ↦
      (fderiv ℝ φ w v).1 * Ks (φ w) y + (fderiv ℝ φ w v).2 * Kt (φ w) y :=
    funext (perturbationPullback_apply φ Ks Kt v w)
  rw [h]
  exact ω.hamiltonianVectorField_const_mul_add_const_mul hKs hKt _ _

/-- **Naturality of the perturbed derivative.** The perturbed derivative of the reparametrized
map `u ∘ φ` for the pulled-back datum `φ^*K` is `(du - X_K) ∘ dφ`. -/
theorem perturbedFDeriv_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w) (hu : DifferentiableAt ℝ u (φ w))
    (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.perturbedFDeriv (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (ω.perturbedFDeriv Ks Kt u (φ w)).comp (fderiv ℝ φ w) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv := (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ).apply_stdComplexLine v
  simp only [ContinuousLinearMap.coe_coe] at hv
  -- Unfold both perturbed derivatives, apply the chain rule and expand `X_{φ^*K}`.
  simp only [ContinuousLinearMap.comp_apply, perturbedFDeriv_apply, fderiv_comp w hu hφ,
    comp_apply, ω.hamiltonianVectorField_perturbationPullback hKs hKt]
  -- Expand `dφ_w v` in the coordinate directions and normalize.
  simp only [hv, Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, add_smul,
    smul_add, mul_smul]
  abel

/-- **The energy density is a two-form.** The Floer energy density of `u ∘ φ` for the
pulled-back datum `φ^*K` is the Jacobian determinant of `φ` times the energy density of `u` for
`K` at `φ w`. -/
theorem floerEnergyDensity_perturbationPullback (ω : SymplecticForm V)
    (hφ : DifferentiableAt ℝ φ w) (hu : DifferentiableAt ℝ u (φ w))
    (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ω.floerEnergyDensity (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w).det * ω.floerEnergyDensity Ks Kt u (φ w) := by
  -- Expand the perturbed derivative of `u` on the columns of `dφ_w`.
  have hP (e : ℝ × ℝ) : ω.perturbedFDeriv Ks Kt u (φ w) (fderiv ℝ φ w e) =
      (fderiv ℝ φ w e).1 • ω.perturbedFDeriv Ks Kt u (φ w) stdComplexLineReal +
        (fderiv ℝ φ w e).2 • ω.perturbedFDeriv Ks Kt u (φ w) stdComplexLineImag := by
    simpa using
      (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V).apply_stdComplexLine (fderiv ℝ φ w e)
  rw [floerEnergyDensity_def, floerEnergyDensity_def,
    ω.perturbedFDeriv_perturbationPullback hφ hu hKs hKt]
  simp only [ContinuousLinearMap.comp_apply, hP]
  exact ω.apply_smul_add_smul_det (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) _ _

/-- **The curvature is a two-form.** For a `C²` change of coordinates `φ`, the curvature of the
pulled-back datum `φ^*K` is the Jacobian determinant of `φ` times the curvature of `K` at `φ w`.
The terms involving second derivatives of `φ` cancel by the symmetry of `d²φ`. -/
theorem hamiltonianCurvature_perturbationPullback (ω : SymplecticForm V)
    (hφ : ContDiffAt ℝ 2 φ w) (hKs : DifferentiableAt ℝ (fun z ↦ Ks z x) (φ w))
    (hKt : DifferentiableAt ℝ (fun z ↦ Kt z x) (φ w)) :
    ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w x =
      (fderiv ℝ φ w).det * ω.hamiltonianCurvature Ks Kt (φ w) x := by
  -- The Poisson bracket term scales by `det dφ`.
  have hbracket : ω.poissonBracket (perturbationPullback φ Ks Kt stdComplexLineReal w)
      (perturbationPullback φ Ks Kt stdComplexLineImag w) x =
        (fderiv ℝ φ w).det * ω.poissonBracket (Ks (φ w)) (Kt (φ w)) x := by
    have h (v : ℝ × ℝ) : perturbationPullback φ Ks Kt v w = fun y ↦
        (fderiv ℝ φ w v).1 * Ks (φ w) y + (fderiv ℝ φ w v).2 * Kt (φ w) y :=
      funext (perturbationPullback_apply φ Ks Kt v w)
    rw [h, h, ω.poissonBracket_comb]
    simp [ContinuousLinearMap.det, LinearMap.det_finTwoProd, stdComplexLineReal_eq,
      stdComplexLineImag_eq]
  have hderiv := fderiv_perturbationPullback_sub_fderiv_perturbationPullback hφ hKs hKt
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def]
  linear_combination hderiv - hbracket

/-- **Holomorphic changes of coordinates preserve the Floer equation.** If `dφ` is complex linear
at `w` and `u` solves `(du - X_K)^{0,1} = 0` at `φ w`, then `u ∘ φ` solves the Floer equation
for the pulled-back datum `φ^*K` at `w`. -/
theorem isComplexLinearMap_perturbedFDeriv_perturbationPullback (ω : SymplecticForm V)
    {J : AlmostComplexStructure V} (hφ : DifferentiableAt ℝ φ w)
    (hu : DifferentiableAt ℝ u (φ w)) (hKs : DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : DifferentiableAt ℝ (Kt (φ w)) (u (φ w)))
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv Ks Kt u (φ w) : ℝ × ℝ →ₗ[ℝ] V)) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedFDeriv (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w : ℝ × ℝ →ₗ[ℝ] V) := by
  rw [ω.perturbedFDeriv_perturbationPullback hφ hu hKs hKt, ContinuousLinearMap.toLinearMap_comp]
  exact h.comp hφJ

end Pointwise

section Integral

variable {s : Set (ℝ × ℝ)}

/-- **Invariance of the energy under changes of coordinates.** For a change of coordinates `φ`
that is injective and orientation preserving on a measurable set `s`, the energy of `u` for `K`
over `φ '' s` is the energy of `u ∘ φ` for `φ^*K` over `s`. -/
theorem integral_floerEnergyDensity_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det) (hu : ∀ w ∈ s, DifferentiableAt ℝ u (φ w))
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ∫ z in φ '' s, ω.floerEnergyDensity Ks Kt u z =
      ∫ w in s, ω.floerEnergyDensity (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ by
    rw [abs_of_nonneg (hdet w hw), smul_eq_mul,
      ω.floerEnergyDensity_perturbationPullback (hφ w hw) (hu w hw) (hKs w hw) (hKt w hw)]

/-- **Invariance of the integrated curvature under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective and orientation preserving on a measurable set `s`, the integral
of the curvature `R_K(u)` over `φ '' s` is the integral of `R_{φ^*K}(u ∘ φ)` over `s`. -/
theorem integral_hamiltonianCurvature_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w)) :
    ∫ z in φ '' s, ω.hamiltonianCurvature Ks Kt z (u z) =
      ∫ w in s, ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w)) :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj
    (fun w hw ↦ (hφ w hw).differentiableAt (by norm_num)) fun w hw ↦ by
      rw [abs_of_nonneg (hdet w hw), smul_eq_mul, ω.hamiltonianCurvature_perturbationPullback
        (hφ w hw) (hKs w hw) (hKt w hw)]

/-- **Invariance of the curvature allowance under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective on a measurable set `s`, the integral of `|R_K(u)|` over
`φ '' s` is the integral of `|R_{φ^*K}(u ∘ φ)|` over `s`. No orientation hypothesis is needed,
since both sides are absolute values. Curvature bounds used in energy estimates may therefore be
computed in any chart. -/
theorem integral_abs_hamiltonianCurvature_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w)) :
    ∫ z in φ '' s, |ω.hamiltonianCurvature Ks Kt z (u z)| =
      ∫ w in s, |ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w))| :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj
    (fun w hw ↦ (hφ w hw).differentiableAt (by norm_num)) fun w hw ↦ by
      rw [ω.hamiltonianCurvature_perturbationPullback (hφ w hw) (hKs w hw) (hKt w hw), abs_mul,
        smul_eq_mul]

/-- **Invariance of the curvature allowance as a lower integral.** For a `C²` change of
coordinates `φ` that is injective on a measurable set `s`, the lower Lebesgue integral of
`|R_K(u)|` over `φ '' s` is that of `|R_{φ^*K}(u ∘ φ)|` over `s`. Unlike
`TauCeti.SymplecticForm.integral_abs_hamiltonianCurvature_image`, no integrability or
measurability of the integrands is needed, so curvature allowances along arbitrary maps `u` may
be computed in any chart. -/
theorem lintegral_enorm_hamiltonianCurvature_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w)) :
    ∫⁻ z in φ '' s, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ =
      ∫⁻ w in s, ‖ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w))‖ₑ :=
  lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul hs hinj
    (fun w hw ↦ (hφ w hw).differentiableAt (by norm_num)) fun w hw ↦
      ω.hamiltonianCurvature_perturbationPullback (hφ w hw) (hKs w hw) (hKt w hw)

end Integral

section RealChart

/-! ### Rectangles of an end in the coordinates of a holomorphic end lift -/

variable {f : ℂ → ℂ} {P : ℂ → V → ℂ →L[ℝ] ℝ} {Ω : Set (ℝ × ℝ)}

omit [FiniteDimensional ℝ V] in
/-- The pullback along the real chart of a `C²` holomorphic map `f` of a datum `P` that is `C¹` on
`Ω`, evaluated on a fixed tangent vector `v`, is `C¹` on the preimage of `Ω`. -/
private theorem contDiffOn_uncurry_comp_realChart (hf : ContDiff ℂ 2 f)
    (hP : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ P (Complex.equivRealProdCLM.symm p.1) p.2)
      (Ω ×ˢ univ)) (v : ℂ) :
    ContDiffOn ℝ 1 (uncurry fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
      (deriv f (Complex.equivRealProdCLM.symm w) * v)) ((realChart f ⁻¹' Ω) ×ˢ univ) := by
  have hφ : ContDiff ℝ 1 (realChart f) := TauCeti.Complex.contDiff_realChart (hf.of_le one_le_two)
  have h₁ : ContDiffOn ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ P (Complex.equivRealProdCLM.symm (realChart f p.1)) p.2)
      ((realChart f ⁻¹' Ω) ×ˢ univ) :=
    hP.comp ((hφ.comp contDiff_fst).prodMk contDiff_snd).contDiffOn
      fun p hp ↦ ⟨hp.1, mem_univ _⟩
  have h₂ : ContDiff ℝ 1
      (fun p : (ℝ × ℝ) × V ↦ deriv f (Complex.equivRealProdCLM.symm p.1) * v) :=
    ((((contDiff_succ_iff_deriv.1 hf).2.2).restrict_scalars ℝ).comp
      (Complex.equivRealProdCLM.symm.contDiff.comp contDiff_fst)).mul contDiff_const
  refine (h₁.clm_apply h₂.contDiffOn).congr fun ⟨w, x⟩ _ ↦ ?_
  simp only [uncurry_apply_pair, realChart_apply, ContinuousLinearEquiv.symm_apply_apply]

/-- The energy identity of
`TauCeti.SymplecticForm.integral_floerEnergyDensity_image_realChart_Icc_prod_Ico` in the coordinates
of `f`: for the pulled-back datum, which is `g(s) G(t) dt` on the closed rectangle
`[α, β] × [-1/2, 1/2]`. -/
private theorem integral_floerEnergyDensity_comp_realChart_Icc_prod_Ico (ω : SymplecticForm V)
    (hf : ContDiff ℂ 2 f) {α β : ℝ} (hαβ : α ≤ β) (hΩ : IsOpen Ω)
    (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc (-1 / 2 : ℝ) (1 / 2), realChart f z ∈ Ω)
    (hP : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ P (Complex.equivRealProdCLM.symm p.1) p.2)
      (Ω ×ˢ univ))
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u Ω) {g : ℝ → ℝ} {G : ℝ → V → ℝ}
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc (-1 / 2 : ℝ) (1 / 2), ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    ∫ w in Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2), ω.floerEnergyDensity
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * 1))
        (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) (u ∘ realChart f) w =
      (∫ w in Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2),
          ω (fderiv ℝ (u ∘ realChart f) w stdComplexLineReal)
            (fderiv ℝ (u ∘ realChart f) w stdComplexLineImag)) +
        (g β * (∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (β, t)))) -
          g α * ∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (α, t)))) -
        ∫ w in Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2), ω.hamiltonianCurvature
          (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
            (deriv f (Complex.equivRealProdCLM.symm w) * 1))
          (fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
            (deriv f (Complex.equivRealProdCLM.symm w) * Complex.I)) w (u (realChart f w)) := by
  have hφ : ContDiff ℝ 1 (realChart f) := TauCeti.Complex.contDiff_realChart (hf.of_le one_le_two)
  -- The half-open strip and the closed rectangle differ by a null set.
  have hae : Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2) =ᵐ[volume]
      Icc ((α, -1 / 2) : ℝ × ℝ) (β, 1 / 2) := by
    rw [Icc_prod_eq, Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq (ae_eq_refl _) Ico_ae_eq_Icc
  simp only [setIntegral_congr_set hae]
  have hIccU : Icc ((α, -1 / 2) : ℝ × ℝ) (β, 1 / 2) ⊆ realChart f ⁻¹' Ω := fun z hz ↦ hfΩ z (by
    rw [Icc_prod_eq] at hz
    exact hz)
  rw [ω.integral_floerEnergyDensity (hΩ.preimage hφ.continuous)
    (hu.comp hφ.contDiffOn fun _ hw ↦ hw) (contDiffOn_uncurry_comp_realChart hf hP 1)
    (contDiffOn_uncurry_comp_realChart hf hP Complex.I) (Prod.mk_le_mk.2 ⟨hαβ, by norm_num⟩)
    hIccU]
  -- The `ds` components vanish and the `dt` components are `g(s) G(t)` on the rectangle.
  have hs₀ {t₀ : ℝ} (ht₀ : t₀ ∈ Icc (-1 / 2 : ℝ) (1 / 2)) :
      ∫ s in α..β, P (f (Complex.equivRealProdCLM.symm (s, t₀))) ((u ∘ realChart f) (s, t₀))
        (deriv f (Complex.equivRealProdCLM.symm (s, t₀)) * 1) = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ ↦ 0) fun s hs ↦ ?_,
      intervalIntegral.integral_zero]
    rw [uIcc_of_le hαβ] at hs
    rw [hPf (s, t₀) ⟨hs, ht₀⟩, Complex.one_im, zero_mul]
  have ht {s₀ : ℝ} (hs₀ : s₀ ∈ Icc α β) :
      ∫ t in (-1 / 2 : ℝ)..1 / 2, P (f (Complex.equivRealProdCLM.symm (s₀, t)))
          ((u ∘ realChart f) (s₀, t))
          (deriv f (Complex.equivRealProdCLM.symm (s₀, t)) * Complex.I) =
        g s₀ * ∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (s₀, t))) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t ht ↦ ?_
    rw [uIcc_of_le (by norm_num)] at ht
    rw [hPf (s₀, t) ⟨hs₀, ht⟩, Complex.I_im, one_mul, comp_apply]
  rw [hs₀ (by norm_num), hs₀ (by norm_num), ht ⟨le_rfl, hαβ⟩, ht ⟨hαβ, le_rfl⟩]
  simp only [comp_apply]
  ring

/-- **The energy identity on the image of a rectangle of an end.** Let `f` be a `C²` holomorphic
map, such as the end lift of a cylindrical end, whose real chart is injective on the rectangle
`[α, β] × [-1/2, 1/2)` and maps the closed rectangle `[α, β] × [-1/2, 1/2]` into an open set `Ω`.
Let the datum `P` and the map `u` be `C¹` on `Ω`, and suppose that in the coordinates of `f` the
datum is `g(s) G(t) dt` on that closed rectangle. Then over the image of the rectangle the Floer
energy is the symplectic area, plus `g(β)` times the integral of `G` along the image of the side
`s = β`, minus `g(α)` times that along the side `s = α`, minus the integrated curvature. -/
theorem integral_floerEnergyDensity_image_realChart_Icc_prod_Ico (ω : SymplecticForm V)
    (hf : ContDiff ℂ 2 f) {α β : ℝ} (hαβ : α ≤ β)
    (hinj : InjOn (realChart f) (Icc α β ×ˢ Ico (-1 / 2) (1 / 2)))
    (hΩ : IsOpen Ω) (hfΩ : ∀ z ∈ Icc α β ×ˢ Icc (-1 / 2 : ℝ) (1 / 2), realChart f z ∈ Ω)
    (hP : ContDiffOn ℝ 1 (fun p : (ℝ × ℝ) × V ↦ P (Complex.equivRealProdCLM.symm p.1) p.2)
      (Ω ×ˢ univ))
    {u : ℝ × ℝ → V} (hu : ContDiffOn ℝ 1 u Ω) {g : ℝ → ℝ} {G : ℝ → V → ℝ}
    (hPf : ∀ z ∈ Icc α β ×ˢ Icc (-1 / 2 : ℝ) (1 / 2), ∀ x v,
      P (f (Complex.equivRealProdCLM.symm z)) x (deriv f (Complex.equivRealProdCLM.symm z) * v) =
        v.im * (g z.1 * G z.2 x)) :
    ∫ z in realChart f '' (Icc α β ×ˢ Ico (-1 / 2) (1 / 2)), ω.floerEnergyDensity
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
        (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) u z =
      (∫ z in realChart f '' (Icc α β ×ˢ Ico (-1 / 2) (1 / 2)),
          ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) +
        (g β * (∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (β, t)))) -
          g α * ∫ t in (-1 / 2 : ℝ)..1 / 2, G t (u (realChart f (α, t)))) -
        ∫ z in realChart f '' (Icc α β ×ˢ Ico (-1 / 2) (1 / 2)), ω.hamiltonianCurvature
          (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
          (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) z (u z) := by
  set φ := realChart f
  set s : Set (ℝ × ℝ) := Icc α β ×ˢ Ico (-1 / 2 : ℝ) (1 / 2)
  have hφ : ContDiff ℝ 2 φ := TauCeti.Complex.contDiff_realChart hf
  have hmeas : MeasurableSet s := measurableSet_Icc.prod measurableSet_Ico
  have hφd (w : ℝ × ℝ) : DifferentiableAt ℝ φ w := hφ.differentiable (by norm_num) w
  have hdet (w : ℝ × ℝ) : 0 ≤ (fderiv ℝ φ w).det :=
    TauCeti.Complex.det_fderiv_realChart_nonneg (hf.differentiable (by norm_num) _).hasDerivAt
  have hsΩ {w : ℝ × ℝ} (hw : w ∈ s) : φ w ∈ Ω := hfΩ w ⟨hw.1, Ico_subset_Icc_self hw.2⟩
  have hud {w : ℝ × ℝ} (hw : w ∈ s) : DifferentiableAt ℝ u (φ w) :=
    (hu.differentiableOn one_ne_zero _ (hsΩ hw)).differentiableAt (hΩ.mem_nhds (hsΩ hw))
  have hPd {w : ℝ × ℝ} (hw : w ∈ s) (x : V) :
      DifferentiableAt ℝ (fun p : (ℝ × ℝ) × V ↦ P (Complex.equivRealProdCLM.symm p.1) p.2)
        (φ w, x) :=
    (hP.differentiableOn one_ne_zero _ ⟨hsΩ hw, mem_univ x⟩).differentiableAt
      ((hΩ.prod isOpen_univ).mem_nhds ⟨hsΩ hw, mem_univ x⟩)
  have hdom {w : ℝ × ℝ} (hw : w ∈ s) (x : V) (v : ℂ) :=
    ((hPd hw x).comp (f := fun z' : ℝ × ℝ ↦ (z', x)) (φ w)
      (differentiableAt_id.prodMk (differentiableAt_const x))).clm_apply (differentiableAt_const v)
  have htgt {w : ℝ × ℝ} (hw : w ∈ s) (x : V) (v : ℂ) :=
    ((hPd hw x).comp (f := fun y : V ↦ (φ w, y)) x
      ((differentiableAt_const (φ w)).prodMk differentiableAt_id)).clm_apply
      (differentiableAt_const v)
  -- Change variables to the coordinates of `f`, in each of the three integrals.
  have harea := ω.integral_floerEnergyDensity_image (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0)
    hmeas hinj (fun w _ ↦ hφd w) (fun w _ ↦ hdet w) (fun w hw ↦ hud hw)
    (fun _ _ ↦ differentiableAt_const _) (fun _ _ ↦ differentiableAt_const _)
  have h₀ (v : ℝ × ℝ) : perturbationPullback φ (fun (_ : ℝ × ℝ) (_ : V) ↦ (0 : ℝ))
      (fun _ _ ↦ 0) v = fun _ _ ↦ 0 := by
    funext w x
    simp [perturbationPullback_apply]
  simp only [h₀, floerEnergyDensity_zero] at harea
  rw [harea, ω.integral_floerEnergyDensity_image hmeas hinj (fun w _ ↦ hφd w)
      (fun w _ ↦ hdet w) (fun w hw ↦ hud hw) (fun w hw ↦ htgt hw _ 1)
      (fun w hw ↦ htgt hw _ Complex.I),
    ω.integral_hamiltonianCurvature_image hmeas hinj (fun w _ ↦ hφ.contDiffAt) (fun w _ ↦ hdet w)
      (fun w hw ↦ hdom hw _ 1) (fun w hw ↦ hdom hw _ Complex.I)]
  -- The pulled-back datum, evaluated on a tangent vector `v`, is `P` at `f` on `f' v`.
  have hpb (v : ℝ × ℝ) : perturbationPullback φ (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x 1)
      (fun z x ↦ P (Complex.equivRealProdCLM.symm z) x Complex.I) v =
        fun w x ↦ P (f (Complex.equivRealProdCLM.symm w)) x
          (deriv f (Complex.equivRealProdCLM.symm w) * Complex.equivRealProdCLM.symm v) := by
    funext w x
    exact perturbationPullback_realChart P
      (hf.differentiable (by norm_num) _).hasDerivAt v x
  simp only [hpb, equivRealProdCLM_symm_stdComplexLineReal,
    equivRealProdCLM_symm_stdComplexLineImag]
  exact integral_floerEnergyDensity_comp_realChart_Icc_prod_Ico ω hf hαβ hΩ hfΩ hP hu hPf

end RealChart

end SymplecticForm

end TauCeti
