/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Energy
public import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

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

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1, on
  Hamiltonian perturbations as one-forms on the domain, their curvature two-form and the
  energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8, on perturbation data on
  surfaces with strip-like ends.
-/

public section

open Function MeasureTheory Set

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
    (hKt : DifferentiableAt ℝ (fun z ↦ Kt z x) (φ w))
    (hKs' : DifferentiableAt ℝ (Ks (φ w)) x) (hKt' : DifferentiableAt ℝ (Kt (φ w)) x) :
    ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w x =
      (fderiv ℝ φ w).det * ω.hamiltonianCurvature Ks Kt (φ w) x := by
  have hφ₁ : DifferentiableAt ℝ φ w := hφ.differentiableAt (by norm_num)
  have hφ₂ : DifferentiableAt ℝ (fderiv ℝ φ) w :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  have hsymm : fderiv ℝ (fderiv ℝ φ) w stdComplexLineReal stdComplexLineImag =
      fderiv ℝ (fderiv ℝ φ) w stdComplexLineImag stdComplexLineReal :=
    hφ.isSymmSndFDerivAt (by norm_num [minSmoothness_of_isRCLikeNormedField]) _ _
  -- The Poisson bracket term scales by `det dφ`.
  have hbracket : ω.poissonBracket (perturbationPullback φ Ks Kt stdComplexLineReal w)
      (perturbationPullback φ Ks Kt stdComplexLineImag w) x =
        (fderiv ℝ φ w).det * ω.poissonBracket (Ks (φ w)) (Kt (φ w)) x := by
    simp only [poissonBracket_def, ω.hamiltonianVectorField_perturbationPullback hKs' hKt']
    exact ω.apply_smul_add_smul_det (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) _ _
  -- The derivative terms scale by `det dφ`: the second derivatives of `φ` cancel by `hsymm`,
  -- after expanding the derivatives of `K_s` and `K_t` on the columns of `dφ_w`.
  have hκ (κ : ℝ × ℝ →L[ℝ] ℝ) (e : ℝ × ℝ) : κ (fderiv ℝ φ w e) =
      (fderiv ℝ φ w e).1 * κ stdComplexLineReal + (fderiv ℝ φ w e).2 * κ stdComplexLineImag := by
    simpa using (κ : ℝ × ℝ →ₗ[ℝ] ℝ).apply_stdComplexLine (fderiv ℝ φ w e)
  have hderiv :
      fderiv ℝ (fun w' ↦ perturbationPullback φ Ks Kt stdComplexLineImag w' x) w
          stdComplexLineReal -
        fderiv ℝ (fun w' ↦ perturbationPullback φ Ks Kt stdComplexLineReal w' x) w
          stdComplexLineImag =
        (fderiv ℝ φ w).det * (fderiv ℝ (fun z ↦ Kt z x) (φ w) stdComplexLineReal -
          fderiv ℝ (fun z ↦ Ks z x) (φ w) stdComplexLineImag) := by
    simp only [fderiv_perturbationPullback_apply hφ₂ hφ₁ hKs hKt, hsymm, hκ]
    simp only [ContinuousLinearMap.det, LinearMap.det_finTwoProd, ContinuousLinearMap.coe_coe,
      stdComplexLineReal_eq, stdComplexLineImag_eq]
    ring
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
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw ↦ (hφ w hw).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setIntegral_congr_fun hs fun w hw ↦ ?_
  rw [abs_of_nonneg (hdet w hw), smul_eq_mul,
    ω.floerEnergyDensity_perturbationPullback (hφ w hw) (hu w hw) (hKs w hw) (hKt w hw)]

/-- **Invariance of the integrated curvature under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective and orientation preserving on a measurable set `s`, the integral
of the curvature `R_K(u)` over `φ '' s` is the integral of `R_{φ^*K}(u ∘ φ)` over `s`. -/
theorem integral_hamiltonianCurvature_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w))
    (hKs' : ∀ w ∈ s, DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt' : ∀ w ∈ s, DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ∫ z in φ '' s, ω.hamiltonianCurvature Ks Kt z (u z) =
      ∫ w in s, ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w)) := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw ↦ ((hφ w hw).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setIntegral_congr_fun hs fun w hw ↦ ?_
  rw [abs_of_nonneg (hdet w hw), smul_eq_mul, ω.hamiltonianCurvature_perturbationPullback
    (hφ w hw) (hKs w hw) (hKt w hw) (hKs' w hw) (hKt' w hw)]

/-- **Invariance of the curvature allowance under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective on a measurable set `s`, the integral of `|R_K(u)|` over
`φ '' s` is the integral of `|R_{φ^*K}(u ∘ φ)|` over `s`. No orientation hypothesis is needed,
since both sides are absolute values. Curvature bounds used in energy estimates may therefore be
computed in any chart. -/
theorem integral_abs_hamiltonianCurvature_image (ω : SymplecticForm V) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w))
    (hKs' : ∀ w ∈ s, DifferentiableAt ℝ (Ks (φ w)) (u (φ w)))
    (hKt' : ∀ w ∈ s, DifferentiableAt ℝ (Kt (φ w)) (u (φ w))) :
    ∫ z in φ '' s, |ω.hamiltonianCurvature Ks Kt z (u z)| =
      ∫ w in s, |ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w))| := by
  -- Lebesgue measure on `ℝ × ℝ` is the product measure, an additive Haar measure.
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  rw [integral_image_eq_integral_abs_det_fderiv_smul volume hs
    (fun w hw ↦ ((hφ w hw).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt) hinj]
  refine setIntegral_congr_fun hs fun w hw ↦ ?_
  rw [ω.hamiltonianCurvature_perturbationPullback (hφ w hw) (hKs w hw) (hKt w hw) (hKs' w hw)
    (hKt' w hw), abs_mul, smul_eq_mul]

end Integral

end SymplecticForm

end TauCeti
