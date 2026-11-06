/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Manifold
public import TauCeti.Geometry.Symplectic.Floer.Pullback
import TauCeti.Analysis.Calculus.DifferentialForm.Stokes
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# The Floer energy identity for manifold targets

For a map `u : ℝ × ℝ → M` and a Hamiltonian one-form `K = Ks ds + Kt dt`, the
perturbed derivative takes values in the actual tangent space `T_(u z) M`. Its symplectic
area density satisfies

`ω(du - X_K) = ω(du) + d(K(u)) - R_K(u)`.

Here `R_K = ∂s Kt - ∂t Ks - {Ks, Kt}` uses the intrinsic Hamiltonian vector fields, with convention
`ι_(X_H) ω = dH`. The curvature of a cylindrical perturbation `K = H_t dt`, with no `ds` component
and independent of `s`, vanishes (`TauCeti.SmoothTwoForm.hamiltonianCurvature_cylindrical`). For a
nondegenerate two-form on a finite-dimensional model, the identity holds for differentiable maps and
jointly differentiable Hamiltonians on the domain times the manifold. Neither closedness of the
two-form nor the Floer equation is needed for this pointwise identity. For solutions of the equation
the density is nonnegative under tameness, and is half the standard quadratic energy density. The
almost complex structure may be chosen independently at each domain point, as is needed for
domain-dependent perturbations.

Integrating the identity over a rectangle `[a₁, b₁] × [a₂, b₂]` of the domain gives

`∫ ω(du - X_K) = ∫ u^* ω + ∮ K(u) - ∫ R_K(u)`

(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`). The exterior derivative
`d(K(u))` is a function on the domain alone, so the divergence theorem applies to it whatever
the target. The integrability of the energy density and of `R_K(u)` is assumed, and that of the
area density follows.

A punctured domain carries no global coordinate, so these objects must also be compared across
changes of domain coordinates `φ`. For the pulled-back datum `φ^*K`
(`TauCeti.Floer.perturbationPullback`) and the reparametrized map `u ∘ φ`, the perturbed
derivative is `(du - X_K) ∘ dφ`, and both the energy density and the curvature are multiplied by
the Jacobian determinant `det dφ`. By the change of variables formula the energy and the
integrated curvature over a region may therefore be computed in any orientation-preserving
chart. These are the manifold-target versions of the identities in
`TauCeti.Geometry.Symplectic.Floer.Pullback`. The domain-derivative part of the curvature,
Green's theorem for `K(u)` and the change of variables formula do not see the target, and are
shared with them through
`TauCeti.Floer.fderiv_perturbationPullback_sub_fderiv_perturbationPullback`,
`TauCeti.integral_fderiv_sub_fderiv_Icc` and
`TauCeti.integral_image_eq_integral_of_eq_abs_det_smul`.

These are coordinate-domain energy identities for arbitrary manifold targets, not a compactness
theorem or an identity involving caps at punctured ends. On a vector-space target with constant
form they recover the vector-space definitions.

## Main results

* `SmoothTwoForm.hamiltonianCurvature_cylindrical`: the curvature of `K = H_t dt` vanishes, and
  `SmoothTwoForm.hamiltonianCurvature_continuation`: that of `K = β(s) H_t dt` is `β'(s) H_t`.
* `SmoothTwoForm.hamiltonianCurvature_congr_of_eventuallyEq`: the curvature is local in the
  domain.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_eq`: the pointwise energy identity.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`: the energy identity on a
  rectangle.
* `SmoothTwoForm.perturbedMFDeriv_perturbationPullback`,
  `SmoothTwoForm.floerEnergyDensity_perturbationPullback`,
  `SmoothTwoForm.hamiltonianCurvature_perturbationPullback`: naturality of the perturbed
  derivative, and the energy density and curvature as two-forms on the domain.
* `SmoothTwoForm.integral_floerEnergyDensity_image`,
  `SmoothTwoForm.integral_hamiltonianCurvature_image`,
  `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_image`: invariance of the energy, the
  integrated curvature and the curvature allowance under changes of domain coordinates.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian perturbations, curvature, and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8.
-/

public noncomputable section

open Function
open scoped Manifold Topology

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- The curvature `∂s Kt - ∂t Ks - {Ks, Kt}` of a Hamiltonian one-form with manifold target. -/
def hamiltonianCurvature (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (z : ℝ × ℝ) (x : M) : ℝ :=
  fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal -
    fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag - ω.poissonBracket (Ks z) (Kt z) x

/-- The defining curvature formula, separating domain derivatives and target Poisson bracket. -/
theorem hamiltonianCurvature_def (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature Ks Kt z x =
      fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w x) z stdComplexLineImag - ω.poissonBracket (Ks z) (Kt z) x :=
  (rfl)

/-- Without a `ds` component, the curvature of `K = K_t dt` is `∂_s K_t`. -/
theorem hamiltonianCurvature_zero_left (ω : SmoothTwoForm I M) (Kt : ℝ × ℝ → M → ℝ)
    (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) Kt z x =
      fderiv ℝ (fun w ↦ Kt w x) z stdComplexLineReal := by
  simp only [hamiltonianCurvature_def, poissonBracket_def, hamiltonianVectorField_const,
    Pi.zero_apply, SmoothBundleForm.eval₂_apply]
  -- The bracket pairs the zero vector field of the zero Hamiltonian with `X_{K_t}`.
  rw [ContinuousAlternatingMap.map_coord_zero _ 0 rfl]
  simp

/-- A cylindrical perturbation `K = H_t dt`, independent of `s`, has zero curvature. -/
theorem hamiltonianCurvature_cylindrical (ω : SmoothTwoForm I M) (H : ℝ → M → ℝ) (z : ℝ × ℝ)
    (x : M) : ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w ↦ H w.2) z x = 0 := by
  rw [hamiltonianCurvature_zero_left, stdComplexLineReal_eq]
  exact fderiv_comp_snd_apply_mk_zero (fun t ↦ H t x) z 1

/-- A continuation perturbation `K = β(s) H_t dt` has curvature `β'(s) H_t`. -/
theorem hamiltonianCurvature_continuation (ω : SmoothTwoForm I M) {β : ℝ → ℝ} {H : ℝ → M → ℝ}
    {z : ℝ × ℝ} {x : M} (hβ : DifferentiableAt ℝ β z.1)
    (hH : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w y ↦ β w.1 * H w.2 y) z x =
      deriv β z.1 * H z.2 x := by
  rw [hamiltonianCurvature_zero_left, stdComplexLineReal_eq]
  exact fderiv_mul_apply_one_zero (h := fun t ↦ H t x) hβ hH

/-- The curvature only depends on the germs of the perturbation data at the domain point. -/
theorem hamiltonianCurvature_congr_of_eventuallyEq (ω : SmoothTwoForm I M)
    {Ks Kt Ks' Kt' : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ} (hs : Ks =ᶠ[𝓝 z] Ks') (ht : Kt =ᶠ[𝓝 z] Kt') :
    ω.hamiltonianCurvature Ks Kt z = ω.hamiltonianCurvature Ks' Kt' z := by
  ext x
  have hs' : (fun w ↦ Ks w x) =ᶠ[𝓝 z] fun w ↦ Ks' w x := hs.mono fun _ hw ↦ congrFun hw x
  have ht' : (fun w ↦ Kt w x) =ᶠ[𝓝 z] fun w ↦ Kt' w x := ht.mono fun _ hw ↦ congrFun hw x
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def, hs'.fderiv_eq, ht'.fderiv_eq,
    hs.eq_of_nhds, ht.eq_of_nhds]

/-- The intrinsic perturbed derivative `du - X_K`, valued in `T_(u z) M`.
As with `mfderiv`, using this as an actual differential requires differentiability of `u`. -/
def perturbedMFDeriv (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ × ℝ →L[ℝ] TangentSpace I (u z) :=
  -- On the model domain the tangent space is definitionally `ℝ × ℝ`; the type
  -- annotation supplies this identification before forming differences of maps.
  let du : ℝ × ℝ →L[ℝ] TangentSpace I (u z) := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z
  du - (ContinuousLinearMap.fst ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Ks z) (u z)) -
    (ContinuousLinearMap.snd ℝ ℝ ℝ).smulRight (ω.hamiltonianVectorField (Kt z) (u z))

/-- Evaluation of the perturbed derivative on a domain tangent vector. -/
theorem perturbedMFDeriv_apply (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z v : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z v = mfderiv 𝓘(ℝ, ℝ × ℝ) I u z v -
      v.1 • ω.hamiltonianVectorField (Ks z) (u z) -
      v.2 • ω.hamiltonianVectorField (Kt z) (u z) :=
  (rfl)

/-- The real-coordinate component is `∂s u - X_(Ks)`. -/
@[simp]
theorem perturbedMFDeriv_apply_stdComplexLineReal (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) := by
  simp [perturbedMFDeriv_apply]

/-- The imaginary-coordinate component is `∂t u - X_(Kt)`. -/
@[simp]
theorem perturbedMFDeriv_apply_stdComplexLineImag (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z) := by
  simp [perturbedMFDeriv_apply]

/-- The perturbed derivative is complex linear exactly when the coordinate Floer equation
`∂s u - X_(Ks) + J (∂t u - X_(Kt)) = 0` holds in the target tangent fiber. -/
theorem isComplexLinearMap_perturbedMFDeriv_iff (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (z : ℝ × ℝ)
    (J : AlmostComplexStructure (TangentSpace I (u z))) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap ↔
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal - ω.hamiltonianVectorField (Ks z) (u z) +
        J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
          ω.hamiltonianVectorField (Kt z) (u z)) = 0 := by
  rw [isComplexLinearMap_stdComplexLine_iff]
  simp only [ContinuousLinearMap.coe_coe, perturbedMFDeriv_apply_stdComplexLineReal,
    perturbedMFDeriv_apply_stdComplexLineImag]
  constructor
  · intro h
    rw [h, AlmostComplexStructure.apply_apply, add_neg_cancel]
  · intro h
    rw [add_eq_zero_iff_eq_neg] at h
    rw [h, map_neg, AlmostComplexStructure.apply_apply, neg_neg]

/-- The symplectic area density of `du - X_K` for a manifold target. -/
def floerEnergyDensity (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) : ℝ :=
  SmoothBundleForm.eval₂ ω (u z) (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
    (ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag)

/-- Floer energy density is the two-form evaluated on the two perturbed coordinate derivatives. -/
theorem floerEnergyDensity_def (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerEnergyDensity Ks Kt u z =
      SmoothBundleForm.eval₂ ω (u z) (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal)
        (ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag) :=
  (rfl)

variable {ω : SmoothTwoForm I M} {Ks Kt : ℝ × ℝ → M → ℝ}
  {u : ℝ × ℝ → M} {z : ℝ × ℝ}

/-- The pointwise energy identity for a manifold target: symplectic area plus the exterior
derivative of `K(u)`, minus Hamiltonian curvature. -/
theorem IsNondegenerate.floerEnergyDensity_eq [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z)
    (hKs : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Ks) (z, u z))
    (hKt : MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry Kt) (z, u z)) :
    ω.floerEnergyDensity Ks Kt u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) +
      (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
        fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
      ω.hamiltonianCurvature Ks Kt z (u z) := by
  rw [floerEnergyDensity_def, hamiltonianCurvature_def, poissonBracket_def,
    perturbedMFDeriv_apply_stdComplexLineReal, perturbedMFDeriv_apply_stdComplexLineImag,
    fderiv_comp_graph_apply_of_mdifferentiableAt hu hKt,
    fderiv_comp_graph_apply_of_mdifferentiableAt hu hKs]
  -- The Hamiltonian contractions are precisely the target terms of the chain rule.
  have hs := hω.eval₂_hamiltonianVectorField (Ks z) (u z)
    (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag)
  have ht : SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (ω.hamiltonianVectorField (Kt z) (u z)) =
        -mvfderiv I (Kt z) (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal) := by
    rw [SmoothBundleForm.eval₂_swap, hω.eval₂_hamiltonianVectorField]
  simp only [← SmoothForm.bilinFormAt_apply, map_sub, LinearMap.sub_apply] at hs ht ⊢
  rw [hs, ht]
  ring

/-- On a solution the density is half the standard quadratic energy density of the perturbed
derivative. The almost complex structure here is a structure on a single tangent fiber. -/
theorem floerEnergyDensity_eq_stdComplexLineEnergyDensity_div_two
    {J : AlmostComplexStructure (TangentSpace I (u z))}
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) (hω : ω.IsNondegenerate) :
    ω.floerEnergyDensity Ks Kt u z =
      (hω.symplecticFormAt (u z)).stdComplexLineEnergyDensity J
        (ω.perturbedMFDeriv Ks Kt u z).toLinearMap / 2 := by
  rw [h.stdComplexLineEnergyDensity_eq_two_mul_symplecticForm]
  simp only [floerEnergyDensity_def, IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe]
  ring

/-- A Floer solution has nonnegative energy density for a tamed structure on the target fiber. -/
theorem floerEnergyDensity_nonneg {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hω : ω.IsNondegenerate) (hJ : (hω.symplecticFormAt (u z)).Tames J)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z := by
  simpa only [floerEnergyDensity_def, IsNondegenerate.symplecticFormAt_apply,
    ContinuousLinearMap.coe_coe] using
      h.symplecticForm_apply_stdComplexLineReal_stdComplexLineImag_nonneg hJ

/-! ### Changes of domain coordinates -/

section Pullback

open Floer

variable {φ : ℝ × ℝ → ℝ × ℝ} {w : ℝ × ℝ} {x : M}

/-- The Hamiltonian vector field of a component of the pullback `φ^*K` is the corresponding
combination of the Hamiltonian vector fields of `K_s` and `K_t` at `φ w`. -/
theorem hamiltonianVectorField_perturbationPullback (ω : SmoothTwoForm I M)
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) x) (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) x)
    (v : ℝ × ℝ) :
    ω.hamiltonianVectorField (perturbationPullback φ Ks Kt v w) x =
      (fderiv ℝ φ w v).1 • ω.hamiltonianVectorField (Ks (φ w)) x +
        (fderiv ℝ φ w v).2 • ω.hamiltonianVectorField (Kt (φ w)) x := by
  have h : perturbationPullback φ Ks Kt v w =
      (fderiv ℝ φ w v).1 • Ks (φ w) + (fderiv ℝ φ w v).2 • Kt (φ w) := by
    funext y
    simp [perturbationPullback_apply]
  rw [h, hamiltonianVectorField_add (hKs.const_smul _) (hKt.const_smul _),
    hamiltonianVectorField_const_smul, hamiltonianVectorField_const_smul]

/-- **Naturality of the perturbed derivative.** The perturbed derivative of the reparametrized
map `u ∘ φ` for the pulled-back datum `φ^*K` is `(du - X_K) ∘ dφ`, in the tangent space
`T_(u (φ w)) M`. -/
theorem perturbedMFDeriv_perturbationPullback (ω : SmoothTwoForm I M)
    (hφ : DifferentiableAt ℝ φ w) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w))
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w))) :
    ω.perturbedMFDeriv (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (ω.perturbedMFDeriv Ks Kt u (φ w)).comp (fderiv ℝ φ w) := by
  refine ContinuousLinearMap.ext fun v ↦ ?_
  have hv := (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ).apply_stdComplexLine v
  simp only [ContinuousLinearMap.coe_coe] at hv
  -- The chain rule, with the derivative of `φ` read as an `fderiv`.
  have hd : mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ φ) w v =
      mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ w) (fderiv ℝ φ w v) := by
    rw [mfderiv_comp w hu hφ.mdifferentiableAt, mfderiv_eq_fderiv]
    exact ContinuousLinearMap.comp_apply _ _ _
  -- Unfold both perturbed derivatives and expand `X_{φ^*K}`.
  simp only [ContinuousLinearMap.comp_apply, perturbedMFDeriv_apply, hd, comp_apply,
    ω.hamiltonianVectorField_perturbationPullback hKs hKt]
  -- Expand `dφ_w v` in the coordinate directions and normalize.
  simp only [hv,
    Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul, add_smul, smul_add,
    mul_smul]
  abel

/-- **The energy density is a two-form.** The Floer energy density of `u ∘ φ` for the
pulled-back datum `φ^*K` is the Jacobian determinant of `φ` times the energy density of `u` for
`K` at `φ w`. No nondegeneracy of the two-form is needed. -/
theorem floerEnergyDensity_perturbationPullback (ω : SmoothTwoForm I M)
    (hφ : DifferentiableAt ℝ φ w) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w))
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w))) :
    ω.floerEnergyDensity (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w =
      (fderiv ℝ φ w).det * ω.floerEnergyDensity Ks Kt u (φ w) := by
  -- Expand the perturbed derivative of `u` on the columns of `dφ_w`.
  have hP (e : ℝ × ℝ) : ω.perturbedMFDeriv Ks Kt u (φ w) (fderiv ℝ φ w e) =
      (fderiv ℝ φ w e).1 • ω.perturbedMFDeriv Ks Kt u (φ w) stdComplexLineReal +
        (fderiv ℝ φ w e).2 • ω.perturbedMFDeriv Ks Kt u (φ w) stdComplexLineImag := by
    simpa using (ω.perturbedMFDeriv Ks Kt u (φ w) :
      ℝ × ℝ →ₗ[ℝ] TangentSpace I (u (φ w))).apply_stdComplexLine (fderiv ℝ φ w e)
  rw [floerEnergyDensity_def, floerEnergyDensity_def,
    ω.perturbedMFDeriv_perturbationPullback hφ hu hKs hKt]
  simp only [ContinuousLinearMap.comp_apply, hP, stdComplexLineReal_eq, stdComplexLineImag_eq]
  exact ω.eval₂_smul_add_smul_det _ (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) _ _

/-- **The curvature is a two-form.** For a `C²` change of coordinates `φ`, the curvature of the
pulled-back datum `φ^*K` is the Jacobian determinant of `φ` times the curvature of `K` at `φ w`. -/
theorem hamiltonianCurvature_perturbationPullback (ω : SmoothTwoForm I M)
    (hφ : ContDiffAt ℝ 2 φ w) (hKs : DifferentiableAt ℝ (fun z ↦ Ks z x) (φ w))
    (hKt : DifferentiableAt ℝ (fun z ↦ Kt z x) (φ w))
    (hKs' : MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) x)
    (hKt' : MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) x) :
    ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w x =
      (fderiv ℝ φ w).det * ω.hamiltonianCurvature Ks Kt (φ w) x := by
  have hbracket : ω.poissonBracket (perturbationPullback φ Ks Kt stdComplexLineReal w)
      (perturbationPullback φ Ks Kt stdComplexLineImag w) x =
        (fderiv ℝ φ w).det * ω.poissonBracket (Ks (φ w)) (Kt (φ w)) x := by
    simp only [poissonBracket_def, ω.hamiltonianVectorField_perturbationPullback hKs' hKt',
      stdComplexLineReal_eq, stdComplexLineImag_eq]
    exact ω.eval₂_smul_add_smul_det _ (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ) _ _
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def]
  linear_combination fderiv_perturbationPullback_sub_fderiv_perturbationPullback hφ hKs hKt -
    hbracket

end Pullback

section Integral

open Floer MeasureTheory Set

variable {φ : ℝ × ℝ → ℝ × ℝ} {s : Set (ℝ × ℝ)}

/-- **Invariance of the energy under changes of coordinates.** For a change of coordinates `φ`
that is injective and orientation preserving on a measurable set `s`, the energy of `u` for `K`
over `φ '' s` is the energy of `u ∘ φ` for `φ^*K` over `s`. -/
theorem integral_floerEnergyDensity_image (ω : SmoothTwoForm I M) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hu : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w))
    (hKs : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w))) :
    ∫ z in φ '' s, ω.floerEnergyDensity Ks Kt u z =
      ∫ w in s, ω.floerEnergyDensity (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ by
    rw [abs_of_nonneg (hdet w hw), smul_eq_mul,
      ω.floerEnergyDensity_perturbationPullback (hφ w hw) (hu w hw) (hKs w hw) (hKt w hw)]

/-- **Invariance of the integrated curvature under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective and orientation preserving on a measurable set `s`, the integral
of the curvature `R_K(u)` over `φ '' s` is the integral of `R_{φ^*K}(u ∘ φ)` over `s`. -/
theorem integral_hamiltonianCurvature_image (ω : SmoothTwoForm I M) (hs : MeasurableSet s)
    (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w))
    (hKs' : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt' : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w))) :
    ∫ z in φ '' s, ω.hamiltonianCurvature Ks Kt z (u z) =
      ∫ w in s, ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w)) :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj
    (fun w hw ↦ (hφ w hw).differentiableAt (by norm_num)) fun w hw ↦ by
      rw [abs_of_nonneg (hdet w hw), smul_eq_mul, ω.hamiltonianCurvature_perturbationPullback
        (hφ w hw) (hKs w hw) (hKt w hw) (hKs' w hw) (hKt' w hw)]

/-- **Invariance of the curvature allowance under changes of coordinates.** For a `C²` change of
coordinates `φ` that is injective on a measurable set `s`, the lower Lebesgue integral of
`|R_K(u)|` over `φ '' s` is that of `|R_{φ^*K}(u ∘ φ)|` over `s`. No orientation, integrability
or measurability hypothesis is needed, so curvature allowances along arbitrary maps `u` may be
computed in any chart. -/
theorem lintegral_enorm_hamiltonianCurvature_image (ω : SmoothTwoForm I M)
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, ContDiffAt ℝ 2 φ w)
    (hKs : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Ks z (u (φ w))) (φ w))
    (hKt : ∀ w ∈ s, DifferentiableAt ℝ (fun z ↦ Kt z (u (φ w))) (φ w))
    (hKs' : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt' : ∀ w ∈ s, MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w))) :
    ∫⁻ z in φ '' s, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ =
      ∫⁻ w in s, ‖ω.hamiltonianCurvature (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) w (u (φ w))‖ₑ :=
  lintegral_enorm_image_eq_lintegral_enorm_of_eq_det_smul hs hinj
    (fun w hw ↦ (hφ w hw).differentiableAt (by norm_num)) fun w hw ↦
      ω.hamiltonianCurvature_perturbationPullback (hφ w hw) (hKs w hw) (hKt w hw) (hKs' w hw)
        (hKt' w hw)

/-- **The energy identity on a rectangle, for a manifold target.** Let `u` and the perturbation
data `K = K_s ds + K_t dt` be `C¹` over an open neighbourhood `U` of a rectangle
`[a₁, b₁] × [a₂, b₂]`, for a nondegenerate two-form on a finite-dimensional manifold. If the
energy density and the curvature `R_K(u)` are integrable over the rectangle, then the energy over
the rectangle is the symplectic area `∫ u^* ω`, plus the integral of the pulled-back one-form
`K(u) = K_s(u) ds + K_t(u) dt` over the positively oriented boundary, minus the integral of
`R_K(u)`. Closedness of the two-form is not used. -/
theorem IsNondegenerate.integral_floerEnergyDensity [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) {U : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    {a b : ℝ × ℝ} (hab : a ≤ b) (habU : Icc a b ⊆ U)
    (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) (Icc a b))
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) (Icc a b)) :
    ∫ z in Icc a b, ω.floerEnergyDensity Ks Kt u z =
      (∫ z in Icc a b, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
        ((∫ s in a.1..b.1, Ks (s, a.2) (u (s, a.2))) + (∫ t in a.2..b.2, Kt (b.1, t) (u (b.1, t))) -
          (∫ s in a.1..b.1, Ks (s, b.2) (u (s, b.2))) -
          ∫ t in a.2..b.2, Kt (a.1, t) (u (a.1, t))) -
        ∫ z in Icc a b, ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- The pulled-back components `K_s(u)` and `K_t(u)` are `C¹` functions on the domain, to which
  -- Green's theorem applies.
  have hgraph : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) 1 (fun w ↦ (w, u w)) U :=
    contMDiffOn_id.prodMk hu
  have hmem : MapsTo (fun w ↦ (w, u w)) U (U ×ˢ univ) := fun _ hz ↦ ⟨hz, mem_univ _⟩
  have hf : ContDiffOn ℝ 1 (fun w ↦ Kt w (u w)) U :=
    contMDiffOn_iff_contDiffOn.mp (hKt.comp hgraph hmem)
  have hg : ContDiffOn ℝ 1 (fun w ↦ Ks w (u w)) U :=
    contMDiffOn_iff_contDiffOn.mp (hKs.comp hgraph hmem)
  have hderiv : IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) (Icc a b) :=
    integrableOn_fderiv_sub_fderiv_Icc hU hg hf habU
  -- The pointwise energy identity on the rectangle.
  have hpt : ∀ z ∈ Icc a b, ω.floerEnergyDensity Ks Kt u z =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
        ω.hamiltonianCurvature Ks Kt z (u z) := by
    intro z hz
    have hzU := habU hz
    have hzU' : (z, u z) ∈ U ×ˢ (univ : Set M) := hmem hzU
    exact hω.floerEnergyDensity_eq
      ((hu.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt one_ne_zero)
      ((hKs.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hzU')).mdifferentiableAt one_ne_zero)
      ((hKt.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hzU')).mdifferentiableAt one_ne_zero)
  -- The symplectic area density is integrable, as the difference of integrable functions.
  have harea : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) (Icc a b) := by
    refine ((hE.sub hderiv).add hR).congr_fun (fun z hz ↦ ?_) measurableSet_Icc
    simp only [Pi.add_apply, Pi.sub_apply, hpt z hz]
    ring
  have hsum : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag)) (Icc a b) :=
    harea.add hderiv
  rw [setIntegral_congr_fun measurableSet_Icc hpt, integral_sub hsum hR,
    integral_add harea hderiv, stdComplexLineReal_eq, stdComplexLineImag_eq,
    integral_fderiv_sub_fderiv_Icc hU hg hf hab habU]

end Integral

end TauCeti.SmoothTwoForm

namespace TauCeti.SymplecticForm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- A constant smooth two-form has the same Hamiltonian curvature as the vector-space form. -/
@[simp]
theorem hamiltonianCurvature_constSmooth (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (z : ℝ × ℝ) (x : V) :
    ω.constSmooth.hamiltonianCurvature Ks Kt z x = ω.hamiltonianCurvature Ks Kt z x := by
  rw [SmoothTwoForm.hamiltonianCurvature_def, hamiltonianCurvature_def,
    poissonBracket_constSmooth]

/-- Under the canonical target tangent identification the intrinsic perturbed derivative
for a constant form is the vector-space perturbed derivative. -/
theorem fromTangentSpace_perturbedMFDeriv_constSmooth_apply (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z v : ℝ × ℝ) :
    NormedSpace.fromTangentSpace (u z) (ω.constSmooth.perturbedMFDeriv Ks Kt u z v) =
      ω.perturbedFDeriv Ks Kt u z v := by
  have hd : mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z
        ((NormedSpace.fromTangentSpace z).symm v) =
      (NormedSpace.fromTangentSpace (u z)).symm (fderiv ℝ u z v) := by
    simp only [mfderiv_eq_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply]
  have hd' := congrArg (NormedSpace.fromTangentSpace (u z)) hd
  rw [ContinuousLinearEquiv.apply_symm_apply,
    NormedSpace.fromTangentSpace_symm_apply] at hd'
  rw [SmoothTwoForm.perturbedMFDeriv_apply, map_sub, map_sub, map_smul, map_smul,
    perturbedFDeriv_apply, hd']
  rw [NormedSpace.fromTangentSpace_apply, NormedSpace.fromTangentSpace_apply,
    hamiltonianVectorField_constSmooth, hamiltonianVectorField_constSmooth]

/-- The intrinsic energy density for a constant form agrees with the vector-space density. -/
@[simp]
theorem floerEnergyDensity_constSmooth (ω : SymplecticForm V)
    (Ks Kt : ℝ × ℝ → V → ℝ) (u : ℝ × ℝ → V) (z : ℝ × ℝ) :
    ω.constSmooth.floerEnergyDensity Ks Kt u z = ω.floerEnergyDensity Ks Kt u z := by
  rw [SmoothTwoForm.floerEnergyDensity_def, floerEnergyDensity_def,
    fromTangentSpace_constSmooth_apply, fromTangentSpace_perturbedMFDeriv_constSmooth_apply,
    fromTangentSpace_perturbedMFDeriv_constSmooth_apply]

end TauCeti.SymplecticForm
