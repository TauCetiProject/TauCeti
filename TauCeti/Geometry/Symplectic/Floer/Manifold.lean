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
import TauCeti.Analysis.Calculus.LineDeriv.IntegrationByParts
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth

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
area density follows. If `K(u)` has compact support in the plane, the boundary term disappears
and the energy over the whole plane is `∫ u^* ω - ∫ R_K(u)`
(`SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_hasCompactSupport`). This is the
form of the identity on a closed domain, such as a sphere whose perturbation data vanish near one
point. More generally, when the perturbation data themselves vanish outside a compact set and
`u` is only `C¹` near that set, the energy over every region containing it is
`∫ u^* ω - ∫ R_K(u)`
(`SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`).

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

* `SmoothTwoForm.hamiltonianCurvature_cylindrical`: the curvature of `K = H_t dt` vanishes.
* `SmoothTwoForm.hamiltonianCurvature_congr_of_eventuallyEq`,
  `SmoothTwoForm.hamiltonianCurvature_continuation`: the curvature is local in the domain, and a
  continuation perturbation `K = β(s) H_t dt` has curvature `β'(s) H_t`.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_eq`: the pointwise energy identity.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_nonneg`,
  `SmoothTwoForm.continuous_hamiltonianCurvature_zero_left_comp` and
  `SmoothTwoForm.IsNondegenerate.continuous_floerEnergyDensity_zero_left`: for a perturbation
  `K = K_t dt`, nonnegativity of the energy density on solutions, and continuity of the curvature
  and of the energy density.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`: the energy identity on a
  rectangle.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_hasCompactSupport`: the energy
  identity on the plane for a compactly supported perturbation.
* `SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`: for
  perturbation data vanishing outside a compact set, the energy over any region containing that
  set is `∫ u^* ω - ∫ R_K(u)`, with no boundary term; the vector-space case is
  `SymplecticForm.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`.
* `SmoothTwoForm.perturbedMFDeriv_perturbationPullback`,
  `SmoothTwoForm.floerEnergyDensity_perturbationPullback`,
  `SmoothTwoForm.hamiltonianCurvature_perturbationPullback`: naturality of the perturbed
  derivative, and the energy density and curvature as two-forms on the domain.
* `SmoothTwoForm.integral_floerEnergyDensity_image`,
  `SmoothTwoForm.integral_hamiltonianCurvature_image`,
  `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_image`: invariance of the energy, the
  integrated curvature and the curvature allowance under changes of domain coordinates.
* `SmoothTwoForm.hamiltonianCurvature_comp_add_right`,
  `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_comp_add_right`: translations of the domain
  translate the curvature and preserve the curvature allowance along a map.

## References

* D. McDuff and D. Salamon, *J-holomorphic curves and symplectic topology*, Section 8.1,
  on Hamiltonian perturbations, curvature, and the energy identity.
* P. Seidel, *Fukaya categories and Picard–Lefschetz theory*, Section 8.
-/

public noncomputable section

open Function
open scoped Manifold

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

/-- For the zero perturbation the Floer energy density is the symplectic area density
`ω(∂_s u, ∂_t u)`. -/
@[simp]
theorem floerEnergyDensity_zero (ω : SmoothTwoForm I M) (u : ℝ × ℝ → M) (z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun _ _ ↦ 0) u z =
      SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) := by
  simp [floerEnergyDensity_def]

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

/-- A solution of the Floer equation `∂_s u + J (∂_t u - X_{K_t}(u)) = 0` for a perturbation
`K = K_t dt` without `ds` component has nonnegative energy density at `z` when `J` is tamed by `ω`
at `u z`. -/
theorem IsNondegenerate.floerEnergyDensity_zero_left_nonneg (hω : ω.IsNondegenerate)
    {J : AlmostComplexStructure (TangentSpace I (u z))} (hJ : (hω.symplecticFormAt (u z)).Tames J)
    (hfloer : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt z) (u z)) = 0) :
    0 ≤ ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u z :=
  floerEnergyDensity_nonneg hω hJ <|
    (ω.isComplexLinearMap_perturbedMFDeriv_iff _ _ u z J).2 (by simpa using hfloer)

/-- For a `C¹` map `u` and a `C¹` family of Hamiltonians `K_t`, the curvature `∂_s K_t` of the
perturbation `K = K_t dt`, evaluated along `u`, is continuous. -/
theorem continuous_hamiltonianCurvature_zero_left_comp
    (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) :
    Continuous fun z ↦ ω.hamiltonianCurvature (fun _ _ ↦ 0) Kt z (u z) := by
  simp only [hamiltonianCurvature_zero_left]
  -- The derivative of `w ↦ K_t(w, u z)` at `w = z` depends continuously on `z`.
  have h : ContDiff ℝ 1 (uncurry fun z w ↦ Kt w (u z)) := contMDiff_iff_contDiff.mp <|
    hKt.comp (contDiff_snd.contMDiff.prodMk (hu.comp contDiff_fst.contMDiff))
  exact (h.fderiv (n := 0) contDiff_id (by norm_num)).continuous.clm_apply continuous_const

/-- For a `C¹` map `u` and a `C¹` family of Hamiltonians `K_t`, the Floer energy density of the
perturbation `K = K_t dt` is continuous. -/
theorem IsNondegenerate.continuous_floerEnergyDensity_zero_left [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt))
    (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u) :
    Continuous (ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u) := by
  have hω₀ : IsSmoothForm I 0 ω.1 := ω.isSmoothForm.of_le (by simp)
  -- The three terms of the pointwise energy identity are continuous.
  have harea : Continuous fun z ↦ SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) :=
    (hω₀.continuous_apply_mfderiv hu (1, 0) (0, 1)).congr fun z ↦ by
      simp [SmoothBundleForm.eval₂_apply, stdComplexLineReal_eq, stdComplexLineImag_eq]
  have hK : ContDiff ℝ 1 fun w ↦ Kt w (u w) :=
    contMDiff_iff_contDiff.mp (hKt.comp (contMDiff_id.prodMk hu))
  have hdK : Continuous fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal :=
    (hK.continuous_fderiv one_ne_zero).clm_apply continuous_const
  refine ((harea.add hdK).sub
    (continuous_hamiltonianCurvature_zero_left_comp (ω := ω) hKt hu)).congr fun z ↦ ?_
  rw [hω.floerEnergyDensity_eq ((hu z).mdifferentiableAt one_ne_zero)
    (contMDiffAt_const.mdifferentiableAt one_ne_zero) ((hKt _).mdifferentiableAt one_ne_zero)]
  simp

/-! ### Local formulas for the curvature -/

section Curvature

open Filter Topology

/-- The curvature only depends on the germs of the perturbation data at the domain point. -/
theorem hamiltonianCurvature_congr_of_eventuallyEq (ω : SmoothTwoForm I M)
    {Ks Kt Ks' Kt' : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ} (hs : Ks =ᶠ[𝓝 z] Ks') (ht : Kt =ᶠ[𝓝 z] Kt') :
    ω.hamiltonianCurvature Ks Kt z = ω.hamiltonianCurvature Ks' Kt' z := by
  funext x
  have hs' : (fun w ↦ Ks w x) =ᶠ[𝓝 z] fun w ↦ Ks' w x := hs.mono fun _ hw ↦ congrFun hw x
  have ht' : (fun w ↦ Kt w x) =ᶠ[𝓝 z] fun w ↦ Kt' w x := ht.mono fun _ hw ↦ congrFun hw x
  rw [hamiltonianCurvature_def, hamiltonianCurvature_def, hs'.fderiv_eq, ht'.fderiv_eq,
    hs.eq_of_nhds, ht.eq_of_nhds]

/-- Translating the perturbation data by `v` translates the curvature by `v`. -/
theorem hamiltonianCurvature_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (v z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) z x =
      ω.hamiltonianCurvature Ks Kt (z + v) x := by
  simp only [hamiltonianCurvature_def]
  rw [fderiv_comp_add_right (f := fun w ↦ Kt w x), fderiv_comp_add_right (f := fun w ↦ Ks w x)]

/-- The zero perturbation has zero curvature. -/
@[simp]
theorem hamiltonianCurvature_zero (ω : SmoothTwoForm I M) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun _ _ ↦ 0) z x = 0 := by
  simp [hamiltonianCurvature_def]

/-- A continuation perturbation `K = β(s) H_t dt` has curvature `β'(s) H_t`. -/
theorem hamiltonianCurvature_continuation (ω : SmoothTwoForm I M) {β : ℝ → ℝ} {H : ℝ → M → ℝ}
    {z : ℝ × ℝ} {x : M} (hβ : DifferentiableAt ℝ β z.1)
    (hH : DifferentiableAt ℝ (fun t ↦ H t x) z.2) :
    ω.hamiltonianCurvature (fun _ _ ↦ 0) (fun w y ↦ β w.1 * H w.2 y) z x =
      deriv β z.1 * H z.2 x := by
  simp only [hamiltonianCurvature_def, poissonBracket_const_left, fderiv_const_apply,
    zero_apply, sub_zero]
  exact fderiv_mul_apply_stdComplexLineReal (h := fun t ↦ H t x) hβ hH

end Curvature

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

/-- Translations of the domain preserve the integrated curvature along a map. -/
theorem lintegral_enorm_hamiltonianCurvature_comp_add_right (ω : SmoothTwoForm I M)
    (Ks Kt : ℝ × ℝ → M → ℝ) (u : ℝ × ℝ → M) (v : ℝ × ℝ) :
    ∫⁻ z, ‖ω.hamiltonianCurvature (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) z (u (z + v))‖ₑ =
      ∫⁻ z, ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ := by
  have hv : MeasurePreserving (· + v) volume volume :=
    (measurePreserving_add_right volume v.1).prod (measurePreserving_add_right volume v.2)
  simp only [hamiltonianCurvature_comp_add_right]
  exact hv.lintegral_comp_emb (measurableEmbedding_addRight v)
    (fun z ↦ ‖ω.hamiltonianCurvature Ks Kt z (u z)‖ₑ)

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

/-- **The energy identity on the plane, for a compactly supported perturbation.** Let `u` and the
perturbation data `K = K_s ds + K_t dt` be `C¹` on the whole plane, for a nondegenerate two-form
on a finite-dimensional manifold, and suppose that the pulled-back one-form
`K(u) = K_s(u) ds + K_t(u) dt` has compact support. If the energy density and the curvature
`R_K(u)` are integrable over the plane, then the energy is the symplectic area `∫ u^* ω` minus the
integral of `R_K(u)`: the exterior derivative `d(K(u))` integrates to zero. This applies to
perturbation data on a closed surface that vanish near a point, written in the plane chart of the
complement of that point. -/
theorem IsNondegenerate.integral_floerEnergyDensity_of_hasCompactSupport
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) (hu : ContMDiff 𝓘(ℝ, ℝ × ℝ) I 1 u)
    (hKs : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks))
    (hKt : ContMDiff (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt))
    (hKs₀ : HasCompactSupport fun w ↦ Ks w (u w)) (hKt₀ : HasCompactSupport fun w ↦ Kt w (u w))
    (hE : Integrable (ω.floerEnergyDensity Ks Kt u))
    (hR : Integrable fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) :
    ∫ z, ω.floerEnergyDensity Ks Kt u z =
      (∫ z, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z, ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- The pulled-back components `K_s(u)` and `K_t(u)` are compactly supported `C¹` functions on
  -- the plane, so the integrals of their partial derivatives vanish.
  have hgraph : ContMDiff 𝓘(ℝ, ℝ × ℝ) (𝓘(ℝ, ℝ × ℝ).prod I) 1 (fun w ↦ (w, u w)) :=
    contMDiff_id.prodMk hu
  have hf : ContDiff ℝ 1 (fun w ↦ Kt w (u w)) := contMDiff_iff_contDiff.mp (hKt.comp hgraph)
  have hg : ContDiff ℝ 1 (fun w ↦ Ks w (u w)) := contMDiff_iff_contDiff.mp (hKs.comp hgraph)
  have hf' : Integrable fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hKt₀.fderiv_apply (𝕜 := ℝ) _)
  have hg' : Integrable fun z ↦ fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag :=
    ((hg.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hKs₀.fderiv_apply (𝕜 := ℝ) _)
  have hdK : Integrable fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag := hf'.sub hg'
  have hderiv : ∫ z, (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) = 0 := by
    rw [integral_sub hf' hg', integral_fderiv_apply_eq_zero_of_hasCompactSupport hf hKt₀,
      integral_fderiv_apply_eq_zero_of_hasCompactSupport hg hKs₀, sub_zero]
  -- The pointwise energy identity.
  have hpt (z : ℝ × ℝ) : ω.floerEnergyDensity Ks Kt u z =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
        ω.hamiltonianCurvature Ks Kt z (u z) :=
    hω.floerEnergyDensity_eq ((hu z).mdifferentiableAt one_ne_zero)
      ((hKs _).mdifferentiableAt one_ne_zero) ((hKt _).mdifferentiableAt one_ne_zero)
  -- The symplectic area density is integrable, as a combination of integrable functions.
  have harea : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) :=
    ((hE.sub hdK).add hR).congr (Filter.Eventually.of_forall fun z ↦ by
      simp only [Pi.add_apply, Pi.sub_apply, hpt z]
      ring)
  have hsum : Integrable fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) := harea.add hdK
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hsum hR,
    integral_add harea hdK, hderiv, add_zero]

open Filter Topology

/-- The pointwise energy identity `E = u^* ω + d(K(u)) - R_K(u)` holds at every point of the
domain, if the data vanish outside a closed set `C` and `u` and `K` are `C¹` over an open
neighbourhood of `C`: off `C` every perturbation term vanishes. -/
private theorem IsNondegenerate.floerEnergyDensity_eq_of_forall_notMem_eq_zero
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) {U C : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    (hC : IsClosed C) (hCU : C ⊆ U) (hKsC : ∀ z ∉ C, Ks z = 0) (hKtC : ∀ z ∉ C, Kt z = 0)
    (z : ℝ × ℝ) :
    ω.floerEnergyDensity Ks Kt u z =
      (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
          fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) -
        ω.hamiltonianCurvature Ks Kt z (u z) := by
  by_cases hz : z ∈ C
  · have hzU := hCU hz
    have hzU' : (z, u z) ∈ U ×ˢ (univ : Set M) := ⟨hzU, mem_univ _⟩
    exact hω.floerEnergyDensity_eq
      ((hu.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt one_ne_zero)
      ((hKs.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hzU')).mdifferentiableAt one_ne_zero)
      ((hKt.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hzU')).mdifferentiableAt one_ne_zero)
  · -- Off `C`, the data and their pullbacks along `u` vanish near `z`.
    have hev {K : ℝ × ℝ → M → ℝ} (hK : ∀ z ∉ C, K z = 0) : K =ᶠ[𝓝 z] fun _ _ ↦ 0 :=
      notMem_tsupport_iff_eventuallyEq.1 fun h ↦
        hz (closure_minimal (support_subset_iff'.2 hK) hC h)
    have hd {K : ℝ × ℝ → M → ℝ} (hK : ∀ z ∉ C, K z = 0) :
        fderiv ℝ (fun w ↦ K w (u w)) z = 0 :=
      fderiv_of_notMem_tsupport ℝ fun h ↦ hz
        (closure_minimal (support_subset_iff'.2 fun w hw ↦ by simp [hK w hw]) hC h)
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (hev hKsC) (hev hKtC),
      hamiltonianCurvature_zero, hd hKsC, hd hKtC]
    simp [floerEnergyDensity_def, hKsC z hz, hKtC z hz, Pi.zero_def, hamiltonianVectorField_const]

/-- **The energy identity for compactly supported perturbation data, for a manifold target.**
Let the perturbation data `K = K_s ds + K_t dt` vanish outside a compact set `C` of the domain,
and let `u` and `K` be `C¹` over an open neighbourhood `U` of `C`, for a nondegenerate two-form on
a finite-dimensional manifold. Then for every measurable set `D ⊇ C` over which the energy density
and the curvature `R_K(u)` are integrable, the energy over `D` is the symplectic area `∫_D u^* ω`
minus the integral of `R_K(u)`: the exterior derivative `d(K(u))` is compactly supported, so the
boundary term of the energy identity vanishes. Closedness of the two-form is not used. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) {U C D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    (hC : IsCompact C) (hCU : C ⊆ U) (hKsC : ∀ z ∉ C, Ks z = 0) (hKtC : ∀ z ∉ C, Kt z = 0)
    (hD : MeasurableSet D) (hCD : C ⊆ D)
    (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) D)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) D) :
    ∫ z in D, ω.floerEnergyDensity Ks Kt u z =
      (∫ z in D, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z) := by
  have := Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure ℝ)
  -- Each pulled-back component `K(u)` is `C¹` on the whole domain, with support in `C`.
  have hcomp {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ))
      (hKC : ∀ z ∉ C, K z = 0) :
      ContDiff ℝ 1 (fun w ↦ K w (u w)) ∧ HasCompactSupport (fun w ↦ K w (u w)) ∧
        tsupport (fun w ↦ K w (u w)) ⊆ C := by
    have hsupp : tsupport (fun w ↦ K w (u w)) ⊆ C :=
      closure_minimal (support_subset_iff'.2 fun w hw ↦ by simp [hKC w hw]) hC.isClosed
    have hKU : ContDiffOn ℝ 1 (fun w ↦ K w (u w)) U :=
      contMDiffOn_iff_contDiffOn.mp (hK.comp (contMDiffOn_id.prodMk hu)
        fun _ hz ↦ ⟨hz, mem_univ _⟩)
    refine ⟨contDiff_iff_contDiffAt.2 fun z ↦ ?_,
      HasCompactSupport.intro hC fun w hw ↦ by simp [hKC w hw], hsupp⟩
    by_cases hz : z ∈ U
    · exact hKU.contDiffAt (hU.mem_nhds hz)
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hCU (hsupp h)))
  obtain ⟨hs, hsc, hss⟩ := hcomp hKs hKsC
  obtain ⟨ht, htc, hts⟩ := hcomp hKt hKtC
  have hpt := hω.floerEnergyDensity_eq_of_forall_notMem_eq_zero hU hu hKs hKt hC.isClosed hCU
    hKsC hKtC
  -- The exterior derivative `d(K(u))` is integrable, vanishes off `C`, and has integral zero.
  set d : ℝ × ℝ → ℝ := fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
    fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag with hd
  have hint {f : ℝ × ℝ → ℝ} (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (v : ℝ × ℝ) :
      Integrable fun z ↦ fderiv ℝ f z v :=
    ((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const).integrable_of_hasCompactSupport
      (hfc.fderiv_apply (𝕜 := ℝ) v)
  have hdi : Integrable d := (hint ht htc _).sub (hint hs hsc _)
  have hdD : ∫ z in D, d z = 0 := by
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero fun z hz ↦ ?_, hd,
      integral_sub (hint ht htc _) (hint hs hsc _),
      integral_fderiv_apply_eq_zero_of_hasCompactSupport ht htc,
      integral_fderiv_apply_eq_zero_of_hasCompactSupport hs hsc, sub_zero]
    have hzC : z ∉ C := fun h ↦ hz (hCD h)
    simp only [hd, fderiv_of_notMem_tsupport ℝ fun h ↦ hzC (hss h),
      fderiv_of_notMem_tsupport ℝ fun h ↦ hzC (hts h), zero_apply, sub_zero]
  -- The area density is integrable, as a combination of integrable functions.
  have harea : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) D := by
    refine ((hE.sub hdi.integrableOn).add hR).congr_fun (fun z _ ↦ ?_) hD
    simp only [Pi.add_apply, Pi.sub_apply, hpt z, hd]
    ring
  have hsum : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) + d z) D :=
    harea.add hdi.integrableOn
  rw [setIntegral_congr_fun hD fun z _ ↦ hpt z, integral_sub hsum hR,
    integral_add harea hdi.integrableOn, hdD, add_zero]


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

/-- For a constant form, the intrinsic symplectic area density of a map of the plane is the
vector-space area density `ω(∂_s u, ∂_t u)`. -/
theorem eval₂_constSmooth_mfderiv_stdComplexLine (ω : SymplecticForm V) (u : ℝ × ℝ → V)
    (z : ℝ × ℝ) :
    SmoothBundleForm.eval₂ ω.constSmooth (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, V) u z stdComplexLineImag) =
      ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag) := by
  rw [← SmoothTwoForm.floerEnergyDensity_zero, floerEnergyDensity_constSmooth,
    floerEnergyDensity_zero]

open MeasureTheory Set Filter Topology in
/-- **The energy identity for compactly supported perturbation data.** Let the perturbation data
`K = K_s ds + K_t dt` vanish outside a compact set `C` of the domain, and let `u` and `K` be `C¹`
over an open neighbourhood `U` of `C`. Then for every measurable set `D ⊇ C` over which the energy
density is integrable, the energy over `D` is the symplectic area `∫_D u^* ω` minus the integral of
the curvature `R_K(u)`. This is the constant-form case of
`TauCeti.SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`; the
curvature is continuous here, so its integrability is automatic. -/
theorem setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero (ω : SymplecticForm V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {U C D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ)) (hC : IsCompact C) (hCU : C ⊆ U)
    (hKsC : ∀ z ∉ C, Ks z = 0) (hKtC : ∀ z ∉ C, Kt z = 0) (hD : MeasurableSet D) (hCD : C ⊆ D)
    (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) D) :
    ∫ z in D, ω.floerEnergyDensity Ks Kt u z =
      (∫ z in D, ω (fderiv ℝ u z stdComplexLineReal) (fderiv ℝ u z stdComplexLineImag)) -
        ∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- The curvature is continuous on `U` and vanishes off the compact set `C ⊆ U`.
  have hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) D := by
    refine (((ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn hKs hKt).mono
      hCU).integrableOn_compact hC).of_forall_sdiff_eq_zero hD fun z hz ↦ ?_
    have hev {K : ℝ × ℝ → V → ℝ} (hK : ∀ z ∉ C, K z = 0) : K =ᶠ[𝓝 z] fun _ _ ↦ 0 :=
      Filter.eventually_of_mem (hC.isClosed.isOpen_compl.mem_nhds hz.2) fun w hw ↦ hK w hw
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq (hev hKsC) (hev hKtC),
      hamiltonianCurvature_zero_left]
    simp
  have hK' {K : ℝ × ℝ → V → ℝ} (hK : ContDiffOn ℝ 1 (uncurry K) (U ×ˢ univ)) :
      ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod 𝓘(ℝ, V)) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ) := by
    have h := contMDiffOn_iff_contDiffOn.mpr hK
    rw [modelWithCornersSelf_prod, ← chartedSpaceSelf_prod] at h
    exact h
  have hE' : ω.constSmooth.floerEnergyDensity Ks Kt u = ω.floerEnergyDensity Ks Kt u :=
    funext (floerEnergyDensity_constSmooth ω Ks Kt u)
  have hR' : (fun z ↦ ω.constSmooth.hamiltonianCurvature Ks Kt z (u z)) =
      fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z) :=
    funext fun z ↦ hamiltonianCurvature_constSmooth ω Ks Kt z (u z)
  have h :=
    (isNondegenerate_constSmooth ω).setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero hU
    (contMDiffOn_iff_contDiffOn.mpr hu) (hK' hKs) (hK' hKt) hC hCU hKsC hKtC hD hCD
    (hE' ▸ hE) (hR' ▸ hR)
  simpa only [hE', hR', eval₂_constSmooth_mfderiv_stdComplexLine] using h


end TauCeti.SymplecticForm
