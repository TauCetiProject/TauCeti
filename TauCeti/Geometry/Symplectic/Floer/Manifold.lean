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
import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.DifferentialForm.Pullback.Smooth
import TauCeti.Geometry.Manifold.MFDeriv.Translation
import TauCeti.Topology.VectorBundle.Trivialization

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
the density is nonnegative as soon as `ω(v, J v) > 0` for nonzero `v`, without nondegeneracy
(`SmoothTwoForm.floerEnergyDensity_nonneg_of_forall_pos`), and is half the standard quadratic
energy density. The almost complex structure may be chosen independently at each domain point, as
is needed for domain-dependent perturbations.

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
Since `d(K(u))` is linear in `K`, the energy plus the integrated curvature over a compact region
only depends on the data near its boundary: two data that agree outside the region give the same
value (`IsNondegenerate.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`).
This compares a family of perturbations with a fixed datum that agrees with it far out on the
ends of a punctured domain.

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
* `SmoothTwoForm.hamiltonianCurvature_eq_zero_of_cylindrical`: the curvature vanishes along a line
  near which the perturbation is cylindrical; the vector-space case is
  `SymplecticForm.hamiltonianCurvature_eq_zero_of_cylindrical`.
* `SmoothTwoForm.hamiltonianCurvature_add_const`, `SmoothTwoForm.perturbedMFDeriv_add_const`,
  `SmoothTwoForm.floerEnergyDensity_add_const`: adding a target-independent one-form to the
  perturbation adds its exterior derivative to the curvature, and changes neither the Floer
  equation nor the energy density.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_eq`: the pointwise energy identity.
* `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_eq_symplecticFormAt`,
  `SmoothTwoForm.IsNondegenerate.floerEnergyDensity_zero_left_nonneg`,
  `SmoothTwoForm.continuous_hamiltonianCurvature_zero_left_comp` and
  `SmoothTwoForm.IsNondegenerate.continuous_floerEnergyDensity_zero_left`: for a perturbation
  `K = K_t dt`, the energy density `ω(η, J η)` of a solution, with `η = ∂_t u - X_{K_t}(u)`, its
  nonnegativity, and continuity of the curvature and of the energy density.
* `SmoothTwoForm.tendsto_perturbedMFDeriv` and `SmoothTwoForm.continuousOn_floerEnergyDensity`:
  convergence of perturbed derivatives in the tangent bundle, and continuity of the energy density
  of a `C¹` map when the Hamiltonian vector fields are continuous into the tangent bundle.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity`: the energy identity on a
  rectangle.
* `SmoothTwoForm.IsNondegenerate.integral_floerEnergyDensity_of_hasCompactSupport`: the energy
  identity on the plane for a compactly supported perturbation.
* `SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`: for
  perturbation data vanishing outside a compact set, the energy over any region containing that
  set is `∫ u^* ω - ∫ R_K(u)`, with no boundary term; the vector-space case is
  `SymplecticForm.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero`.
* `SmoothTwoForm.IsNondegenerate.integrableOn_floerEnergyDensity`: over a compact set where `u`
  and `K` are `C¹`, the energy density is integrable whenever the curvature is.
* `SmoothTwoForm.integral_floerEnergyDensity_sub_add_eq_of_eventuallyEq_zero`: where the
  perturbation data vanish the energy is the area, so energy minus area plus integrated curvature
  does not change when a region is shrunk to the part where the data live.
* `IsNondegenerate.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`:
  changing the perturbation data inside a compact region `D` does not change the energy plus the
  integrated curvature over `D`; the vector-space case is
  `SymplecticForm.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`.
* `SmoothTwoForm.perturbedMFDeriv_perturbationPullback`,
  `SmoothTwoForm.floerEnergyDensity_perturbationPullback`,
  `SmoothTwoForm.eval₂_mfderiv_comp_stdComplexLine`,
  `SmoothTwoForm.hamiltonianCurvature_perturbationPullback`: naturality of the perturbed
  derivative, and the energy density, the area density and the curvature as two-forms on the
  domain. Consequently holomorphic changes of coordinates preserve the Floer equation
  (`SmoothTwoForm.isComplexLinearMap_perturbedMFDeriv_perturbationPullback`).
* `SmoothTwoForm.integral_floerEnergyDensity_image`,
  `SmoothTwoForm.integral_eval₂_mfderiv_stdComplexLine_image`,
  `SmoothTwoForm.integral_hamiltonianCurvature_image`,
  `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_image`: invariance of the energy, the
  symplectic area, the integrated curvature and the curvature allowance under changes of domain
  coordinates.
* `SmoothTwoForm.hamiltonianCurvature_comp_add_right`,
  `SmoothTwoForm.lintegral_enorm_hamiltonianCurvature_comp_add_right`,
  `SmoothTwoForm.perturbedMFDeriv_comp_add_right`,
  `SmoothTwoForm.floerEnergyDensity_comp_add_right`,
  `SmoothTwoForm.floerEnergyDensity_cylindrical_comp_add_right`: translations of the domain
  translate the curvature, the perturbed derivative and the energy density, and preserve the
  curvature allowance along a map.

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

/-- **The perturbed derivative of a translate.** The perturbed derivative of `w ↦ u (w + v)` for
the translated data `w ↦ K (w + v)` at `z` is the perturbed derivative of `u` for `K` at `z + v`. -/
theorem perturbedMFDeriv_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (v z : ℝ × ℝ) :
    ω.perturbedMFDeriv (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.perturbedMFDeriv Ks Kt u (z + v) := by
  refine ContinuousLinearMap.ext fun a ↦ ?_
  rw [perturbedMFDeriv_apply, perturbedMFDeriv_apply, mfderiv_comp_add_right]
  -- The two sides differ only in how the tangent spaces at `u (z + v)` are written.
  rfl

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

/-- Translating a map and its perturbation data by `v` translates the Floer energy density by
`v`. -/
theorem floerEnergyDensity_comp_add_right (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (v z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun w ↦ Ks (w + v)) (fun w ↦ Kt (w + v)) (fun w ↦ u (w + v)) z =
      ω.floerEnergyDensity Ks Kt u (z + v) := by
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedMFDeriv_comp_add_right]

/-- For the cylindrical perturbation `K = H_t dt`, the energy density of the translate
`(s, t) ↦ u(s + c, t)` at `z` is the energy density of `u` at `z + (c, 0)`. -/
theorem floerEnergyDensity_cylindrical_comp_add_right (ω : SmoothTwoForm I M) (H : ℝ → M → ℝ)
    (u : ℝ × ℝ → M) (c : ℝ) (z : ℝ × ℝ) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) (fun w ↦ u (w + (c, 0))) z =
      ω.floerEnergyDensity (fun _ _ ↦ 0) (fun w ↦ H w.2) u (z + (c, 0)) := by
  simpa using ω.floerEnergyDensity_comp_add_right (fun _ _ ↦ 0) (fun w ↦ H w.2) u (c, 0) z

section Continuity

open Filter Set Topology

/-- **Convergence of perturbed derivatives.** Let the derivatives of maps `u i` at points
`z i → z₀` converge in the tangent bundle, `du_i(z i) e → L e` over `x₀`, and let the Hamiltonian
vector fields of `K` be continuous at `(z₀, x₀)` as maps into the tangent bundle. Then the perturbed
derivatives `(du_i - X_K)(z i) e` converge in the tangent bundle to
`L e - e.1 • X_{K_s}(z₀, x₀) - e.2 • X_{K_t}(z₀, x₀)`. -/
theorem tendsto_perturbedMFDeriv (ω : SmoothTwoForm I M) {Ks Kt : ℝ × ℝ → M → ℝ} {ι : Type*}
    {l : Filter ι} {u : ι → ℝ × ℝ → M} {z : ι → ℝ × ℝ} {z₀ : ℝ × ℝ} {x₀ : M}
    {L : ℝ × ℝ →L[ℝ] TangentSpace I x₀} (hz : Tendsto z l (𝓝 z₀))
    (hL : ∀ e, Tendsto (fun i ↦ (⟨u i (z i), mfderiv 𝓘(ℝ, ℝ × ℝ) I (u i) (z i) e⟩ :
      TangentBundle I M)) l (𝓝 ⟨x₀, L e⟩))
    (hXs : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (hXt : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀))
    (e : ℝ × ℝ) :
    Tendsto (fun i ↦ (⟨u i (z i), ω.perturbedMFDeriv Ks Kt (u i) (z i) e⟩ :
      TangentBundle I M)) l (𝓝 ⟨x₀, L e - e.1 • ω.hamiltonianVectorField (Ks z₀) x₀ -
        e.2 • ω.hamiltonianVectorField (Kt z₀) x₀⟩) := by
  -- Convergence in the tangent bundle is convergence of the coordinates at `x₀`, which are linear
  -- in the vectors.
  set T := trivializationAt E (TangentSpace I) x₀
  have hx₀ : x₀ ∈ T.baseSet := FiberBundle.mem_baseSet_trivializationAt E _ x₀
  obtain ⟨hx, hD⟩ := (T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hL e)
  have hX {K : ℝ × ℝ → M → ℝ} (hK : ContinuousAt (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (K p.1) p.2⟩ : TangentBundle I M)) (z₀, x₀)) :=
    ((T.tendsto_mk_nhds_mk_iff ℝ hx₀).1 (hK.tendsto.comp (hz.prodMk_nhds hx))).2
  refine (T.tendsto_mk_nhds_mk_iff ℝ hx₀).2 ⟨hx, ?_⟩
  simp only [perturbedMFDeriv_apply, map_sub, map_smul]
  exact (hD.sub ((hX hXs).const_smul e.1)).sub ((hX hXt).const_smul e.2)

/-- **Continuity of the Floer energy density, for a manifold target.** If `u` is `C¹` on an open
set `U` of the domain and the Hamiltonian vector fields of the perturbation `K = K_s ds + K_t dt`
are continuous on `U × M` as maps into the tangent bundle, then the Floer energy density of `u` is
continuous on `U`. The vector-space case is `SymplecticForm.continuousOn_floerEnergyDensity`. -/
theorem continuousOn_floerEnergyDensity (ω : SmoothTwoForm I M) {Ks Kt : ℝ × ℝ → M → ℝ}
    {u : ℝ × ℝ → M} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hXs : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Ks p.1) p.2⟩ : TangentBundle I M)) (U ×ˢ univ))
    (hXt : ContinuousOn (fun p : (ℝ × ℝ) × M ↦
      (⟨p.2, ω.hamiltonianVectorField (Kt p.1) p.2⟩ : TangentBundle I M)) (U ×ˢ univ)) :
    ContinuousOn (ω.floerEnergyDensity Ks Kt u) U := by
  have hfun : ω.floerEnergyDensity Ks Kt u = fun z ↦ ω.1 (u z)
      ![ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal,
        ω.perturbedMFDeriv Ks Kt u z stdComplexLineImag] :=
    funext fun z ↦ by rw [floerEnergyDensity_def, SmoothBundleForm.eval₂_apply]
  rw [hfun]
  intro z hz
  have hzU := hU.mem_nhds hz
  have hUM := (hU.prod isOpen_univ).mem_nhds (mk_mem_prod hz (mem_univ (u z)))
  -- The derivatives of `u` along fixed vectors are continuous into the tangent bundle at `z`, and
  -- so are the perturbed derivatives.
  have hD (e : ℝ × ℝ) : Tendsto (fun z' ↦ (⟨u z', mfderiv 𝓘(ℝ, ℝ × ℝ) I u z' e⟩ :
      TangentBundle I M)) (𝓝 z) (𝓝 ⟨u z, mfderiv 𝓘(ℝ, ℝ × ℝ) I u z e⟩) :=
    (((hu.contMDiffAt hzU).continuousAt_tangentMap le_rfl).comp
      ((tangentBundleModelSpaceHomeomorph 𝓘(ℝ, ℝ × ℝ)).symm.continuous.continuousAt.comp
        (continuous_id.prodMk continuous_const).continuousAt)).tendsto
  have hP (e : ℝ × ℝ) := ω.tendsto_perturbedMFDeriv (u := fun _ ↦ u) tendsto_id hD
    (hXs.continuousAt hUM) (hXt.continuousAt hUM) e
  simp only [id_eq] at hP
  refine ((ω.isSmoothForm.of_le (by simp)).tendsto_apply (hu.contMDiffAt hzU).continuousAt
    (Fin.forall_fin_two.2 ⟨?_, ?_⟩)).mono_left nhdsWithin_le_nhds
  -- The limit in `hP` is the perturbed derivative of `u` at `z`, unfolded by
  -- `perturbedMFDeriv_apply`; `convert` matches the two up to the tangent-space instances that the
  -- unfolded form elaborates with.
  · convert hP stdComplexLineReal using 3 <;> exact perturbedMFDeriv_apply ..
  · convert hP stdComplexLineImag using 3 <;> exact perturbedMFDeriv_apply ..

end Continuity

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

/-- A Floer solution has nonnegative energy density for a structure `J` on the target fiber with
`ω(v, J v) > 0` for every nonzero `v`. Neither nondegeneracy nor closedness of `ω` is used. -/
theorem floerEnergyDensity_nonneg_of_forall_pos {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hJ : ∀ v : TangentSpace I (u z), v ≠ 0 → 0 < SmoothBundleForm.eval₂ ω (u z) v (J v))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z := by
  have hP := h.apply_stdComplexLineImag
  simp only [ContinuousLinearMap.coe_coe] at hP
  rw [floerEnergyDensity_def, hP]
  rcases eq_or_ne (ω.perturbedMFDeriv Ks Kt u z stdComplexLineReal) 0 with h0 | h0
  · rw [h0, map_zero, SmoothBundleForm.eval₂_apply]
    exact (ContinuousAlternatingMap.map_coord_zero _ 0 rfl).ge
  · exact (hJ _ h0).le

/-- A Floer solution has nonnegative energy density for a tamed structure on the target fiber. -/
theorem floerEnergyDensity_nonneg {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hω : ω.IsNondegenerate) (hJ : (hω.symplecticFormAt (u z)).Tames J)
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u z).toLinearMap) :
    0 ≤ ω.floerEnergyDensity Ks Kt u z :=
  floerEnergyDensity_nonneg_of_forall_pos (fun v hv ↦ by
    simpa only [IsNondegenerate.symplecticFormAt_apply] using hJ v hv) h

/-- For a solution of the Floer equation `∂_s u + J η = 0` with `η = ∂_t u - X_{K_t}(u)`, for a
perturbation `K = K_t dt` without `ds` component, the energy density at `z` is `ω(η, J η)`. -/
theorem IsNondegenerate.floerEnergyDensity_zero_left_eq_symplecticFormAt
    (hω : ω.IsNondegenerate) {J : AlmostComplexStructure (TangentSpace I (u z))}
    (hfloer : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal +
      J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
        ω.hamiltonianVectorField (Kt z) (u z)) = 0) :
    ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u z =
      hω.symplecticFormAt (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z))
        (J (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag -
          ω.hamiltonianVectorField (Kt z) (u z))) := by
  set η := mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag - ω.hamiltonianVectorField (Kt z) (u z)
  have hs : mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal = -J η :=
    eq_neg_of_add_eq_zero_left hfloer
  have hρ : ω.floerEnergyDensity (fun _ _ ↦ 0) Kt u z =
      hω.symplecticFormAt (u z) (-J η) η := by
    rw [floerEnergyDensity_def, perturbedMFDeriv_apply_stdComplexLineImag,
      perturbedMFDeriv_apply_stdComplexLineReal, hs, hamiltonianVectorField_const, Pi.zero_apply,
      sub_zero, IsNondegenerate.symplecticFormAt_apply]
  rw [hρ, ← (hω.symplecticFormAt (u z)).neg_eq (J η)]
  simp

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

/-- If both components of a Hamiltonian one-form vanish near a domain point, its curvature
vanishes there. No differentiability assumption is needed. -/
theorem hamiltonianCurvature_eq_zero_of_eventuallyEq_zero (ω : SmoothTwoForm I M)
    {Ks Kt : ℝ × ℝ → M → ℝ} {z : ℝ × ℝ}
    (hs : Ks =ᶠ[𝓝 z] 0) (ht : Kt =ᶠ[𝓝 z] 0) (x : M) :
    ω.hamiltonianCurvature Ks Kt z x = 0 := by
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht]
  simp [hamiltonianCurvature_def]

/-- If both components of a Hamiltonian one-form vanish off a closed domain set, its curvature
also vanishes off that set. No differentiability assumption is needed. -/
theorem hamiltonianCurvature_eq_zero_of_notMem (ω : SmoothTwoForm I M)
    {Ks Kt : ℝ × ℝ → M → ℝ} {D : Set (ℝ × ℝ)} (hD : IsClosed D)
    (hs : ∀ z ∉ D, Ks z = 0) (ht : ∀ z ∉ D, Kt z = 0)
    {z : ℝ × ℝ} (hz : z ∉ D) (x : M) : ω.hamiltonianCurvature Ks Kt z x = 0 := by
  have h : ∀ᶠ w in 𝓝 z, w ∉ D := hD.isOpen_compl.mem_nhds hz
  exact ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero
    (h.mono fun w hw ↦ hs w hw) (h.mono fun w hw ↦ ht w hw) x

/-- Adding a perturbation supported in a closed set inside an open region where the original
one-form vanishes adds their curvatures exactly: there are no mixed Poisson-bracket terms. -/
theorem hamiltonianCurvature_add_of_eq_zero_on (ω : SmoothTwoForm I M)
    {Ks Kt δs δt : ℝ × ℝ → M → ℝ} {D U : Set (ℝ × ℝ)}
    (hD : IsClosed D) (hU : IsOpen U) (hDU : D ⊆ U)
    (hKs : ∀ z ∈ U, Ks z = 0) (hKt : ∀ z ∈ U, Kt z = 0)
    (hδs : ∀ z ∉ D, δs z = 0) (hδt : ∀ z ∉ D, δt z = 0) (z : ℝ × ℝ) (x : M) :
    ω.hamiltonianCurvature (fun w y ↦ Ks w y + δs w y) (fun w y ↦ Kt w y + δt w y) z x =
      ω.hamiltonianCurvature Ks Kt z x + ω.hamiltonianCurvature δs δt z x := by
  by_cases hz : z ∈ D
  · have hs : Ks =ᶠ[𝓝 z] 0 := eventually_of_mem (hU.mem_nhds (hDU hz)) hKs
    have ht : Kt =ᶠ[𝓝 z] 0 := eventually_of_mem (hU.mem_nhds (hDU hz)) hKt
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
      (Ks' := δs) (Kt' := δt)
      (hs.mono fun w hw ↦ by simp [hw]) (ht.mono fun w hw ↦ by simp [hw]),
      ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero hs ht x, zero_add]
  · have hs : δs =ᶠ[𝓝 z] 0 := eventually_of_mem (hD.isOpen_compl.mem_nhds hz) hδs
    have ht : δt =ᶠ[𝓝 z] 0 := eventually_of_mem (hD.isOpen_compl.mem_nhds hz) hδt
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq
      (Ks' := Ks) (Kt' := Kt)
      (hs.mono fun w hw ↦ by simp [hw]) (ht.mono fun w hw ↦ by simp [hw]),
      ω.hamiltonianCurvature_eq_zero_of_eventuallyEq_zero hs ht x, add_zero]

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

/-- A datum `K = K_s ds + K_t dt` with `K_s = 0` and `K_t` independent of `s` near the line
`s = c` has zero curvature along that line. -/
theorem hamiltonianCurvature_eq_zero_of_cylindrical (ω : SmoothTwoForm I M)
    {Ks Kt : ℝ × ℝ → M → ℝ} {c : ℝ} (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (t : ℝ) (x : M) :
    ω.hamiltonianCurvature Ks Kt (c, t) x = 0 := by
  have hfst : Tendsto Prod.fst (𝓝 ((c, t) : ℝ × ℝ)) (𝓝 c) := continuous_fst.tendsto (c, t)
  have hs : Ks =ᶠ[𝓝 (c, t)] fun _ _ ↦ 0 := by
    filter_upwards [hfst.eventually hKs] with w hw
    funext x
    simpa using congrFun (hw w.2) x
  have ht : Kt =ᶠ[𝓝 (c, t)] fun w ↦ Kt (c, w.2) := by
    filter_upwards [hfst.eventually hKt] with w hw
    simpa using hw w.2
  rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hs ht]
  exact ω.hamiltonianCurvature_cylindrical (fun t ↦ Kt (c, t)) (c, t) x

end Curvature

section TargetIndependent

/-! ### Target-independent perturbations

Adding to `K` a one-form `k = k_s ds + k_t dt` whose components are functions of the domain point
alone changes no Hamiltonian vector field. The perturbed derivative, and with it the Floer equation
and the energy density, are unchanged, while the curvature changes by the exterior derivative
`∂_s k_t - ∂_t k_s` of `k`. Normalizing the Hamiltonians on the ends by functions of time is the
main example. These are the manifold-target versions of the identities of
`TauCeti.Geometry.Symplectic.Floer.Energy`. -/

/-- The curvature of a target-independent perturbation `k = k_s ds + k_t dt` is the exterior
derivative `∂_s k_t - ∂_t k_s`; the Poisson bracket term vanishes. -/
@[simp]
theorem hamiltonianCurvature_const (ω : SmoothTwoForm I M) (ks kt : ℝ × ℝ → ℝ) (z : ℝ × ℝ)
    (x : M) :
    ω.hamiltonianCurvature (fun w _ ↦ ks w) (fun w _ ↦ kt w) z x =
      fderiv ℝ kt z stdComplexLineReal - fderiv ℝ ks z stdComplexLineImag := by
  simp [hamiltonianCurvature_def]

/-- Adding a target-independent one-form to the perturbation adds its exterior derivative to the
curvature: `R_{K + k} = R_K + ∂_s k_t - ∂_t k_s`, at a point where the components are
differentiable in the domain. -/
theorem hamiltonianCurvature_add_const (ω : SmoothTwoForm I M) {Ks Kt : ℝ × ℝ → M → ℝ}
    {ks kt : ℝ × ℝ → ℝ} {z : ℝ × ℝ} {x : M} (hKs : DifferentiableAt ℝ (fun w ↦ Ks w x) z)
    (hKt : DifferentiableAt ℝ (fun w ↦ Kt w x) z) (hks : DifferentiableAt ℝ ks z)
    (hkt : DifferentiableAt ℝ kt z) :
    ω.hamiltonianCurvature (fun w y ↦ Ks w y + ks w) (fun w y ↦ Kt w y + kt w) z x =
      ω.hamiltonianCurvature Ks Kt z x +
        ω.hamiltonianCurvature (fun w _ ↦ ks w) (fun w _ ↦ kt w) z x := by
  rw [hamiltonianCurvature_const, hamiltonianCurvature_def, hamiltonianCurvature_def,
    fderiv_fun_add hKt hkt, fderiv_fun_add hKs hks]
  simp only [add_apply, poissonBracket_add_const_left,
    poissonBracket_add_const_right]
  ring

/-- Adding a target-independent one-form to the perturbation does not change the perturbed
derivative, so a map solves the Floer equation for `K + k` exactly when it solves it for `K`. -/
@[simp]
theorem perturbedMFDeriv_add_const (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (ks kt : ℝ × ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.perturbedMFDeriv (fun w y ↦ Ks w y + ks w) (fun w y ↦ Kt w y + kt w) u =
      ω.perturbedMFDeriv Ks Kt u := by
  funext z
  simp only [perturbedMFDeriv, hamiltonianVectorField_add_const]

/-- Adding a target-independent one-form to the perturbation does not change the Floer energy
density. -/
@[simp]
theorem floerEnergyDensity_add_const (ω : SmoothTwoForm I M) (Ks Kt : ℝ × ℝ → M → ℝ)
    (ks kt : ℝ × ℝ → ℝ) (u : ℝ × ℝ → M) :
    ω.floerEnergyDensity (fun w y ↦ Ks w y + ks w) (fun w y ↦ Kt w y + kt w) u =
      ω.floerEnergyDensity Ks Kt u := by
  funext z
  rw [floerEnergyDensity_def, floerEnergyDensity_def, perturbedMFDeriv_add_const]

end TargetIndependent

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

/-- **Holomorphic changes of coordinates preserve the Floer equation.** If `dφ` is complex linear
at `w` and `u` solves `(du - X_K)^{0,1} = 0` at `φ w` for an almost complex structure `J` on
`T_(u (φ w)) M`, then `u ∘ φ` solves the Floer equation for the pulled-back datum `φ^*K` at `w`. -/
theorem isComplexLinearMap_perturbedMFDeriv_perturbationPullback (ω : SmoothTwoForm I M)
    {J : AlmostComplexStructure (TangentSpace I (u (φ w)))} (hφ : DifferentiableAt ℝ φ w)
    (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w))
    (hKs : MDifferentiableAt I 𝓘(ℝ) (Ks (φ w)) (u (φ w)))
    (hKt : MDifferentiableAt I 𝓘(ℝ) (Kt (φ w)) (u (φ w)))
    (hφJ : IsComplexLinearMap (AlmostComplexStructure.product ℝ)
      (AlmostComplexStructure.product ℝ) (fderiv ℝ φ w : ℝ × ℝ →ₗ[ℝ] ℝ × ℝ))
    (h : IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv Ks Kt u (φ w)).toLinearMap) :
    IsComplexLinearMap (AlmostComplexStructure.product ℝ) J
      (ω.perturbedMFDeriv (perturbationPullback φ Ks Kt stdComplexLineReal)
        (perturbationPullback φ Ks Kt stdComplexLineImag) (u ∘ φ) w).toLinearMap := by
  rw [ω.perturbedMFDeriv_perturbationPullback hφ hu hKs hKt, ContinuousLinearMap.toLinearMap_comp]
  exact h.comp hφJ

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

/-- **The area density is a two-form.** The symplectic area density `ω(∂_s (u ∘ φ), ∂_t (u ∘ φ))`
at `w` is the Jacobian determinant of `φ` times the area density `ω(∂_s u, ∂_t u)` at `φ w`. -/
theorem eval₂_mfderiv_comp_stdComplexLine (ω : SmoothTwoForm I M)
    (hφ : DifferentiableAt ℝ φ w) (hu : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w)) :
    SmoothBundleForm.eval₂ ω ((u ∘ φ) w) (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ φ) w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ φ) w stdComplexLineImag) =
      (fderiv ℝ φ w).det * SmoothBundleForm.eval₂ ω (u (φ w))
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ w) stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u (φ w) stdComplexLineImag) := by
  -- The area density is the energy density of the zero perturbation.
  simpa only [perturbationPullback_zero, floerEnergyDensity_zero] using
    ω.floerEnergyDensity_perturbationPullback (Ks := fun _ _ ↦ 0) (Kt := fun _ _ ↦ 0) hφ hu
      mdifferentiableAt_const mdifferentiableAt_const

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

/-- **Invariance of the symplectic area under changes of coordinates.** For a change of
coordinates `φ` that is injective and orientation preserving on a measurable set `s`, the
symplectic area `∫ ω(∂_s u, ∂_t u)` of `u` over `φ '' s` is the symplectic area of `u ∘ φ`
over `s`. -/
theorem integral_eval₂_mfderiv_stdComplexLine_image (ω : SmoothTwoForm I M)
    (hs : MeasurableSet s) (hinj : InjOn φ s) (hφ : ∀ w ∈ s, DifferentiableAt ℝ φ w)
    (hdet : ∀ w ∈ s, 0 ≤ (fderiv ℝ φ w).det)
    (hu : ∀ w ∈ s, MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u (φ w)) :
    ∫ z in φ '' s, SmoothBundleForm.eval₂ ω (u z)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) =
      ∫ w in s, SmoothBundleForm.eval₂ ω ((u ∘ φ) w)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ φ) w stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I (u ∘ φ) w stdComplexLineImag) :=
  integral_image_eq_integral_of_eq_abs_det_smul hs hinj hφ fun w hw ↦ by
    rw [abs_of_nonneg (hdet w hw), smul_eq_mul,
      ω.eval₂_mfderiv_comp_stdComplexLine (hφ w hw) (hu w hw)]

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
  have hdK : Integrable fun z ↦ fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag :=
    (integrable_fderiv_apply_of_hasCompactSupport hf hKt₀ _).sub
      (integrable_fderiv_apply_of_hasCompactSupport hg hKs₀ _)
  have hderiv : ∫ z, (fderiv ℝ (fun w ↦ Kt w (u w)) z stdComplexLineReal -
      fderiv ℝ (fun w ↦ Ks w (u w)) z stdComplexLineImag) = 0 := by
    simpa using setIntegral_fderiv_apply_sub_fderiv_apply_eq_zero hf hKt₀ (subset_univ _) hg hKs₀
      (subset_univ _) stdComplexLineReal stdComplexLineImag
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
a finite-dimensional manifold. Then for every set `D ⊇ C` over which the energy density
and the curvature `R_K(u)` are integrable, the energy over `D` is the symplectic area `∫_D u^* ω`
minus the integral of `R_K(u)`: the exterior derivative `d(K(u))` is compactly supported, so the
boundary term of the energy identity vanishes. Closedness of the two-form is not used. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) {U C D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    (hC : IsCompact C) (hCU : C ⊆ U) (hKsC : ∀ z ∉ C, Ks z = 0) (hKtC : ∀ z ∉ C, Kt z = 0)
    (hCD : C ⊆ D)
    (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) D)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) D) :
    ∫ z in D, ω.floerEnergyDensity Ks Kt u z =
      (∫ z in D, (SmoothBundleForm.eval₂ ω (u z)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) -
        ∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z) := by
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
  have hdi : Integrable d := (integrable_fderiv_apply_of_hasCompactSupport ht htc _).sub
    (integrable_fderiv_apply_of_hasCompactSupport hs hsc _)
  have hdD : ∫ z in D, d z = 0 :=
    setIntegral_fderiv_apply_sub_fderiv_apply_eq_zero ht htc (hts.trans hCD) hs hsc
      (hss.trans hCD) _ _
  -- The area density is integrable, as a combination of integrable functions.
  have harea : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) D := by
    refine ((hE.sub hdi.integrableOn).add hR).congr (Filter.Eventually.of_forall fun z ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply, hpt z, hd]
    ring
  have hsum : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) + d z) D :=
    harea.add hdi.integrableOn
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt), integral_sub hsum hR,
    integral_add harea hdi.integrableOn, hdD, add_zero]

/-- **The area density is integrable over compact sets.** If `u` is `C¹` on an open set `U`, then
over a compact set `C ⊆ U` the two-form evaluated on the derivatives of `u` along two fixed
vectors, `z ↦ ω_{u(z)}(du_z a, du_z b)`, is integrable. -/
theorem integrableOn_eval₂_mfderiv (ω : SmoothTwoForm I M) {U C : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U) (hC : IsCompact C) (hCU : C ⊆ U) (a b : ℝ × ℝ) :
    IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z a)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z b) : ℝ)) C := by
  have h := (ω.isSmoothForm.of_le (by simp)).continuousOn_apply_mfderiv hU hu a b
  simp only [← SmoothBundleForm.eval₂_apply] at h
  exact (h.mono hCU).integrableOn_compact hC

/-- **Integrability of the energy density, for a manifold target.** Let `u` and the perturbation
datum `K = K_s ds + K_t dt` be `C¹` over an open set `U` of the domain, for a nondegenerate
two-form on a finite-dimensional manifold, and let `T ⊆ U` be compact. If the curvature `R_K(u)` is
integrable over `T`, so is the Floer energy density: by the pointwise energy identity it differs
from `R_K(u)` by the symplectic area density and the exterior derivative `d(K(u))`, both continuous
on `U`. -/
theorem IsNondegenerate.integrableOn_floerEnergyDensity [FiniteDimensional ℝ E]
    (hω : ω.IsNondegenerate) {U T : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    (hT : IsCompact T) (hTU : T ⊆ U)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) T) :
    IntegrableOn (ω.floerEnergyDensity Ks Kt u) T := by
  have hmem : MapsTo (fun w ↦ (w, u w)) U (U ×ˢ univ) := fun _ hz ↦ ⟨hz, mem_univ _⟩
  have harea := ω.integrableOn_eval₂_mfderiv hU hu hT hTU stdComplexLineReal stdComplexLineImag
  -- Each pulled-back component `K(u)` is `C¹` on `U`, so its derivative is continuous on `U`.
  have hd {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) (e : ℝ × ℝ) :
      IntegrableOn (fun z ↦ fderiv ℝ (fun w ↦ K w (u w)) z e) T := by
    have hKu : ContDiffOn ℝ 1 (fun w ↦ K w (u w)) U :=
      contMDiffOn_iff_contDiffOn.mp (hK.comp (contMDiffOn_id.prodMk hu) hmem)
    exact (((hKu.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const).mono
      hTU).integrableOn_compact hT
  refine ((harea.add ((hd hKt stdComplexLineReal).sub (hd hKs stdComplexLineImag))).sub
    hR).congr_fun (fun z hz ↦ ?_) hT.isClosed.measurableSet
  have hzU := hTU hz
  have hmd {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) :
      MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, u z) :=
    (hK.contMDiffAt ((hU.prod isOpen_univ).mem_nhds (hmem hzU))).mdifferentiableAt one_ne_zero
  rw [hω.floerEnergyDensity_eq ((hu.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt
    one_ne_zero) (hmd hKs) (hmd hKt)]
  rfl

/-- **Changing the perturbation inside a compact region, for a manifold target.** Let `u` and two
perturbation data `K = K_s ds + K_t dt` and `K' = K'_s ds + K'_t dt` be `C¹` over an open set `U`
of the domain, for a nondegenerate two-form on a finite-dimensional manifold, and let `D ⊆ U` be
compact. If `K` and `K'` agree at every point of `U` outside `D`, and the energy densities and the
curvatures along `u` are integrable over `D`, then the energy plus the integrated curvature over
`D` is the same for both data:

`∫_D E_K(u) + ∫_D R_K(u) = ∫_D E_{K'}(u) + ∫_D R_{K'}(u)`.

By the pointwise energy identity the difference of the two sides is the integral of the exterior
derivative `d((K - K')(u))`, and `(K - K')(u)` is supported in `D`. In particular the boundary
term of the energy identity over `D` only sees the datum near the boundary of `D`. -/
theorem IsNondegenerate.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn
    [FiniteDimensional ℝ E] (hω : ω.IsNondegenerate) {Ks' Kt' : ℝ × ℝ → M → ℝ}
    {U D : Set (ℝ × ℝ)} (hU : IsOpen U) (hu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) I 1 u U)
    (hKs : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt) (U ×ˢ univ))
    (hKs' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Ks') (U ×ˢ univ))
    (hKt' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry Kt') (U ×ˢ univ))
    (hD : IsCompact D) (hDU : D ⊆ U) (hs : EqOn Ks Ks' (U \ D)) (ht : EqOn Kt Kt' (U \ D))
    (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) D)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) D)
    (hE' : IntegrableOn (ω.floerEnergyDensity Ks' Kt' u) D)
    (hR' : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks' Kt' z (u z)) D) :
    (∫ z in D, ω.floerEnergyDensity Ks Kt u z) +
        ∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z) =
      (∫ z in D, ω.floerEnergyDensity Ks' Kt' u z) +
        ∫ z in D, ω.hamiltonianCurvature Ks' Kt' z (u z) := by
  have hmem : MapsTo (fun w ↦ (w, u w)) U (U ×ˢ univ) := fun _ hz ↦ ⟨hz, mem_univ _⟩
  have hpull {K : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) :
      ContDiffOn ℝ 1 (fun w ↦ K w (u w)) U :=
    contMDiffOn_iff_contDiffOn.mp (hK.comp (contMDiffOn_id.prodMk hu) hmem)
  -- The difference `(K - K')(u)` of each component, cut off outside `D`, is a compactly
  -- supported `C¹` function on the plane which agrees with the difference near every point of `U`.
  have hdiff {K K' : ℝ × ℝ → M → ℝ}
      (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ))
      (hK' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K') (U ×ˢ univ))
      (hKK' : EqOn K K' (U \ D)) :
      ContDiff ℝ 1 (D.indicator fun w ↦ K w (u w) - K' w (u w)) ∧
        HasCompactSupport (D.indicator fun w ↦ K w (u w) - K' w (u w)) ∧
        tsupport (D.indicator fun w ↦ K w (u w) - K' w (u w)) ⊆ D ∧
        ∀ z ∈ U, D.indicator (fun w ↦ K w (u w) - K' w (u w)) =ᶠ[𝓝 z]
          fun w ↦ K w (u w) - K' w (u w) := by
    have hsupp : tsupport (D.indicator fun w ↦ K w (u w) - K' w (u w)) ⊆ D :=
      closure_minimal (support_indicator_subset) hD.isClosed
    have hloc : ∀ z ∈ U, D.indicator (fun w ↦ K w (u w) - K' w (u w)) =ᶠ[𝓝 z]
        fun w ↦ K w (u w) - K' w (u w) := fun z hz ↦ by
      filter_upwards [hU.mem_nhds hz] with w hw
      by_cases hwD : w ∈ D
      · rw [indicator_of_mem hwD]
      · rw [indicator_of_notMem hwD, hKK' ⟨hw, hwD⟩, sub_self]
    refine ⟨contDiff_iff_contDiffAt.2 fun z ↦ ?_, HasCompactSupport.intro hD fun w hw ↦
      indicator_of_notMem hw _, hsupp, hloc⟩
    by_cases hz : z ∈ U
    · exact (((hpull hK).sub (hpull hK')).contDiffAt (hU.mem_nhds hz)).congr_of_eventuallyEq
        (hloc z hz)
    · exact (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq
        (notMem_tsupport_iff_eventuallyEq.1 fun h ↦ hz (hDU (hsupp h)))
  obtain ⟨hfs, hfsc, hfss, hfsl⟩ := hdiff hKs hKs' hs
  obtain ⟨hft, hftc, hfts, hftl⟩ := hdiff hKt hKt' ht
  -- The exterior derivative of the cut-off difference integrates to zero over `D`.
  set d : ℝ × ℝ → ℝ := fun z ↦
    fderiv ℝ (D.indicator fun w ↦ Kt w (u w) - Kt' w (u w)) z stdComplexLineReal -
      fderiv ℝ (D.indicator fun w ↦ Ks w (u w) - Ks' w (u w)) z stdComplexLineImag with hd
  have hdi : Integrable d := (integrable_fderiv_apply_of_hasCompactSupport hft hftc _).sub
    (integrable_fderiv_apply_of_hasCompactSupport hfs hfsc _)
  have hdD : ∫ z in D, d z = 0 :=
    setIntegral_fderiv_apply_sub_fderiv_apply_eq_zero hft hftc hfts hfs hfsc hfss _ _
  -- On `D`, by the pointwise energy identity for both data, the energy plus the curvature
  -- changes by this exterior derivative.
  have hpt : ∀ z ∈ D, ω.floerEnergyDensity Ks Kt u z + ω.hamiltonianCurvature Ks Kt z (u z) =
      ω.floerEnergyDensity Ks' Kt' u z + ω.hamiltonianCurvature Ks' Kt' z (u z) + d z := by
    intro z hz
    have hzU := hDU hz
    have hzU' : (z, u z) ∈ U ×ˢ (univ : Set M) := hmem hzU
    have hmd {K : ℝ × ℝ → M → ℝ}
        (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) :
        MDifferentiableAt (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) (uncurry K) (z, u z) :=
      (hK.contMDiffAt ((hU.prod isOpen_univ).mem_nhds hzU')).mdifferentiableAt one_ne_zero
    have hud : MDifferentiableAt 𝓘(ℝ, ℝ × ℝ) I u z :=
      (hu.contMDiffAt (hU.mem_nhds hzU)).mdifferentiableAt one_ne_zero
    have hda {K : ℝ × ℝ → M → ℝ}
        (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ)) :
        DifferentiableAt ℝ (fun w ↦ K w (u w)) z :=
      ((hpull hK).contDiffAt (hU.mem_nhds hzU)).differentiableAt one_ne_zero
    have hfd (K K' : ℝ × ℝ → M → ℝ)
        (hK : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K) (U ×ˢ univ))
        (hK' : ContMDiffOn (𝓘(ℝ, ℝ × ℝ).prod I) 𝓘(ℝ) 1 (uncurry K') (U ×ˢ univ))
        (hloc : D.indicator (fun w ↦ K w (u w) - K' w (u w)) =ᶠ[𝓝 z]
          fun w ↦ K w (u w) - K' w (u w)) (v : ℝ × ℝ) :
        fderiv ℝ (D.indicator fun w ↦ K w (u w) - K' w (u w)) z v =
          fderiv ℝ (fun w ↦ K w (u w)) z v - fderiv ℝ (fun w ↦ K' w (u w)) z v := by
      rw [hloc.fderiv_eq, fderiv_fun_sub (hda hK) (hda hK'), sub_apply]
    rw [hω.floerEnergyDensity_eq hud (hmd hKs) (hmd hKt),
      hω.floerEnergyDensity_eq hud (hmd hKs') (hmd hKt'), hd]
    beta_reduce
    rw [hfd Kt Kt' hKt hKt' (hftl z hzU), hfd Ks Ks' hKs hKs' (hfsl z hzU)]
    ring
  rw [← integral_add hE hR, ← integral_add hE' hR', setIntegral_congr_fun hD.measurableSet hpt,
    integral_add (f := fun z ↦ ω.floerEnergyDensity Ks' Kt' u z +
      ω.hamiltonianCurvature Ks' Kt' z (u z)) (hE'.add hR') hdi.integrableOn, hdD, add_zero]

/-- **Shrinking to where the datum lives, for a manifold target.** Let `T ⊆ D` with `D`
measurable, and let `K_s` and `K_t` vanish near every point of `D \ T`. If the energy density, the
symplectic area density and the curvature `R_K(u)` are integrable over `D`, then the Floer energy
minus the symplectic area plus the integrated curvature is the same over `D` as over `T`. -/
theorem integral_floerEnergyDensity_sub_add_eq_of_eventuallyEq_zero {D T : Set (ℝ × ℝ)}
    (hD : MeasurableSet D) (hTD : T ⊆ D) (hKsD : ∀ z ∈ D \ T, Ks =ᶠ[𝓝 z] 0)
    (hKtD : ∀ z ∈ D \ T, Kt =ᶠ[𝓝 z] 0) (hE : IntegrableOn (ω.floerEnergyDensity Ks Kt u) D)
    (hA : IntegrableOn (fun z ↦ (SmoothBundleForm.eval₂ ω (u z)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
      (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) D)
    (hR : IntegrableOn (fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z)) D) :
    (∫ z in D, ω.floerEnergyDensity Ks Kt u z) -
      (∫ z in D, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
      (∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z)) =
    (∫ z in T, ω.floerEnergyDensity Ks Kt u z) -
      (∫ z in T, (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
        (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ)) +
      ∫ z in T, ω.hamiltonianCurvature Ks Kt z (u z) := by
  -- Off `T` the datum vanishes, so the energy is the area and the curvature vanishes.
  have hzero (z : ℝ × ℝ) (hz : z ∈ D \ T) :
      ω.floerEnergyDensity Ks Kt u z -
        (SmoothBundleForm.eval₂ ω (u z) (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineReal)
          (mfderiv 𝓘(ℝ, ℝ × ℝ) I u z stdComplexLineImag) : ℝ) +
        ω.hamiltonianCurvature Ks Kt z (u z) = 0 := by
    have hKs' : Ks =ᶠ[𝓝 z] fun _ _ ↦ 0 := hKsD z hz
    have hKt' : Kt =ᶠ[𝓝 z] fun _ _ ↦ 0 := hKtD z hz
    rw [ω.hamiltonianCurvature_congr_of_eventuallyEq hKs' hKt', hamiltonianCurvature_zero]
    simp [floerEnergyDensity_def, hKs'.self_of_nhds, hKt'.self_of_nhds,
      hamiltonianVectorField_const]
  have h := setIntegral_eq_of_subset_of_forall_sdiff_eq_zero (μ := volume) hD hTD hzero
  have e₁ := integral_add (hE.sub hA) hR
  have e₂ := integral_sub hE hA
  have e₃ := integral_add ((hE.mono_set hTD).sub (hA.mono_set hTD)) (hR.mono_set hTD)
  have e₄ := integral_sub (hE.mono_set hTD) (hA.mono_set hTD)
  simp only [Pi.sub_apply] at e₁ e₃
  linarith

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

open Filter Topology in
/-- A datum `K = K_s ds + K_t dt` on a symplectic vector space with `K_s = 0` and `K_t` independent
of `s` near the line `s = c` has zero curvature along that line. This is the constant-form case of
`TauCeti.SmoothTwoForm.hamiltonianCurvature_eq_zero_of_cylindrical`. -/
theorem hamiltonianCurvature_eq_zero_of_cylindrical (ω : SymplecticForm V)
    {Ks Kt : ℝ × ℝ → V → ℝ} {c : ℝ} (hKs : ∀ᶠ s in 𝓝 c, ∀ t, Ks (s, t) = 0)
    (hKt : ∀ᶠ s in 𝓝 c, ∀ t, Kt (s, t) = Kt (c, t)) (t : ℝ) (x : V) :
    ω.hamiltonianCurvature Ks Kt (c, t) x = 0 := by
  simpa only [hamiltonianCurvature_constSmooth] using
    ω.constSmooth.hamiltonianCurvature_eq_zero_of_cylindrical hKs hKt t x

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
  have hE' : ω.constSmooth.floerEnergyDensity Ks Kt u = ω.floerEnergyDensity Ks Kt u :=
    funext (floerEnergyDensity_constSmooth ω Ks Kt u)
  have hR' : (fun z ↦ ω.constSmooth.hamiltonianCurvature Ks Kt z (u z)) =
      fun z ↦ ω.hamiltonianCurvature Ks Kt z (u z) :=
    funext fun z ↦ hamiltonianCurvature_constSmooth ω Ks Kt z (u z)
  have h :=
    (isNondegenerate_constSmooth ω).setIntegral_floerEnergyDensity_of_forall_notMem_eq_zero hU
    (contMDiffOn_iff_contDiffOn.mpr hu)
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKs))
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKt))
    hC hCU hKsC hKtC hCD
    (hE' ▸ hE) (hR' ▸ hR)
  simpa only [hE', hR', eval₂_constSmooth_mfderiv_stdComplexLine] using h

open MeasureTheory Set SmoothTwoForm in
/-- **Changing the perturbation inside a compact region.** Let `u` and two perturbation data `K`
and `K'` be `C¹` over an open set `U` of the domain, and let `D ⊆ U` be compact. If `K` and `K'`
agree at every point of `U` outside `D`, then the energy plus the integrated curvature over `D` is
the same for both data:

`∫_D E_K(u) + ∫_D R_K(u) = ∫_D E_{K'}(u) + ∫_D R_{K'}(u)`.

This is the constant-form case of
`SmoothTwoForm.IsNondegenerate.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn`;
all four integrands are continuous on `U`, so their integrability over `D` is automatic. -/
theorem setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn (ω : SymplecticForm V)
    {Ks Kt Ks' Kt' : ℝ × ℝ → V → ℝ} {u : ℝ × ℝ → V} {U D : Set (ℝ × ℝ)} (hU : IsOpen U)
    (hu : ContDiffOn ℝ 1 u U) (hKs : ContDiffOn ℝ 1 (uncurry Ks) (U ×ˢ univ))
    (hKt : ContDiffOn ℝ 1 (uncurry Kt) (U ×ˢ univ))
    (hKs' : ContDiffOn ℝ 1 (uncurry Ks') (U ×ˢ univ))
    (hKt' : ContDiffOn ℝ 1 (uncurry Kt') (U ×ˢ univ)) (hD : IsCompact D) (hDU : D ⊆ U)
    (hs : EqOn Ks Ks' (U \ D)) (ht : EqOn Kt Kt' (U \ D)) :
    (∫ z in D, ω.floerEnergyDensity Ks Kt u z) +
        ∫ z in D, ω.hamiltonianCurvature Ks Kt z (u z) =
      (∫ z in D, ω.floerEnergyDensity Ks' Kt' u z) +
        ∫ z in D, ω.hamiltonianCurvature Ks' Kt' z (u z) := by
  -- The energy densities and the curvatures are continuous on `U`, hence integrable over `D`.
  have hint {f : ℝ × ℝ → ℝ} (hf : ContinuousOn f U) : IntegrableOn f D :=
    (hf.mono hDU).integrableOn_compact hD
  have h := IsNondegenerate.setIntegral_floerEnergyDensity_add_hamiltonianCurvature_eq_of_eqOn
    (isNondegenerate_constSmooth ω) hU (contMDiffOn_iff_contDiffOn.mpr hu)
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKs))
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKt))
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKs'))
    (contMDiffOn_prod_modelWithCornersSelf_iff.mpr (contMDiffOn_iff_contDiffOn.mpr hKt'))
    hD hDU hs ht
    (funext (floerEnergyDensity_constSmooth ω Ks Kt u) ▸
      hint (ω.continuousOn_floerEnergyDensity hU hu hKs hKt))
    (by simpa only [hamiltonianCurvature_constSmooth] using
      hint (ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn hKs hKt))
    (funext (floerEnergyDensity_constSmooth ω Ks' Kt' u) ▸
      hint (ω.continuousOn_floerEnergyDensity hU hu hKs' hKt'))
    (by simpa only [hamiltonianCurvature_constSmooth] using
      hint (ω.continuousOn_hamiltonianCurvature_comp hU hu.continuousOn hKs' hKt'))
  simpa only [floerEnergyDensity_constSmooth, hamiltonianCurvature_constSmooth] using h

end TauCeti.SymplecticForm
