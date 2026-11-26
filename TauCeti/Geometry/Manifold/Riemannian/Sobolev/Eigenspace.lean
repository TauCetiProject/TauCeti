/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Regularity

/-!
# Weak eigenfunctions of the Laplacian on a closed manifold

Let `M` be a closed manifold with a Riemannian metric, its Riemannian volume `dV` and the Sobolev
space `H¹(M)` (`TauCeti.Manifold.SobolevH1`) with its Dirichlet form `D`, which extends
`∫ ⟪∇u, ∇v⟫ dV` from smooth functions. The **weak `μ`-eigenspace** of the nonnegative Laplacian
`Δ⁺ = -div grad` is the closed subspace

`{w ∈ H¹(M) | D(w, v) = μ ⟪w, v⟫_{L²} for every v ∈ H¹(M)}`

(`TauCeti.Manifold.SobolevH1.weakEigenspace`), the kernel of the continuous bilinear form
`D - μ ⟪·, ·⟫_{L²}`. It asks for no second derivatives, only for the energy form, and testing
against smooth functions is enough (`mem_weakEigenspace_iff_forall_ofSmooth`). For a `C¹` metric
it is zero unless `μ ≥ 0` (`nonneg_of_mem_weakEigenspace`), since `D` is nonnegative.

When the metric is smooth, weak eigenfunctions are classical ones. By elliptic regularity a weak
eigenfunction is a smooth function `u` with `-Δu = μ u`
(`exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_mul_of_dirichletForm_eq_mul`), and conversely a
smooth eigenfunction is a weak one by Green's identity (`ofSmooth_mem_weakEigenspace_iff`). So the
inclusion of the smooth functions restricts to a linear equivalence

`TauCeti.Manifold.SobolevH1.weakEigenspaceEquiv I M μ :
  eigenspace (smoothLaplaceBeltrami I M) (-μ) ≃ₗ[ℝ] weakEigenspace I M μ`

from the `(-μ)`-eigenspace of the Laplace–Beltrami operator `Δ = div grad` on smooth functions.

## Main results

* `TauCeti.Manifold.SobolevH1.weakEigenspace`: the weak eigenspaces of `Δ⁺` in `H¹(M)`, with
  `mem_weakEigenspace_iff` and `mem_weakEigenspace_iff_forall_ofSmooth`.
* `TauCeti.Manifold.SobolevH1.nonneg_of_mem_weakEigenspace_of_toLp_ne_zero`,
  `TauCeti.Manifold.SobolevH1.nonneg_of_mem_weakEigenspace`: weak eigenvalues are nonnegative.
* `TauCeti.Manifold.SobolevH1.ofSmooth_mem_weakEigenspace_iff`: a smooth function is a weak
  eigenfunction exactly when it is a classical one.
* `TauCeti.Manifold.SobolevH1.weakEigenspaceEquiv`: for a smooth metric, every weak eigenfunction
  is smooth, and the weak eigenspace is the smooth eigenspace.
-/

public section

open Bundle MeasureTheory Module
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

section WeakEigenspace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- The **weak `μ`-eigenspace** of the nonnegative Laplacian `Δ⁺ = -div grad` on `H¹(M)`: the
elements `w` with `D(w, v) = μ ⟪w, v⟫_{L²}` for every `v ∈ H¹(M)`, where `D` is the Dirichlet
form (`TauCeti.Manifold.SobolevH1.mem_weakEigenspace_iff`). -/
def weakEigenspace (μ : ℝ) : Submodule ℝ (SobolevH1 I M) :=
  (dirichletForm (I := I) (M := M) - μ •
    ((innerSL ℝ).bilinearComp (toLp (I := I) (M := M)) toLp :
      SobolevH1 I M →L[ℝ] SobolevH1 I M →L[ℝ] ℝ)).ker

/-- `w ∈ H¹(M)` is a weak `μ`-eigenfunction exactly when `D(w, v) = μ ⟪w, v⟫_{L²}` for every
`v ∈ H¹(M)`. -/
theorem mem_weakEigenspace_iff {μ : ℝ} {w : SobolevH1 I M} :
    w ∈ weakEigenspace I M μ ↔ ∀ v, dirichletForm w v = μ * ⟪toLp w, toLp v⟫_ℝ := by
  simp [weakEigenspace, ContinuousLinearMap.ext_iff, sub_eq_zero]

/-- The weak eigenspaces are closed. -/
theorem isClosed_weakEigenspace (μ : ℝ) :
    IsClosed (weakEigenspace I M μ : Set (SobolevH1 I M)) :=
  ContinuousLinearMap.isClosed_ker _

/-- It suffices to test the weak eigenvalue equation against smooth functions:
`w ∈ H¹(M)` is a weak eigenfunction exactly when `D(w, φ) = μ ∫ w φ dV` for every smooth `φ`. -/
theorem mem_weakEigenspace_iff_forall_ofSmooth {μ : ℝ} {w : SobolevH1 I M} :
    w ∈ weakEigenspace I M μ ↔ ∀ φ : C^∞⟮I, M; ℝ⟯,
      dirichletForm w (ofSmooth φ) = μ * ∫ x, toLp w x * φ x ∂riemannianVolume I M := by
  simp_rw [mem_weakEigenspace_iff, ← inner_toLp_ofSmooth_right]
  refine ⟨fun h φ ↦ h _, fun h v ↦ ?_⟩
  induction v using induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | h φ => exact h φ

/-- **Weak eigenvalues are nonnegative.** If `w ∈ H¹(M)` has nonzero value in `L²(M)` and satisfies
`D(w, v) = μ ⟪w, v⟫_{L²}` for every `v`, then `μ ≥ 0`, since `μ ‖w‖²_{L²} = D(w, w) ≥ 0`. -/
theorem nonneg_of_mem_weakEigenspace_of_toLp_ne_zero {μ : ℝ} {w : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) (hw₀ : toLp w ≠ 0) : 0 ≤ μ := by
  have h := mem_weakEigenspace_iff.1 hw w
  rw [real_inner_self_eq_norm_sq] at h
  have hpos : 0 < ‖toLp w‖ ^ 2 := by positivity
  nlinarith [dirichletForm_self_nonneg w]

end WeakEigenspace

section Regularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

section C1

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] instIsContinuousRiemannianBundleOfContMDiffOne

/-- **Weak eigenvalues are nonnegative.** On a closed manifold with a `C¹` metric, if a nonzero
`w ∈ H¹(M)` satisfies `D(w, v) = μ ⟪w, v⟫_{L²}` for every `v`, then `μ ≥ 0`. -/
theorem nonneg_of_mem_weakEigenspace {μ : ℝ} {w : SobolevH1 I M}
    (hw : w ∈ weakEigenspace I M μ) (hw₀ : w ≠ 0) : 0 ≤ μ :=
  nonneg_of_mem_weakEigenspace_of_toLp_ne_zero hw (toLp_eq_zero_iff.not.2 hw₀)

/-- **Smooth weak eigenfunctions are classical eigenfunctions.** On a closed manifold with a `C¹`
metric, a smooth function `u` lies in the weak `μ`-eigenspace of `Δ⁺` exactly when
`-Δu = μ u` everywhere, where `Δ = div grad`. -/
theorem ofSmooth_mem_weakEigenspace_iff {μ : ℝ} {u : C^∞⟮I, M; ℝ⟯} :
    ofSmooth u ∈ weakEigenspace I M μ ↔ ∀ x, -laplaceBeltrami I u x = μ * u x := by
  have hu (φ : C^∞⟮I, M; ℝ⟯) : ∫ x, toLp (ofSmooth u) x * φ x ∂riemannianVolume I M =
      ∫ x, u x * φ x ∂riemannianVolume I M :=
    integral_congr_ae ((toLp_ofSmooth_ae_eq u).mono fun x hx ↦ congrArg (· * φ x) hx)
  simp_rw [mem_weakEigenspace_iff_forall_ofSmooth, hu, ← integral_const_mul, ← mul_assoc]
  refine ⟨fun h ↦ (eq_ofSmooth_and_neg_laplaceBeltrami_eq_of_dirichletForm_eq
    (continuous_const.mul (map_continuous u)) (toLp_ofSmooth_ae_eq u) h).2, fun h φ ↦ ?_⟩
  -- Green's identity moves `Δ⁺` onto `u`.
  rw [dirichletForm_comm, dirichletForm_ofSmooth_right]
  refine integral_congr_ae ((toLp_ofSmooth_ae_eq φ).mono fun x hx ↦ ?_)
  dsimp only
  rw [hx, h]
  ring

end C1

variable [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

attribute [local instance] instIsContinuousRiemannianBundleOfContMDiffInfty

variable (I M) in
/-- **Weak eigenfunctions are smooth.** On a closed manifold with a smooth metric, the inclusion of
the smooth functions into `H¹(M)` restricts to a linear equivalence from the `(-μ)`-eigenspace of
the Laplace–Beltrami operator `Δ = div grad` on smooth functions onto the weak `μ`-eigenspace of
`Δ⁺ = -Δ`. -/
def weakEigenspaceEquiv (μ : ℝ) :
    End.eigenspace (smoothLaplaceBeltrami I M) (-μ) ≃ₗ[ℝ] weakEigenspace I M μ :=
  LinearEquiv.ofBijective
    (ofSmooth.restrict fun _ hu ↦ ofSmooth_mem_weakEigenspace_iff.2 fun x ↦ by
      rw [mem_eigenspace_smoothLaplaceBeltrami_iff.1 hu x]
      ring)
    ⟨fun _ _ huv ↦ Subtype.ext (ofSmooth_injective (congrArg Subtype.val huv)), fun w ↦ by
      obtain ⟨u, hwu, hu⟩ :=
        exists_eq_ofSmooth_and_neg_laplaceBeltrami_eq_mul_of_dirichletForm_eq_mul
          (mem_weakEigenspace_iff_forall_ofSmooth.1 w.property)
      exact ⟨⟨u, mem_eigenspace_smoothLaplaceBeltrami_iff.2 fun x ↦ by linarith [hu x]⟩,
        Subtype.ext hwu.symm⟩⟩

@[simp]
theorem coe_weakEigenspaceEquiv_apply (μ : ℝ)
    (u : End.eigenspace (smoothLaplaceBeltrami I M) (-μ)) :
    (weakEigenspaceEquiv I M μ u : SobolevH1 I M) = ofSmooth (u : C^∞⟮I, M; ℝ⟯) :=
  (rfl)

/-- **Weak eigenfunctions are smooth.** The smooth eigenfunction corresponding to a weak
eigenfunction `w` under `weakEigenspaceEquiv` is `w` itself, viewed in `H¹(M)`. -/
@[simp]
theorem ofSmooth_weakEigenspaceEquiv_symm_apply (μ : ℝ) (w : weakEigenspace I M μ) :
    ofSmooth ((weakEigenspaceEquiv I M μ).symm w : C^∞⟮I, M; ℝ⟯) = w := by
  rw [← coe_weakEigenspaceEquiv_apply, LinearEquiv.apply_symm_apply]

end Regularity

end TauCeti.Manifold.SobolevH1
