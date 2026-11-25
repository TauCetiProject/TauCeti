/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.FullyNonlinear.AdmissiblePair
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralGradient
public import TauCeti.Analysis.Matrix.Eigenvalues.SpectralFunction.ContDiff
public import TauCeti.Analysis.Convex.SpectralFunction
import TauCeti.Analysis.Matrix.Eigenvalues.Continuous

/-!
# The operator of an admissible pair

An admissible pair `(f, Γ)` (`TauCeti.IsAdmissiblePair`) on `ℝⁿ`, for `n` the size of the
matrices, defines the operator `F_f(A) = f(λ(A))` on the Hermitian matrices `A` whose decreasingly
sorted eigenvalue vector `λ(A)` lies in `Γ`, with gradient `∇F_f(A)`
(`Matrix.IsHermitian.spectralGradient`). This file transfers the conditions on the pair to the
operator:

* the domain `{A | λ(A) ∈ Γ}` is open, and `F_f` is `C¹` on it (Lewis's theorem,
  `Matrix.contDiffOn_spectralFunction_iff`), applied to the symmetric extension of `f` by `0`
  off `Γ`;
* `∇F_f(A)` is positive definite (ellipticity);
* Euler's identity `Re tr(∇F_f(A) A) = F_f(A)`;
* `F_f` is concave on its domain when the pair is concave;
* the structural condition `∏ⱼ ∂ⱼ f ≥ γ` on `Γ` holds if and only if `det ∇F_f(A) ≥ γ` for every
  Hermitian `A` with `λ(A) ∈ Γ`, since `det ∇F_f(A) = ∏ⱼ ∂ⱼ f(λ(A))` and the product of the
  partial derivatives of a symmetric function is invariant under permutations of the point.

## Main results

* `TauCeti.IsAdmissiblePair.contDiffOn_spectralFunction`: `F_f` is `C¹` on `{A | λ(A) ∈ Γ}`.
* `TauCeti.IsAdmissiblePair.posDef_spectralGradient`: `∇F_f(A)` is positive definite.
* `TauCeti.IsAdmissiblePair.re_trace_spectralGradient_mul_self`: Euler's identity.
* `TauCeti.IsAdmissiblePair.concaveOn_spectralFunction`: concavity for a concave pair.
* `TauCeti.IsAdmissiblePair.fderiv_comp_perm_apply_single`: the partial derivatives of `f`
  permute with the point.
* `TauCeti.IsAdmissiblePair.hasStructuralConstant_iff_le_re_det_spectralGradient`: the structural
  condition through `det ∇F_f`.

## References

* `TauCetiRoadmap/ComplexHessianEquations/README.md`, §2.4, the structural condition and the API.
-/

public section

noncomputable section

open Finset
open scoped Matrix.Norms.Frobenius ComplexOrder

namespace TauCeti.IsAdmissiblePair

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {Γ : Set (Fin (Fintype.card ι) → ℝ)} {f : (Fin (Fintype.card ι) → ℝ) → ℝ}

/-- The domain `{A | λ(A) ∈ Γ}` of the operator of an admissible pair is open. -/
theorem isOpen_setOf_eigenvalues₀_mem (h : IsAdmissiblePair Γ f) :
    IsOpen {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) |
      B.property.isHermitian.eigenvalues₀ ∈ Γ} :=
  h.isAdmissibleCone.isOpen.preimage Matrix.continuous_eigenvalues₀_selfAdjoint

/-- **The operator of an admissible pair is `C¹`** on the Hermitian matrices `A` with
`λ(A) ∈ Γ`. -/
theorem contDiffOn_spectralFunction (h : IsAdmissiblePair Γ f) :
    ContDiffOn ℝ 1 (fun B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) ↦
      f B.property.isHermitian.eigenvalues₀)
      {B : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | B.property.isHermitian.eigenvalues₀ ∈ Γ} := by
  classical
  -- The extension of `f` by `0` off `Γ` is symmetric on all of `ℝⁿ`.
  set g : (Fin (Fintype.card ι) → ℝ) → ℝ := fun μ ↦ if μ ∈ Γ then f μ else 0 with hg_def
  have hg (σ : Equiv.Perm (Fin (Fintype.card ι))) (μ : Fin (Fintype.card ι) → ℝ) :
      g (μ ∘ σ) = g μ := by
    by_cases hμ : μ ∈ Γ
    · simp [hg_def, hμ, h.isAdmissibleCone.comp_perm_mem σ hμ, h.apply_comp_perm σ hμ]
    · have hμσ : μ ∘ σ ∉ Γ := fun h' ↦ hμ (by
        simpa [Function.comp_assoc] using h.isAdmissibleCone.comp_perm_mem σ.symm h')
      simp [hg_def, hμ, hμσ]
  have hgC : ContDiffOn ℝ 1 g Γ := h.contDiffOn.congr fun μ hμ ↦ by simp [hg_def, hμ]
  exact ((Matrix.contDiffOn_spectralFunction_iff hg h.isAdmissibleCone.isOpen
    fun σ μ hμ ↦ h.isAdmissibleCone.comp_perm_mem σ hμ).2 hgC).congr fun B hB ↦ by
      simp only [Set.mem_ofPred_eq] at hB
      simp [hg_def, hB]

/-- **Ellipticity of the operator**: the gradient `∇F_f(A)` of the operator of an admissible pair
is positive definite at every Hermitian `A` with `λ(A) ∈ Γ`. -/
theorem posDef_spectralGradient (h : IsAdmissiblePair Γ f) {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hAΓ : hA.eigenvalues₀ ∈ Γ) : (hA.spectralGradient f).PosDef :=
  hA.posDef_spectralGradient (h.fderiv_single_pos hAΓ)

/-- **Euler's identity for the operator** of an admissible pair:
`Re tr(∇F_f(A) A) = F_f(A)` for Hermitian `A` with `λ(A) ∈ Γ`. -/
theorem re_trace_spectralGradient_mul_self (h : IsAdmissiblePair Γ f) {A : Matrix ι ι 𝕜}
    (hA : A.IsHermitian) (hAΓ : hA.eigenvalues₀ ∈ Γ) :
    RCLike.re (hA.spectralGradient f * A).trace = f hA.eigenvalues₀ :=
  hA.re_trace_spectralGradient_mul_self_of_homogeneous (h.differentiableAt hAΓ)
    fun _ ht ↦ h.apply_smul ht hAΓ

/-- **Concavity of the operator** of a concave admissible pair on the Hermitian matrices `A` with
`λ(A) ∈ Γ`. -/
theorem concaveOn_spectralFunction (h : IsAdmissiblePair Γ f) (hf : ConcaveOn ℝ Γ f) :
    ConcaveOn ℝ
      {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | A.property.isHermitian.eigenvalues₀ ∈ Γ}
      fun A ↦ f A.property.isHermitian.eigenvalues₀ :=
  Matrix.concaveOn_spectralFunction (fun σ _ hμ ↦ h.isAdmissibleCone.comp_perm_mem σ hμ)
    (fun σ _ hμ ↦ h.apply_comp_perm σ hμ) hf

omit [DecidableEq ι] in
/-- **The partial derivatives of a symmetric function permute with the point**: for an admissible
pair, `∂ⱼ f(μ ∘ τ) = ∂_{τ j} f(μ)` at every `μ ∈ Γ`. -/
theorem fderiv_comp_perm_apply_single (h : IsAdmissiblePair Γ f) {μ : Fin (Fintype.card ι) → ℝ}
    (hμ : μ ∈ Γ) (τ : Equiv.Perm (Fin (Fintype.card ι))) (j : Fin (Fintype.card ι)) :
    fderiv ℝ f (μ ∘ τ) (Pi.single j 1) = fderiv ℝ f μ (Pi.single (τ j) 1) := by
  set L : (Fin (Fintype.card ι) → ℝ) →L[ℝ] Fin (Fintype.card ι) → ℝ :=
    ContinuousLinearMap.pi fun i ↦ ContinuousLinearMap.proj (τ i)
  have hL (ν : Fin (Fintype.card ι) → ℝ) : L ν = ν ∘ τ := rfl
  have hcomp : HasFDerivAt (fun ν ↦ f (L ν)) ((fderiv ℝ f (μ ∘ τ)).comp L) μ :=
    (h.differentiableAt (h.isAdmissibleCone.comp_perm_mem τ hμ)).hasFDerivAt.comp μ
      L.hasFDerivAt
  have heq : (fun ν ↦ f (L ν)) =ᶠ[nhds μ] f := by
    filter_upwards [h.isAdmissibleCone.isOpen.mem_nhds hμ] with ν hν
    exact h.apply_comp_perm τ hν
  have hsingle : L (Pi.single (τ j) 1) = Pi.single j 1 := by
    rw [hL]
    funext i
    simp [Pi.single_apply, τ.injective.eq_iff]
  rw [(hcomp.congr_of_eventuallyEq heq.symm).fderiv, ContinuousLinearMap.comp_apply, hsingle]

omit [DecidableEq ι] in
/-- The product of the partial derivatives of `f` is invariant under permutations of the point. -/
theorem prod_fderiv_comp_perm_apply_single (h : IsAdmissiblePair Γ f)
    {μ : Fin (Fintype.card ι) → ℝ} (hμ : μ ∈ Γ) (τ : Equiv.Perm (Fin (Fintype.card ι))) :
    ∏ j, fderiv ℝ f (μ ∘ τ) (Pi.single j 1) = ∏ j, fderiv ℝ f μ (Pi.single j 1) := by
  simp_rw [h.fderiv_comp_perm_apply_single hμ τ]
  exact Equiv.prod_comp τ fun j ↦ fderiv ℝ f μ (Pi.single j 1)

/-- **The structural condition through the gradient of the operator** (Guo–Phong–Tong (1.4)):
an admissible pair has structural constant `γ` if and only if `det ∇F_f(A) ≥ γ` for every
Hermitian `A` with `λ(A) ∈ Γ`. -/
theorem hasStructuralConstant_iff_le_re_det_spectralGradient (h : IsAdmissiblePair Γ f)
    {γ : ℝ} : HasStructuralConstant Γ f γ ↔
      ∀ (A : Matrix ι ι 𝕜) (hA : A.IsHermitian), hA.eigenvalues₀ ∈ Γ →
        γ ≤ RCLike.re (hA.spectralGradient f).det := by
  simp_rw [Matrix.IsHermitian.det_spectralGradient, RCLike.ofReal_re]
  refine ⟨fun hs A hA hAΓ ↦ hs.le_prod_fderiv_single hAΓ, fun H ↦ ⟨fun {μ} hμ ↦ ?_⟩⟩
  -- Evaluate at the diagonal matrix `diag(μ)`, whose sorted eigenvalues are a permutation of `μ`.
  set B := Matrix.conjDiagonalSelfAdjoint (1 : Matrix ι ι 𝕜) μ
  have hB : B.property.isHermitian.eigenvalues₀ = μ ∘ Tuple.sortDesc μ :=
    Matrix.eigenvalues₀_conjDiagonalSelfAdjoint (one_mem _) μ
  have := H B B.property.isHermitian (by rw [hB]; exact h.isAdmissibleCone.comp_perm_mem _ hμ)
  rwa [hB, h.prod_fderiv_comp_perm_apply_single hμ] at this

end TauCeti.IsAdmissiblePair
