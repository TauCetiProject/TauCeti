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
import TauCeti.Analysis.Calculus.FDeriv.Pi.Basic

/-!
# The operator of an admissible pair

An admissible pair `(f, Γ)` (`TauCeti.IsAdmissiblePair`) on `ℝⁿ`, for `n` the size of the
matrices, defines the operator `F_f(A) = f(λ(A))` on the Hermitian matrices `A` whose decreasingly
sorted eigenvalue vector `λ(A)` lies in `Γ`, with gradient `∇F_f(A)`
(`Matrix.IsHermitian.spectralGradient`). This file transfers the conditions on the pair to the
operator:

* the domain `{A | λ(A) ∈ Γ}` is open (`Matrix.isOpen_setOf_eigenvalues₀_mem`, as `Γ` is open),
  and `F_f` is `C¹` on it (Lewis's theorem,
  `Matrix.contDiffOn_spectralFunction_iff`), applied to the symmetric extension of `f` by `0`
  off `Γ`;
* `∇F_f(A)` is positive definite (ellipticity);
* Euler's identity `Re tr(∇F_f(A) A) = F_f(A)`, and `∇ log F_f = ∇F_f / F_f`;
* `F_f` is concave on its domain when the pair is concave;
* the structural condition `∏ⱼ ∂ⱼ f ≥ γ` on `Γ` holds if and only if `det ∇F_f(A) ≥ γ` for every
  Hermitian `A` with `λ(A) ∈ Γ`, since `det ∇F_f(A) = ∏ⱼ ∂ⱼ f(λ(A))` and the product of the
  partial derivatives of a symmetric function is invariant under permutations of the point.

## Main results

* `TauCeti.IsAdmissiblePair.contDiffOn_spectralFunction`: `F_f` is `C¹` on `{A | λ(A) ∈ Γ}`.
* `TauCeti.IsAdmissiblePair.posDef_spectralGradient`: `∇F_f(A)` is positive definite.
* `TauCeti.IsAdmissiblePair.re_trace_spectralGradient_mul_self`: Euler's identity.
* `TauCeti.IsAdmissiblePair.spectralGradient_log`: `∇ log F_f = ∇F_f / F_f`.
* `TauCeti.IsAdmissiblePair.concaveOn_spectralFunction`: concavity for a concave pair.
* `TauCeti.IsAdmissiblePair.hasStructuralConstant_iff_le_re_det_spectralGradient`: the structural
  condition through `det ∇F_f`.

## References

* B. Guo, D. H. Phong and F. Tong, *On L∞ estimates for complex Monge–Ampère equations*,
  Ann. of Math. 198 (2023), (1.4) for the structural condition.
-/

public section

noncomputable section

open Finset
open scoped Matrix.Norms.Frobenius ComplexOrder

variable {𝕜 ι : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
  {Γ : Set (Fin (Fintype.card ι) → ℝ)} {f : (Fin (Fintype.card ι) → ℝ) → ℝ}

namespace TauCeti.IsAdmissiblePair

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

/-- **The gradient of `log F_f`** for an admissible pair: `∇ log F_f(A) = ∇F_f(A) / F_f(A)` at
every Hermitian `A` with `λ(A) ∈ Γ`. The case of interest is `F_f(A) > 0`, which holds for
instance whenever `A` is positive definite (`TauCeti.IsAdmissiblePair.pos_of_forall_pos`). -/
theorem spectralGradient_log (h : IsAdmissiblePair Γ f) {A : Matrix ι ι 𝕜} (hA : A.IsHermitian)
    (hAΓ : hA.eigenvalues₀ ∈ Γ) :
    hA.spectralGradient (fun μ ↦ Real.log (f μ)) =
      ((f hA.eigenvalues₀)⁻¹ : 𝕜) • hA.spectralGradient f :=
  hA.spectralGradient_log (h.differentiableAt hAΓ)

/-- **Concavity of the operator** of a concave admissible pair on the Hermitian matrices `A` with
`λ(A) ∈ Γ`. -/
theorem concaveOn_spectralFunction (h : IsAdmissiblePair Γ f) (hf : ConcaveOn ℝ Γ f) :
    ConcaveOn ℝ
      {A : selfAdjoint.submodule ℝ (Matrix ι ι 𝕜) | A.property.isHermitian.eigenvalues₀ ∈ Γ}
      fun A ↦ f A.property.isHermitian.eigenvalues₀ :=
  Matrix.concaveOn_spectralFunction (fun σ _ hμ ↦ h.isAdmissibleCone.comp_perm_mem σ hμ)
    (fun σ _ hμ ↦ h.apply_comp_perm σ hμ) hf

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
  -- `f` is symmetric near `μ ∈ Γ`, so the product of its partials is the same at `μ ∘ σ`.
  have hsymm : (fun ν ↦ f (ν ∘ Tuple.sortDesc μ)) =ᶠ[nhds μ] f := by
    filter_upwards [h.isAdmissibleCone.isOpen.mem_nhds hμ] with ν hν
    exact h.apply_comp_perm _ hν
  rwa [hB, prod_fderiv_comp_perm_apply_single hsymm] at this

end TauCeti.IsAdmissiblePair
