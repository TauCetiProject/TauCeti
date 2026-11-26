/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Laplacian
import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Rellich

/-!
# The spectrum of the Laplacian of a closed manifold

Let `M` be a closed manifold with a Riemannian metric, its Riemannian volume `dV`, and the
self-adjoint realization `Δ⁺` of the nonnegative Laplacian `-div grad` on `L²(M)`
(`TauCeti.Manifold.SobolevH1.negLaplacian`). This file describes its spectrum
`(negLaplacian I M).spectrum` and its eigenspaces `ker (Δ⁺ - μ)`.

* **Eigenspaces.** `ker (Δ⁺ - μ)` is the image in `L²(M)` of the weak `μ`-eigenspace
  `TauCeti.Manifold.SobolevH1.weakEigenspace I M μ ⊆ H¹(M)`
  (`TauCeti.Manifold.SobolevH1.ker_subScalar_negLaplacian`). For a `C¹` metric the value map
  `H¹(M) → L²(M)` is injective, so it restricts to a linear equivalence between the two
  (`TauCeti.Manifold.SobolevH1.weakEigenspaceEquivKerSubScalar`).
* **Pure point spectrum.** `Δ⁺` is the operator of the Dirichlet form along the value map, which
  is compact by the Rellich–Kondrachov theorem, so every point of its spectrum is a weak
  eigenvalue (`TauCeti.IsCoercive.mem_spectrum_formOperator_iff`): `μ` lies in the spectrum exactly
  when the weak `μ`-eigenspace is nonzero
  (`TauCeti.Manifold.SobolevH1.mem_spectrum_negLaplacian_iff`). Weak eigenvalues are nonnegative,
  so the spectrum lies in `[0, ∞)` (`TauCeti.Manifold.SobolevH1.spectrum_negLaplacian_subset_Ici`).

So statements about weak eigenfunctions, such as the transplantation of eigenfunctions along
finite coverings or Sunada's theorem, become statements about the spectrum and the eigenspaces of
the self-adjoint operator `Δ⁺`.

## Main results

* `TauCeti.Manifold.SobolevH1.ker_subScalar_negLaplacian`: the eigenspaces of `Δ⁺` are the values
  of the weak eigenspaces.
* `TauCeti.Manifold.SobolevH1.weakEigenspaceEquivKerSubScalar`: for a `C¹` metric, the value map is
  a linear equivalence from the weak `μ`-eigenspace onto `ker (Δ⁺ - μ)`.
* `TauCeti.Manifold.SobolevH1.mem_spectrum_negLaplacian_iff`: the spectrum of `Δ⁺` consists of
  the weak eigenvalues.
* `TauCeti.Manifold.SobolevH1.spectrum_negLaplacian_subset_Ici`: the spectrum of `Δ⁺` is
  nonnegative.

## References

* I. Chavel, *Eigenvalues in Riemannian Geometry*, Academic Press, 1984, Chapter I (the discrete
  spectrum of the Laplacian of a closed manifold).
* M. Reed and B. Simon, *Methods of Modern Mathematical Physics IV: Analysis of Operators*,
  §XIII.14.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I ∞ M]
  [T2Space M] [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]

/-- **The eigenspaces of the Laplacian.** The `μ`-eigenspace `ker (Δ⁺ - μ)` of the self-adjoint
Laplacian on `L²(M)` is the image of the weak `μ`-eigenspace in `H¹(M)` under the value map. -/
theorem ker_subScalar_negLaplacian (μ : ℝ) :
    ((negLaplacian I M).subScalar μ).ker =
      (weakEigenspace I M μ).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap := by
  ext f
  rw [LinearPMap.mem_ker_subScalar_iff, exists_negLaplacian_apply_eq_smul_iff, Submodule.mem_map,
    ContinuousLinearMap.coe_coe]

variable [I.Boundaryless]

/-- **The Laplacian has pure point spectrum.** `μ` lies in the spectrum of the self-adjoint
Laplacian `Δ⁺` on `L²(M)` exactly when the weak `μ`-eigenspace is nonzero. -/
theorem mem_spectrum_negLaplacian_iff {μ : ℝ} :
    μ ∈ (negLaplacian I M).spectrum ↔ weakEigenspace I M μ ≠ ⊥ := by
  simp_rw [negLaplacian_def, isCoercive_innerSL.mem_spectrum_formOperator_iff isCompactOperator_toLp
    denseRange_toLp inner_eq_dirichletForm_add, Submodule.ne_bot_iff, mem_weakEigenspace_iff]
  exact exists_congr fun w ↦ and_comm

/-- **The spectrum of the Laplacian is nonnegative.** Every point of the spectrum of the
self-adjoint Laplacian `Δ⁺` on `L²(M)` is nonnegative. -/
theorem spectrum_negLaplacian_subset_Ici : (negLaplacian I M).spectrum ⊆ Set.Ici 0 := fun μ hμ ↦ by
  obtain ⟨w, hw, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mem_spectrum_negLaplacian_iff.1 hμ)
  -- A weak eigenfunction with zero value is zero: its `H¹` norm is `D(w, w) + ‖J w‖² = 0`.
  refine nonneg_of_mem_weakEigenspace_of_toLp_ne_zero hw fun h ↦ hw₀ ?_
  have hw' := inner_eq_dirichletForm_add w w
  rw [mem_weakEigenspace_iff.1 hw w, h, inner_zero_left, mul_zero, mul_zero, add_zero,
    innerSL_apply_apply] at hw'
  exact inner_self_eq_zero.1 hw'

variable [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

variable (I M) in
/-- For a `C¹` metric, the value map `H¹(M) → L²(M)` restricts to a linear equivalence from the weak
`μ`-eigenspace onto the `μ`-eigenspace `ker (Δ⁺ - μ)` of the self-adjoint Laplacian. -/
def weakEigenspaceEquivKerSubScalar (μ : ℝ) :
    weakEigenspace I M μ ≃ₗ[ℝ] ((negLaplacian I M).subScalar μ).ker :=
  (Submodule.equivMapOfInjective (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap toLp_injective _).trans
    (LinearEquiv.ofEq _ _ (ker_subScalar_negLaplacian μ).symm)

@[simp]
theorem coe_weakEigenspaceEquivKerSubScalar_apply (μ : ℝ) (w : weakEigenspace I M μ) :
    (weakEigenspaceEquivKerSubScalar I M μ w : Lp ℝ 2 (riemannianVolume I M)) = toLp w :=
  (rfl)

@[simp]
theorem toLp_weakEigenspaceEquivKerSubScalar_symm_apply (μ : ℝ)
    (f : ((negLaplacian I M).subScalar μ).ker) :
    toLp ((weakEigenspaceEquivKerSubScalar I M μ).symm f : SobolevH1 I M) = f := by
  rw [← coe_weakEigenspaceEquivKerSubScalar_apply, LinearEquiv.apply_symm_apply]

end TauCeti.Manifold.SobolevH1
