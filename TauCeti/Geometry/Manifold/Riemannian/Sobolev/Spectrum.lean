/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.Resolvent.PointSpectrum
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Laplacian

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
* **Pure point spectrum.** `Δ⁺` has compact resolvent, so every point of its spectrum is an
  eigenvalue (`LinearPMap.HasCompactResolvent.mem_spectrum_iff_ker_subScalar_ne_bot`): `μ` lies in
  the spectrum exactly when the weak `μ`-eigenspace is nonzero
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

variable [I.Boundaryless] [IsContMDiffRiemannianBundle I 1 E (fun x : M ↦ TangentSpace I x)]

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

/-- **The Laplacian has pure point spectrum.** For a `C¹` metric, `μ` lies in the spectrum of the
self-adjoint Laplacian `Δ⁺` on `L²(M)` exactly when the weak `μ`-eigenspace is nonzero. -/
theorem mem_spectrum_negLaplacian_iff {μ : ℝ} :
    μ ∈ (negLaplacian I M).spectrum ↔ weakEigenspace I M μ ≠ ⊥ := by
  rw [hasCompactResolvent_negLaplacian.mem_spectrum_iff_ker_subScalar_ne_bot,
    ← Submodule.nontrivial_iff_ne_bot, ← Submodule.nontrivial_iff_ne_bot]
  exact (weakEigenspaceEquivKerSubScalar I M μ).toEquiv.nontrivial_congr.symm

/-- **The spectrum of the Laplacian is nonnegative.** For a `C¹` metric, every point of the spectrum
of the self-adjoint Laplacian `Δ⁺` on `L²(M)` is nonnegative. -/
theorem spectrum_negLaplacian_subset_Ici : (negLaplacian I M).spectrum ⊆ Set.Ici 0 := fun μ hμ ↦ by
  obtain ⟨w, hw, hw₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (mem_spectrum_negLaplacian_iff.1 hμ)
  exact nonneg_of_mem_weakEigenspace hw hw₀

end TauCeti.Manifold.SobolevH1
