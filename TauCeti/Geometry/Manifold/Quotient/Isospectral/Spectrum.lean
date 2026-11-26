/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Isospectral.Weak
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Spectrum

/-!
# Sunada's theorem for the self-adjoint Laplacian

Let a finite group `Q` act on a closed manifold `M` by isometries, and let `K₁`, `K₂` be
almost-conjugate subgroups acting freely, with metrics on the orbit spaces making the orbit
projections local isometries. **Sunada's theorem** says that the Laplacians of `M ⧸ K₁` and
`M ⧸ K₂` are isospectral with multiplicities. This file states it for the self-adjoint
realizations `Δ⁺` of the nonnegative Laplacian `-div grad` on `L²(M ⧸ K₁)` and `L²(M ⧸ K₂)`
(`TauCeti.Manifold.SobolevH1.negLaplacian`):

* the two operators have the same spectrum
  (`Subgroup.AlmostConjugate.spectrum_negLaplacian_eq`);
* for every `μ`, their eigenspaces `ker (Δ⁺ - μ)` are linearly equivalent
  (`Subgroup.AlmostConjugate.nonempty_linearEquiv_ker_subScalar_negLaplacian`), so they have the
  same dimension (`Subgroup.AlmostConjugate.finrank_ker_subScalar_negLaplacian_eq`).

The eigenspaces of `Δ⁺` are the values in `L²` of the weak eigenspaces in `H¹`
(`TauCeti.Manifold.SobolevH1.weakEigenspaceEquivKerSubScalar`), which Sunada's theorem for the weak
eigenspaces identifies on the two quotients
(`Subgroup.AlmostConjugate.nonempty_linearEquiv_weakEigenspace`). Since `Δ⁺` has compact
resolvent, its spectrum consists of the eigenvalues
(`TauCeti.Manifold.SobolevH1.mem_spectrum_negLaplacian_iff`), so equal eigenspaces give equal
spectra.

## Main results

* `Subgroup.AlmostConjugate.spectrum_negLaplacian_eq`: the self-adjoint Laplacians of the two
  quotients have the same spectrum.
* `Subgroup.AlmostConjugate.nonempty_linearEquiv_ker_subScalar_negLaplacian`,
  `Subgroup.AlmostConjugate.finrank_ker_subScalar_negLaplacian_eq`: their eigenspaces are linearly
  equivalent, with the same dimension.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité I*, Math. Ann. **292** (1992), §II, Theorem 17.
-/

public section

open Bundle MeasureTheory Module
open scoped ContDiff Manifold

noncomputable section

namespace Subgroup.AlmostConjugate

open TauCeti TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  {Q : Type} [Group Q] [Finite Q] [MulAction Q M] [ContMDiffConstSMul I ∞ Q M]
  [ContinuousConstSMul Q M] [T2Space M] [LocallyCompactSpace M]
  {K₁ K₂ : Subgroup Q} [IsCancelSMul K₁ M] [IsCancelSMul K₂ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [MeasurableSpace (MulAction.orbitRel.Quotient K₁ M)]
  [BorelSpace (MulAction.orbitRel.Quotient K₁ M)]
  [RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x)]
  [MeasurableSpace (MulAction.orbitRel.Quotient K₂ M)]
  [BorelSpace (MulAction.orbitRel.Quotient K₂ M)]
  [RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x)]

attribute [local instance] SobolevH1.instIsContinuousRiemannianBundleOfContMDiffInfty

/-- **Sunada's theorem** for the eigenspaces of the self-adjoint Laplacian. Let a finite group `Q`
act on a closed manifold `M` by isometries, and let `K₁`, `K₂` be almost-conjugate subgroups of `Q`
acting freely on `M`. Give the orbit spaces `M ⧸ K₁` and `M ⧸ K₂` smooth metrics for which the
orbit projections are local Riemannian isometries. Then for every `μ` the eigenspaces
`ker (Δ⁺ - μ)` of the self-adjoint Laplacians on `L²(M ⧸ K₁)` and on `L²(M ⧸ K₂)` are linearly
equivalent. -/
theorem nonempty_linearEquiv_ker_subScalar_negLaplacian (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    Nonempty
      (((SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₁ M)).subScalar μ).ker ≃ₗ[ℝ]
        ((SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₂ M)).subScalar μ).ker) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_weakEigenspace hQ h₁ h₂ μ
  ⟨(SobolevH1.weakEigenspaceEquivKerSubScalar I _ μ).symm ≪≫ₗ e ≪≫ₗ
    SobolevH1.weakEigenspaceEquivKerSubScalar I _ μ⟩

/-- **Equal multiplicities.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_ker_subScalar_negLaplacian`, the eigenspaces
`ker (Δ⁺ - μ)` of the self-adjoint Laplacians on `L²(M ⧸ K₁)` and on `L²(M ⧸ K₂)` have the same
`finrank`. -/
theorem finrank_ker_subScalar_negLaplacian_eq (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    finrank ℝ ((SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₁ M)).subScalar μ).ker =
      finrank ℝ ((SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₂ M)).subScalar μ).ker :=
  let ⟨e⟩ := h.nonempty_linearEquiv_ker_subScalar_negLaplacian hQ h₁ h₂ μ
  e.finrank_eq

/-- **Isospectrality.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_ker_subScalar_negLaplacian`, the self-adjoint
Laplacians on `L²(M ⧸ K₁)` and on `L²(M ⧸ K₂)` have the same spectrum. -/
theorem spectrum_negLaplacian_eq (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) :
    (SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₁ M)).spectrum =
      (SobolevH1.negLaplacian I (MulAction.orbitRel.Quotient K₂ M)).spectrum := by
  ext μ
  obtain ⟨e⟩ := h.nonempty_linearEquiv_weakEigenspace hQ h₁ h₂ μ
  rw [SobolevH1.mem_spectrum_negLaplacian_iff, SobolevH1.mem_spectrum_negLaplacian_iff,
    ← Submodule.nontrivial_iff_ne_bot, ← Submodule.nontrivial_iff_ne_bot]
  exact e.toEquiv.nontrivial_congr

end Subgroup.AlmostConjugate
