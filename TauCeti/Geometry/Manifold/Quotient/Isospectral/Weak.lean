/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.Isospectral
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenspace

/-!
# Sunada's theorem for the weak eigenspaces

Let a finite group `Q` act on a closed manifold `M` by isometries, and let `K₁`, `K₂` be
almost-conjugate subgroups acting freely, with metrics on the orbit spaces making the orbit
projections local isometries. Then the weak `μ`-eigenspaces
(`TauCeti.Manifold.SobolevH1.weakEigenspace`) in `H¹(M ⧸ K₁)` and `H¹(M ⧸ K₂)` are linearly
equivalent for every `μ` (`Subgroup.AlmostConjugate.nonempty_linearEquiv_weakEigenspace`), so they
have the same dimension (`Subgroup.AlmostConjugate.finrank_weakEigenspace_eq`). This transfers the
smooth version `Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami`
through `TauCeti.Manifold.SobolevH1.weakEigenspaceEquiv` on both quotients.

## Main results

* `Subgroup.AlmostConjugate.nonempty_linearEquiv_weakEigenspace`,
  `Subgroup.AlmostConjugate.finrank_weakEigenspace_eq`: Sunada's theorem for the weak eigenspaces.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Theorem 17, p. 159.
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

/-- **Sunada's theorem** for the weak eigenspaces. Let a finite group `Q` act on a closed manifold
`M` by isometries, and let `K₁`, `K₂` be almost-conjugate subgroups of `Q` acting freely on `M`.
Give the orbit spaces `M ⧸ K₁` and `M ⧸ K₂` smooth metrics for which the orbit projections are
local Riemannian isometries. Then for every `μ` the weak `μ`-eigenspaces of `Δ⁺` in `H¹(M ⧸ K₁)`
and in `H¹(M ⧸ K₂)` are linearly equivalent. -/
theorem nonempty_linearEquiv_weakEigenspace (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    Nonempty (SobolevH1.weakEigenspace I (MulAction.orbitRel.Quotient K₁ M) μ ≃ₗ[ℝ]
      SobolevH1.weakEigenspace I (MulAction.orbitRel.Quotient K₂ M) μ) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami hQ h₁ h₂ (-μ)
  ⟨(SobolevH1.weakEigenspaceEquiv I _ μ).symm ≪≫ₗ e ≪≫ₗ SobolevH1.weakEigenspaceEquiv I _ μ⟩

/-- **Equal multiplicities.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_weakEigenspace`, the weak eigenspaces of `Δ⁺` in
`H¹(M ⧸ K₁)` and in `H¹(M ⧸ K₂)` have the same `finrank`. -/
theorem finrank_weakEigenspace_eq (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    finrank ℝ (SobolevH1.weakEigenspace I (MulAction.orbitRel.Quotient K₁ M) μ) =
      finrank ℝ (SobolevH1.weakEigenspace I (MulAction.orbitRel.Quotient K₂ M) μ) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_weakEigenspace hQ h₁ h₂ μ
  e.finrank_eq

end Subgroup.AlmostConjugate
