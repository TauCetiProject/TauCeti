/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DifferentialOperator.LaplaceType
public import TauCeti.Geometry.Manifold.Quotient.Sunada
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Descent

/-!
# Isospectral quotients of a Riemannian manifold

Let a finite group `Q` act on a Riemannian manifold `M` by isometries, and let `K₁`, `K₂` be
almost-conjugate subgroups of `Q` (subgroups meeting every conjugacy class of `Q` in the same
number of elements) acting freely on `M`. Give the orbit spaces `M ⧸ K₁` and `M ⧸ K₂` the quotient
metrics, the metrics for which the orbit projections `π₁` and `π₂` are local Riemannian
isometries. **Sunada's theorem** says that the Laplace–Beltrami operators of `M ⧸ K₁` and
`M ⧸ K₂` have the same eigenvalues with the same multiplicities. Here this is proved for their
smooth eigenfunctions: for every `μ`, the `μ`-eigenspaces of the Laplace–Beltrami operators on
the smooth functions of `M ⧸ K₁` and of `M ⧸ K₂` are linearly equivalent.

The proof applies Sunada's theorem for operators on smooth functions intertwined by pullback
(`Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_of_intertwine`) to the Laplacians
`Δ_M`, `Δ₁` and `Δ₂`. Its two hypotheses are naturality properties of the Laplacian under local
isometries (`TauCeti.IsLocalRiemannianIsometry.smoothLaplaceBeltrami_comp`):

* since `Q` acts by isometries, `Δ_M` commutes with the action `u ↦ u ∘ q⁻¹` of `Q` on smooth
  functions (`TauCeti.commute_smoothLaplaceBeltrami_smoothFunctionRep`);
* since the orbit projections are local isometries, `Δ_M (u ∘ πᵢ) = (Δᵢ u) ∘ πᵢ` for every
  smooth function `u` on `M ⧸ Kᵢ`.

On a compact manifold every `L²` eigenfunction of the Laplacian is smooth by elliptic
regularity, so there these smooth eigenspaces are the eigenspaces of the self-adjoint Laplacian;
that comparison is not made here.

The quotient metrics exist and are unique (`Bundle.ContMDiffRiemannianMetric.quotient`,
`Bundle.ContMDiffRiemannianMetric.pullback_eq_iff_eq_quotient`). The theorem is stated both for
arbitrary metrics on `M ⧸ Kᵢ` making the projections local isometries and for these quotient
metrics.

## Main results

* `TauCeti.commute_smoothLaplaceBeltrami_smoothFunctionRep`: the Laplace–Beltrami operator
  commutes with an action by isometries.
* `Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami`: **Sunada's
  theorem** for the Laplace–Beltrami operators, for metrics on the orbit spaces making the orbit
  projections local Riemannian isometries.
* `Subgroup.AlmostConjugate.hasEigenvalue_smoothLaplaceBeltrami_iff`,
  `Subgroup.AlmostConjugate.finrank_eigenspace_smoothLaplaceBeltrami_eq`: the two Laplacians have
  the same eigenvalues, with eigenspaces of the same `finrank`.
* `Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami_quotient`:
  the same for the quotient metrics.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Theorem 17, p. 159.
-/

public section

open Bundle Module
open scoped ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- If a group `G` acts on `M` by isometries, the Laplace–Beltrami operator commutes with the
action `u ↦ u ∘ g⁻¹` of `G` on smooth functions (`TauCeti.smoothFunctionRep`). -/
theorem commute_smoothLaplaceBeltrami_smoothFunctionRep {G : Type*} [Group G] [MulAction G M]
    [ContMDiffConstSMul I ∞ G M] (hG : ∀ g : G, IsLocalRiemannianIsometry I I (g • · : M → M))
    (g : G) : Commute (smoothLaplaceBeltrami I M) (smoothFunctionRep ℝ I M ℝ ∞ G g) :=
  LinearMap.ext fun u ↦ by
    have hu (v : C^∞⟮I, M; ℝ⟯) : smoothFunctionRep ℝ I M ℝ ∞ G g v =
        v.comp ⟨(g⁻¹ • ·), contMDiff_const_smul g⁻¹⟩ :=
      ContMDiffMap.ext fun y ↦ smoothFunctionRep_apply_apply g v y
    rw [mul_apply_eq_comp, mul_apply_eq_comp, hu, hu]
    exact (hG g⁻¹).smoothLaplaceBeltrami_comp u

end TauCeti

namespace Subgroup.AlmostConjugate

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {Q : Type} [Group Q] [Finite Q] [MulAction Q M] [ContMDiffConstSMul I ∞ Q M]
  [ContinuousConstSMul Q M] [T2Space M] [LocallyCompactSpace M]
  {K₁ K₂ : Subgroup Q} [IsCancelSMul K₁ M] [IsCancelSMul K₂ M]

section LocalIsometry

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  [RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x)]
  [RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x)]

/-- **Sunada's theorem** for the Laplace–Beltrami operators. Let a finite group `Q` act on `M` by
isometries, and let `K₁`, `K₂` be almost-conjugate subgroups of `Q` acting freely on `M`. Give the
orbit spaces `M ⧸ K₁` and `M ⧸ K₂` metrics for which the orbit projections are local Riemannian
isometries. Then for every `μ` the `μ`-eigenspaces of the Laplace–Beltrami operators on the smooth
functions of `M ⧸ K₁` and of `M ⧸ K₂` are linearly equivalent. -/
theorem nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    Nonempty
      (End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₁ M)) μ ≃ₗ[ℝ]
        End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₂ M)) μ) := by
  rw [← coe_smoothQuotientMk (I := I) (n := ∞) (G := K₁)] at h₁
  rw [← coe_smoothQuotientMk (I := I) (n := ∞) (G := K₂)] at h₂
  exact h.nonempty_linearEquiv_eigenspace_of_intertwine
    (commute_smoothLaplaceBeltrami_smoothFunctionRep hQ) h₁.smoothLaplaceBeltrami_comp
    h₂.smoothLaplaceBeltrami_comp μ

/-- **Isospectrality.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami`, the
Laplace–Beltrami operators on the smooth functions of `M ⧸ K₁` and of `M ⧸ K₂` have the same
eigenvalues. -/
theorem hasEigenvalue_smoothLaplaceBeltrami_iff (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    End.HasEigenvalue (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₁ M)) μ ↔
      End.HasEigenvalue (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₂ M)) μ := by
  obtain ⟨e⟩ := h.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami hQ h₁ h₂ μ
  rw [End.hasEigenvalue_iff, End.hasEigenvalue_iff, ← Submodule.nontrivial_iff_ne_bot,
    ← Submodule.nontrivial_iff_ne_bot]
  exact e.toEquiv.nontrivial_congr

/-- **Equal multiplicities.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami`, the eigenspaces
of the Laplace–Beltrami operators on the smooth functions of `M ⧸ K₁` and of `M ⧸ K₂` have the
same `finrank`. -/
theorem finrank_eigenspace_smoothLaplaceBeltrami_eq (h : K₁.AlmostConjugate K₂)
    (hQ : ∀ q : Q, IsLocalRiemannianIsometry I I (q • · : M → M))
    (h₁ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₁ M)))
    (h₂ : IsLocalRiemannianIsometry I I (Quotient.mk (MulAction.orbitRel K₂ M))) (μ : ℝ) :
    finrank ℝ (End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₁ M)) μ) =
      finrank ℝ (End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₂ M)) μ) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami hQ h₁ h₂ μ
  e.finrank_eq

end LocalIsometry

/-- **Sunada's theorem** for the quotient metrics. Let `g` be a smooth Riemannian metric on `M`
invariant under a finite group `Q` acting on `M`, and let `K₁`, `K₂` be almost-conjugate subgroups
of `Q` acting freely on `M`. Give the orbit spaces `M ⧸ K₁` and `M ⧸ K₂` the metrics descended
from `g` (`Bundle.ContMDiffRiemannianMetric.quotient`). Then for every `μ` the `μ`-eigenspaces of
the Laplace–Beltrami operators on the smooth functions of `M ⧸ K₁` and of `M ⧸ K₂` are linearly
equivalent. -/
theorem nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami_quotient
    (h : K₁.AlmostConjugate K₂) (g : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x))
    (hg : ∀ (q : Q) (x : M) (v w : TangentSpace I x),
      g.inner (q • x) (mfderiv I I (q • ·) x v) (mfderiv I I (q • ·) x w) = g.inner x v w)
    (μ : ℝ) :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x) :=
      ⟨(g.quotient fun (a : K₁) ↦ hg a).toRiemannianMetric⟩
    letI : RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x) :=
      ⟨(g.quotient fun (a : K₂) ↦ hg a).toRiemannianMetric⟩
    Nonempty
      (End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₁ M)) μ ≃ₗ[ℝ]
        End.eigenspace (smoothLaplaceBeltrami I (MulAction.orbitRel.Quotient K₂ M)) μ) := by
  let : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let : RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₁ M ↦ TangentSpace I x) :=
    ⟨(g.quotient fun (a : K₁) ↦ hg a).toRiemannianMetric⟩
  let : RiemannianBundle (fun x : MulAction.orbitRel.Quotient K₂ M ↦ TangentSpace I x) :=
    ⟨(g.quotient fun (a : K₂) ↦ hg a).toRiemannianMetric⟩
  -- Each `q • ·` is a local Riemannian isometry, and so are the orbit projections onto the
  -- descended metrics.
  exact h.nonempty_linearEquiv_eigenspace_smoothLaplaceBeltrami
    (fun q ↦ g.isLocalRiemannianIsometry_smul q (hg q))
    (g.isLocalRiemannianIsometry_quotient fun (a : K₁) ↦ hg a)
    (g.isLocalRiemannianIsometry_quotient fun (a : K₂) ↦ hg a) μ

end Subgroup.AlmostConjugate
