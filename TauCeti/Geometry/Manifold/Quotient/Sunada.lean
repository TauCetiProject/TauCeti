/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Quotient.SmoothFunctions
public import TauCeti.RepresentationTheory.Induction.AlmostConjugate

/-!
# Sunada's theorem for smooth functions on orbit spaces

Let a finite group `Q` act on a manifold `M` by `C^n` maps, and let `K₁`, `K₂` be almost-conjugate
subgroups of `Q` (subgroups meeting every conjugacy class of `Q` in the same number of elements),
each acting freely on `M`. Over a scalar field `𝕜` of characteristic zero, Sunada's argument shows
that operators on the `C^n` maps on `M ⧸ K₁` and on `M ⧸ K₂` intertwined by pullback with one
operator `T` commuting with `Q` have linearly equivalent eigenspaces
(`Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_of_intertwine`), and in particular
eigenspaces of the same `finrank`
(`Subgroup.AlmostConjugate.finrank_eigenspace_eq_of_intertwine`). Each eigenspace on `M ⧸ Kᵢ` is
identified with the `Kᵢ`-invariant vectors of the corresponding eigenspace of `T`
(`TauCeti.eigenspaceEquivInvariantsInfEigenspace`), and the representation theory, through
Frobenius reciprocity, is
`Subgroup.AlmostConjugate.nonempty_linearEquiv_invariants_inf_eigenspace`. That result needs the
scalar field, the group and the representation to share one universe, so here `𝕜`, `M`, `F` and
`Q` all live in one universe `Type u`.

In Sunada's construction of isospectral manifolds, `T` and `S₁`, `S₂` are the Laplacians of a
`Q`-invariant Riemannian metric on `M` and of the quotient metrics; neither those operators nor
their intertwining is constructed here.

## Main results

* `Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_of_intertwine`: **Sunada's theorem**
  for operators on smooth functions intertwined by pullback.
* `Subgroup.AlmostConjugate.finrank_eigenspace_eq_of_intertwine`: the eigenspaces have the same
  `finrank`.

## References

* T. Sunada, *Riemannian coverings and isospectral manifolds*, Ann. of Math. **121** (1985),
  169–186.
* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Theorem 17, p. 159.
-/

public section

open Module
open scoped ContDiff Manifold

namespace Subgroup.AlmostConjugate

open TauCeti

universe u

variable {𝕜 : Type u} [NontriviallyNormedField 𝕜] [CharZero 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type u} [NormedAddCommGroup F] [NormedSpace 𝕜 F] {n : ℕ∞ω}
  {Q : Type u} [Group Q] [Finite Q] [MulAction Q M] [ContMDiffConstSMul I n Q M]
  [ContinuousConstSMul Q M] [T2Space M] [LocallyCompactSpace M] [IsManifold I n M]
  {K₁ K₂ : Subgroup Q} [IsCancelSMul K₁ M] [IsCancelSMul K₂ M]

/-- **Sunada's theorem for smooth functions.** Let a finite group `Q` act on `M` by `C^n` maps,
and let `K₁`, `K₂` be almost-conjugate subgroups of `Q` acting freely on `M`. Let `T` be an
operator on the `C^n` maps `M → F` commuting with the action of `Q`, and `S₁`, `S₂` operators on
the `C^n` maps on `M ⧸ K₁` and `M ⧸ K₂` intertwined with `T` by pullback along the orbit
projections. If the scalar field `𝕜` has characteristic zero, then for every `μ` the
`μ`-eigenspaces of `S₁` and `S₂` are linearly equivalent. -/
theorem nonempty_linearEquiv_eigenspace_of_intertwine (h : K₁.AlmostConjugate K₂)
    {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hT : ∀ q, Commute T (smoothFunctionRep 𝕜 I M F n Q q))
    {S₁ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₁ M; 𝓘(𝕜, F), F⟯}
    {S₂ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₂ M; 𝓘(𝕜, F), F⟯}
    (hS₁ : ∀ u, T (u.comp (smoothQuotientMk I M n K₁)) = (S₁ u).comp (smoothQuotientMk I M n K₁))
    (hS₂ : ∀ u, T (u.comp (smoothQuotientMk I M n K₂)) = (S₂ u).comp (smoothQuotientMk I M n K₂))
    (μ : 𝕜) : Nonempty (S₁.eigenspace μ ≃ₗ[𝕜] S₂.eigenspace μ) := by
  obtain ⟨e⟩ := h.nonempty_linearEquiv_invariants_inf_eigenspace _ hT μ
  rw [smoothFunctionRep_comp_subtype, smoothFunctionRep_comp_subtype] at e
  exact ⟨eigenspaceEquivInvariantsInfEigenspace hS₁ μ ≪≫ₗ e ≪≫ₗ
    (eigenspaceEquivInvariantsInfEigenspace hS₂ μ).symm⟩

/-- **Sunada's theorem for smooth functions, dimension form.** Under the hypotheses of
`Subgroup.AlmostConjugate.nonempty_linearEquiv_eigenspace_of_intertwine` (in particular, over a
scalar field `𝕜` of characteristic zero), the `μ`-eigenspaces of `S₁` and `S₂` have the same
`finrank`. This is their common dimension when they are finite-dimensional, as for Laplacian
eigenspaces on compact quotients. -/
theorem finrank_eigenspace_eq_of_intertwine (h : K₁.AlmostConjugate K₂)
    {T : End 𝕜 C^n⟮I, M; 𝓘(𝕜, F), F⟯} (hT : ∀ q, Commute T (smoothFunctionRep 𝕜 I M F n Q q))
    {S₁ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₁ M; 𝓘(𝕜, F), F⟯}
    {S₂ : End 𝕜 C^n⟮I, MulAction.orbitRel.Quotient K₂ M; 𝓘(𝕜, F), F⟯}
    (hS₁ : ∀ u, T (u.comp (smoothQuotientMk I M n K₁)) = (S₁ u).comp (smoothQuotientMk I M n K₁))
    (hS₂ : ∀ u, T (u.comp (smoothQuotientMk I M n K₂)) = (S₂ u).comp (smoothQuotientMk I M n K₂))
    (μ : 𝕜) : finrank 𝕜 (S₁.eigenspace μ) = finrank 𝕜 (S₂.eigenspace μ) :=
  let ⟨e⟩ := h.nonempty_linearEquiv_eigenspace_of_intertwine hT hS₁ hS₂ μ
  e.finrank_eq

end Subgroup.AlmostConjugate
