/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Covering
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenbasis
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Resolvent
import TauCeti.MeasureTheory.Function.L2Space

/-!
# Transplantation of eigenfunctions along finite Riemannian coverings

Let a finite group `G` act on a closed Riemannian manifold `M`, and let `q : M → N` be a quotient
covering map for this action which is a local Riemannian isometry onto a closed Riemannian
manifold `N`. The normalized pullback `J = |G| ^ (-1/2) q^*` is a linear isometry from `H¹(N)`
onto the deck-invariant part of `H¹(M)`, and from `L²(N)` onto the deck-invariant part of `L²(M)`,
which preserves the Dirichlet form (`TauCeti.Manifold.SobolevH1.normalizedPullback`,
`IsQuotientCoveringMap.normalizedPullbackLp`). This file shows that `J` transports the nonnegative
Laplacian `Δ⁺ = -div grad` of `N` to the invariant part of that of `M`, at the level of its weak
eigenspaces, its resolvents and its spectral projections:

* `J w` is a weak `μ`-eigenfunction on `M` exactly when `w` is one on `N`
  (`TauCeti.Manifold.SobolevH1.normalizedPullback_mem_weakEigenspace_iff`), and the image of the
  weak `μ`-eigenspace of `N` is the space of deck-invariant weak `μ`-eigenfunctions on `M`
  (`TauCeti.Manifold.SobolevH1.image_normalizedPullback_weakEigenspace`);
* `J` intertwines the resolvents `(Δ⁺ + t)⁻¹ : L² → H¹`, `t > 0`
  (`TauCeti.Manifold.SobolevH1.resolvent`):
  `J ∘ (Δ⁺_N + t)⁻¹ = (Δ⁺_M + t)⁻¹ ∘ J`
  (`TauCeti.Manifold.SobolevH1.normalizedPullback_resolvent`);
* on `L²`, `J` intertwines the orthogonal projections `Π_μ` onto the values of the weak
  `μ`-eigenspaces: `J ∘ Π_μ^N = Π_μ^M ∘ J`
  (`TauCeti.Manifold.SobolevH1.normalizedPullbackLp_starProjection`).

The values of the weak eigenspaces of distinct eigenvalues are orthogonal, and `L²` has a Hilbert
basis of values of weak eigenfunctions
(`TauCeti.Manifold.SobolevH1.exists_hilbertBasis_mem_weakEigenspace`), so the projections `Π_μ`
are the projections of the spectral decomposition of `Δ⁺`.

## The argument

Both the weak eigenvalue equation and the weak equation of the resolvent are equations
`D(u, v) + c ⟪u, v⟫_{L²} = ⟪F, v⟫_{L²}` for the shifted form `D + c ⟪·, ·⟫_{L²}`
(`ContinuousLinearMap.shiftedForm`), with `c = -μ`, `F = 0` and with `c = t`. This form is
invariant under the deck transformations
(`TauCeti.Manifold.SobolevH1.shiftedForm_dirichletForm_compRiemannianIsometry`), and so is `J w`.
So the linear map `v ↦ D(J w, v) + c ⟪J w, v⟫_{L²}` takes the same value at `v` and at its deck
average `|G|⁻¹ ∑_g (g ·)^* v`
(`TauCeti.Manifold.SobolevH1.map_normalizedPullback_eq_of_eq_smul_sum`), which is itself a
normalized pullback `J v'` (`TauCeti.Manifold.SobolevH1.exists_normalizedPullback_eq_smul_sum`).
So testing the equation of `J w` on `M` against an arbitrary `v` reduces to testing it against
`J v'`, where it is the equation of `w` on `N` tested against `v'`. The elements `J F` of the
range of `J` in `L²(M)` are deck invariant as well, so they too pair with `v` as with `J v'`
(`TauCeti.Manifold.SobolevH1.forall_shiftedForm_dirichletForm_normalizedPullback_iff`). The same
pairing shows that `J` maps the orthogonal complement of the `μ`-eigenfunctions of `N` into that
of `M`.

## Main results

* `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_mem_weakEigenspace_iff`: pullback along a
  Riemannian isometry preserves the weak eigenspaces.
* `TauCeti.Manifold.SobolevH1.forall_shiftedForm_dirichletForm_normalizedPullback_iff`:
  transplantation of the weak equation of `Δ⁺ + c`.
* `TauCeti.Manifold.SobolevH1.normalizedPullback_mem_weakEigenspace_iff` and
  `TauCeti.Manifold.SobolevH1.image_normalizedPullback_weakEigenspace`: transplantation of weak
  eigenfunctions.
* `TauCeti.Manifold.SobolevH1.normalizedPullback_resolvent`: the normalized pullback intertwines
  the resolvents.
* `TauCeti.Manifold.SobolevH1.normalizedPullbackLp_starProjection`: the normalized pullback
  intertwines the projections onto the eigenspaces.

## References

* P. Bérard, *Transplantation et isospectralité I*, Séminaire de Théorie spectrale et
  géométrie **9** (1990–1991), §II, Theorem 14, Lemma 16 and Comment 18, pp. 158–160.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff Manifold InnerProductSpace

noncomputable section

namespace TauCeti.Manifold.SobolevH1

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [CompactSpace M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x)]
  {H' : Type*} [TopologicalSpace H'] {I' : ModelWithCorners ℝ E H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [CompactSpace N] [IsManifold I' 1 N]
  [MeasurableSpace N] [BorelSpace N] [RiemannianBundle (fun y : N ↦ TangentSpace I' y)]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)]

/-! ### Weak eigenspaces under Riemannian isometries -/

/-- Pullback along a Riemannian isometry preserves the shifted form `D + c ⟪·, ·⟫_{L²}`. -/
theorem shiftedForm_dirichletForm_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N)
    (c : ℝ) (u v : SobolevH1 I' N) :
    toLp.shiftedForm dirichletForm c (compRiemannianIsometry Φ u) (compRiemannianIsometry Φ v) =
      toLp.shiftedForm dirichletForm c u v := by
  simp only [shiftedForm_dirichletForm_apply, dirichletForm_compRiemannianIsometry,
    inner_toLp_compRiemannianIsometry]

/-- **Riemannian isometries preserve the weak eigenspaces.** For a Riemannian isometry
`Φ : M → N`, the pullback `Φ^* w` of `w ∈ H¹(N)` is a weak `μ`-eigenfunction on `M` exactly when
`w` is one on `N`. -/
@[simp]
theorem compRiemannianIsometry_mem_weakEigenspace_iff (Φ : RiemannianIsometry I I' M N) {μ : ℝ}
    {w : SobolevH1 I' N} :
    compRiemannianIsometry Φ w ∈ weakEigenspace I M μ ↔ w ∈ weakEigenspace I' N μ := by
  simp only [mem_weakEigenspace_iff]
  refine ⟨fun h v ↦ ?_, fun h v ↦ ?_⟩
  · simpa using h (compRiemannianIsometry Φ v)
  · obtain ⟨v, rfl⟩ := (compRiemannianIsometry Φ).surjective v
    simpa using h v

/-! ### Transplantation along a finite covering -/

variable [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold I' ∞ N]
  {q : M → N} {G : Type*} [Group G] [MulAction G M] [Finite G]

/-- The deck-invariant normalized pullback `J F` of `F ∈ L²(N)` pairs with the value of `v` in
`L²(M)` as with that of `J v'`, when `J v'` is the deck average of `v`. -/
private theorem inner_normalizedPullbackLp_eq_of_eq_smul_sum [Fintype G]
    (hq : IsQuotientCoveringMap q G) (hf : IsLocalRiemannianIsometry I I' q)
    {v : SobolevH1 I M} {v' : SobolevH1 I' N} (hv' : normalizedPullback hq hf v' =
      (Fintype.card G : ℝ)⁻¹ • ∑ g : G, compRiemannianIsometry (hq.deckIsometry hf g) v)
    (F : Lp ℝ 2 (riemannianVolume I' N)) :
    ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv F, toLp v⟫_ℝ =
      ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv F, toLp (normalizedPullback hq hf v')⟫_ℝ := by
  refine (map_normalizedPullback_eq_of_eq_smul_sum hq hf
    ((innerSL ℝ (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv F)).comp toLp).toLinearMap
    (fun g ↦ ?_) hv').symm
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply, innerSL_apply_apply,
    toLp_compRiemannianIsometry]
  conv_lhs => rw [← hq.compMeasurePreserving_normalizedPullbackLp hf g F]
  exact Lp.inner_compMeasurePreserving _ _ _

/-- **Transplantation of the weak equation of `Δ⁺ + c`.** For `w ∈ H¹(N)` and `F ∈ L²(N)`, the
normalized pullbacks `J w` and `J F` along the finite quotient covering `q : M → N` satisfy the
weak equation `D(J w, v) + c ⟪J w, v⟫_{L²} = ⟪J F, v⟫_{L²}` on `M` exactly when `w` and `F`
satisfy it on `N`. -/
theorem forall_shiftedForm_dirichletForm_normalizedPullback_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {c : ℝ} {w : SobolevH1 I' N}
    {F : Lp ℝ 2 (riemannianVolume I' N)} :
    (∀ v, toLp.shiftedForm dirichletForm c (normalizedPullback hq hf w) v =
        ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv F, toLp v⟫_ℝ) ↔
      ∀ v, toLp.shiftedForm dirichletForm c w v = ⟪F, toLp v⟫_ℝ := by
  refine ⟨fun h v ↦ ?_, fun h v ↦ ?_⟩
  · simpa [shiftedForm_dirichletForm_apply, -ContinuousLinearMap.shiftedForm_apply,
      toLp_normalizedPullback] using h (normalizedPullback hq hf v)
  -- test against the normalized pullback `J v'` of the deck average of `v`
  have := Fintype.ofFinite G
  obtain ⟨v', hv'⟩ := exists_normalizedPullback_eq_smul_sum hq hf v
  -- the deck-invariant `J w` pairs with each deck pullback of `v` as with `v`
  have hB := map_normalizedPullback_eq_of_eq_smul_sum hq hf
    (toLp.shiftedForm dirichletForm c (normalizedPullback hq hf w)).toLinearMap (fun g ↦ by
      conv_lhs => rw [← compRiemannianIsometry_normalizedPullback hq hf
        (Φ := hq.deckIsometry hf g) (fun x ↦ by simp [hq.map_smul]) w]
      exact shiftedForm_dirichletForm_compRiemannianIsometry _ c _ _) hv'
  rw [ContinuousLinearMap.coe_coe] at hB
  rw [← hB, inner_normalizedPullbackLp_eq_of_eq_smul_sum hq hf hv', toLp_normalizedPullback,
    LinearIsometry.inner_map_map, ← h v']
  simp [shiftedForm_dirichletForm_apply, -ContinuousLinearMap.shiftedForm_apply]

/-- **Transplantation of weak eigenfunctions.** The normalized pullback `J w` of `w ∈ H¹(N)` along
the finite quotient covering `q : M → N` is a weak `μ`-eigenfunction of `Δ⁺` on `M` exactly when
`w` is one on `N`. -/
@[simp]
theorem normalizedPullback_mem_weakEigenspace_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {μ : ℝ} {w : SobolevH1 I' N} :
    normalizedPullback hq hf w ∈ weakEigenspace I M μ ↔ w ∈ weakEigenspace I' N μ := by
  simpa [mem_weakEigenspace_iff_shiftedForm, -ContinuousLinearMap.shiftedForm_apply] using
    forall_shiftedForm_dirichletForm_normalizedPullback_iff hq hf (c := -μ) (w := w) (F := 0)

/-- **The transplanted eigenspace.** The normalized pullback maps the weak `μ`-eigenspace of `Δ⁺`
on `N` onto the weak `μ`-eigenfunctions on `M` invariant under every deck transformation of the
finite quotient covering `q : M → N`. -/
theorem image_normalizedPullback_weakEigenspace (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (μ : ℝ) :
    normalizedPullback hq hf '' weakEigenspace I' N μ = {v | v ∈ weakEigenspace I M μ ∧
      ∀ g : G, compRiemannianIsometry (hq.deckIsometry hf g) v = v} := by
  ext v
  refine ⟨?_, fun ⟨hv, hinv⟩ ↦ ?_⟩
  · rintro ⟨w, hw, rfl⟩
    exact ⟨(normalizedPullback_mem_weakEigenspace_iff hq hf).2 hw,
      (mem_range_normalizedPullback_iff hq hf).1 ⟨w, rfl⟩⟩
  · obtain ⟨w, rfl⟩ := (mem_range_normalizedPullback_iff hq hf).2 hinv
    exact ⟨w, (normalizedPullback_mem_weakEigenspace_iff hq hf).1 hv, rfl⟩

/-! ### The resolvent -/

/-- **The normalized pullback intertwines the resolvents.** For `t > 0`, the resolvents
`(Δ⁺ + t)⁻¹ : L² → H¹` of `M` and `N` and the normalized pullbacks `J = |G| ^ (-1/2) q^*` on `L²`
and on `H¹` along the finite quotient covering `q : M → N` satisfy
`J ((Δ⁺_N + t)⁻¹ f) = (Δ⁺_M + t)⁻¹ (J f)` for every `f ∈ L²(N)`. -/
theorem normalizedPullback_resolvent (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {t : ℝ} (ht : 0 < t)
    (f : Lp ℝ 2 (riemannianVolume I' N)) :
    normalizedPullback hq hf (resolvent I' N ht f) =
      resolvent I M ht (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv f) := by
  refine eq_resolvent ht fun v ↦ ?_
  rw [← shiftedForm_dirichletForm_apply]
  refine (forall_shiftedForm_dirichletForm_normalizedPullback_iff hq hf).2 (fun v' ↦ ?_) v
  rw [shiftedForm_dirichletForm_apply, dirichletForm_resolvent_add]

/-! ### Spectral projections -/

variable [I.Boundaryless] [T2Space M] [I'.Boundaryless] [T2Space N]

omit [BoundarylessManifold I M] in
/-- **The normalized pullback intertwines the spectral projections.** Let `Π_μ` be the orthogonal
projection of `L²` onto the values of the weak `μ`-eigenspace of `Δ⁺`, its spectral projection at
`μ`. Then the normalized pullback `J = |G| ^ (-1/2) q^*` along the finite quotient covering
`q : M → N` satisfies `J (Π_μ^N f) = Π_μ^M (J f)` for every `f ∈ L²(N)`. -/
theorem normalizedPullbackLp_starProjection (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (μ : ℝ) (f : Lp ℝ 2 (riemannianVolume I' N)) :
    hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv
        (((weakEigenspace I' N μ).map (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap).starProjection
          f) =
      ((weakEigenspace I M μ).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap).starProjection
        (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv f) := by
  set J := hq.normalizedPullbackLp (F := ℝ) ℝ 2 hf.inner_mfderiv
  set KN := (weakEigenspace I' N μ).map (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap
  set KM := (weakEigenspace I M μ).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap
  have hJ (w : SobolevH1 I' N) : J (toLp w) = toLp (normalizedPullback hq hf w) :=
    (toLp_normalizedPullback hq hf w).symm
  refine (KM.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun x hx ↦ ?_).symm
  · obtain ⟨w, hw, hwf⟩ := Submodule.mem_map.1 (KN.starProjection_apply_mem f)
    rw [← hwf, ContinuousLinearMap.coe_coe, hJ]
    exact Submodule.mem_map_of_mem ((normalizedPullback_mem_weakEigenspace_iff hq hf).2 hw)
  obtain ⟨x, hxμ, rfl⟩ := Submodule.mem_map.1 hx
  rw [ContinuousLinearMap.coe_coe, ← map_sub]
  -- `J g` is deck invariant, so it pairs with `toLp x` as with the deck average `J x'` of `x`
  have := Fintype.ofFinite G
  obtain ⟨x', hx'⟩ := exists_normalizedPullback_eq_smul_sum hq hf x
  -- the deck average of a weak eigenfunction is the normalized pullback of one
  have hx'μ : x' ∈ weakEigenspace I' N μ := by
    rw [← normalizedPullback_mem_weakEigenspace_iff hq hf, hx']
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ ↦
      (compRiemannianIsometry_mem_weakEigenspace_iff _).2 hxμ)
  rw [inner_normalizedPullbackLp_eq_of_eq_smul_sum hq hf hx', ← hJ, LinearIsometry.inner_map_map]
  exact KN.inner_left_of_mem_orthogonal (Submodule.mem_map_of_mem hx'μ)
    (KN.sub_starProjection_mem_orthogonal f)

end TauCeti.Manifold.SobolevH1
