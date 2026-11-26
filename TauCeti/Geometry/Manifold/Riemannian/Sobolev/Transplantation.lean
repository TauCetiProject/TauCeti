/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Covering
public import TauCeti.Geometry.Manifold.Riemannian.Sobolev.Eigenbasis

/-!
# Transplantation of eigenfunctions and spectral projections along finite coverings

Let a finite group `G` act on a closed Riemannian manifold `M`, and let `q : M → N` be a quotient
covering map for this action (`IsQuotientCoveringMap q G`) which is a local Riemannian isometry
onto a closed Riemannian manifold `N`, as for the projection `X → X / H` onto the quotient by a
finite group of isometries acting freely. The normalized pullback `J = |G| ^ (-1/2) q^*` is a
linear isometry `H¹(N) → H¹(M)` (`TauCeti.Manifold.SobolevH1.normalizedPullback`) and
`L²(N) → L²(M)` (`IsQuotientCoveringMap.normalizedPullbackLp`), onto the deck-invariant elements,
and it preserves the Dirichlet form `D`. This file shows that it transplants the spectral theory of
the nonnegative Laplacian `Δ⁺ = -div grad` of `N` into that of `M`.

* **Eigenfunctions.** `w ∈ H¹(N)` is a weak `μ`-eigenfunction of `Δ⁺` exactly when `J w` is one
  on `M` (`normalizedPullback_mem_weakEigenspace_iff`), so `J` maps the weak `μ`-eigenspace of `N`
  onto the deck-invariant part of the weak `μ`-eigenspace of `M`
  (`map_normalizedPullback_weakEigenspace`). One direction is the identity
  `D(J w, J v) = D(w, v)`. For the other, the weak eigenvalue equation of the invariant element
  `J w` has to be tested against every `v ∈ H¹(M)`, not only the invariant ones; but the defect
  `v ↦ D(J w, v) - μ ⟪J w, v⟫_{L²}` is invariant under the deck transformations, so it takes the
  same value at `v` and at the average of `v` over the deck group, which is invariant and hence
  of the form `J y`.
* **Spectral projections.** On a closed manifold `L²` has a Hilbert basis of values of weak
  eigenfunctions (`exists_hilbertBasis_mem_weakEigenspace`), and the values of the weak
  `μ`-eigenspace are spanned by the basis vectors of eigenvalue `μ`
  (`map_toLp_weakEigenspace_eq_span`). So `Δ⁺` has pure point spectrum, and its spectral
  projection for the eigenvalue `μ` is the orthogonal projection `Π_μ` of `L²` onto the values of
  the weak `μ`-eigenspace, a finite-dimensional subspace. The normalized pullback intertwines
  these projections:

  `J (Π^N_μ f) = Π^M_μ (J f)` for every `f ∈ L²(N)`

  (`normalizedPullbackLp_starProjection`). Indeed `J Π^N_μ f` is a `μ`-eigenfunction on `M`, and
  `J (f - Π^N_μ f)` is orthogonal to every `μ`-eigenfunction `e` on `M`: being deck-invariant, its
  inner product with `e` is its inner product with the average of `e` over the deck group, which
  is the transplant `J e'` of a `μ`-eigenfunction `e'` on `N`, orthogonal to `f - Π^N_μ f`.

Isometries of `M` preserve the weak eigenspaces
(`compRiemannianIsometry_mem_weakEigenspace_iff`), the weak form of the fact that the Laplacian
commutes with isometries.

## Main results

* `TauCeti.Manifold.SobolevH1.compRiemannianIsometry_mem_weakEigenspace_iff`: pullback along a
  Riemannian isometry preserves weak eigenfunctions.
* `TauCeti.Manifold.SobolevH1.normalizedPullback_mem_weakEigenspace_iff`,
  `TauCeti.Manifold.SobolevH1.map_normalizedPullback_weakEigenspace`: the normalized pullback
  identifies the weak `μ`-eigenspace of `N` with the deck-invariant weak `μ`-eigenspace of `M`.
* `TauCeti.Manifold.SobolevH1.map_normalizedPullbackLp_map_toLp_weakEigenspace`: the same for the
  `μ`-eigenspaces in `L²`.
* `TauCeti.Manifold.SobolevH1.normalizedPullbackLp_starProjection`: the normalized pullback
  intertwines the spectral projections of `Δ⁺`.

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

/-! ### Weak eigenfunctions under isometries -/

/-- **Isometries preserve weak eigenfunctions.** For a Riemannian isometry `Φ : M → N`, the
pullback `w ∘ Φ` of `w ∈ H¹(N)` is a weak `μ`-eigenfunction of `Δ⁺` on `M` exactly when `w` is
one on `N`. -/
@[simp]
theorem compRiemannianIsometry_mem_weakEigenspace_iff (Φ : RiemannianIsometry I I' M N)
    {μ : ℝ} {w : SobolevH1 I' N} :
    compRiemannianIsometry Φ w ∈ weakEigenspace I M μ ↔ w ∈ weakEigenspace I' N μ := by
  simp only [mem_weakEigenspace_iff]
  refine ⟨fun h v ↦ by simpa using h (compRiemannianIsometry Φ v), fun h v ↦ ?_⟩
  obtain ⟨v, rfl⟩ := (compRiemannianIsometry Φ).surjective v
  simpa using h v

/-! ### Averaging over the deck group -/

variable [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold I' ∞ N]
  {G : Type*} [Group G] [MulAction G M] {q : M → N}

omit [CompactSpace N] [IsManifold I' 1 N] [MeasurableSpace N] [BorelSpace N]
  [IsContinuousRiemannianBundle E (fun y : N ↦ TangentSpace I' y)] in
/-- A linear functional on `H¹(M)` which is invariant under pullback along the deck
transformations takes at the average `|G|⁻¹ ∑_g (g ·)^* v` of `v` over the deck group the value it
takes at `v`. -/
private theorem apply_smul_sum_compRiemannianIsometry [Fintype G]
    (hq : IsQuotientCoveringMap q G) (hf : IsLocalRiemannianIsometry I I' q)
    (ℓ : SobolevH1 I M →ₗ[ℝ] ℝ)
    (hℓ : ∀ g v, ℓ (compRiemannianIsometry (hq.deckIsometry hf g) v) = ℓ v)
    (v : SobolevH1 I M) :
    ℓ ((Fintype.card G : ℝ)⁻¹ • ∑ g : G, compRiemannianIsometry (hq.deckIsometry hf g) v) =
      ℓ v := by
  have hG : (Fintype.card G : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [map_smul, map_sum]
  simp only [hℓ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, smul_eq_mul]
  field_simp

variable [Finite G]

/-! ### Transplantation of weak eigenfunctions -/

/-- **Transplantation of eigenfunctions.** For a finite quotient covering map `q : M → N` which
is a local Riemannian isometry, the normalized pullback `J w` of `w ∈ H¹(N)` is a weak
`μ`-eigenfunction of `Δ⁺` on `M` exactly when `w` is one on `N`. -/
@[simp]
theorem normalizedPullback_mem_weakEigenspace_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {μ : ℝ} {w : SobolevH1 I' N} :
    normalizedPullback hq hf w ∈ weakEigenspace I M μ ↔ w ∈ weakEigenspace I' N μ := by
  simp only [mem_weakEigenspace_iff]
  refine ⟨fun h v ↦ by simpa [toLp_normalizedPullback] using h (normalizedPullback hq hf v),
    fun h v ↦ ?_⟩
  set a := normalizedPullback hq hf w
  -- the defect of the eigenvalue equation of `a`, a deck-invariant linear functional
  let ℓ : SobolevH1 I M →ₗ[ℝ] ℝ :=
    ((dirichletForm a : SobolevH1 I M →L[ℝ] ℝ) -
      μ • (innerSL ℝ (toLp a)).comp (toLp : SobolevH1 I M →L[ℝ] _)).toLinearMap
  have hℓ (v : SobolevH1 I M) : ℓ v = dirichletForm a v - μ * ⟪toLp a, toLp v⟫_ℝ := by
    simp [ℓ]
  have ha (g : G) : compRiemannianIsometry (hq.deckIsometry hf g) a = a :=
    compRiemannianIsometry_normalizedPullback hq hf (fun x ↦ by simp [hq.map_smul]) w
  have hinv (g : G) (v : SobolevH1 I M) :
      ℓ (compRiemannianIsometry (hq.deckIsometry hf g) v) = ℓ v := by
    rw [hℓ, hℓ]
    conv_lhs => rw [← ha g]
    rw [dirichletForm_compRiemannianIsometry, inner_toLp_compRiemannianIsometry]
  -- so it takes at `v` its value at the average of `v`, the transplant of some `y`
  have := Fintype.ofFinite G
  obtain ⟨y, hy⟩ := smul_sum_compRiemannianIsometry_mem_range_normalizedPullback hq hf v
  have hy₀ : ℓ (normalizedPullback hq hf y) = 0 := by
    rw [hℓ, dirichletForm_normalizedPullback, toLp_normalizedPullback, toLp_normalizedPullback,
      LinearIsometry.inner_map_map, h y, sub_self]
  rw [← sub_eq_zero, ← hℓ, ← apply_smul_sum_compRiemannianIsometry hq hf ℓ hinv v, ← hy, hy₀]

/-- **The transplanted eigenspace.** The normalized pullback maps the weak `μ`-eigenspace of `Δ⁺`
on `N` onto the deck-invariant weak `μ`-eigenfunctions on `M`. -/
theorem map_normalizedPullback_weakEigenspace (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (μ : ℝ) :
    (weakEigenspace I' N μ).map (normalizedPullback hq hf).toLinearMap =
      weakEigenspace I M μ ⊓ LinearMap.range (normalizedPullback hq hf).toLinearMap := by
  have h : weakEigenspace I' N μ =
      (weakEigenspace I M μ).comap (normalizedPullback hq hf).toLinearMap :=
    Submodule.ext fun _ ↦ (normalizedPullback_mem_weakEigenspace_iff hq hf).symm
  rw [h, Submodule.map_comap_eq, inf_comm]

/-! ### The eigenspaces in `L²` and their spectral projections -/

/-- The normalized pullback of `f ∈ L²(N)` has the same `L²` inner product with the pullback of
`u` along a deck transformation as with `u`, since it is deck invariant. -/
private theorem inner_normalizedPullbackLp_toLp_compRiemannianIsometry
    (hq : IsQuotientCoveringMap q G) (hf : IsLocalRiemannianIsometry I I' q)
    (f : Lp ℝ 2 (riemannianVolume I' N)) (g : G) (u : SobolevH1 I M) :
    ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv f,
        toLp (compRiemannianIsometry (hq.deckIsometry hf g) u)⟫_ℝ =
      ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv f, toLp u⟫_ℝ := by
  rw [toLp_compRiemannianIsometry]
  simp only [IsQuotientCoveringMap.coe_deckIsometry]
  conv_lhs => rw [← hq.compMeasurePreserving_normalizedPullbackLp hf.inner_mfderiv f g]
  exact LinearIsometry.inner_map_map (𝕜 := ℝ) (Lp.compMeasurePreservingₗᵢ (E := ℝ) (p := 2) ℝ
    (g • ·) (hq.measurePreserving_smul_riemannianVolume hf.inner_mfderiv g)) _ _

/-- **Transplantation of the `L²` eigenspaces.** The normalized pullback `L²(N) → L²(M)` maps the
values of the weak `μ`-eigenspace of `Δ⁺` on `N` onto the deck-invariant elements of the values
of the weak `μ`-eigenspace on `M`. -/
theorem map_normalizedPullbackLp_map_toLp_weakEigenspace (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (μ : ℝ) :
    ((weakEigenspace I' N μ).map (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap).map
        (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv).toLinearMap =
      (weakEigenspace I M μ).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap ⊓
        LinearMap.range (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv).toLinearMap := by
  ext f
  simp only [Submodule.mem_map, Submodule.mem_inf, LinearMap.mem_range,
    ContinuousLinearMap.coe_coe, LinearIsometry.coe_toLinearMap]
  refine ⟨?_, ?_⟩
  · rintro ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨⟨normalizedPullback hq hf w, (normalizedPullback_mem_weakEigenspace_iff hq hf).2 hw,
      toLp_normalizedPullback hq hf w⟩, toLp w, rfl⟩
  · rintro ⟨⟨u, hu, rfl⟩, f, hfu⟩
    -- `u` is deck invariant: `(g ·)^* u` and `u` are eigenfunctions with the same value in `L²`
    have hinv (g : G) : compRiemannianIsometry (hq.deckIsometry hf g) u = u :=
      congrArg Subtype.val <| toLp_domRestrict_weakEigenspace_injective μ
        (a₁ := ⟨_, (compRiemannianIsometry_mem_weakEigenspace_iff _).2 hu⟩) (a₂ := ⟨u, hu⟩) <| by
        simp only [LinearMap.domRestrict_apply, ContinuousLinearMap.coe_coe]
        rw [toLp_compRiemannianIsometry, ← hfu]
        simpa only [IsQuotientCoveringMap.coe_deckIsometry] using
          hq.compMeasurePreserving_normalizedPullbackLp (𝕜 := ℝ) hf.inner_mfderiv f g
    -- so `u` is the transplant of some `y`
    obtain ⟨y, rfl⟩ := (mem_range_normalizedPullback_iff hq hf).2 hinv
    exact ⟨toLp y, ⟨y, (normalizedPullback_mem_weakEigenspace_iff hq hf).1 hu, rfl⟩,
      (toLp_normalizedPullback hq hf y).symm⟩

/-- **Transplantation of spectral projections.** For a finite quotient covering map `q : M → N`
which is a local Riemannian isometry, the normalized pullback `J : L²(N) → L²(M)` intertwines the
spectral projections of `Δ⁺` for the eigenvalue `μ`, the orthogonal projections `Π_μ` onto the
values of the weak `μ`-eigenspaces: `J (Π^N_μ f) = Π^M_μ (J f)`. On closed manifolds these values
form finite-dimensional subspaces (`finiteDimensional_weakEigenspace`), so the projections exist. -/
theorem normalizedPullbackLp_starProjection (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) (μ : ℝ)
    [((weakEigenspace I' N μ).map
      (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap).HasOrthogonalProjection]
    [((weakEigenspace I M μ).map
      (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap).HasOrthogonalProjection]
    (f : Lp ℝ 2 (riemannianVolume I' N)) :
    hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv
        (((weakEigenspace I' N μ).map (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap).starProjection
          f) =
      ((weakEigenspace I M μ).map (toLp : SobolevH1 I M →L[ℝ] _).toLinearMap).starProjection
        (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv f) := by
  set K := (weakEigenspace I' N μ).map (toLp : SobolevH1 I' N →L[ℝ] _).toLinearMap
  symm
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero ?_ fun e he ↦ ?_
  · obtain ⟨w, hw, hwf⟩ := Submodule.mem_map.1 (K.starProjection_apply_mem f)
    rw [← hwf]
    exact ⟨normalizedPullback hq hf w, (normalizedPullback_mem_weakEigenspace_iff hq hf).2 hw,
      toLp_normalizedPullback hq hf w⟩
  obtain ⟨u, hu, rfl⟩ := he
  have := Fintype.ofFinite G
  -- replace `u` by its average over the deck group, the transplant of an eigenfunction on `N`
  obtain ⟨y, hy⟩ := smul_sum_compRiemannianIsometry_mem_range_normalizedPullback hq hf u
  have hyμ : y ∈ weakEigenspace I' N μ := by
    rw [← normalizedPullback_mem_weakEigenspace_iff hq hf, hy]
    exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun g _ ↦
      (compRiemannianIsometry_mem_weakEigenspace_iff _).2 hu)
  have havg : ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv (f - K.starProjection f),
      toLp (normalizedPullback hq hf y)⟫_ℝ =
      ⟪hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv (f - K.starProjection f), toLp u⟫_ℝ := by
    rw [hy]
    exact apply_smul_sum_compRiemannianIsometry hq hf
      ((innerSL ℝ (hq.normalizedPullbackLp ℝ 2 hf.inner_mfderiv (f - K.starProjection f))).comp
        (toLp : SobolevH1 I M →L[ℝ] _)).toLinearMap
      (inner_normalizedPullbackLp_toLp_compRiemannianIsometry hq hf _) u
  rw [ContinuousLinearMap.coe_coe, ← map_sub, ← havg, toLp_normalizedPullback,
    LinearIsometry.inner_map_map, real_inner_comm]
  exact K.sub_starProjection_mem_orthogonal f _ ⟨y, hyμ, rfl⟩

end TauCeti.Manifold.SobolevH1
