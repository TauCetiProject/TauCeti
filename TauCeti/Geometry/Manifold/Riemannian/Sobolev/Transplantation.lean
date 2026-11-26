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
# Transplantation of eigenfunctions, resolvents and spectral projections along finite coverings

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
  of the form `J y`. The same argument transplants the weak equation
  `D(u, v) + c ⟪u, v⟫_{L²} = ⟪F, v⟫_{L²}` of `Δ⁺ + c` for the shifted form `D + c ⟪·, ·⟫_{L²}`
  (`ContinuousLinearMap.shiftedForm`) with right-hand side `J F`
  (`forall_shiftedForm_dirichletForm_normalizedPullback_iff`); the eigenvalue equation is its
  case `c = -μ`, `F = 0`.
* **Resolvents.** The case `c = t > 0` shows that `J` intertwines the resolvents
  `(Δ⁺ + t)⁻¹ : L² → H¹` (`TauCeti.Manifold.SobolevH1.resolvent`):
  `J ((Δ⁺_N + t)⁻¹ f) = (Δ⁺_M + t)⁻¹ (J f)` (`normalizedPullback_resolvent`).
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
* `TauCeti.Manifold.SobolevH1.forall_shiftedForm_dirichletForm_normalizedPullback_iff`:
  transplantation of the weak equation of `Δ⁺ + c`.
* `TauCeti.Manifold.SobolevH1.normalizedPullback_mem_weakEigenspace_iff`,
  `TauCeti.Manifold.SobolevH1.map_normalizedPullback_weakEigenspace`: the normalized pullback
  identifies the weak `μ`-eigenspace of `N` with the deck-invariant weak `μ`-eigenspace of `M`.
* `TauCeti.Manifold.SobolevH1.map_normalizedPullbackLp_map_toLp_weakEigenspace`: the same for the
  `μ`-eigenspaces in `L²`.
* `TauCeti.Manifold.SobolevH1.normalizedPullback_resolvent`: the normalized pullback intertwines
  the resolvents of `Δ⁺`.
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

/-- Pullback along a Riemannian isometry preserves the shifted form `D + c ⟪·, ·⟫_{L²}`. -/
theorem shiftedForm_dirichletForm_compRiemannianIsometry (Φ : RiemannianIsometry I I' M N)
    (c : ℝ) (u v : SobolevH1 I' N) :
    toLp.shiftedForm dirichletForm c (compRiemannianIsometry Φ u) (compRiemannianIsometry Φ v) =
      toLp.shiftedForm dirichletForm c u v := by
  simp only [shiftedForm_dirichletForm_apply, dirichletForm_compRiemannianIsometry,
    inner_toLp_compRiemannianIsometry]

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

/-! ### Transplantation of weak eigenfunctions -/

variable [BoundarylessManifold I M] [IsManifold I ∞ M] [IsManifold I' ∞ N]
  {G : Type*} [Group G] [MulAction G M] {q : M → N} [Finite G]

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
    toLp_compRiemannianIsometry, IsQuotientCoveringMap.coe_deckIsometry]
  conv_lhs => rw [← hq.compMeasurePreserving_normalizedPullbackLp hf.inner_mfderiv F g]
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
  obtain ⟨v', hv'⟩ := smul_sum_compRiemannianIsometry_mem_range_normalizedPullback hq hf v
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

/-- **Transplantation of eigenfunctions.** For a finite quotient covering map `q : M → N` which
is a local Riemannian isometry, the normalized pullback `J w` of `w ∈ H¹(N)` is a weak
`μ`-eigenfunction of `Δ⁺` on `M` exactly when `w` is one on `N`. -/
@[simp]
theorem normalizedPullback_mem_weakEigenspace_iff (hq : IsQuotientCoveringMap q G)
    (hf : IsLocalRiemannianIsometry I I' q) {μ : ℝ} {w : SobolevH1 I' N} :
    normalizedPullback hq hf w ∈ weakEigenspace I M μ ↔ w ∈ weakEigenspace I' N μ := by
  simpa [mem_weakEigenspace_iff_shiftedForm, -ContinuousLinearMap.shiftedForm_apply] using
    forall_shiftedForm_dirichletForm_normalizedPullback_iff hq hf (c := -μ) (w := w) (F := 0)

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

/-! ### The eigenspaces in `L²` and their spectral projections -/

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
    exact (inner_normalizedPullbackLp_eq_of_eq_smul_sum hq hf hy _).symm
  rw [ContinuousLinearMap.coe_coe, ← map_sub, ← havg, toLp_normalizedPullback,
    LinearIsometry.inner_map_map, real_inner_comm]
  exact K.sub_starProjection_mem_orthogonal f _ ⟨y, hyμ, rfl⟩

end TauCeti.Manifold.SobolevH1
