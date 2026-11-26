/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology
public import TauCeti.Analysis.Distribution.WaveFrontSet.Pullback.Basic
import TauCeti.Algebra.Module.ZLattice.Scaling
import TauCeti.Analysis.Distribution.WaveFrontSet.NormalTopology.LatticeSeries
import TauCeti.Analysis.Normed.Lp.ProdLp
import TauCeti.Analysis.Normed.Module.Cone

/-!
# Continuity of the pullback to `E × {0}` in the normal topology

Let `W` be an open set of the Euclidean product `WithLp 2 (E × D)` of finite-dimensional real
inner product spaces, `U` an open set of `E` with `U × {0} ⊆ W`, and `Γ` a closed cone of nonzero
covectors over `W` (closed in `W × ((E × D) \ {0})`) containing no conormal covector
`((x, 0), (0, η))` of `E × {0}` over `U`. Every distribution `T` with wave front set in `Γ` then
has a pullback `ι^* T` along the inclusion `ι : x ↦ (x, 0)` (`Distribution.pullbackInl`), whose
wave front set lies in the fixed cone

`ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}` (`TauCeti.pullbackInlCone`).

This file proves that the pullback is continuous for the normal topologies of Hörmander's spaces
(`TauCeti.WaveFrontSpace.pullbackInlCLM`):

`ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{ιᵀ Γ}(U)`.

This is the restriction step of the pullback along a smooth map, which composes it with a pullback
along a submersion (Brouder, Dang and Hélein, Theorem 6.3, in the case of a linear injection).

## The estimates

Fix a compact set `K ⊆ U` and a closed cone `V` of frequencies with no point of `ιᵀ Γ` over `K` in
a direction of `V`; for a seminorm `‖ι^* T‖_{ψ,V,N}` of the target, `K` is the support of `ψ`, and
for the topology of `𝓓'(U)`, `V = {0}`. Since `Γ` is a closed cone, no point of `Γ` lies over a
neighbourhood of `K × {0}` in a direction of the closed cone
`A = {ζ | dist (ζ.fst, V) ≤ ε ‖ζ‖}` for small `ε > 0`
(`TauCeti.WaveFrontSpace.exists_forall_mem_thickening_forall_notMem`, for the projection
`ζ ↦ ζ.fst`), so a cutoff `χ` equal to one on `K × closedBall 0 δ` and supported in that
neighbourhood has no point of `Γ` over its support in a direction of `A`
(`exists_cutoff_forall_notMem`). The localized Fourier transform of `ι^* T` with a cutoff `ψ`
supported in `K` is the lattice series

`ι^* T (ψ e_ξ) = ∑ m, (covolume L)⁻¹ 𝓕 ψ (ξ + m.fst) T (χ e_(-m))`

(`Distribution.localFourier_pullbackInl_eq_tsum`). Its estimates by continuous seminorms of
`𝓓'_Γ(W)`, for the projection `(ξ, η) ↦ ξ` transposing `ι`, are those of
`TauCeti.WaveFrontSpace.exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le`
and `TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_tsum_le`. For the topology of
`𝓓'(U)`, the criterion `TauCeti.WaveFrontSpace.continuous_linearMap_of_forall_isCompact_le`
needs these estimates only on compact sets of test functions supported in one compact set `K`.

## Main declarations

* `TauCeti.WaveFrontSpace.pullbackInlCLM`: the pullback `ι^* : 𝓓'_Γ(W) →L[ℂ] 𝓓'_{ιᵀ Γ}(U)`.
* `TauCeti.WaveFrontSpace.toDistribution_pullbackInlCLM`: it is `Distribution.pullbackInl`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 8.2.4 (the pullback and its sequential continuity on `𝓓'_Γ`).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on distributions
  having a specified wave front set (with a counterexample by Semyon Alesker)*, Studia Math. 232
  (2016), arXiv:1409.7662v2, Theorem 6.3 (continuity of the pullback in the normal topology).
-/

public section

noncomputable section

open Complex Filter Function Metric Set TopologicalSpace TestFunction WithLp
open scoped Distributions Topology FourierTransform ContDiff Real RealInnerProductSpace Pointwise
  SchwartzMap

namespace TauCeti

open Distribution

namespace WaveFrontSpace

variable {E D : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  {U : Opens E} {W : Opens (WithLp 2 (E × D))} {Γ : Set (WithLp 2 (E × D) × WithLp 2 (E × D))}

/-! ### A cutoff adapted to `Γ` -/

/-- A cutoff `χ` equal to one on `K × closedBall 0 δ`, such that no point of `Γ` lies over its
support in a direction of the cone `A = {ζ | dist (ζ.fst, V) ≤ ε ‖ζ‖}`. -/
private theorem exists_cutoff_forall_notMem
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) {V : Set E} (hV : IsClosed V) (hV0 : (0 : E) ∈ V)
    (hVcone : ∀ t : ℝ, 0 < t → ∀ ξ ∈ V, t • ξ ∈ V)
    (hKV : Disjoint (K ×ˢ V) (pullbackInlCone Γ)) :
    ∃ ε > 0, ∃ δ > 0, ∃ χ : 𝓓(W, ℂ), (∀ x ∈ K, ∀ y : D, ‖y‖ ≤ δ → χ (toLp 2 (x, y)) = 1) ∧
      ∀ p ∈ tsupport χ, ∀ ζ : WithLp 2 (E × D), infDist ζ.fst V ≤ ε * ‖ζ‖ → (p, ζ) ∉ Γ := by
  set ι : E → WithLp 2 (E × D) := fun x ↦ toLp 2 (x, (0 : D))
  have hι : Continuous ι :=
    (prod_continuous_toLp 2 E D).comp (continuous_id.prodMk continuous_const)
  -- No covector of `Γ` over `K × {0}` has its first component in `V`.
  have hιKV : ∀ y ∈ ι '' K, ∀ ζ, (y, ζ) ∈ Γ → fstL 2 ℝ E D ζ ∉ V := by
    rintro _ ⟨x, hx, rfl⟩ ζ hζ hζV
    refine disjoint_left.1 hKV (mk_mem_prod hx hζV) (mem_pullbackInlCone.2 ⟨ζ.snd, ?_⟩)
    have hζeq : toLp 2 (ζ.fst, ζ.snd) = ζ := by
      rw [← ofLp_fst, ← ofLp_snd, Prod.mk.eta, toLp_ofLp]
    simpa [ι, hζeq] using hζ
  obtain ⟨ε, hε, hεΓ⟩ := exists_forall_mem_thickening_forall_notMem (fstL 2 ℝ E D) hΓ hcone hΓ0
    (hK.image hι) (image_subset_iff.2 fun x hx ↦ hU (hKU hx)) hV hV0 hVcone hιKV
  obtain ⟨δ, hδ, χ, hχ1, hχG⟩ := exists_cutoff_eq_one_prod_closedBall hK
    (isOpen_thickening (δ := ε) (E := ι '' K))
    fun x hx ↦ ⟨self_subset_thickening hε _ ⟨x, hx, rfl⟩, hU (hKU hx)⟩
  exact ⟨ε, hε, δ, hδ, χ, hχ1, fun p hp ζ hζ ↦ hεΓ p (hχG hp) ζ hζ⟩

section Measurable

variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D]

omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- A distribution with wave front set in `Γ` has no conormal covector of `E × {0}` over `U` in
its wave front set. -/
private theorem notMem_waveFrontSet
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) : ∀ x ∈ U, ∀ η : D, η ≠ 0 →
      (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ u.toDistribution.waveFrontSet :=
  fun x hx η hη hmem ↦ hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem)


omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- With the cutoff `χ` of `exists_cutoff_forall_notMem`, the localized Fourier transform of a
distribution with wave front set in `Γ` decays rapidly on the cone `‖ζ.fst‖ < ε ‖ζ.snd‖` around
the conormal directions of `E × {0}`. -/
private theorem exists_decay_localFourier {χ : 𝓓(W, ℂ)} {V : Set E} (hV0 : (0 : E) ∈ V) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hχ : ∀ p ∈ tsupport χ, ∀ ζ : WithLp 2 (E × D), infDist ζ.fst V ≤ ε * ‖ζ‖ → (p, ζ) ∉ Γ)
    (u : WaveFrontSpace W Γ) (N : ℕ) : ∃ C, ∀ ζ : WithLp 2 (E × D),
      ‖ζ.fst‖ < ε * ‖ζ.snd‖ → (1 + ‖ζ‖) ^ N * ‖u.toDistribution.localFourier χ ζ‖ ≤ C := by
  set A : Set (WithLp 2 (E × D)) := {ζ | ‖ζ.fst‖ ≤ ε * ‖ζ‖}
  have hA : ∀ t : ℝ, 0 < t → ∀ ζ ∈ A, t • ζ ∈ A := fun t ht ζ hζ ↦ by
    simp only [A, mem_ofPred_eq, WithLp.smul_fst, norm_smul, Real.norm_of_nonneg ht.le] at hζ ⊢
    nlinarith
  have hχA : Disjoint (tsupport χ ×ˢ A) u.toDistribution.waveFrontSet := by
    refine disjoint_left.2 ?_
    rintro ⟨p, ζ⟩ ⟨hp, hζ⟩ hmem
    exact hχ p hp ζ (((infDist_le_dist_of_mem hV0).trans_eq (dist_zero_right _)).trans hζ)
      (u.waveFrontSet_toDistribution_subset hmem)
  obtain ⟨C, -, hC⟩ := exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint
    (isClosed_le (by fun_prop) (by fun_prop)) hA hχA N
  exact ⟨C, fun ζ hζ ↦ hC ζ
    (hζ.le.trans (mul_le_mul_of_nonneg_left (WithLp.norm_snd_le (x := ζ)) hε))⟩

/-- **The seminorms of the pullback.** For the data `(φ, V, N)` of a seminorm of `𝓓'_{ιᵀ Γ}(U)`,
the decay estimate `(1 + ‖ξ‖) ^ N ‖ι^* T (φ e_ξ)‖ ≤ p T` on `V` holds for a continuous seminorm
`p` of `𝓓'_Γ(W)`. -/
private theorem exists_seminorm_localFourier_pullbackInl_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (j : WaveFrontSeminormIndex U (pullbackInlCone Γ)) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ξ ∈ j.cone,
      (1 + ‖ξ‖) ^ j.order *
        ‖(u.toDistribution.pullbackInl hU (notMem_waveFrontSet hN u)).localFourier j.cutoff ξ‖ ≤
          p u := by
  rcases j.cone.eq_empty_or_nonempty with hV | ⟨ξ₀, hξ₀⟩
  · exact ⟨0, continuous_const, fun u ξ hξ ↦ by simp [hV] at hξ⟩
  have hV0 := j.isClosed_cone.zero_mem_of_smul_mem j.smul_mem_cone hξ₀
  obtain ⟨ε, hε, δ, hδ, χ, hχ1, hχΓ⟩ := exists_cutoff_forall_notMem hU hΓ hcone hΓ0
    j.cutoff.hasCompactSupport.isCompact j.cutoff.tsupport_subset j.isClosed_cone hV0
    j.smul_mem_cone j.disjoint
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  obtain ⟨p, hp, hpV⟩ := exists_continuous_seminorm_one_add_norm_pow_mul_norm_tsum_le
    (fstL 2 ℝ E D) j.isClosed_cone j.smul_mem_cone hε (fun p hp ζ hζ ↦ hχΓ p hp ζ hζ) L
    j.cutoff j.order
  refine ⟨p, hp, fun u ξ hξ ↦ ?_⟩
  rw [localFourier_pullbackInl_eq_tsum _ hU _ hδ hχ1 L hL hε
    (exists_decay_localFourier hV0 hε.le hχΓ u) ξ]
  exact hpV u ξ hξ

omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ D]
  [FiniteDimensional ℝ D] [MeasurableSpace E] [BorelSpace E] [MeasurableSpace D] [BorelSpace D] in
/-- No point of `ιᵀ Γ` over `K ⊆ U` lies in the direction `0`, when `Γ` contains neither zero
covectors nor conormal covectors of `E × {0}` over `U`. -/
private theorem disjoint_prod_zero_pullbackInlCone (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Set E} (hKU : K ⊆ U) : Disjoint (K ×ˢ ({0} : Set E)) (pullbackInlCone Γ) := by
  refine disjoint_left.2 ?_
  rintro ⟨x, ξ⟩ ⟨hx, hξ⟩ hmem
  obtain ⟨η, hη⟩ := mem_pullbackInlCone.1 hmem
  rw [mem_singleton_iff] at hξ
  subst hξ
  rcases eq_or_ne η 0 with rfl | hη0
  · exact hΓ0 _ hη (by simp)
  · exact hN x (hKU hx) η hη0 hη


/-- **The pullback on a compact set of test functions.** For a compact set `Q` of complex test
functions supported in a common compact subset `K` of `U`, the values `ι^* T ψ`, `ψ ∈ Q`, are
bounded by a continuous seminorm of `𝓓'_Γ(W)`. -/
private theorem exists_seminorm_localFourier_zero_pullbackInl_le
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    {K : Compacts E} (hKU : (K : Set E) ⊆ U) {Q : Set 𝓓(U, ℂ)} (hQ : IsCompact Q)
    (hQK : ∀ ψ ∈ Q, tsupport ψ ⊆ K) :
    ∃ p : Seminorm ℂ (WaveFrontSpace W Γ), Continuous p ∧ ∀ u : WaveFrontSpace W Γ, ∀ ψ ∈ Q,
      ‖(u.toDistribution.pullbackInl hU (notMem_waveFrontSet hN u)).localFourier ψ 0‖ ≤ p u := by
  obtain ⟨ε, hε, δ, hδ, χ, hχ1, hχΓ⟩ := exists_cutoff_forall_notMem hU hΓ hcone hΓ0 K.isCompact
    hKU isClosed_singleton (mem_singleton 0) forall_smul_mem_singleton_zero
    (disjoint_prod_zero_pullbackInlCone hΓ0 hN hKU)
  obtain ⟨L, _, _, hL⟩ :=
    ZLattice.exists_forall_add_mem_eq_zero_of_isBounded χ.hasCompactSupport.isCompact.isBounded
  obtain ⟨p, hp, hpQ⟩ := exists_continuous_seminorm_norm_tsum_le (fstL 2 ℝ E D) hε
    (fun p hp ζ hζ ↦ hχΓ p hp ζ (by simpa using hζ)) L hQ
  refine ⟨p, hp, fun u ψ hψ ↦ ?_⟩
  rw [localFourier_pullbackInl_eq_tsum _ hU _ hδ (fun x hx ↦ hχ1 x (hQK ψ hψ hx)) L hL hε
    (exists_decay_localFourier (mem_singleton 0) hε.le hχΓ u) 0]
  simp only [zero_add]
  exact hpQ u ψ hψ

end Measurable

/-! ### The pullback as a continuous linear map -/

/-- The pullback `ι^* : 𝓓'_Γ(W) → 𝓓'_{ιᵀ Γ}(U)` as a linear map, before its continuity is
proved. -/
private def pullbackInlₗ (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →ₗ[ℂ] WaveFrontSpace U (pullbackInlCone Γ) where
  toFun u := mk (u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
      hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem))
    (waveFrontSet_pullbackInl_subset_pullbackInlCone hU _ u.waveFrontSet_toDistribution_subset)
  map_add' u v := ext <| by
    simp only [toDistribution_mk, map_add]
    exact pullbackInl_add hU (notMem_waveFrontSet hN u) (notMem_waveFrontSet hN v)
  map_smul' c u := ext <| by
    simp only [toDistribution_mk, map_smul, RingHom.id_apply]
    exact pullbackInl_smul hU c (notMem_waveFrontSet hN u)

private theorem toDistribution_pullbackInlₗ
    (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlₗ hU hN u).toDistribution =
      u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
        hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem) :=
  toDistribution_mk _ _

/-- **Continuity of the pullback to `E × {0}` in the normal topology.** Let `Γ` be a cone of
nonzero covectors over `W`, closed in `W × ((E × D) \ {0})`, containing no conormal covector
`((x, 0), (0, η))` of `E × {0}` over `U`. Then the pullback `ι^* T` along `ι : x ↦ (x, 0)`
(`Distribution.pullbackInl`) is a continuous linear map from `𝓓'_Γ(W)` to `𝓓'_{ιᵀ Γ}(U)`, where
`ιᵀ Γ = {(x, ξ) | ∃ η, ((x, 0), (ξ, η)) ∈ Γ}` (Brouder, Dang and Hélein, Theorem 6.3, for the
linear injection `ι`). -/
def pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ) :
    WaveFrontSpace W Γ →L[ℂ] WaveFrontSpace U (pullbackInlCone Γ) :=
  ⟨pullbackInlₗ hU hN, by
    borelize E D
    exact continuous_linearMap_of_forall_isCompact_le _
      (fun _ hKU _ hQ hQK ↦ by
        simpa only [toDistribution_pullbackInlₗ] using
          exists_seminorm_localFourier_zero_pullbackInl_le hU hΓ hcone hΓ0 hN hKU hQ hQK)
      fun j ↦ by
        simpa only [toDistribution_pullbackInlₗ] using
          exists_seminorm_localFourier_pullbackInl_le hU hΓ hcone hΓ0 hN j⟩

@[simp]
theorem toDistribution_pullbackInlCLM (hU : MapsTo (fun x ↦ toLp 2 (x, (0 : D))) (U : Set E) W)
    (hΓ : IsOpen (((W : Set (WithLp 2 (E × D))) ×ˢ {0}ᶜ) \ Γ))
    (hcone : ∀ p ∈ Γ, ∀ t : ℝ, 0 < t → (p.1, t • p.2) ∈ Γ) (hΓ0 : ∀ p ∈ Γ, p.2 ≠ 0)
    (hN : ∀ x ∈ U, ∀ η : D, η ≠ 0 → (toLp 2 (x, (0 : D)), toLp 2 ((0 : E), η)) ∉ Γ)
    (u : WaveFrontSpace W Γ) :
    (pullbackInlCLM hU hΓ hcone hΓ0 hN u).toDistribution =
      u.toDistribution.pullbackInl hU fun x hx η hη hmem ↦
        hN x hx η hη (u.waveFrontSet_toDistribution_subset hmem) :=
  toDistribution_pullbackInlₗ hU hN u

end WaveFrontSpace

end TauCeti
