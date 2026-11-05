/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.Pullback

/-!
# Pushforward of compactly supported currents along smooth maps

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, with `E` finite-dimensional, and
let `T` be a current on `Ω`: a continuous linear map on test `k`-forms. Pushing `T` forward along a
map `Φ : E → E'` by `Φ_# T = T ∘ Φ^*` needs the pullback `Φ^* ω` of a test form on `Ω'` to be a
test form on `Ω`, which holds when `Φ` is proper from `Ω` to `Ω'` (`TestFunction.pullbackCLM`).
When the support of `T` is a compact subset of `Ω`, properness is not needed: choose a test
function `χ` on `Ω` equal to one near the support of `T` (`TestFunction.exists_eventually_eq_one`)
and put

`Φ_# T = T ∘ (χ Φ^*)`,

where `χ Φ^*` is the pullback with cutoff `TestFunction.cutoffPullbackCLM`, defined for every map
`Φ` smooth on `Ω`. This file proves:

* `Φ_# T` does not depend on the cutoff: only the germ of `χ` along the support of `T` matters;
* when `Φ` is proper, `Φ_# T` is the pushforward `T ∘ Φ^*`;
* `∂ (Φ_# T) = Φ_# (∂ T)`, where `∂ T = T ∘ d`;
* the support of `Φ_# T` lies in the image under `Φ` of the support of `T`;
* if `|χ| ≤ 1` and `‖DΦ‖ ≤ L` on the support of `χ`, then `M(Φ_# T) ≤ L ^ k M(T)`;
* functoriality: `(Ψ ∘ Φ)_# T = Ψ_# (Φ_# T)`.

## Main declarations

* `ContinuousLinearMap.comp_cutoffPullbackCLM_congr`: independence of the cutoff.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_eq_comp_pullbackCLM`: agreement with the
  pushforward along a proper map.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_extDerivCLM`: `∂ (Φ_# T) = Φ_# (∂ T)`.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_cutoffPullbackCLM`: functoriality.
* `Distribution.dsupport_comp_cutoffPullbackCLM_subset`: `spt (Φ_# T) ⊆ Φ (tsupport χ ∩ spt T)`.
* `Distribution.mass_comp_cutoffPullbackCLM_le`: `M(Φ_# T) ≤ L ^ k M(T)`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the pushforward of a current whose support is
  compact, defined with a cutoff).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
-/

public section

open Set Filter TopologicalSpace TestFunction Distribution
open scoped Distributions Topology NNReal ENNReal BoundedContinuousFunction

namespace ContinuousLinearMap

variable {E E' E'' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F] [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {Φ : E → E'} {k : ℕ} {χ χ₁ χ₂ : 𝓓(Ω, ℝ)}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}

/-- **Independence of the cutoff**: the pushforward `T ∘ (χ Φ^*)` of a current `T` depends only on
the germ of `χ` along the support of `T`. -/
theorem comp_cutoffPullbackCLM_congr (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₂) :
    (T ∘L cutoffPullbackCLM χ₁ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) =
      T ∘L cutoffPullbackCLM χ₂ Φ hΦ := by
  ext ω
  exact map_eq_map_of_eventuallyEq T (h.mono fun x hx ↦ by simp [hx])

/-- **Agreement with the proper pushforward**: if `Φ` is proper from `Ω` to `Ω'` and `χ` is equal to
one near the support of `T`, then `T ∘ (χ Φ^*) = T ∘ Φ^*`. -/
theorem comp_cutoffPullbackCLM_eq_comp_pullbackCLM (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)) :
    (T ∘L cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) =
      T ∘L pullbackCLM Φ hΦ hΦp := by
  ext ω
  refine map_eq_map_of_eventuallyEq T (hχ.mono fun x hx ↦ ?_)
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hx]))
  simp [hx, hxΩ]

/-- **The pushforward commutes with the boundary**: if `χ` is equal to one near the support of a
current `T` on test `(k + 1)`-forms, then `∂ (T ∘ (χ Φ^*)) = (∂ T) ∘ (χ Φ^*)`, where
`∂ T = T ∘ d`. The support of `∂ T` lies in that of `T`, so the right-hand side is the pushforward
of `∂ T`. -/
theorem comp_cutoffPullbackCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L cutoffPullbackCLM χ Φ hΦ) ∘L (extDerivCLM : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      (T ∘L extDerivCLM) ∘L cutoffPullbackCLM χ Φ hΦ := by
  ext ω
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  exact (extDerivCLM_cutoffPullbackCLM_apply ω hx).symm

/-- **Functoriality of the pushforward**: `(Ψ ∘ Φ)_# T = Ψ_# (Φ_# T)`, when `χ` is equal to one near
the support of `T`, `χ'` is equal to one near its image under `Φ`, and `Φ` maps the support of `χ`
into `Ω'`. -/
theorem comp_cutoffPullbackCLM_comp_cutoffPullbackCLM (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    {Ψ : E' → E''} {χ' : 𝓓(Ω', ℝ)} {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'}
    {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω} (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hχ' : ∀ᶠ y in 𝓝ˢ (Φ '' dsupport T), χ' y = 1) (hmaps : MapsTo Φ (tsupport χ) Ω') :
    (T ∘L cutoffPullbackCLM χ Φ hΦ) ∘L
        (cutoffPullbackCLM χ' Ψ hΨ : 𝓓(Ω'', E'' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (Ψ ∘ Φ) hΨΦ := by
  have hTΩ : dsupport T ⊆ Ω := fun x hx ↦
    χ.tsupport_subset (subset_tsupport _ (by simp [hχ.self_of_nhdsSet x hx]))
  -- `Φ` is continuous on `Ω`, so `χ' ∘ Φ` is equal to one near the support of `T`.
  have hχ'Φ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ' (Φ x) = 1 := by
    rw [eventually_nhdsSet_iff_forall] at hχ' ⊢
    exact fun x hx ↦ (hΦ.continuousOn.continuousAt (Ω.isOpen.mem_nhds (hTΩ hx))).tendsto.eventually
      (hχ' (Φ x) (mem_image_of_mem Φ hx))
  ext ω
  simp only [comp_apply]
  refine map_eq_map_of_eventuallyEq T (hχ'Φ.mono fun x hx ↦ ?_)
  exact (cutoffPullbackCLM_cutoffPullbackCLM (hΨΦ := hΨΦ) hmaps ω x).trans (by rw [hx, one_smul])

end ContinuousLinearMap

namespace Distribution

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {Φ : E → E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {𝓕 : Type*}

/-- **The support of a pushforward**: the support of `T ∘ (χ Φ^*)` lies in the image under `Φ` of
the part of the support of `T` in the support of `χ`. In particular it is compact, and when `χ` is
equal to one near the support of `T`, it lies in the image of the support of `T`. -/
theorem dsupport_comp_cutoffPullbackCLM_subset [FiniteDimensional ℝ E] [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    dsupport (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ⊆
      Φ '' (tsupport χ ∩ dsupport T) := by
  have hS : IsCompact (Φ '' (tsupport χ ∩ dsupport T)) :=
    (IsCompact.inter_right χ.hasCompactSupport isClosed_dsupport).image_of_continuousOn
      (hΦ.continuousOn.mono (inter_subset_left.trans χ.tsupport_subset))
  -- A test form supported off this image pulls back to a test form supported off `spt T`.
  have hvan : IsVanishingOn (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _))
      (Φ '' (tsupport χ ∩ dsupport T))ᶜ := fun ω hω ↦
    map_eq_zero_of_disjoint_dsupport T <| disjoint_left.2 fun x hx hxT ↦
      hω (tsupport_cutoffPullbackCLM_subset ω hx).2 ⟨x, ⟨(tsupport_cutoffPullbackCLM_subset ω hx).1,
        hxT⟩, rfl⟩
  have h := (hvan.disjoint_dsupport hS.isClosed.isOpen_compl).subset_compl_left
  rwa [compl_compl] at h

/-- **The mass of a pushforward**: if `|χ| ≤ 1` and `‖DΦ‖ ≤ L` on the support of `χ`, then the
pushforward `T ∘ (χ Φ^*)` of a `k`-current `T` has mass at most `L ^ k` times the mass of `T`. -/
theorem mass_comp_cutoffPullbackCLM_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) (hχ : ∀ x, |χ x| ≤ 1) {L : ℝ≥0} (hL : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ x‖ ≤ L) :
    mass (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ≤
      (L : ℝ≥0∞) ^ k * mass T := by
  refine mass_le_iff.2 fun ω hω ↦ ?_
  have hb : ‖(cutoffPullbackCLM χ Φ hΦ ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ ≤ L ^ k := by
    refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun x ↦ ?_
    rw [coe_toBoundedContinuousFunction]
    by_cases hx : x ∈ tsupport χ
    · refine (norm_cutoffPullbackCLM_apply_le ω x).trans ?_
      calc |χ x| * (‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k) ≤ 1 * (1 * (L : ℝ) ^ k) := by
            gcongr
            exacts [hχ x, hω _, hL x hx]
        _ = L ^ k := by ring
    · simp [image_eq_zero_of_notMem_tsupport hx]
  calc ‖T (cutoffPullbackCLM χ Φ hΦ ω)‖ₑ
      ≤ mass T * ‖(cutoffPullbackCLM χ Φ hΦ ω : E →ᵇ E [⋀^Fin k]→L[ℝ] F)‖ₑ :=
        enorm_apply_le_mass_mul T _
    _ ≤ mass T * (L : ℝ≥0∞) ^ k := by
        gcongr
        rw [← ofReal_norm, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_pow L.coe_nonneg]
        exact ENNReal.ofReal_le_ofReal hb
    _ = (L : ℝ≥0∞) ^ k * mass T := mul_comm _ _

end Distribution
