/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.Pullback

/-!
# Pushforward of compactly supported currents and distributions along smooth maps

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

The same construction pushes forward a distribution `T` on `Ω`, a continuous linear map on real
test functions: `Φ_* T = T ∘ (χ Φ^*)`, where `χ Φ^* g = χ (g ∘ Φ)` is
`TestFunction.cutoffCompCLM`. With `χ` equal to one near the support of `T`, it does not depend on
`χ` and it is `T` for the identity map; in general it is the pushforward of `χ T`, it is
functorial, and its support lies in the image of `supp χ ∩ supp T`. The pushforward of the point
mass at `x` is `χ x` times the point mass at `Φ x`, and pushing `T` forward along a constant map
concentrates `χ T` at the image point.

## Main declarations

* `ContinuousLinearMap.comp_cutoffPullbackCLM_congr`: independence of the cutoff.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_eq_comp_pullbackCLM`: agreement with the
  pushforward along a proper map.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_extDerivCLM`: `∂ (Φ_# T) = Φ_# (∂ T)`.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_cutoffPullbackCLM`: functoriality.
* `Distribution.dsupport_comp_cutoffPullbackCLM_subset`: `spt (Φ_# T) ⊆ Φ (tsupport χ ∩ spt T)`.
* `Distribution.mass_comp_cutoffPullbackCLM_le`: `M(Φ_# T) ≤ L ^ k M(T)`.
* `Distribution.cutoffPushforwardCLM`: the pushforward `T ↦ T ∘ (χ Φ^*)` of distributions, with
  `Distribution.cutoffPushforwardCLM_congr` (independence of the cutoff),
  `Distribution.cutoffPushforwardCLM_id`, `Distribution.cutoffPushforwardCLM_cutoffPushforwardCLM`
  (functoriality), `Distribution.dsupport_cutoffPushforwardCLM_subset` (support),
  `Distribution.cutoffPushforwardCLM_id_eq_smulLeftCLM` (along the identity it is `χ T`),
  `Distribution.cutoffPushforwardCLM_mapCLM`, `Distribution.cutoffPushforwardCLM_delta` and
  `Distribution.cutoffPushforwardCLM_const_apply`.
* `Distribution.complexPairing_cutoffPushforwardCLM`: the complex-linear extension of `Φ_* T` to
  complex test functions is computed by the same formula.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the pushforward of a current whose support is
  compact, defined with a cutoff).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §6.1 (the pushforward of
  a distribution along a map proper on its support, there along a projection).
-/

public section

open Set Filter TopologicalSpace TestFunction Distribution
open scoped Distributions Topology NNReal ENNReal BoundedContinuousFunction

/-- If `χ'` is equal to one near the image under `Φ` of the part of `s` in the support of `χ`, then
near `s` either `χ' ∘ Φ` is equal to one or `χ` vanishes: the two cutoffs of a composite
pushforward agree with the single cutoff `χ` near `s`. -/
private theorem eventually_cutoff_comp_eq_one_or_eq_zero {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'}
    {Φ : E → E'} {χ : 𝓓(Ω, ℝ)} {χ' : 𝓓(Ω', ℝ)} {s : Set E} (hΦ : ContinuousOn Φ Ω)
    (hχ' : ∀ᶠ y in 𝓝ˢ (Φ '' (tsupport χ ∩ s)), χ' y = 1) :
    ∀ᶠ x in 𝓝ˢ s, χ' (Φ x) = 1 ∨ χ x = 0 := by
  rw [eventually_nhdsSet_iff_forall] at hχ' ⊢
  intro x hx
  by_cases hxχ : x ∈ tsupport χ
  · exact ((hΦ.continuousAt (Ω.isOpen.mem_nhds (χ.tsupport_subset hxχ))).tendsto.eventually
      (hχ' (Φ x) ⟨x, ⟨hxχ, hx⟩, rfl⟩)).mono fun _ h ↦ Or.inl h
  · exact eventually_of_mem ((isClosed_tsupport χ).isOpen_compl.mem_nhds hxχ) fun _ h ↦
      Or.inr (image_eq_zero_of_notMem_tsupport h)

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

/-- **Functoriality of the pushforward**: `(Ψ ∘ Φ)_# T = Ψ_# (Φ_# T)`, when `χ'` is equal to one
near the image under `Φ` of the part of the support of `T` in the support of `χ`. -/
theorem comp_cutoffPullbackCLM_comp_cutoffPullbackCLM (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    {Ψ : E' → E''} {χ' : 𝓓(Ω', ℝ)} {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'}
    {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω}
    (hχ' : ∀ᶠ y in 𝓝ˢ (Φ '' (tsupport χ ∩ dsupport T)), χ' y = 1) :
    (T ∘L cutoffPullbackCLM χ Φ hΦ) ∘L
        (cutoffPullbackCLM χ' Ψ hΨ : 𝓓(Ω'', E'' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (Ψ ∘ Φ) hΨΦ := by
  ext ω
  simp only [comp_apply]
  refine map_eq_map_of_eventuallyEq T
    ((eventually_cutoff_comp_eq_one_or_eq_zero hΦ.continuousOn hχ').mono fun x hx ↦ ?_)
  rw [cutoffPullbackCLM_cutoffPullbackCLM (hΨΦ := hΨΦ) ω x]
  rcases hx with hx | hx
  · rw [hx, one_smul]
  · simp [hx]

end ContinuousLinearMap

namespace Distribution

variable {E E' E'' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {Φ : E → E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {𝓕 : Type*}

/-- The support of `T ∘ P` lies in the image under `Φ` of the part of the support of `T` in the
support of `χ`, for every map `P` of test functions whose values `P ω` are supported in the support
of `χ`, over the support of `ω`. -/
private theorem dsupport_comp_subset_image [FiniteDimensional ℝ E] {W W' : Type*}
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedAddCommGroup W'] [NormedSpace ℝ W']
    [AddCommMonoid V] [FunLike 𝓕 𝓓(Ω, W) V] [AddMonoidHomClass 𝓕 𝓓(Ω, W) V] (T : 𝓕)
    (hΦ : ContinuousOn Φ Ω) {P : 𝓓(Ω', W') → 𝓓(Ω, W)}
    (hP : ∀ ω, tsupport (P ω) ⊆ tsupport χ ∩ Φ ⁻¹' tsupport ω) :
    dsupport (T ∘ P) ⊆ Φ '' (tsupport χ ∩ dsupport T) := by
  have hS : IsCompact (Φ '' (tsupport χ ∩ dsupport T)) :=
    (IsCompact.inter_right χ.hasCompactSupport isClosed_dsupport).image_of_continuousOn
      (hΦ.mono (inter_subset_left.trans χ.tsupport_subset))
  -- A test form supported off this image is sent to a test form supported off `spt T`.
  have hvan : IsVanishingOn (T ∘ P) (Φ '' (tsupport χ ∩ dsupport T))ᶜ := fun ω hω ↦
    map_eq_zero_of_disjoint_dsupport T <| disjoint_left.2 fun x hx hxT ↦
      hω (hP ω hx).2 ⟨x, ⟨(hP ω hx).1, hxT⟩, rfl⟩
  have h := (hvan.disjoint_dsupport hS.isClosed.isOpen_compl).subset_compl_left
  rwa [compl_compl] at h

/-- **The support of a pushforward**: the support of `T ∘ (χ Φ^*)` lies in the image under `Φ` of
the part of the support of `T` in the support of `χ`. In particular it is compact, and when `χ` is
equal to one near the support of `T`, it lies in the image of the support of `T`. -/
theorem dsupport_comp_cutoffPullbackCLM_subset [FiniteDimensional ℝ E] [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    dsupport (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ⊆
      Φ '' (tsupport χ ∩ dsupport T) :=
  dsupport_comp_subset_image T hΦ.continuousOn tsupport_cutoffPullbackCLM_subset

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

/-! ### Pushforward of distributions -/

section Pushforward

variable {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G] [IsTopologicalAddGroup G]
  [ContinuousSMul ℝ G]

/-- The **pushforward of a distribution with a cutoff**: a distribution `T` on `Ω` and a test
function `χ` on `Ω` give the distribution `g ↦ T (χ (g ∘ Φ))` on `Ω'`, for every map `Φ` smooth
on `Ω`. When `χ` is equal to one near the support of `T` (which is then compact), this is the
pushforward `Φ_* T` of `T`: it does not depend on such `χ`
(`Distribution.cutoffPushforwardCLM_congr`) and it is `T` for the identity map. In general it is
the pushforward of `χ T`, and it is functorial. -/
noncomputable def cutoffPushforwardCLM (χ : 𝓓(Ω, ℝ)) (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
    𝓓'(Ω, G) →L[ℝ] 𝓓'(Ω', G) :=
  (cutoffCompCLM χ Φ hΦ).precompCompactConvergenceCLM G

/-- The pushforward with a cutoff pairs a test function `g` with `T` through `T (χ (g ∘ Φ))`. -/
@[simp]
theorem cutoffPushforwardCLM_apply (T : 𝓓'(Ω, G)) (g : 𝓓(Ω', ℝ)) :
    cutoffPushforwardCLM χ Φ hΦ T g = T (cutoffCompCLM χ Φ hΦ g) :=
  (rfl)

/-- Along the identity, the pushforward with a cutoff `χ` is the product `χ T`. -/
@[simp]
theorem cutoffPushforwardCLM_id_eq_smulLeftCLM {hid : ContDiffOn ℝ (⊤ : ℕ∞) (id : E → E) Ω}
    (T : 𝓓'(Ω, G)) : (cutoffPushforwardCLM χ id hid T : 𝓓'(Ω, G)) = smulLeftCLM χ.contDiff T := by
  ext g
  rw [cutoffPushforwardCLM_apply, smulLeftCLM_apply]
  congr 1
  ext x
  simp

/-- The pushforward commutes with a continuous linear map applied to the values of a
distribution. -/
@[simp]
theorem cutoffPushforwardCLM_mapCLM {G' : Type*} [AddCommGroup G'] [Module ℝ G']
    [TopologicalSpace G'] [IsTopologicalAddGroup G'] [ContinuousSMul ℝ G'] (A : G →L[ℝ] G')
    (T : 𝓓'(Ω, G)) :
    (cutoffPushforwardCLM χ Φ hΦ (mapCLM A T) : 𝓓'(Ω', G')) =
      mapCLM A (cutoffPushforwardCLM χ Φ hΦ T) := by
  ext g
  simp

/-- The pushforward of the point mass at `x` with a cutoff `χ` is `χ x` times the point mass at
`Φ x`. -/
@[simp]
theorem cutoffPushforwardCLM_delta (x : E) :
    cutoffPushforwardCLM χ Φ hΦ (delta x : 𝓓'(Ω, ℝ)) = χ x • (delta (Φ x) : 𝓓'(Ω', ℝ)) := by
  ext g
  simp [delta_apply]

/-- The pushforward of `T` along the constant map at `y` pairs a test function `g` with
`g y • T χ`: all of `χ T` is concentrated at `y`. The simplifier computes it through
`TestFunction.cutoffCompCLM_const`. -/
theorem cutoffPushforwardCLM_const_apply (y : E') (T : 𝓓'(Ω, G)) (g : 𝓓(Ω', ℝ)) :
    cutoffPushforwardCLM χ (fun _ ↦ y) contDiffOn_const T g = g y • T χ := by
  rw [cutoffPushforwardCLM_apply, cutoffCompCLM_const, map_smul]

/-- **The support of a pushforward**: the support of the pushforward of `T` with a cutoff `χ` lies
in the image under `Φ` of the part of the support of `T` in the support of `χ`. In particular it
is compact. -/
theorem dsupport_cutoffPushforwardCLM_subset [FiniteDimensional ℝ E] (T : 𝓓'(Ω, G)) :
    dsupport (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', G)) ⊆ Φ '' (tsupport χ ∩ dsupport T) := by
  rw [show ⇑(cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', G)) = T ∘ cutoffCompCLM χ Φ hΦ from
    funext (cutoffPushforwardCLM_apply T)]
  exact dsupport_comp_subset_image T hΦ.continuousOn tsupport_cutoffCompCLM_subset

variable [FiniteDimensional ℝ E]

/-- **Independence of the cutoff**: the pushforward of `T` with a cutoff `χ` depends only on the
germ of `χ` along the part of the support of `T` that `Φ` maps into `Ω'`. -/
theorem cutoffPushforwardCLM_congr (T : 𝓓'(Ω, G)) {χ₁ χ₂ : 𝓓(Ω, ℝ)}
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T ∩ Φ ⁻¹' Ω')] χ₂) :
    (cutoffPushforwardCLM χ₁ Φ hΦ T : 𝓓'(Ω', G)) = cutoffPushforwardCLM χ₂ Φ hΦ T := by
  ext g
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply]
  refine map_eq_map_of_eventuallyEq T (eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_)
  by_cases hxΦ : Φ x ∈ Ω'
  · exact (eventually_nhdsSet_iff_forall.1 h x ⟨hx, hxΦ⟩).mono fun y hy ↦ by simp [hy]
  by_cases hxΩ : x ∈ Ω
  · -- `g ∘ Φ` vanishes near `x`, since `Φ x` lies outside the support of `g`.
    filter_upwards [(hΦ.continuousOn.continuousAt (Ω.isOpen.mem_nhds hxΩ)).preimage_mem_nhds
      ((isClosed_tsupport g).isOpen_compl.mem_nhds fun hg ↦ hxΦ (g.tsupport_subset hg))]
      with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · -- Both cutoffs vanish near `x`, which lies outside `Ω`.
    filter_upwards [(isClosed_tsupport χ₁).isOpen_compl.mem_nhds
        fun h₁ ↦ hxΩ (χ₁.tsupport_subset h₁),
      (isClosed_tsupport χ₂).isOpen_compl.mem_nhds fun h₂ ↦ hxΩ (χ₂.tsupport_subset h₂)]
      with y hy₁ hy₂
    simp [image_eq_zero_of_notMem_tsupport hy₁, image_eq_zero_of_notMem_tsupport hy₂]

/-- **The pushforward along the identity**: if `χ` is equal to one near the support of `T`, then
pushing `T` forward along the identity of `Ω` gives back `T`. -/
theorem cutoffPushforwardCLM_id (T : 𝓓'(Ω, G)) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (cutoffPushforwardCLM χ id contDiffOn_id T : 𝓓'(Ω, G)) = T := by
  ext g
  rw [cutoffPushforwardCLM_apply]
  exact map_eq_map_of_eventuallyEq T (hχ.mono fun x hx ↦ by simp [hx])

/-- **Functoriality of the pushforward**: `(Ψ ∘ Φ)_* T = Ψ_* (Φ_* T)` for the pushforwards of
`χ T`, when `χ'` is equal to one near the image under `Φ` of the part of the support of `T` in the
support of `χ`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM (T : 𝓓'(Ω, G)) {Ψ : E' → E''} {χ' : 𝓓(Ω', ℝ)}
    {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'} {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω}
    (hχ' : ∀ᶠ y in 𝓝ˢ (Φ '' (tsupport χ ∩ dsupport T)), χ' y = 1) :
    (cutoffPushforwardCLM χ' Ψ hΨ (cutoffPushforwardCLM χ Φ hΦ T) : 𝓓'(Ω'', G)) =
      cutoffPushforwardCLM χ (Ψ ∘ Φ) hΨΦ T := by
  ext g
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply]
  refine map_eq_map_of_eventuallyEq T
    ((eventually_cutoff_comp_eq_one_or_eq_zero hΦ.continuousOn hχ').mono fun x hx ↦ ?_)
  rcases hx with hx | hx <;> simp [hx]

end Pushforward

/-- The complex-linear extension of the pushforward of a complex distribution `T` with a cutoff
`χ` pairs a complex test function `g` with `T` through `T (χ (g ∘ Φ))`. -/
@[simp]
theorem complexPairing_cutoffPushforwardCLM (T : 𝓓'(Ω, ℂ)) (g : 𝓓(Ω', ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T).complexPairing g =
      T.complexPairing (cutoffCompCLM χ Φ hΦ g) := by
  simp only [complexPairing_apply, cutoffPushforwardCLM_apply]
  congr 3 <;> ext x <;> simp

end Distribution
