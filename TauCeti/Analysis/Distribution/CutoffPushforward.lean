/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.ComplexPairing
public import TauCeti.Analysis.Distribution.SmulLeft
public import TauCeti.Analysis.Distribution.Support
public import TauCeti.Analysis.Distribution.TestFunction.Homotopy
import TauCeti.Analysis.Calculus.ContDiff.Bounds
import TauCeti.Analysis.Calculus.FDeriv.Prod

/-!
# Pushforward of compactly supported currents and distributions along smooth maps

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, and
let `T` be a current on `Ω`: a continuous linear map on test `k`-forms. Pushing `T` forward along a
map `Φ : E → E'` by `Φ_# T = T ∘ Φ^*` needs the pullback `Φ^* ω` of a test form on `Ω'` to be a
test form on `Ω`, which holds when `Φ` is proper from `Ω` to `Ω'` (`TestFunction.pullbackCLM`).
When the support of `T` is a compact subset of `Ω`, properness is not needed: choose a test
function `χ` on `Ω` equal to one near the support of `T` (when `E` is finite-dimensional,
`TestFunction.exists_eventually_eq_one` supplies one) and put

`Φ_# T = T ∘ (χ Φ^*)`,

where `χ Φ^*` is the pullback with cutoff `TestFunction.cutoffPullbackCLM`, defined for every map
`Φ` smooth on `Ω`. This file proves:

* `Φ_# T` does not depend on the cutoff: only the germ of `χ` along the support of `T` matters;
* when `Φ` is proper, `Φ_# T` is the pushforward `T ∘ Φ^*`;
* `∂ (Φ_# T) = Φ_# (∂ T)`, where `∂ T = T ∘ d`;
* the support of `Φ_# T` lies in the image under `Φ` of the support of `T`, and for a proper `Φ`
  the support of `T ∘ Φ^*` lies in the closure of that image;
* if `|χ| ≤ 1` and `‖DΦ‖ ≤ L` on the support of `χ`, then `M(Φ_# T) ≤ L ^ k M(T)`;
* functoriality: `(Ψ ∘ Φ)_# T = Ψ_# (Φ_# T)`.

For a homotopy `H` smooth near `Ω × [0, 1]`, not necessarily proper, the homotopy current
`H_# ([[0, 1]] × T) = T ∘ K_χ` is defined with the homotopy operator with cutoff
`TestFunction.cutoffHomotopyPullbackCLM`. It does not depend on the cutoff, agrees with
`T ∘ TestFunction.homotopyPullbackCLM` when `H` is proper, and satisfies the **homotopy formula**
`∂ H_# ([[0, 1]] × T) + H_# ([[0, 1]] × ∂ T) = H₁# T - H₀# T`, where `Hₜ = H (·, t)`. Its support
lies in the image under `H` of `(tsupport χ ∩ spt T) × [0, 1]`, and
`M(H_# ([[0, 1]] × T)) ≤ A L ^ k M(T)` when `|χ| ≤ 1`, `‖∂ₜ H‖ ≤ A` and the spatial derivative of
`H` is bounded by `L` on `tsupport χ × [0, 1]`.

The same construction pushes forward distributions `T : 𝓓'(Ω, F)`: the composition with a cutoff
`TestFunction.cutoffCompCLM χ Φ`, `f ↦ χ (f ∘ Φ)`, takes test functions on `Ω'` to test functions
on `Ω`, and `Distribution.cutoffPushforwardCLM χ Φ` is its transpose `T ↦ T ∘ (χ Φ^*)`. When `χ`
is equal to one near the support of `T`, this is the pushforward `Φ_* T` of a distribution with
compact support: it does not depend on `χ` and it is `T` for the identity map. In general it is
the pushforward of `χ T`, it is functorial, and its support lies in the image of
`supp χ ∩ supp T`. The pushforward of the point mass at `x` is `χ x` times the point mass at
`Φ x`, and along a constant map with value `c` it is the multiple `T χ` of the point mass at `c`,
whatever the regularity of `T`.

## Main declarations

* `ContinuousLinearMap.comp_cutoffPullbackCLM_congr`: independence of the cutoff.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_eq_comp_pullbackCLM`: agreement with the
  pushforward along a proper map.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_extDerivCLM`: `∂ (Φ_# T) = Φ_# (∂ T)`.
* `ContinuousLinearMap.comp_cutoffPullbackCLM_comp_cutoffPullbackCLM`: functoriality.
* `Distribution.dsupport_comp_subset_image_of_tsupport_subset`: the support of `T ∘ P` for an
  operator `P` on test functions with `tsupport (P φ) ⊆ tsupport χ ∩ Φ ⁻¹' tsupport φ`.
* `Distribution.dsupport_comp_cutoffPullbackCLM_subset`: `spt (Φ_# T) ⊆ Φ (tsupport χ ∩ spt T)`.
* `Distribution.dsupport_comp_pullbackCLM_subset`: for a proper map `Φ`,
  `spt (Φ_# T) ⊆ closure (Φ (Ω ∩ spt T))`.
* `Distribution.mass_comp_cutoffPullbackCLM_le`: `M(Φ_# T) ≤ L ^ k M(T)`.
* `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_congr`,
  `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_eq_comp_homotopyPullbackCLM`: independence of
  the cutoff and agreement with the proper homotopy current.
* `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM`: the homotopy formula, and
  `ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero` in degree zero.
* `Distribution.dsupport_comp_cutoffHomotopyPullbackCLM_subset`,
  `Distribution.mass_comp_cutoffHomotopyPullbackCLM_le`: the support and mass of the homotopy
  current.
* `Distribution.IsLocallyNormal.isNormal_comp_cutoffHomotopyPullbackCLM`,
  `Distribution.IsNormal.comp_cutoffHomotopyPullbackCLM`: the homotopy current `T ∘ K_χ` of a
  locally normal current `T` is normal.
* `Distribution.cutoffPushforwardCLM`: the pushforward of distributions with a cutoff, with its
  independence of the cutoff `Distribution.cutoffPushforwardCLM_congr`, its support
  `Distribution.dsupport_cutoffPushforwardCLM_subset`, its complex-linear extension
  `Distribution.complexPairing_cutoffPushforwardCLM`, its functoriality
  `Distribution.cutoffPushforwardCLM_id`, `Distribution.cutoffPushforwardCLM_cutoffPushforwardCLM`,
  `Distribution.cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one`, its value
  `Distribution.cutoffPushforwardCLM_id_eq_smulLeftCLM` along the identity, its commutation
  `Distribution.mapCLM_cutoffPushforwardCLM` with maps of the values, the image
  `Distribution.cutoffPushforwardCLM_delta` of a point mass, and its value along a constant map
  `Distribution.cutoffPushforwardCLM_const_apply`, the point mass
  `Distribution.cutoffPushforwardCLM_const`.

## References

* H. Federer, *Geometric Measure Theory*, §4.1.7 (the pushforward of a current whose support is
  compact, defined with a cutoff) and §4.1.9 (the homotopy formula).
* L. Simon, *Introduction to Geometric Measure Theory*, Chapter 6, §2.
* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.2 (the pushforward
  of a distribution along a map proper on its support, before Theorem 8.2.13).
-/

public section

open Set Filter TopologicalSpace TestFunction Distribution TauCeti
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

variable {E E' E'' F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
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

section Homotopy

/-! ### The homotopy formula for currents with compact support -/

variable [CompleteSpace F] {H : E × ℝ → E'}
  {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}

/-- **Independence of the cutoff for homotopy currents**: the current
`T ∘ TestFunction.cutoffHomotopyPullbackCLM χ hH` depends only on the germ of `χ` along the support
of `T`. -/
theorem comp_cutoffHomotopyPullbackCLM_congr (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G)
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T)] χ₂) :
    (T ∘L cutoffHomotopyPullbackCLM χ₁ hH : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) =
      T ∘L cutoffHomotopyPullbackCLM χ₂ hH := by
  ext ω
  exact map_eq_map_of_eventuallyEq T (h.mono fun x hx ↦ by simp [hx])

/-- **Agreement with the proper homotopy current**: if `H` is proper on `Ω × [0, 1]` and `χ` is
equal to one near the support of `T`, then `T ∘ K_χ = T ∘ K`, where `K_χ` and `K` are the homotopy
operators with and without cutoff. -/
theorem comp_cutoffHomotopyPullbackCLM_eq_comp_homotopyPullbackCLM
    (T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1)
    (hHp : ∀ K : Set E', IsCompact K → K ⊆ Ω' →
      IsCompact (((Ω : Set E) ×ˢ Icc (0 : ℝ) 1) ∩ H ⁻¹' K)) :
    (T ∘L cutoffHomotopyPullbackCLM χ hH : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) =
      T ∘L homotopyPullbackCLM hH hHp := by
  ext ω
  refine map_eq_map_of_eventuallyEq T (hχ.mono fun x hx ↦ ?_)
  have hxΩ : x ∈ Ω := χ.tsupport_subset (subset_tsupport _ (by simp [hx]))
  simp [hx, hxΩ]

variable [IsTopologicalAddGroup G]

/-- **The homotopy formula for currents with compact support**: if `χ` is equal to one near the
support of a current `T` on test `(k + 1)`-forms, then
`∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T - H_# ([[0, 1]] × ∂ T)`, where
`H_# ([[0, 1]] × T) = T ∘ K_χ` for the homotopy operator `K_χ` with cutoff, `Hₜ# T = T ∘ (χ Hₜ^*)`
for the slices `Hₜ = H (·, t)` and `∂ T = T ∘ d`. No properness of `H` is needed. -/
theorem comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM
    (T : 𝓓(Ω, E [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L cutoffHomotopyPullbackCLM χ hH) ∘L
        (extDerivCLM : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 1))
          (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩) -
        T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 0))
          (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩) -
        (T ∘L extDerivCLM) ∘L cutoffHomotopyPullbackCLM χ hH := by
  ext ω
  simp only [comp_apply, sub_apply, ← map_sub]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  simp only [FunLike.coe_sub, Pi.sub_apply]
  exact cutoffHomotopyPullbackCLM_extDerivCLM_apply ω hx

/-- **The homotopy formula for `0`-currents with compact support**: if `χ` is equal to one near the
support of a current `T` on test `0`-forms, then `∂ H_# ([[0, 1]] × T) = H₁# T - H₀# T`, where
`H_# ([[0, 1]] × T) = T ∘ K_χ` and `Hₜ# T = T ∘ (χ Hₜ^*)`. -/
theorem comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero
    (T : 𝓓(Ω, E [⋀^Fin 0]→L[ℝ] F) →L[ℝ] G) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (T ∘L cutoffHomotopyPullbackCLM χ hH) ∘L
        (extDerivCLM : 𝓓(Ω', E' [⋀^Fin 0]→L[ℝ] F) →L[ℝ] _) =
      T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 1))
          (contDiffOn_comp_prodMk_left hH ⟨zero_le_one, le_rfl⟩) -
        T ∘L cutoffPullbackCLM χ (fun x ↦ H (x, 0))
          (contDiffOn_comp_prodMk_left hH ⟨le_rfl, zero_le_one⟩) := by
  ext ω
  simp only [comp_apply, sub_apply, ← map_sub]
  refine map_eq_map_of_eventuallyEq T ?_
  filter_upwards [hχ.eventually_nhdsSet] with x hx
  simp only [FunLike.coe_sub, Pi.sub_apply]
  exact cutoffHomotopyPullbackCLM_extDerivCLM_apply_finZero ω hx

end Homotopy

end ContinuousLinearMap

namespace Distribution

variable {E E' F V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {Φ : E → E'} {k : ℕ} {χ : 𝓓(Ω, ℝ)}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} {𝓕 : Type*}

/-- **The support of a composition with a cutoff operator**: if `P` takes test functions on `Ω'`
to test functions on `Ω` supported in `tsupport χ ∩ Φ ⁻¹' tsupport φ`, then the support of `T ∘ P`
lies in the image under `Φ` of the part of the support of `T` in the support of `χ`. -/
theorem dsupport_comp_subset_image_of_tsupport_subset {G G' : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup G'] [NormedSpace ℝ G']
    [AddCommMonoid V] [FunLike 𝓕 𝓓(Ω, G) V] [AddMonoidHomClass 𝓕 𝓓(Ω, G) V] (T : 𝓕)
    (hΦc : ContinuousOn Φ Ω) {P : 𝓓(Ω', G') → 𝓓(Ω, G)}
    (hP : ∀ φ, tsupport (P φ) ⊆ tsupport χ ∩ Φ ⁻¹' tsupport φ) :
    dsupport (T ∘ P) ⊆ Φ '' (tsupport χ ∩ dsupport T) :=
  -- A test function supported off this image is taken to one supported off `spt T`.
  dsupport_comp_subset_of_disjoint T ((IsCompact.inter_right χ.hasCompactSupport
    isClosed_dsupport).image_of_continuousOn
      (hΦc.mono (inter_subset_left.trans χ.tsupport_subset))).isClosed
    fun φ hφ ↦ disjoint_left.2 fun x hx hxT ↦
      disjoint_left.1 hφ (hP φ hx).2 ⟨x, ⟨(hP φ hx).1, hxT⟩, rfl⟩

/-- **The support of a pushforward**: the support of `T ∘ (χ Φ^*)` lies in the image under `Φ` of
the part of the support of `T` in the support of `χ`. In particular it is compact, and when `χ` is
equal to one near the support of `T`, it lies in the image of the support of `T`. -/
theorem dsupport_comp_cutoffPullbackCLM_subset [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    dsupport (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ⊆
      Φ '' (tsupport χ ∩ dsupport T) :=
  dsupport_comp_subset_image_of_tsupport_subset T hΦ.continuousOn
    fun ω ↦ tsupport_cutoffPullbackCLM_subset ω

/-- **The support of a proper pushforward**: if `Φ` is proper from `Ω` to `Ω'`, the support of
`Φ_# T = T ∘ Φ^*` lies in the closure of the image under `Φ` of the support of `T` in `Ω`. -/
theorem dsupport_comp_pullbackCLM_subset [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) {hΦp : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)} :
    dsupport (T ∘ (pullbackCLM Φ hΦ hΦp : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ⊆
      closure (Φ '' ((Ω : Set E) ∩ dsupport T)) :=
  -- A test form supported off this closure pulls back to a test form supported off `spt T`.
  dsupport_comp_subset_of_disjoint T isClosed_closure fun ω hω ↦ disjoint_left.2 fun x hx hxT ↦
    disjoint_left.1 hω (tsupport_pullbackCLM_subset ω hx).2 <| subset_closure
      ⟨x, ⟨(tsupport_pullbackCLM_subset ω hx).1, hxT⟩, rfl⟩

/-- **The mass of a pushforward**: if `|χ| ≤ 1` and `‖DΦ‖ ≤ L` on the support of `χ`, then the
pushforward `T ∘ (χ Φ^*)` of a `k`-current `T` has mass at most `L ^ k` times the mass of `T`. -/
theorem mass_comp_cutoffPullbackCLM_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) (hχ : ∀ x, |χ x| ≤ 1) {L : ℝ≥0} (hL : ∀ x ∈ tsupport χ, ‖fderiv ℝ Φ x‖ ≤ L) :
    mass (T ∘ (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ≤
      (L : ℝ≥0∞) ^ k * mass T := by
  refine (mass_comp_le_of_norm_apply_le T (c := L ^ k) (by positivity) fun ω hω x ↦ ?_).trans_eq
    (by simp [ENNReal.ofReal_pow, ENNReal.ofReal_coe_nnreal])
  by_cases hx : x ∈ tsupport χ
  · refine (norm_cutoffPullbackCLM_apply_le ω x).trans ?_
    calc |χ x| * (‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k) ≤ 1 * (1 * (L : ℝ) ^ k) := by
          gcongr
          exacts [hχ x, hω _, hL x hx]
      _ = L ^ k := by ring
  · simp [image_eq_zero_of_notMem_tsupport hx]

/-- **The mass of a pushforward, bounded on the support**: if `|χ| ≤ 1` and `‖DΦ‖ ≤ L` at the
points of the support of `T`, then `M(T ∘ (χ Φ^*)) ≤ L ^ k M(T)`. -/
theorem mass_comp_cutoffPullbackCLM_le_of_forall_mem_dsupport
    {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] ℝ} (hT : HasLocallyFiniteMass T)
    (hχ : ∀ x ∈ dsupport T, |χ x| ≤ 1) {L : ℝ≥0}
    (hL : ∀ x ∈ dsupport T, ‖fderiv ℝ Φ x‖ ≤ L) :
    mass (T ∘L (cutoffPullbackCLM χ Φ hΦ : 𝓓(Ω', E' [⋀^Fin k]→L[ℝ] F) →L[ℝ] _)) ≤
      L ^ k * mass T := by
  borelize E
  refine mass_le_iff.2 fun ω hω ↦ ?_
  rw [ContinuousLinearMap.comp_apply]
  refine enorm_apply_le_mul_mass_of_forall_mem_dsupport hT fun x hx ↦ ?_
  have hreal : |χ x| * (‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k) ≤ (L : ℝ) ^ k :=
    calc |χ x| * (‖ω (Φ x)‖ * ‖fderiv ℝ Φ x‖ ^ k) ≤ 1 * (1 * (L : ℝ) ^ k) := by
          gcongr
          exacts [hχ x hx, hω _, hL x hx]
      _ = L ^ k := by ring
  exact_mod_cast (norm_cutoffPullbackCLM_apply_le ω x).trans hreal

section Homotopy

variable [CompleteSpace F] {H : E × ℝ → E'}
  {hH : ∀ p ∈ (Ω : Set E) ×ˢ Icc (0 : ℝ) 1, ContDiffAt ℝ (⊤ : ℕ∞) H p}

/-- **The support of a homotopy current**: the support of `T ∘ K_χ`, where `K_χ` is the homotopy
operator with cutoff `χ`, lies in the image under `H` of the product of the part of the support of
`T` in the support of `χ` with `[0, 1]`. In particular it is compact. -/
theorem dsupport_comp_cutoffHomotopyPullbackCLM_subset [AddCommMonoid V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [AddMonoidHomClass 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) :
    dsupport (T ∘ (cutoffHomotopyPullbackCLM χ hH :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ⊆
      H '' ((tsupport χ ∩ dsupport T) ×ˢ Icc (0 : ℝ) 1) :=
  -- A test form supported off this image is sent to a test form supported off `spt T`.
  dsupport_comp_subset_of_disjoint T (((IsCompact.inter_right χ.hasCompactSupport
    isClosed_dsupport).prod isCompact_Icc).image_of_continuousOn fun p hp ↦
      (hH p ⟨χ.tsupport_subset hp.1.1, hp.2⟩).continuousAt.continuousWithinAt).isClosed
    fun ω hω ↦ disjoint_left.2 fun x hx hxT ↦ by
      obtain ⟨p, ⟨⟨hpχ, hpt⟩, hpω⟩, rfl⟩ := tsupport_cutoffHomotopyPullbackCLM_subset ω hx
      exact disjoint_left.1 hω hpω ⟨p, ⟨⟨hpχ, hxT⟩, hpt⟩, rfl⟩

/-- **The mass of a homotopy current with compact support**: if `|χ| ≤ 1`, `‖∂ₜ H‖ ≤ A` and the
spatial derivative of `H` has operator norm at most `L` on `tsupport χ × [0, 1]`, then
`M(T ∘ K_χ) ≤ A L ^ k M(T)` for a `k`-current `T`, where `K_χ` is the homotopy operator with
cutoff `χ`. -/
theorem mass_comp_cutoffHomotopyPullbackCLM_le [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FunLike 𝓕 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V] [LinearMapClass 𝓕 ℝ 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) V]
    (T : 𝓕) (hχ : ∀ x, |χ x| ≤ 1) {A L : ℝ≥0}
    (hA : ∀ p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ H p (0, 1)‖ ≤ A)
    (hL : ∀ p ∈ tsupport χ ×ˢ Icc (0 : ℝ) 1, ‖(fderiv ℝ H p).comp (.inl ℝ E ℝ)‖ ≤ L) :
    mass (T ∘ (cutoffHomotopyPullbackCLM χ hH :
        𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) ≤ A * L ^ k * mass T := by
  refine (mass_comp_le_of_norm_apply_le T (c := A * L ^ k) (by positivity)
    fun ω hω x ↦ ?_).trans_eq (by simp [ENNReal.ofReal_mul, ENNReal.ofReal_pow,
      ENNReal.ofReal_coe_nnreal])
  by_cases hx : x ∈ tsupport χ
  · refine (norm_cutoffHomotopyPullbackCLM_apply_le (B := 1) (fun t _ ↦ hω _)
      (fun t ht ↦ hA _ ⟨hx, ht⟩) fun t ht ↦ hL _ ⟨hx, ht⟩).trans ?_
    calc |χ x| * (1 * A * L ^ k : ℝ) ≤ 1 * (1 * A * L ^ k) := by gcongr; exact hχ x
      _ = A * L ^ k := by ring
  · rw [cutoffHomotopyPullbackCLM_apply, image_eq_zero_of_notMem_tsupport hx, zero_smul,
      norm_zero]
    positivity

/-- The homotopy current `T ∘ K_χ` of a normal current `T` whose support lies in the interior of
`{χ = 1}` is normal. -/
private theorem IsNormal.comp_cutoffHomotopyPullbackCLM_of_eventually_eq_one [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    IsNormal (T ∘L (cutoffHomotopyPullbackCLM χ hH :
      𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) := by
  -- Replace `χ` by a cutoff `ψ` with `|ψ| ≤ 1`; this does not change the current.
  obtain ⟨ψ, hψ1, hψ, -, hχψ⟩ := exists_cutoff_abs_le_one hχ
  rw [ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_congr T hχψ]
  obtain ⟨M, hM⟩ := (ψ.hasCompactSupport.isCompact.prod isCompact_Icc).exists_norm_fderiv_le
    (by simp) fun p (hp : p ∈ tsupport ψ ×ˢ Icc (0 : ℝ) 1) ↦
      hH p ⟨ψ.tsupport_subset hp.1, hp.2⟩
  -- The time derivative, the spatial derivative and the slices of `H` are bounded by `M`.
  have hA : ∀ p ∈ tsupport ψ ×ˢ Icc (0 : ℝ) 1, ‖fderiv ℝ H p (0, 1)‖ ≤ M := fun p hp ↦ by
    refine ((fderiv ℝ H p).le_opNorm _).trans ?_
    rw [Prod.norm_mk, norm_zero, norm_one, max_eq_right zero_le_one, mul_one]
    exact hM p hp
  have hL : ∀ p ∈ tsupport ψ ×ˢ Icc (0 : ℝ) 1, ‖(fderiv ℝ H p).comp (.inl ℝ E ℝ)‖ ≤ M :=
    fun p hp ↦ ((fderiv ℝ H p).opNorm_comp_le _).trans
      ((mul_le_of_le_one_right (norm_nonneg _) (ContinuousLinearMap.norm_inl_le_one ℝ E ℝ)).trans
        (hM p hp))
  have hslice {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
      ∀ x ∈ tsupport ψ, ‖fderiv ℝ (fun y ↦ H (y, t)) x‖ ≤ M := fun x hx ↦ by
    rw [fderiv_slice_left ((hH _ ⟨ψ.tsupport_subset hx, ht⟩).differentiableAt (by simp))]
    exact hL _ ⟨hx, ht⟩
  have hmass {j : ℕ} {S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] V} (hS : mass S ≠ ⊤) :
      mass (S ∘ (cutoffHomotopyPullbackCLM ψ hH :
        𝓓(Ω', E' [⋀^Fin (j + 1)]→L[ℝ] F) →L[ℝ] _)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (mass_comp_cutoffHomotopyPullbackCLM_le S hψ hA hL)
  have hpush {j : ℕ} {S : 𝓓(Ω, E [⋀^Fin j]→L[ℝ] F) →L[ℝ] V} (hS : mass S ≠ ⊤) {t : ℝ}
      (ht : t ∈ Icc (0 : ℝ) 1) {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) (fun y ↦ H (y, t)) Ω} :
      mass (S ∘ (cutoffPullbackCLM ψ (fun y ↦ H (y, t)) hΦ :
        𝓓(Ω', E' [⋀^Fin j]→L[ℝ] F) →L[ℝ] _)) ≠ ⊤ :=
    ne_top_of_le_ne_top (by finiteness) (mass_comp_cutoffPullbackCLM_le S hψ (hslice ht))
  refine isNormal_succ_iff.2 ⟨hmass hT.mass_ne_top, ?_⟩
  cases k with
  | zero =>
    rw [ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM_finZero T hψ1]
    rw [FunLike.coe_sub]
    exact ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨hpush hT.mass_ne_top ⟨zero_le_one, le_rfl⟩,
      hpush hT.mass_ne_top ⟨le_rfl, zero_le_one⟩⟩) mass_sub_le
  | succ k =>
    rw [ContinuousLinearMap.comp_cutoffHomotopyPullbackCLM_comp_extDerivCLM T hψ1,
      FunLike.coe_sub, FunLike.coe_sub]
    refine ne_top_of_le_ne_top ?_ (mass_sub_le.trans (add_le_add_left mass_sub_le _))
    exact ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2
      ⟨hpush hT.mass_ne_top ⟨zero_le_one, le_rfl⟩, hpush hT.mass_ne_top ⟨le_rfl, zero_le_one⟩⟩,
      hmass (isNormal_succ_iff.1 hT).2⟩

/-- **Homotopy currents of locally normal currents are normal**: for a locally normal current `T`,
the homotopy current `T ∘ K_χ` is normal, where `K_χ` is the homotopy operator with cutoff `χ`. -/
theorem IsLocallyNormal.isNormal_comp_cutoffHomotopyPullbackCLM [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsLocallyNormal T) :
    IsNormal (T ∘L (cutoffHomotopyPullbackCLM χ hH :
      𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) := by
  -- `T ∘ K_χ = (χ T) ∘ K_ψ` for a cutoff `ψ` equal to one near `tsupport χ`, and `χ T` is a
  -- normal current supported in `tsupport χ`.
  obtain ⟨ψ, -, hψ1, -⟩ := TestFunction.exists_cutoff_tsupport_subset (n := (⊤ : ℕ∞))
    χ.hasCompactSupport.isCompact Ω.isOpen χ.tsupport_subset le_rfl
  have heq : T ∘L (cutoffHomotopyPullbackCLM χ hH : 𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _) =
      (T ∘L TestFunction.smulLeftCLM χ.contDiff) ∘L cutoffHomotopyPullbackCLM ψ hH := by
    ext ω
    refine congrArg T (TestFunction.ext fun x ↦ ?_)
    by_cases hx : x ∈ tsupport χ
    · simp [TestFunction.smulLeftCLM_apply, hψ1.self_of_nhdsSet x hx]
    · simp [TestFunction.smulLeftCLM_apply, image_eq_zero_of_notMem_tsupport hx]
  have hsub : dsupport (T ∘L TestFunction.smulLeftCLM χ.contDiff) ⊆ tsupport χ := by
    rw [ContinuousLinearMap.coe_comp]
    exact (dsupport_comp_smulLeftCLM_subset T χ.contDiff).trans inter_subset_left
  rw [heq]
  exact (hT.isNormal_comp_smulLeftCLM χ).comp_cutoffHomotopyPullbackCLM_of_eventually_eq_one
    (hψ1.filter_mono (nhdsSet_mono hsub))

/-- **Homotopy currents of normal currents are normal**: for a normal current `T`, the homotopy
current `T ∘ K_χ` is normal, where `K_χ` is the homotopy operator with cutoff `χ`. -/
theorem IsNormal.comp_cutoffHomotopyPullbackCLM [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V] {T : 𝓓(Ω, E [⋀^Fin k]→L[ℝ] F) →L[ℝ] V}
    (hT : IsNormal T) :
    IsNormal (T ∘L (cutoffHomotopyPullbackCLM χ hH :
      𝓓(Ω', E' [⋀^Fin (k + 1)]→L[ℝ] F) →L[ℝ] _)) :=
  hT.isLocallyNormal.isNormal_comp_cutoffHomotopyPullbackCLM

end Homotopy

end Distribution

namespace Distribution

section Scalar

variable {E E' E'' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {Φ : E → E'} {χ χ₁ χ₂ : 𝓓(Ω, ℝ)}
  {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}

/-- The **pushforward of a distribution with a cutoff** `T ↦ T ∘ (χ Φ^*)` along a map `Φ` smooth
on `Ω`, where `χ` is a test function on `Ω`: it pairs a test function `f` on `Ω'` with `T` through
`T (χ (f ∘ Φ))`. When `χ` is equal to one near the support of `T`, it is the pushforward `Φ_* T`,
independent of such `χ` (`Distribution.cutoffPushforwardCLM_congr`). -/
noncomputable def cutoffPushforwardCLM (χ : 𝓓(Ω, ℝ)) (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω) :
    𝓓'(Ω, F) →L[ℝ] 𝓓'(Ω', F) :=
  (cutoffCompCLM χ Φ hΦ).precompCompactConvergenceCLM F

/-- The pushforward with a cutoff pairs `f` with `T` through `T (χ (f ∘ Φ))`. -/
@[simp]
theorem cutoffPushforwardCLM_apply (T : 𝓓'(Ω, F)) (f : 𝓓(Ω', ℝ)) :
    cutoffPushforwardCLM χ Φ hΦ T f = T (cutoffCompCLM χ Φ hΦ f) :=
  (rfl)

/-- **Independence of the cutoff**: the pushforward `T ∘ (χ Φ^*)` depends only on the germ of `χ`
along the part of the support of `T` that `Φ` maps into `Ω'`. -/
theorem cutoffPushforwardCLM_congr (T : 𝓓'(Ω, F))
    (h : (χ₁ : E → ℝ) =ᶠ[𝓝ˢ (dsupport T ∩ Φ ⁻¹' Ω')] χ₂) :
    (cutoffPushforwardCLM χ₁ Φ hΦ T : 𝓓'(Ω', F)) = cutoffPushforwardCLM χ₂ Φ hΦ T := by
  ext f
  rw [cutoffPushforwardCLM_apply, cutoffPushforwardCLM_apply]
  refine map_eq_map_of_eventuallyEq T (eventually_nhdsSet_iff_forall.2 fun x hx ↦ ?_)
  by_cases hxΦ : Φ x ∈ Ω'
  · exact (eventually_nhdsSet_iff_forall.1 h x ⟨hx, hxΦ⟩).mono fun y hy ↦ by simp [hy]
  by_cases hxΩ : x ∈ Ω
  · -- `f ∘ Φ` vanishes near `x`, since `Φ x` lies outside the support of `f`.
    filter_upwards [(hΦ.continuousOn.continuousAt (Ω.isOpen.mem_nhds hxΩ)).preimage_mem_nhds
      ((isClosed_tsupport f).isOpen_compl.mem_nhds fun hf ↦ hxΦ (f.tsupport_subset hf))]
      with y hy
    simp [image_eq_zero_of_notMem_tsupport hy]
  · -- Both cutoffs vanish near `x`, which lies outside `Ω`.
    filter_upwards [(isClosed_tsupport χ₁).isOpen_compl.mem_nhds
        fun h₁ ↦ hxΩ (χ₁.tsupport_subset h₁),
      (isClosed_tsupport χ₂).isOpen_compl.mem_nhds fun h₂ ↦ hxΩ (χ₂.tsupport_subset h₂)]
      with y hy₁ hy₂
    simp [image_eq_zero_of_notMem_tsupport hy₁, image_eq_zero_of_notMem_tsupport hy₂]

/-- **The support of a pushforward**: the support of `T ∘ (χ Φ^*)` lies in the image under `Φ` of
the part of the support of `T` in the support of `χ`. In particular it is compact, and when `χ` is
equal to one near the support of `T`, it lies in the image of the support of `T`. -/
theorem dsupport_cutoffPushforwardCLM_subset (T : 𝓓'(Ω, F)) :
    dsupport (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', F)) ⊆ Φ '' (tsupport χ ∩ dsupport T) := by
  have h : ⇑(cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', F)) = T ∘ cutoffCompCLM χ Φ hΦ :=
    funext fun f ↦ cutoffPushforwardCLM_apply T f
  rw [h]
  exact dsupport_comp_subset_image_of_tsupport_subset T hΦ.continuousOn
    fun f ↦ tsupport_cutoffCompCLM_subset f

/-- **Pushforward along a constant map**: pushing `T` forward along the constant map with value
`c` pairs `f` with `T` through `f c • T χ`, so it is the multiple `T χ` of the point mass at `c`. -/
theorem cutoffPushforwardCLM_const_apply (T : 𝓓'(Ω, F)) (c : E') (f : 𝓓(Ω', ℝ)) :
    cutoffPushforwardCLM χ (fun _ ↦ c) contDiffOn_const T f = f c • T χ := by
  rw [cutoffPushforwardCLM_apply, cutoffCompCLM_const, map_smul]

/-- **Pushforward along a constant map**: the pushforward of `T` along the constant map with value
`c` is the point mass at `c` with weight `T χ`. -/
theorem cutoffPushforwardCLM_const (T : 𝓓'(Ω, F)) (c : E') :
    (cutoffPushforwardCLM χ (fun _ ↦ c) contDiffOn_const T : 𝓓'(Ω', F)) =
      mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (T χ)) (delta c : 𝓓'(Ω', ℝ)) := by
  ext f
  simp [cutoffCompCLM_const]

/-- **The pushforward along the identity**: if `χ` is equal to one near the support of `T`, the
pushforward of `T` along the identity is `T`. -/
theorem cutoffPushforwardCLM_id {hid : ContDiffOn ℝ (⊤ : ℕ∞) (id : E → E) Ω}
    (T : 𝓓'(Ω, F)) (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    (cutoffPushforwardCLM χ id hid T : 𝓓'(Ω, F)) = T := by
  ext f
  exact map_eq_map_of_eventuallyEq T (hχ.mono fun x hx ↦ by simp [hx])

/-- Along the identity, the pushforward with a cutoff `χ` is the product `χ T`. -/
@[simp]
theorem cutoffPushforwardCLM_id_eq_smulLeftCLM {hid : ContDiffOn ℝ (⊤ : ℕ∞) (id : E → E) Ω}
    (T : 𝓓'(Ω, F)) : (cutoffPushforwardCLM χ id hid T : 𝓓'(Ω, F)) = smulLeftCLM χ.contDiff T := by
  ext f
  rw [cutoffPushforwardCLM_apply, smulLeftCLM_apply]
  congr 1
  ext x
  simp

/-- **Functoriality of the pushforward**: pushing `T` forward with the cutoff `χ` along `Φ` and
then with the cutoff `χ'` along `Ψ` is pushing `T` forward with the cutoff `χ (χ' ∘ Φ)` along
`Ψ ∘ Φ`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM {Ψ : E' → E''} {χ' : 𝓓(Ω', ℝ)}
    {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'} {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω} (T : 𝓓'(Ω, F)) :
    (cutoffPushforwardCLM χ' Ψ hΨ (cutoffPushforwardCLM χ Φ hΦ T) : 𝓓'(Ω'', F)) =
      cutoffPushforwardCLM (cutoffCompCLM χ Φ hΦ χ') (Ψ ∘ Φ) hΨΦ T := by
  ext f
  simp only [cutoffPushforwardCLM_apply]
  rw [cutoffCompCLM_cutoffCompCLM (hΨΦ := hΨΦ)]

/-- **Functoriality of the pushforward**: `(Ψ ∘ Φ)_* T = Ψ_* (Φ_* T)` for the pushforwards of
`χ T`, when `χ'` is equal to one near the image under `Φ` of the part of the support of `T` in the
support of `χ`. -/
theorem cutoffPushforwardCLM_cutoffPushforwardCLM_of_eventually_eq_one
    {Ψ : E' → E''} {χ' : 𝓓(Ω', ℝ)} {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'}
    {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω} (T : 𝓓'(Ω, F))
    (hχ' : ∀ᶠ y in 𝓝ˢ (Φ '' (tsupport χ ∩ dsupport T)), χ' y = 1) :
    (cutoffPushforwardCLM χ' Ψ hΨ (cutoffPushforwardCLM χ Φ hΦ T) : 𝓓'(Ω'', F)) =
      cutoffPushforwardCLM χ (Ψ ∘ Φ) hΨΦ T := by
  ext f
  simp only [cutoffPushforwardCLM_apply]
  rw [cutoffCompCLM_cutoffCompCLM (hΨΦ := hΨΦ)]
  refine map_eq_map_of_eventuallyEq T
    ((eventually_cutoff_comp_eq_one_or_eq_zero hΦ.continuousOn hχ').mono fun x hx ↦ ?_)
  rcases hx with hx | hx <;> simp [hx]

/-- The pushforward commutes with applying a continuous linear map to the values. -/
theorem mapCLM_cutoffPushforwardCLM {G : Type*} [AddCommGroup G] [Module ℝ G]
    [TopologicalSpace G] [IsTopologicalAddGroup G] [ContinuousSMul ℝ G] (L : F →L[ℝ] G)
    (T : 𝓓'(Ω, F)) :
    mapCLM L (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', F)) =
      cutoffPushforwardCLM χ Φ hΦ (mapCLM L T) := by
  ext f
  simp

/-- The pushforward of the point mass at `x` with a cutoff `χ` is `χ x` times the point mass at
`Φ x`. -/
@[simp]
theorem cutoffPushforwardCLM_delta (x : E) :
    cutoffPushforwardCLM χ Φ hΦ (delta x : 𝓓'(Ω, ℝ)) = χ x • (delta (Φ x) : 𝓓'(Ω', ℝ)) := by
  ext f
  simp [delta_apply]

end Scalar

/-- The complex-linear extension of a pushforward pairs a complex test function `f` with `T`
through `T (χ (f ∘ Φ))`. -/
@[simp]
theorem complexPairing_cutoffPushforwardCLM {E E' : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E'] {Ω : Opens E} {Ω' : Opens E'}
    {Φ : E → E'} {χ : 𝓓(Ω, ℝ)} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω} (T : 𝓓'(Ω, ℂ))
    (f : 𝓓(Ω', ℂ)) :
    (cutoffPushforwardCLM χ Φ hΦ T).complexPairing f =
      T.complexPairing (cutoffCompCLM χ Φ hΦ f) := by
  simp only [complexPairing_apply, cutoffPushforwardCLM_apply, postcompCLM_cutoffCompCLM]

end Distribution
