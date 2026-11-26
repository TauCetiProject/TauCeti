/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.LocallyConvex.WithSeminorms
public import TauCeti.Analysis.Distribution.WaveFrontSet.LineDeriv
import TauCeti.Analysis.Normed.Module.Seminorm.WeightedSup

/-!
# Distributions with wave front set in a cone and their normal topology

Let `Ω` be an open subset of a finite-dimensional real inner product space `E` and `Γ` a subset
of `E × E`, typically a closed cone in `Ω × (E \ {0})`. Hörmander's space `𝓓'_Γ(Ω)` consists of
the complex distributions `T` on `Ω` whose wave front set lies in `Γ`
(`TauCeti.WaveFrontSpace Ω Γ`). It is the natural carrier of the operations of microlocal
analysis whose existence depends on the position of the wave front set: pullback along a map
whose normal set misses `Γ`, and products of distributions whose wave front sets contain no
opposite covectors. Brouder, Dang and Hélein prove these operations continuous for the *normal
topology*, which adds to the topology of `𝓓'(Ω)` the seminorms

`‖T‖_{φ,V,N} = sup_{η ∈ V} (1 + ‖η‖)^N |T (φ e_η)|`,

one for every test function `φ`, every closed cone `V` such that no point of `Γ` lies over the
support of `φ` in a direction of `V`, and every `N ∈ ℕ`. Here `η ↦ T (φ e_η)` is the localized
Fourier transform `Distribution.localFourier T φ`, the Fourier transform of `φ T`.

These seminorms are finite on `𝓓'_Γ(Ω)`. This is the uniform version of the definition of the
wave front set: if no point of the wave front set of `T` lies over the support of `φ` in a
direction of the closed cone `V`, then the localized Fourier transform of `T` with cutoff `φ`
decreases rapidly on all of `V`
(`Distribution.exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint`): the
definition gives, around each direction of `V`, an open cone of decay uniform over the support of
`φ`, and finitely many of these cones cover `V \ {0}`
(`TauCeti.exists_finset_diff_singleton_subset_biUnion`).

The normal topology is the coarsest topology finer than both the topology of `𝓓'(Ω)` and the
locally convex topology defined by these seminorms. Here `𝓓'(Ω)` carries Mathlib's topology of
uniform convergence on compact sets of test functions; Brouder, Dang and Hélein use the strong
topology of uniform convergence on bounded sets, which is the same since bounded sets of test
functions are relatively compact. The normal topology makes `𝓓'_Γ(Ω)` a Hausdorff topological
group in which a net converges exactly when it converges in `𝓓'(Ω)` and in every seminorm (in fact,
convergence in `𝓓'(Ω)` with eventual boundedness in every seminorm suffices), and a map into
`𝓓'_Γ(Ω)` is continuous exactly when its composite with the inclusion into `𝓓'(Ω)` and its
composites with all the seminorms are continuous. For `Γ ⊆ Γ'` the inclusion
`𝓓'_Γ(Ω) → 𝓓'_Γ'(Ω)` is continuous, and multiplication by a smooth real-valued function,
differentiation and restriction to an open subset are continuous linear maps of these spaces.

## Main declarations

* `TauCeti.waveFrontSubmodule Ω Γ`: the distributions whose wave front set lies in `Γ`.
* `TauCeti.WaveFrontSeminormIndex Ω Γ`: the data `(φ, V, N)` of a seminorm.
* `TauCeti.WaveFrontSpace Ω Γ`: the space `𝓓'_Γ(Ω)` with the normal topology.
* `TauCeti.WaveFrontSpace.seminorm`: the seminorm `‖T‖_{φ,V,N}`, the best constant in the
  decay estimate (`TauCeti.WaveFrontSpace.seminorm_le_iff`).
* `TauCeti.WaveFrontSpace.tendsto_nhds_iff`,
  `TauCeti.WaveFrontSpace.tendsto_nhds_of_eventually_seminorm_le`,
  `TauCeti.WaveFrontSpace.continuous_iff`, `TauCeti.WaveFrontSpace.continuous_of_le`,
  `TauCeti.WaveFrontSpace.continuous_linearMap_iff`: convergence and continuity of maps into
  `𝓓'_Γ(Ω)`.
* `TauCeti.WaveFrontSpace.exists_continuous_seminorm_norm_complexPairing_le`: on a compact set of
  test functions, the values of the members of `𝓓'_Γ(Ω)` are bounded by a continuous seminorm.
* `TauCeti.WaveFrontSpace.inclusionCLM`, `TauCeti.WaveFrontSpace.smulLeftCLM`,
  `TauCeti.WaveFrontSpace.lineDerivCLM`, `TauCeti.WaveFrontSpace.restrictCLM`: the
  inclusion for a larger cone, multiplication by a smooth real-valued function, differentiation
  and restriction as continuous linear maps.
* `TauCeti.WaveFrontSpace.seminorm_inclusionCLM`,
  `TauCeti.WaveFrontSpace.seminorm_smulLeftCLM`,
  `TauCeti.WaveFrontSpace.seminorm_lineDerivCLM_le`,
  `TauCeti.WaveFrontSpace.seminorm_restrictCLM`: the seminorm estimates behind their
  continuity, in terms of the transported data `TauCeti.WaveFrontSeminormIndex.mono`,
  `TauCeti.WaveFrontSeminormIndex.smulLeft`, `TauCeti.WaveFrontSeminormIndex.withOrder`,
  `TauCeti.WaveFrontSeminormIndex.lineDeriv` and
  `TauCeti.WaveFrontSeminormIndex.restrict`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §8.2, Definition 8.2.2 (the space `𝓓'_Γ` and its convergence).
* C. Brouder, N. V. Dang, F. Hélein, *Continuity of the fundamental operations on
  distributions having a specified wave front set (with a counterexample by Semyon Alesker)*,
  Studia Math. 232 (2016), arXiv:1409.7662v2, §3 (the normal topology and its seminorms).
-/

public section

noncomputable section

open Filter LineDeriv Metric Real Set TopologicalSpace
open scoped ContDiff Distributions Topology

namespace TauCeti

open Distribution

/-! ### Seminorm data -/

section SeminormIndex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Ω : Opens E}

variable (Ω) in
/-- The data `(φ, V, N)` of a seminorm `‖T‖_{φ,V,N} = sup_{η ∈ V} (1 + ‖η‖)^N |T (φ e_η)|` of the
normal topology on `𝓓'_Γ(Ω)`: a test function `φ`, a closed cone `V` of frequencies such that
no point of `Γ` lies over the support of `φ` in a direction of `V`, and an order `N`. -/
structure WaveFrontSeminormIndex (Γ : Set (E × E)) where
  /-- The cutoff `φ`. -/
  cutoff : 𝓓(Ω, ℂ)
  /-- The closed cone `V` of frequencies. -/
  cone : Set E
  /-- The order `N` of decay. -/
  order : ℕ
  /-- The cone `V` is closed. -/
  isClosed_cone : IsClosed cone
  /-- The cone `V` is invariant under positive dilations. -/
  smul_mem_cone : ∀ t : ℝ, 0 < t → ∀ η ∈ cone, t • η ∈ cone
  /-- No point of `Γ` lies over the support of `φ` in a direction of `V`. -/
  disjoint : Disjoint (tsupport cutoff ×ˢ cone) Γ

namespace WaveFrontSeminormIndex

variable {Γ Γ' : Set (E × E)}

/-- The data of a seminorm of `𝓓'_Γ'(Ω)` is that of a seminorm of `𝓓'_Γ(Ω)` when `Γ ⊆ Γ'`. -/
def mono (h : Γ ⊆ Γ') (i : WaveFrontSeminormIndex Ω Γ') : WaveFrontSeminormIndex Ω Γ :=
  { i with disjoint := i.disjoint.mono_right h }

@[simp]
theorem mono_cutoff (h : Γ ⊆ Γ') (i : WaveFrontSeminormIndex Ω Γ') :
    (i.mono h).cutoff = i.cutoff :=
  (rfl)

@[simp]
theorem mono_cone (h : Γ ⊆ Γ') (i : WaveFrontSeminormIndex Ω Γ') :
    (i.mono h).cone = i.cone :=
  (rfl)

@[simp]
theorem mono_order (h : Γ ⊆ Γ') (i : WaveFrontSeminormIndex Ω Γ') :
    (i.mono h).order = i.order :=
  (rfl)

/-- The data `(φ, V, M)` of the seminorm `‖·‖_{φ,V,M}` for the data `i = (φ, V, N)`: the order
of decay replaced by `M`. -/
def withOrder (i : WaveFrontSeminormIndex Ω Γ) (M : ℕ) : WaveFrontSeminormIndex Ω Γ :=
  { i with order := M }

@[simp]
theorem withOrder_cutoff (i : WaveFrontSeminormIndex Ω Γ) (M : ℕ) :
    (i.withOrder M).cutoff = i.cutoff :=
  (rfl)

@[simp]
theorem withOrder_cone (i : WaveFrontSeminormIndex Ω Γ) (M : ℕ) :
    (i.withOrder M).cone = i.cone :=
  (rfl)

@[simp]
theorem withOrder_order (i : WaveFrontSeminormIndex Ω Γ) (M : ℕ) :
    (i.withOrder M).order = M :=
  (rfl)

/-- The data `(g φ, V, N)` of the seminorm `‖g ·‖_{φ,V,N}` for the data `i = (φ, V, N)`: the
cutoff `g φ` has support in that of `φ`. -/
def smulLeft {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (i : WaveFrontSeminormIndex Ω Γ) :
    WaveFrontSeminormIndex Ω Γ :=
  { i with
    cutoff := TestFunction.smulLeftCLM hg i.cutoff
    disjoint := i.disjoint.mono_left
      (prod_mono ((TestFunction.tsupport_smulLeftCLM_subset hg _).trans inter_subset_right)
        subset_rfl) }

@[simp]
theorem smulLeft_cutoff {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.smulLeft hg).cutoff = TestFunction.smulLeftCLM hg i.cutoff :=
  (rfl)

@[simp]
theorem smulLeft_cone {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.smulLeft hg).cone = i.cone :=
  (rfl)

@[simp]
theorem smulLeft_order {g : E → ℝ} (hg : ContDiff ℝ ∞ g) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.smulLeft hg).order = i.order :=
  (rfl)

/-- The data `(∂_v φ, V, N)` of the seminorm `‖·‖_{∂_v φ,V,N}` for the data `i = (φ, V, N)`: the
derivative `∂_v φ` has support in that of `φ`. -/
def lineDeriv (v : E) (i : WaveFrontSeminormIndex Ω Γ) : WaveFrontSeminormIndex Ω Γ :=
  { i with
    cutoff := ∂_{v} i.cutoff
    disjoint := i.disjoint.mono_left (prod_mono (tsupport_fderiv_apply_subset ℝ v) subset_rfl) }

@[simp]
theorem lineDeriv_cutoff (v : E) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.lineDeriv v).cutoff = ∂_{v} i.cutoff :=
  (rfl)

@[simp]
theorem lineDeriv_cone (v : E) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.lineDeriv v).cone = i.cone :=
  (rfl)

@[simp]
theorem lineDeriv_order (v : E) (i : WaveFrontSeminormIndex Ω Γ) :
    (i.lineDeriv v).order = i.order :=
  (rfl)

variable (Ω) in
/-- The data of the seminorm `‖T|_{Ω'}‖_{φ,V,N}` for the data `i = (φ, V, N)` on `Ω'`, as data
on `Ω`: the cutoff `φ` extended by zero (or `0` when `¬ Ω' ≤ Ω`), which is admissible for `Γ` when
the part of `Γ` over `Ω'` lies in `Γ'`. -/
def restrict {Ω' : Opens E} (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (i : WaveFrontSeminormIndex Ω' Γ') : WaveFrontSeminormIndex Ω Γ :=
  { i with
    cutoff := TestFunction.monoCLM ℝ i.cutoff
    disjoint := by
      by_cases h : Ω' ≤ Ω
      · refine disjoint_left.2 fun p hp hpΓ ↦ ?_
        -- For `Ω' ≤ Ω`, extending by zero does not change the cutoff as a function.
        have hφ : ((TestFunction.monoCLM ℝ i.cutoff : 𝓓(Ω, ℂ)) : E → ℂ) = i.cutoff := by
          simp [TestFunction.monoCLM_apply, h]
        have hp' : p ∈ tsupport i.cutoff ×ˢ i.cone := ⟨hφ ▸ hp.1, hp.2⟩
        exact disjoint_left.1 i.disjoint hp'
          (hΓ ⟨hpΓ, i.cutoff.tsupport_subset hp'.1, mem_univ _⟩)
      · have h0 : (TestFunction.monoCLM ℝ : 𝓓(Ω', ℂ) →L[ℝ] 𝓓(Ω, ℂ)) = 0 :=
          TestFunction.monoCLM_eq_zero (by simp [h])
        simp [h0] }

variable (Ω) in
@[simp]
theorem restrict_cutoff {Ω' : Opens E} (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (i : WaveFrontSeminormIndex Ω' Γ') :
    (i.restrict Ω hΓ).cutoff = TestFunction.monoCLM ℝ i.cutoff :=
  (rfl)

variable (Ω) in
@[simp]
theorem restrict_cone {Ω' : Opens E} (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (i : WaveFrontSeminormIndex Ω' Γ') : (i.restrict Ω hΓ).cone = i.cone :=
  (rfl)

variable (Ω) in
@[simp]
theorem restrict_order {Ω' : Opens E} (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (i : WaveFrontSeminormIndex Ω' Γ') : (i.restrict Ω hΓ).order = i.order :=
  (rfl)

end WaveFrontSeminormIndex

end SeminormIndex

/-! ### The space `𝓓'_Γ(Ω)` -/

section Space

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {Ω : Opens E}

variable (Ω) in
/-- The complex distributions on `Ω` whose wave front set lies in `Γ`, as a submodule of
`𝓓'(Ω)`. -/
def waveFrontSubmodule (Γ : Set (E × E)) : Submodule ℂ 𝓓'(Ω, ℂ) where
  carrier := {T | T.waveFrontSet ⊆ Γ}
  add_mem' {S T} hS hT := (waveFrontSet_add_subset S T).trans (union_subset hS hT)
  zero_mem' := by simp [waveFrontSet_zero]
  smul_mem' c T hT := (waveFrontSet_smul_subset c T).trans hT

@[simp]
theorem mem_waveFrontSubmodule {Γ : Set (E × E)} {T : 𝓓'(Ω, ℂ)} :
    T ∈ waveFrontSubmodule Ω Γ ↔ T.waveFrontSet ⊆ Γ :=
  Iff.rfl

variable (Ω) in
/-- **Hörmander's space `𝓓'_Γ(Ω)`**: the complex distributions on `Ω` whose wave front set lies
in `Γ`, with the *normal topology*, the coarsest topology finer than both the topology of
`𝓓'(Ω)` and the locally convex topology defined by the seminorms
`TauCeti.WaveFrontSpace.seminorm`. -/
def WaveFrontSpace (Γ : Set (E × E)) : Type _ :=
  waveFrontSubmodule Ω Γ

namespace WaveFrontSpace

variable {Γ Γ' : Set (E × E)}

instance : AddCommGroup (WaveFrontSpace Ω Γ) :=
  inferInstanceAs (AddCommGroup (waveFrontSubmodule Ω Γ))

instance : Module ℂ (WaveFrontSpace Ω Γ) :=
  inferInstanceAs (Module ℂ (waveFrontSubmodule Ω Γ))

/-- The underlying distribution of an element of `𝓓'_Γ(Ω)`. -/
def toDistribution : WaveFrontSpace Ω Γ →ₗ[ℂ] 𝓓'(Ω, ℂ) :=
  (waveFrontSubmodule Ω Γ).subtype

theorem toDistribution_injective :
    Function.Injective (toDistribution : WaveFrontSpace Ω Γ → 𝓓'(Ω, ℂ)) :=
  Subtype.val_injective

@[ext]
theorem ext {u v : WaveFrontSpace Ω Γ} (h : u.toDistribution = v.toDistribution) : u = v :=
  toDistribution_injective h

/-- The wave front set of an element of `𝓓'_Γ(Ω)` lies in `Γ`. -/
theorem waveFrontSet_toDistribution_subset (u : WaveFrontSpace Ω Γ) :
    u.toDistribution.waveFrontSet ⊆ Γ :=
  u.property

/-- A distribution with wave front set in `Γ` as an element of `𝓓'_Γ(Ω)`. -/
def mk (T : 𝓓'(Ω, ℂ)) (hT : T.waveFrontSet ⊆ Γ) : WaveFrontSpace Ω Γ :=
  ⟨T, hT⟩

@[simp]
theorem toDistribution_mk (T : 𝓓'(Ω, ℂ)) (hT : T.waveFrontSet ⊆ Γ) :
    (mk T hT).toDistribution = T :=
  (rfl)

@[simp]
theorem mk_toDistribution (u : WaveFrontSpace Ω Γ) :
    mk u.toDistribution u.waveFrontSet_toDistribution_subset = u :=
  (rfl)

/-- The distributions in `𝓓'_Γ(Ω)` are those with wave front set in `Γ`. -/
theorem range_toDistribution :
    LinearMap.range (toDistribution : WaveFrontSpace Ω Γ →ₗ[ℂ] 𝓓'(Ω, ℂ)) =
      waveFrontSubmodule Ω Γ :=
  Submodule.range_subtype _

/-! ### The seminorms -/

section Seminorm

/-- The localized Fourier transform `T ↦ T (φ e_η)` at a frequency `η ∈ V`, as a linear map. -/
private def localFourierLinearMap (i : WaveFrontSeminormIndex Ω Γ) (η : i.cone) :
    WaveFrontSpace Ω Γ →ₗ[ℂ] ℂ where
  toFun u := u.toDistribution.localFourier i.cutoff η
  map_add' u v := by simp
  map_smul' c u := by simp

/-- The seminorm `‖T‖_{φ,V,N} = sup_{η ∈ V} (1 + ‖η‖)^N |T (φ e_η)|` of the normal topology on
`𝓓'_Γ(Ω)`, for the data `i = (φ, V, N)`: the best constant `C` in the decay estimate
`(1 + ‖η‖)^N ‖T (φ e_η)‖ ≤ C` for `η ∈ V`. -/
protected def seminorm (i : WaveFrontSeminormIndex Ω Γ) : Seminorm ℂ (WaveFrontSpace Ω Γ) :=
  Seminorm.weightedSup (localFourierLinearMap i) (fun η ↦ ((1 + ‖(η : E)‖) ^ i.order)⁻¹)
    fun _ ↦ by positivity

/-- Every element of `𝓓'_Γ(Ω)` satisfies the decay estimates defining
`WaveFrontSpace.seminorm i`. -/
private theorem exists_bound_localFourierLinearMap (i : WaveFrontSeminormIndex Ω Γ)
    (u : WaveFrontSpace Ω Γ) :
    ∃ C, ∀ η : i.cone, ‖localFourierLinearMap i η u‖ ≤ C * ((1 + ‖(η : E)‖) ^ i.order)⁻¹ :=
  let ⟨C, _, hC⟩ := exists_forall_one_add_norm_pow_mul_norm_localFourier_le_of_disjoint
    i.isClosed_cone i.smul_mem_cone (i.disjoint.mono_right u.waveFrontSet_toDistribution_subset)
    i.order
  ⟨C, fun η ↦ (le_mul_inv_iff₀' (by positivity)).2 (hC η η.property)⟩

/-- The seminorm `‖T‖_{φ,V,N}` bounds `(1 + ‖η‖)^N ‖T (φ e_η)‖` for `η ∈ V`. -/
theorem le_seminorm (i : WaveFrontSeminormIndex Ω Γ) (u : WaveFrontSpace Ω Γ) {η : E}
    (hη : η ∈ i.cone) :
    (1 + ‖η‖) ^ i.order * ‖u.toDistribution.localFourier i.cutoff η‖ ≤
      WaveFrontSpace.seminorm i u :=
  (le_mul_inv_iff₀' (by positivity)).1 <| Seminorm.norm_le_weightedSup (localFourierLinearMap i)
    _ _ (exists_bound_localFourierLinearMap i) u ⟨η, hη⟩

/-- A constant in the decay estimate bounds the seminorm `‖T‖_{φ,V,N}`. -/
theorem seminorm_le_bound (i : WaveFrontSeminormIndex Ω Γ) (u : WaveFrontSpace Ω Γ) {C : ℝ}
    (hC : 0 ≤ C)
    (h : ∀ η ∈ i.cone, (1 + ‖η‖) ^ i.order * ‖u.toDistribution.localFourier i.cutoff η‖ ≤ C) :
    WaveFrontSpace.seminorm i u ≤ C :=
  Seminorm.weightedSup_le _ _ _ hC fun η ↦ (le_mul_inv_iff₀' (by positivity)).2 (h η η.property)

/-- The seminorm `‖T‖_{φ,V,N}` is at most `C ≥ 0` exactly when `C` is a constant in the decay
estimate `(1 + ‖η‖)^N ‖T (φ e_η)‖ ≤ C` for `η ∈ V`. -/
theorem seminorm_le_iff {i : WaveFrontSeminormIndex Ω Γ} {u : WaveFrontSpace Ω Γ} {C : ℝ}
    (hC : 0 ≤ C) :
    WaveFrontSpace.seminorm i u ≤ C ↔
      ∀ η ∈ i.cone, (1 + ‖η‖) ^ i.order * ‖u.toDistribution.localFourier i.cutoff η‖ ≤ C :=
  ⟨fun h _ hη ↦ (le_seminorm i u hη).trans h, seminorm_le_bound i u hC⟩

variable (Ω Γ) in
/-- The family of seminorms of the normal topology on `𝓓'_Γ(Ω)`. -/
def seminormFamily : SeminormFamily ℂ (WaveFrontSpace Ω Γ) (WaveFrontSeminormIndex Ω Γ) :=
  WaveFrontSpace.seminorm

@[simp]
theorem seminormFamily_apply (i : WaveFrontSeminormIndex Ω Γ) :
    seminormFamily Ω Γ i = WaveFrontSpace.seminorm i :=
  (rfl)

end Seminorm

/-! ### The normal topology -/

section Topology

/-- The topology of the seminorms `‖T‖_{φ,V,N}` alone. -/
private abbrev seminormTopology : TopologicalSpace (WaveFrontSpace Ω Γ) :=
  (seminormFamily Ω Γ).moduleFilterBasis.topology

/-- The **normal topology** on `𝓓'_Γ(Ω)`: the coarsest topology finer than both the topology of
`𝓓'(Ω)` and the locally convex topology defined by the seminorms `‖T‖_{φ,V,N}`. -/
instance instTopologicalSpace : TopologicalSpace (WaveFrontSpace Ω Γ) :=
  TopologicalSpace.induced toDistribution inferInstance ⊓
    (seminormFamily Ω Γ).moduleFilterBasis.topology

private theorem withSeminorms_seminormFamily :
    WithSeminorms (topology := seminormTopology) (seminormFamily Ω Γ) :=
  WithSeminorms.mk (topology := seminormTopology) rfl

theorem continuous_toDistribution :
    Continuous (toDistribution : WaveFrontSpace Ω Γ → 𝓓'(Ω, ℂ)) :=
  continuous_inf_dom_left (t₂ := seminormTopology) continuous_induced_dom

theorem continuous_seminorm (i : WaveFrontSeminormIndex Ω Γ) :
    Continuous (WaveFrontSpace.seminorm i) :=
  continuous_inf_dom_right (t₁ := .induced toDistribution inferInstance)
    (WithSeminorms.continuous_seminorm (t := seminormTopology) withSeminorms_seminormFamily i)

instance : IsTopologicalAddGroup (WaveFrontSpace Ω Γ) :=
  isTopologicalAddGroup_inf (isTopologicalAddGroup_induced toDistribution)
    (letI : TopologicalSpace (WaveFrontSpace Ω Γ) := seminormTopology
    withSeminorms_seminormFamily.isTopologicalAddGroup)

instance : T2Space (WaveFrontSpace Ω Γ) :=
  .of_injective_continuous toDistribution_injective continuous_toDistribution

/-- **Convergence in `𝓓'_Γ(Ω)`.** A filter converges to `u` in the normal topology exactly when it
converges to `u` in `𝓓'(Ω)` and every seminorm `‖· - u‖_{φ,V,N}` tends to zero along it. -/
theorem tendsto_nhds_iff {α : Type*} {l : Filter α} {f : α → WaveFrontSpace Ω Γ}
    {u : WaveFrontSpace Ω Γ} :
    Tendsto f l (𝓝 u) ↔ Tendsto (fun a ↦ (f a).toDistribution) l (𝓝 u.toDistribution) ∧
      ∀ i ε, 0 < ε → ∀ᶠ a in l, WaveFrontSpace.seminorm i (f a - u) < ε := by
  have hnhds : 𝓝 u = comap toDistribution (𝓝 u.toDistribution) ⊓
      @nhds _ seminormTopology u := by
    rw [← nhds_induced]
    exact nhds_inf (t₁ := .induced toDistribution inferInstance) (t₂ := seminormTopology)
  have hseminorm : Tendsto f l (@nhds _ seminormTopology u) ↔
      ∀ i ε, 0 < ε → ∀ᶠ a in l, WaveFrontSpace.seminorm i (f a - u) < ε :=
    letI : TopologicalSpace (WaveFrontSpace Ω Γ) := seminormTopology
    withSeminorms_seminormFamily.tendsto_nhds f u
  rw [hnhds, tendsto_inf, tendsto_comap_iff, hseminorm, Function.comp_def]

/-- A filter converging in `𝓓'(Ω, ℂ)` along which every seminorm `‖·‖_{φ,V,N}` is eventually
bounded converges in the normal topology: the extra order `N + 1` controls large frequencies and
convergence in `𝓓'(Ω, ℂ)` controls bounded frequencies uniformly. -/
theorem tendsto_nhds_of_eventually_seminorm_le {α : Type*} {l : Filter α}
    {f : α → WaveFrontSpace Ω Γ} {u : WaveFrontSpace Ω Γ}
    (h₁ : Tendsto (fun a ↦ (f a).toDistribution) l (𝓝 u.toDistribution))
    (h₂ : ∀ i : WaveFrontSeminormIndex Ω Γ, ∃ M, ∀ᶠ a in l, WaveFrontSpace.seminorm i (f a) ≤ M) :
    Tendsto f l (𝓝 u) := by
  refine tendsto_nhds_iff.2 ⟨h₁, fun i ε hε ↦ ?_⟩
  obtain ⟨M, hM⟩ := h₂ (i.withOrder (i.order + 1))
  set B : ℝ := max M 0 + WaveFrontSpace.seminorm (i.withOrder (i.order + 1)) u
  have hB : 0 ≤ B := add_nonneg (le_max_right _ _) (apply_nonneg _ _)
  set R : ℝ := 2 * B / ε
  have hball := Metric.tendstoUniformlyOn_iff.1
    (tendstoUniformlyOn_localFourier h₁ i.cutoff (isCompact_closedBall (0 : E) R))
    ((ε / 2) / (1 + R) ^ i.order) (by positivity)
  filter_upwards [hM, hball] with a haM haball
  refine (seminorm_le_bound i (f a - u) (by positivity) fun η hη ↦ ?_).trans_lt (half_lt_self hε)
  by_cases hηR : ‖η‖ ≤ R
  · have hlt :
        ‖(f a - u).toDistribution.localFourier i.cutoff η‖ < (ε / 2) / (1 + R) ^ i.order := by
      have hsub : (f a - u).toDistribution.localFourier i.cutoff η =
          (f a).toDistribution.localFourier i.cutoff η -
            u.toDistribution.localFourier i.cutoff η := by
        rw [map_sub, sub_eq_add_neg, ← neg_one_smul ℂ, localFourier_add, localFourier_smul]
        ring
      rw [hsub]
      simpa [dist_eq_norm, norm_sub_rev] using
        haball η (by simpa [mem_closedBall, dist_zero_right] using hηR)
    have hpow : (1 + ‖η‖) ^ i.order ≤ (1 + R) ^ i.order := by gcongr
    calc (1 + ‖η‖) ^ i.order * ‖(f a - u).toDistribution.localFourier i.cutoff η‖
        ≤ (1 + R) ^ i.order * ((ε / 2) / (1 + R) ^ i.order) :=
          mul_le_mul hpow hlt.le (norm_nonneg _) (by positivity)
      _ = ε / 2 := mul_div_cancel₀ _ (by positivity)
  · push Not at hηR
    have hsub : WaveFrontSpace.seminorm (i.withOrder (i.order + 1)) (f a - u) ≤ B :=
      (map_sub_le_add _ _ _).trans (add_le_add (haM.trans (le_max_left _ _)) le_rfl)
    have hle := (le_seminorm (i.withOrder (i.order + 1)) (f a - u) hη).trans hsub
    rw [WaveFrontSeminormIndex.withOrder_order, WaveFrontSeminormIndex.withOrder_cutoff,
      pow_succ, mul_assoc] at hle
    have h1R : 0 < 1 + R := by positivity
    have h1η : 1 + R ≤ 1 + ‖η‖ := by linarith
    have hBR : B / (1 + R) ≤ ε / 2 := by
      rw [div_le_iff₀ h1R]
      have : 2 * B = R * ε := by simp [R, div_mul_cancel₀ _ hε.ne']
      linarith
    calc (1 + ‖η‖) ^ i.order * ‖(f a - u).toDistribution.localFourier i.cutoff η‖
        = (1 + ‖η‖) ^ i.order * ((1 + ‖η‖) *
            ‖(f a - u).toDistribution.localFourier i.cutoff η‖) / (1 + ‖η‖) := by
          field_simp
      _ ≤ B / (1 + R) := div_le_div₀ hB hle h1R h1η
      _ ≤ ε / 2 := hBR

/-- A map from a topological space into `𝓓'_Γ(Ω)` whose composite with the inclusion into `𝓓'(Ω)`
is continuous, and each of whose seminorms `‖f ·‖_{φ,V,N}` is bounded pointwise by a continuous
real-valued function, is continuous. -/
theorem continuous_of_le {X : Type*} [TopologicalSpace X] {f : X → WaveFrontSpace Ω Γ}
    (h₁ : Continuous fun x ↦ (f x).toDistribution)
    (h₂ : ∀ i, ∃ g : X → ℝ, Continuous g ∧ ∀ x, WaveFrontSpace.seminorm i (f x) ≤ g x) :
    Continuous f := by
  refine continuous_iff_continuousAt.2 fun x₀ ↦
    tendsto_nhds_of_eventually_seminorm_le h₁.continuousAt fun i ↦ ?_
  obtain ⟨g, hg, hle⟩ := h₂ i
  refine ⟨g x₀ + 1, ?_⟩
  filter_upwards [hg.continuousAt.eventually (gt_mem_nhds (lt_add_one (g x₀)))] with x hx
  exact (hle x).trans hx.le

/-- **Continuity of maps into `𝓓'_Γ(Ω)`.** A map from a topological space into `𝓓'_Γ(Ω)` is
continuous exactly when its composite with the inclusion into `𝓓'(Ω)` and its composites with all
the seminorms `‖·‖_{φ,V,N}` are continuous. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {f : X → WaveFrontSpace Ω Γ} :
    Continuous f ↔ Continuous (fun x ↦ (f x).toDistribution) ∧
      ∀ i, Continuous fun x ↦ WaveFrontSpace.seminorm i (f x) :=
  ⟨fun h ↦ ⟨continuous_toDistribution.comp h, fun i ↦ (continuous_seminorm i).comp h⟩,
    fun ⟨h₁, h₂⟩ ↦ continuous_of_le h₁ fun i ↦ ⟨_, h₂ i, fun _ ↦ le_rfl⟩⟩

/-- A linear map into `𝓓'_Γ(Ω)` whose composite with the inclusion into `𝓓'(Ω)` is continuous,
and each of whose seminorms `‖A ·‖_{φ,V,N}` is bounded by a continuous seminorm, is continuous. -/
theorem continuous_linearMap_of_le {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (A : F →ₗ[ℂ] WaveFrontSpace Ω Γ)
    (h₁ : Continuous (toDistribution ∘ₗ A))
    (h₂ : ∀ i, ∃ q : Seminorm ℂ F, Continuous q ∧ (WaveFrontSpace.seminorm i).comp A ≤ q) :
    Continuous A :=
  continuous_of_le h₁ fun i ↦
    let ⟨q, hq, hle⟩ := h₂ i
    ⟨q, hq, hle⟩

/-- **Continuity of linear maps into `𝓓'_Γ(Ω)`.** A linear map from a topological space into
`𝓓'_Γ(Ω)` is continuous exactly when its composite with the inclusion into `𝓓'(Ω)` and its
composites with all the seminorms `‖·‖_{φ,V,N}` are continuous. -/
theorem continuous_linearMap_iff {F : Type*} [AddCommGroup F] [Module ℂ F] [TopologicalSpace F]
    (A : F →ₗ[ℂ] WaveFrontSpace Ω Γ) :
    Continuous A ↔ Continuous (toDistribution ∘ₗ A) ∧
      ∀ i, Continuous ((WaveFrontSpace.seminorm i).comp A) :=
  continuous_iff

/-- **Distributions on a compact set of test functions.** For a compact set `Q` of complex test
functions, `‖T φ‖` is bounded, uniformly for `φ ∈ Q`, by a continuous seminorm of `T` in
`𝓓'_Γ(Ω)`: the normal topology is finer than the topology of `𝓓'(Ω)`, the topology of uniform
convergence on compact sets of test functions. -/
theorem exists_continuous_seminorm_norm_complexPairing_le {Q : Set 𝓓(Ω, ℂ)} (hQ : IsCompact Q) :
    ∃ q : Seminorm ℂ (WaveFrontSpace Ω Γ), Continuous q ∧
      ∀ u : WaveFrontSpace Ω Γ, ∀ φ ∈ Q, ‖u.toDistribution.complexPairing φ‖ ≤ q u := by
  let P : Q → WaveFrontSpace Ω Γ →ₗ[ℂ] ℂ := fun φ ↦
    { toFun := fun u ↦ u.toDistribution.complexPairing φ
      map_add' := fun u v ↦ by simp
      map_smul' := fun c u ↦ by simp }
  have hP (u : WaveFrontSpace Ω Γ) : ∃ C, ∀ φ : Q, ‖P φ u‖ ≤ C * 1 := by
    obtain ⟨C, hC⟩ :=
      hQ.exists_bound_of_continuousOn (u.toDistribution.complexPairing.continuous.continuousOn)
    exact ⟨C, fun φ ↦ by simpa [P] using hC φ φ.property⟩
  refine ⟨Seminorm.weightedSup P (fun _ ↦ 1) (fun _ ↦ one_pos), ?_, fun u φ hφ ↦ by
    simpa [P] using Seminorm.norm_le_weightedSup P _ _ hP u ⟨φ, hφ⟩⟩
  refine Seminorm.continuous_of_forall fun r hr ↦ ?_
  -- The real and imaginary parts of the members of `Q` form a compact set of real test functions.
  set Q' : Set 𝓓(Ω, ℝ) :=
    TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM '' Q ∪
      TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM '' Q
  have hQ' : IsCompact Q' :=
    (hQ.image (TestFunction.postcompCLM _).continuous).union
      (hQ.image (TestFunction.postcompCLM _).continuous)
  have hnhds : {S : 𝓓'(Ω, ℂ) | ∀ g ∈ Q', S g ∈ ball (0 : ℂ) (r / 4)} ∈ 𝓝 (0 : 𝓓'(Ω, ℂ)) :=
    CompactConvergenceCLM.hasBasis_nhds_zero.mem_of_mem (i := (Q', ball (0 : ℂ) (r / 4)))
      ⟨hQ', ball_mem_nhds _ (by positivity)⟩
  filter_upwards [(continuous_toDistribution.tendsto' 0 0 (map_zero _)) hnhds] with u hu
  rw [Seminorm.mem_ball_zero]
  refine (Seminorm.weightedSup_le P _ _ (by positivity : (0 : ℝ) ≤ r / 2) fun φ ↦ ?_).trans_lt
    (half_lt_self hr)
  have h1 := mem_ball_zero_iff.1 (hu _ (Or.inl ⟨φ, φ.property, rfl⟩))
  have h2 := mem_ball_zero_iff.1 (hu _ (Or.inr ⟨φ, φ.property, rfl⟩))
  calc ‖P φ u‖ = ‖u.toDistribution (TestFunction.postcompCLM (𝕜 := ℝ) Complex.reCLM φ) +
        Complex.I * u.toDistribution (TestFunction.postcompCLM (𝕜 := ℝ) Complex.imCLM φ)‖ := by
        simp [P, complexPairing_apply]
    _ ≤ r / 4 + r / 4 := (norm_add_le _ _).trans (add_le_add h1.le (by simpa using h2.le))
    _ = r / 2 * 1 := by ring

end Topology

/-! ### Continuous linear maps between the spaces `𝓓'_Γ(Ω)` -/

section Operations

/-- Two seminorms `‖·‖_{φ,V,N}` agree when their cones and orders agree and the two localized
Fourier transforms agree on the cone. -/
private theorem seminorm_eq_of_localFourier_eq {Ω' : Opens E} {i : WaveFrontSeminormIndex Ω Γ}
    {j : WaveFrontSeminormIndex Ω' Γ'} {u : WaveFrontSpace Ω Γ} {v : WaveFrontSpace Ω' Γ'}
    (hcone : i.cone = j.cone) (horder : i.order = j.order)
    (h : ∀ η ∈ i.cone, u.toDistribution.localFourier i.cutoff η =
      v.toDistribution.localFourier j.cutoff η) :
    WaveFrontSpace.seminorm i u = WaveFrontSpace.seminorm j v :=
  le_antisymm
    (seminorm_le_bound i u (apply_nonneg _ _) fun η hη ↦ by
      rw [h η hη, horder]
      exact le_seminorm j v (hcone ▸ hη))
    (seminorm_le_bound j v (apply_nonneg _ _) fun η hη ↦ by
      rw [← horder, ← h η (hcone ▸ hη)]
      exact le_seminorm i u (hcone ▸ hη))

/-- Lift a `ℂ`-linear map of distributions that sends `𝓓'_Γ(Ω)` into `𝓓'_Γ'(Ω')` to a `ℂ`-linear
map `𝓓'_Γ(Ω) →ₗ[ℂ] 𝓓'_Γ'(Ω')`. -/
private def mkLinearMap {Ω' : Opens E} (f : 𝓓'(Ω, ℂ) →ₗ[ℝ] 𝓓'(Ω', ℂ))
    (hsmul : ∀ (c : ℂ) T, f (c • T) = c • f T)
    (hwf : ∀ T, T.waveFrontSet ⊆ Γ → (f T).waveFrontSet ⊆ Γ') :
    WaveFrontSpace Ω Γ →ₗ[ℂ] WaveFrontSpace Ω' Γ' where
  toFun u := mk (f u.toDistribution) (hwf u.toDistribution u.waveFrontSet_toDistribution_subset)
  map_add' _ _ := ext (by simp)
  map_smul' _ _ := ext (by simp [hsmul])

/-- The inclusion `𝓓'_Γ(Ω) → 𝓓'_Γ'(Ω)` for `Γ ⊆ Γ'`, a continuous linear map. -/
def inclusionCLM (h : Γ ⊆ Γ') : WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω Γ' :=
  let A := mkLinearMap (LinearMap.id : 𝓓'(Ω, ℂ) →ₗ[ℝ] 𝓓'(Ω, ℂ)) (fun _ _ ↦ rfl)
    (fun _ hT ↦ hT.trans h)
  ⟨A, continuous_linearMap_of_le A continuous_toDistribution fun i ↦
    ⟨WaveFrontSpace.seminorm (i.mono h), continuous_seminorm _, fun u ↦
      (seminorm_eq_of_localFourier_eq (i := i) (j := i.mono h) (v := u) rfl rfl
        fun _ _ ↦ rfl).le⟩⟩

@[simp]
theorem toDistribution_inclusionCLM (h : Γ ⊆ Γ') (u : WaveFrontSpace Ω Γ) :
    (inclusionCLM h u).toDistribution = u.toDistribution :=
  (rfl)

/-- The seminorms of `𝓓'_Γ'(Ω)` restrict to seminorms of `𝓓'_Γ(Ω)` along the inclusion. -/
@[simp]
theorem seminorm_inclusionCLM (h : Γ ⊆ Γ') (i : WaveFrontSeminormIndex Ω Γ')
    (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (inclusionCLM h u) = WaveFrontSpace.seminorm (i.mono h) u :=
  seminorm_eq_of_localFourier_eq rfl rfl fun _ _ ↦ rfl

section SmulLeft

variable {g : E → ℝ}

/-- Multiplication `T ↦ g T` by a smooth real function on `𝓓'_Γ(Ω)`, a continuous linear map:
the seminorm `‖g T‖_{φ,V,N}` is the seminorm `‖T‖_{gφ,V,N}`. -/
def smulLeftCLM (hg : ContDiff ℝ ∞ g) : WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω Γ :=
  let A := mkLinearMap (Distribution.smulLeftCLM hg).toLinearMap (fun _ _ ↦ by ext; simp)
    (fun T hT ↦ ((waveFrontSet_smulLeftCLM_subset T hg).trans inter_subset_left).trans hT)
  ⟨A, continuous_linearMap_of_le A
    ((Distribution.smulLeftCLM hg).continuous.comp continuous_toDistribution) fun i ↦
      ⟨WaveFrontSpace.seminorm (i.smulLeft hg), continuous_seminorm _, fun u ↦
        (seminorm_eq_of_localFourier_eq (i := i) (j := i.smulLeft hg) (v := u) rfl rfl
          fun _ _ ↦ localFourier_smulLeftCLM _ hg _ _).le⟩⟩

@[simp]
theorem toDistribution_smulLeftCLM (hg : ContDiff ℝ ∞ g) (u : WaveFrontSpace Ω Γ) :
    (smulLeftCLM hg u).toDistribution = Distribution.smulLeftCLM hg u.toDistribution :=
  (rfl)

/-- The seminorm `‖g T‖_{φ,V,N}` is the seminorm `‖T‖_{gφ,V,N}`. -/
@[simp]
theorem seminorm_smulLeftCLM (hg : ContDiff ℝ ∞ g) (i : WaveFrontSeminormIndex Ω Γ)
    (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (smulLeftCLM hg u) = WaveFrontSpace.seminorm (i.smulLeft hg) u :=
  seminorm_eq_of_localFourier_eq rfl rfl fun η _ ↦ by
    rw [toDistribution_smulLeftCLM, localFourier_smulLeftCLM,
      WaveFrontSeminormIndex.smulLeft_cutoff]

end SmulLeft

/-- The bound `‖∂_v T‖_{φ,V,N} ≤ 2π ‖v‖ ‖T‖_{φ,V,N+1} + ‖T‖_{∂_v φ,V,N}` for any `u'` whose
underlying distribution is `∂_v T`, before `TauCeti.WaveFrontSpace.lineDerivCLM` is
defined. -/
private theorem seminorm_lineDerivOp_le (v : E) (i : WaveFrontSeminormIndex Ω Γ)
    (u : WaveFrontSpace Ω Γ) (u' : WaveFrontSpace Ω Γ)
    (hu' : u'.toDistribution = ∂_{v} u.toDistribution) :
    WaveFrontSpace.seminorm i u' ≤
      2 * π * ‖v‖ * WaveFrontSpace.seminorm (i.withOrder (i.order + 1)) u +
        WaveFrontSpace.seminorm (i.lineDeriv v) u := by
  refine seminorm_le_bound i u' (by positivity) fun η hη ↦ ?_
  rw [hu']
  exact (one_add_norm_pow_mul_norm_localFourier_lineDerivOp_le _ v _ _ η).trans
    (add_le_add (mul_le_mul_of_nonneg_left (le_seminorm (i.withOrder (i.order + 1)) u hη)
      (by positivity)) (le_seminorm (i.lineDeriv v) u hη))

/-- Differentiation `T ↦ ∂_v T` on `𝓓'_Γ(Ω)`, a continuous linear map: the seminorm
`‖∂_v T‖_{φ,V,N}` is at most `2π ‖v‖ ‖T‖_{φ,V,N+1} + ‖T‖_{∂_v φ,V,N}`. -/
def lineDerivCLM (v : E) : WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω Γ :=
  let A := mkLinearMap (Distribution.lineDerivCLM v).toLinearMap
    (fun _ _ ↦ by ext; simp [Distribution.lineDerivCLM_apply])
    (fun T hT ↦ (waveFrontSet_lineDerivOp_subset T v).trans hT)
  ⟨A, continuous_linearMap_of_le A
    ((Distribution.lineDerivCLM v).continuous.comp continuous_toDistribution) fun i ↦
      ⟨(2 * π * ‖v‖).toNNReal • WaveFrontSpace.seminorm (i.withOrder (i.order + 1)) +
          WaveFrontSpace.seminorm (i.lineDeriv v),
        ((continuous_seminorm _).const_smul (2 * π * ‖v‖).toNNReal).add (continuous_seminorm _),
        fun u ↦ by
          have h2π : (0 : ℝ) ≤ 2 * π * ‖v‖ := by positivity
          simpa [NNReal.smul_def, Real.coe_toNNReal _ h2π] using
            seminorm_lineDerivOp_le v i u _ (rfl)⟩⟩

@[simp]
theorem toDistribution_lineDerivCLM (v : E) (u : WaveFrontSpace Ω Γ) :
    (lineDerivCLM v u).toDistribution = ∂_{v} u.toDistribution :=
  (rfl)

/-- **The seminorms of a derivative.** For `T ∈ 𝓓'_Γ(Ω)`,
`‖∂_v T‖_{φ,V,N} ≤ 2π ‖v‖ ‖T‖_{φ,V,N+1} + ‖T‖_{∂_v φ,V,N}`. -/
theorem seminorm_lineDerivCLM_le (v : E) (i : WaveFrontSeminormIndex Ω Γ)
    (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (lineDerivCLM v u) ≤
      2 * π * ‖v‖ * WaveFrontSpace.seminorm (i.withOrder (i.order + 1)) u +
        WaveFrontSpace.seminorm (i.lineDeriv v) u :=
  seminorm_lineDerivOp_le v i u _ (rfl)

section Restriction

variable {Ω' : Opens E}

/-- Restriction maps distributions with wave front set in `Γ` into those with wave front set in
`Γ'` whenever `Γ ∩ (Ω' × univ) ⊆ Γ'` (including when `¬ Ω' ≤ Ω`, where restriction is zero). -/
private theorem waveFrontSet_restrictCLM_subset (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    {T : 𝓓'(Ω, ℂ)} (hT : T.waveFrontSet ⊆ Γ) :
    (Distribution.restrictCLM T : 𝓓'(Ω', ℂ)).waveFrontSet ⊆ Γ' := by
  by_cases h : Ω' ≤ Ω
  · rw [waveFrontSet_restrictCLM h]
    exact (inter_subset_inter_left _ hT).trans hΓ
  · have hmono : (TestFunction.monoCLM ℝ : 𝓓(Ω', ℝ) →L[ℝ] 𝓓(Ω, ℝ)) = 0 :=
      TestFunction.monoCLM_eq_zero (by simp [h])
    have h0 : (Distribution.restrictCLM T : 𝓓'(Ω', ℂ)) = 0 := by
      ext φ
      simp [Distribution.restrictCLM_apply, hmono]
    simp [h0]

/-- Restriction `T ↦ T|_{Ω'}` from `𝓓'_Γ(Ω)` to `𝓓'_Γ'(Ω')`, when the part of `Γ` over `Ω'` lies
in `Γ'`, a continuous linear map (zero unless `Ω' ≤ Ω`): the seminorm `‖T|_{Ω'}‖_{φ,V,N}` is the
seminorm `‖T‖_{φ,V,N}` with `φ` extended by zero. -/
def restrictCLM (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ') :
    WaveFrontSpace Ω Γ →L[ℂ] WaveFrontSpace Ω' Γ' :=
  let A := mkLinearMap (Distribution.restrictCLM (n := ⊤) (F := ℂ)).toLinearMap
    (fun _ _ ↦ by ext; simp) (fun _ hT ↦ waveFrontSet_restrictCLM_subset hΓ hT)
  ⟨A, continuous_linearMap_of_le A
    ((Distribution.restrictCLM (n := ⊤) (F := ℂ)).continuous.comp continuous_toDistribution)
      fun i ↦ ⟨WaveFrontSpace.seminorm (i.restrict Ω hΓ), continuous_seminorm _, fun u ↦
        (seminorm_eq_of_localFourier_eq (i := i) (j := i.restrict Ω hΓ) (v := u) rfl rfl
          fun _ _ ↦ localFourier_restrictCLM _ _ _).le⟩⟩

@[simp]
theorem toDistribution_restrictCLM (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (u : WaveFrontSpace Ω Γ) :
    (restrictCLM hΓ u).toDistribution = Distribution.restrictCLM u.toDistribution :=
  (rfl)

/-- The seminorm `‖T|_{Ω'}‖_{φ,V,N}` is the seminorm `‖T‖_{φ,V,N}` with `φ` extended by zero
(both zero unless `Ω' ≤ Ω`). -/
@[simp]
theorem seminorm_restrictCLM (hΓ : Γ ∩ (Ω' : Set E) ×ˢ univ ⊆ Γ')
    (i : WaveFrontSeminormIndex Ω' Γ') (u : WaveFrontSpace Ω Γ) :
    WaveFrontSpace.seminorm i (restrictCLM hΓ u) =
      WaveFrontSpace.seminorm (i.restrict Ω hΓ) u :=
  seminorm_eq_of_localFourier_eq rfl rfl fun η _ ↦ by
    rw [toDistribution_restrictCLM, localFourier_restrictCLM,
      WaveFrontSeminormIndex.restrict_cutoff]

end Restriction

end Operations

end WaveFrontSpace

end Space

end TauCeti
