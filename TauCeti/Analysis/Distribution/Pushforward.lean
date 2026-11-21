/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Distribution.CutoffPushforward
public import TauCeti.Analysis.Distribution.Restriction
public import TauCeti.Analysis.Distribution.TensorProduct
import TauCeti.Topology.Compactness.Compact

/-!
# Pushforward of distributions along maps proper on their support

Let `Ω ⊆ E` and `Ω' ⊆ E'` be open subsets of real normed spaces, with `E` finite-dimensional, let
`Φ : E → E'` be smooth on `Ω` and let `T` be a distribution on `Ω`. The map `Φ` is *proper on the
support of `T`* (`Distribution.IsProperOnSupport`) if the part `Ω ∩ supp T ∩ Φ⁻¹(K)` of the support
of `T` over every compact `K ⊆ Ω'` is compact. Then `T` has a pushforward `Φ_* T`, the
distribution on `Ω'` given by

`⟨Φ_* T, f⟩ = ⟨T, χ (f ∘ Φ)⟩`,

where the cutoff `χ` is a test function on `Ω` equal to one near `Ω ∩ supp T ∩ Φ⁻¹(supp f)`. It is
characterized by `⟨Φ_* T, f⟩ = ⟨T, g⟩` for every test function `g` on `Ω` that agrees with `f ∘ Φ`
near each point of the support of `T` in `Ω` (`Distribution.pushforward_apply_of_eventuallyEq`), so
it does not depend on the cutoffs. This extends the pushforward of compactly supported
distributions, `Distribution.cutoffPushforwardCLM`
(`Distribution.pushforward_eq_cutoffPushforwardCLM`), since every map continuous on `Ω` is proper
on the support of a compactly supported distribution
(`Distribution.isProperOnSupport_of_isCompact_dsupport`); on the other hand every map proper
from `Ω` to `Ω'` is proper on the support of every distribution
(`Distribution.isProperOnSupport_of_isCompact_inter_preimage`), whatever its support.

The cutoff depends on the support of the test function, so `Φ_* T` is defined test by test and is
continuous for the LF topology because one cutoff serves all test functions supported in a fixed
compact set. This uses the universal property of that topology and needs the values of `T` to lie
in a locally convex space.

For the density `f μ` of a function `f` locally integrable on `Ω`, the pushforward is the integral
`⟨Φ_* (f μ), φ⟩ = ∫_Ω φ (Φ x) f x dμ`: off the support of the distribution `f` vanishes almost
everywhere, and near it the cutoff is one. Along the first projection of `Ω × O` this is
integration over the fibres, `pr₁_* (f (μ × ν))` being the density of `x ↦ ∫_O f (x, y) dν`, and
along a constant map it is the point mass weighted by the total mass of `f`. The zero
covectors in the wave front bound of a pushforward cannot be omitted: the pushforward of a
smooth density of total mass one to a point is a point mass.

## Main declarations

* `Distribution.IsProperOnSupport`: `Φ` is proper on the support of `T`, and
  `Distribution.isProperOnSupport_of_isCompact_dsupport`: every continuous map is proper on the
  support of a compactly supported distribution.
* `Distribution.pushforward`: the pushforward `Φ_* T`.
* `Distribution.pushforward_apply_of_eventuallyEq` and
  `Distribution.pushforward_apply_eq_cutoffCompCLM`: its values.
* `Distribution.pushforward_eq_cutoffPushforwardCLM`: agreement with the pushforward of a
  compactly supported distribution, and `Distribution.restrictCLM_pushforward`: locally, every
  pushforward is such a pushforward.
* `Distribution.dsupport_pushforward_subset`: `supp (Φ_* T) ⊆ closure (Φ (Ω ∩ supp T))`, and
  `Distribution.inter_dsupport_pushforward_subset`: `Ω' ∩ supp (Φ_* T) ⊆ Φ (Ω ∩ supp T)` for
  finite-dimensional `E'`.
* `Distribution.pushforward_add`, `Distribution.pushforward_smul`: linearity.
* `Distribution.pushforward_id`, `Distribution.pushforward_pushforward`: functoriality.
* `Distribution.pushforward_tensorProduct`: `(Φ × Ψ)_* (S ⊗ T) = Φ_* S ⊗ Ψ_* T`.
* `Distribution.pushforward_fst_tensorProduct`: integration over the fibres of the first
  projection, `pr₁_* (S ⊗ T) = ⟨T, 1⟩ S` for `T` of compact support.
* `Distribution.pushforward_ofFun_apply`: the pushforward of the density `f μ` of a locally
  integrable function pairs a test function `φ` with `f` through `φ ∘ Φ`,
  `⟨Φ_* (f μ), φ⟩ = ∫_Ω φ (Φ x) f x dμ`, with integrable integrand
  (`Distribution.IsProperOnSupport.integrableOn_comp_smul`).
* `Distribution.pushforward_fst_ofFun`: integration over the fibres of the first projection for
  densities, `pr₁_* (f (μ × ν)) = (x ↦ ∫_O f (x, y) dν) μ`.
* `Distribution.pushforward_const_ofFun`: along a constant map with value `c` the density `f μ` is
  pushed forward to the point mass at `c` weighted by `∫_Ω f dμ`, and
  `Distribution.not_isProperOnSupport_ofFun_const_const`: a nonzero constant density on a
  nonempty open set is not proper over a point.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, §8.2 (the pushforward
  of a distribution along a map proper on its support, before Theorem 8.2.13) and §5.1 (tensor
  products of distributions).
-/

public section

noncomputable section

open Set Filter TopologicalSpace TestFunction
open scoped Distributions Topology

namespace Distribution

section IsProperOnSupport

variable {E E' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace E']
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F] {Ω : Opens E} {Ω' : Opens E'}
  {Φ : E → E'}

/-! ### Maps proper on the support of a distribution -/

/-- A map `Φ` is *proper on the support of* a distribution `T` on `Ω`, relative to an open set
`Ω'`, if the part `Ω ∩ supp T ∩ Φ⁻¹(K)` of the support of `T` over every compact `K ⊆ Ω'` is
compact. This is the condition for the pushforward `Φ_* T` to `Ω'` (`Distribution.pushforward`).
-/
def IsProperOnSupport (T : 𝓓'(Ω, F)) (Φ : E → E') (Ω' : Opens E') : Prop :=
  ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K)

/-- Unfolds `Distribution.IsProperOnSupport`. -/
theorem isProperOnSupport_iff {T : 𝓓'(Ω, F)} :
    IsProperOnSupport T Φ Ω' ↔
      ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K) :=
  Iff.rfl

/-- If `Φ` is proper on the support of `T`, the part of the support of `T` in `Ω` over a compact
subset of `Ω'` is compact. -/
theorem IsProperOnSupport.isCompact {T : 𝓓'(Ω, F)} (hT : IsProperOnSupport T Φ Ω') {K : Set E'}
    (hK : IsCompact K) (hKΩ' : K ⊆ Ω') : IsCompact ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K) :=
  hT K hK hKΩ'

/-- A map that is proper from `Ω` to `Ω'` is proper on the support of every distribution. -/
theorem isProperOnSupport_of_isCompact_inter_preimage (T : 𝓓'(Ω, F))
    (hΦ : ∀ K : Set E', IsCompact K → K ⊆ Ω' → IsCompact ((Ω : Set E) ∩ Φ ⁻¹' K)) :
    IsProperOnSupport T Φ Ω' := fun K hK hKΩ' ↦ by
  rw [inter_right_comm]
  exact (hΦ K hK hKΩ').inter_right isClosed_dsupport

/-- Every map continuous on `Ω` is proper on the support of a distribution whose support is a
compact subset of `Ω`. -/
theorem isProperOnSupport_of_isCompact_dsupport [T2Space E'] (hΦ : ContinuousOn Φ Ω)
    {T : 𝓓'(Ω, F)} (hT : IsCompact (dsupport T)) (hTΩ : dsupport T ⊆ Ω) :
    IsProperOnSupport T Φ Ω' := fun _ hK _ ↦ by
  rw [inter_eq_right.2 hTΩ]
  exact hT.inter_preimage (hΦ.mono hTΩ) hK.isClosed

/-- Every map is proper on the support of the zero distribution. -/
theorem isProperOnSupport_zero [IsTopologicalAddGroup F] : IsProperOnSupport (0 : 𝓓'(Ω, F)) Φ Ω' :=
  fun _ _ _ ↦ by simp [dsupport_zero]

/-- `Φ` is proper on the support of `T` if, over every compact `K ⊆ Ω'`, the part
`Ω ∩ supp T ∩ Φ⁻¹(K)` of the support of `T` lies in a compact subset of `Ω ∩ Φ⁻¹(K)`. -/
theorem IsProperOnSupport.of_forall_subset {T : 𝓓'(Ω, F)}
    (h : ∀ K : Set E', IsCompact K → K ⊆ Ω' → ∃ C : Set E, IsCompact C ∧
      (Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K ⊆ C ∧ C ⊆ (Ω : Set E) ∩ Φ ⁻¹' K) :
    IsProperOnSupport T Φ Ω' := fun K hK hKΩ' ↦ by
  obtain ⟨C, hC, hTC, hCK⟩ := h K hK hKΩ'
  -- The part of the support of `T` over `K` is the closed part `C ∩ supp T` of `C`.
  have hTC' : (Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K = C ∩ dsupport T := by
    refine Subset.antisymm (subset_inter hTC (inter_subset_left.trans inter_subset_right)) ?_
    rintro x ⟨hxC, hxT⟩
    obtain ⟨hxΩ, hxK⟩ := hCK hxC
    exact ⟨⟨hxΩ, hxT⟩, hxK⟩
  rw [hTC']
  exact hC.inter_right isClosed_dsupport

/-- If `Φ` is proper on the support of `T`, it is proper on the support of every distribution on
`Ω` whose support lies in that of `T`. -/
theorem IsProperOnSupport.mono {G : Type*} [AddCommGroup G] [Module ℝ G] [TopologicalSpace G]
    {S : 𝓓'(Ω, G)} {T : 𝓓'(Ω, F)} (hT : IsProperOnSupport T Φ Ω')
    (hST : dsupport S ⊆ dsupport T) : IsProperOnSupport S Φ Ω' :=
  of_forall_subset fun K hK hKΩ' ↦ ⟨_, hT K hK hKΩ',
    inter_subset_inter_left _ (inter_subset_inter_right _ hST),
    inter_subset_inter_left _ inter_subset_left⟩

omit [TopologicalSpace E'] in
/-- If the support of `U` lies in the union of those of `S` and `T`, then over every `K` the part
`Ω ∩ supp U ∩ Φ⁻¹(K)` of the support of `U` lies in the union of the corresponding parts for `S`
and `T`. -/
private theorem inter_dsupport_inter_preimage_subset_union {S T U : 𝓓'(Ω, F)}
    (h : dsupport U ⊆ dsupport S ∪ dsupport T) (K : Set E') :
    (Ω : Set E) ∩ dsupport U ∩ Φ ⁻¹' K ⊆
      (Ω : Set E) ∩ dsupport S ∩ Φ ⁻¹' K ∪ (Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K := by
  rw [← union_inter_distrib_right, ← inter_union_distrib_left]
  exact inter_subset_inter_left _ (inter_subset_inter_right _ h)

/-- If `Φ` is proper on the supports of `S` and `T`, it is proper on the support of `S + T`. -/
theorem IsProperOnSupport.add [IsTopologicalAddGroup F] {S T : 𝓓'(Ω, F)}
    (hS : IsProperOnSupport S Φ Ω') (hT : IsProperOnSupport T Φ Ω') :
    IsProperOnSupport (S + T) Φ Ω' :=
  -- Over `K`, the support of `S + T` in `Ω` lies in the union of those of `S` and `T`.
  of_forall_subset fun K hK hKΩ' ↦ ⟨_, (hS K hK hKΩ').union (hT K hK hKΩ'),
    inter_dsupport_inter_preimage_subset_union (dsupport_add_subset (⇑S) (⇑T)) K,
    union_subset (inter_subset_inter_left _ inter_subset_left)
      (inter_subset_inter_left _ inter_subset_left)⟩

/-- If `Φ` is proper on the support of `T`, it is proper on the support of `c • T`. -/
theorem IsProperOnSupport.smul {R : Type*} [Monoid R] [DistribMulAction R F]
    [SMulCommClass ℝ R F] [ContinuousConstSMul R F] {Φ : E → E'}
    {T : 𝓓'(Ω, F)} (hT : IsProperOnSupport T Φ Ω') (c : R) :
    IsProperOnSupport (c • T) Φ Ω' :=
  hT.mono (dsupport_smul_subset c (⇑T))

end IsProperOnSupport

variable {E E' E'' F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E'] [NormedSpace ℝ E'] [NormedAddCommGroup E''] [NormedSpace ℝ E'']
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {Ω : Opens E} {Ω' : Opens E'} {Ω'' : Opens E''} {Φ : E → E'} {hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω}

/-! ### Cutoffs -/

omit [NormedSpace ℝ E'] in
/-- A test function `χ` on `Ω` equal to one near `Ω ∩ supp T ∩ Φ⁻¹(K)`, for a compact `K ⊆ Ω'`. -/
private theorem IsProperOnSupport.exists_eventually_eq_one {T : 𝓓'(Ω, F)}
    (hT : IsProperOnSupport T Φ Ω') {K : Set E'} (hK : IsCompact K) (hKΩ' : K ⊆ Ω') :
    ∃ χ : 𝓓(Ω, ℝ), ∀ᶠ x in 𝓝ˢ ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K), χ x = 1 :=
  let ⟨χ, hχ, _⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) (hT K hK hKΩ')
    (inter_subset_left.trans inter_subset_left)
  ⟨χ, hχ⟩

/-! ### The pushforward -/

variable [IsTopologicalAddGroup F] [ContinuousSMul ℝ F] [LocallyConvexSpace ℝ F]

/-- The **pushforward** `Φ_* T` of a distribution `T` on `Ω` along a map `Φ` smooth on `Ω` and
proper on the support of `T`: the distribution on `Ω'` pairing a test function `f` with `T` through
`T (χ (f ∘ Φ))`, where `χ` is a test function on `Ω` equal to one near `Ω ∩ supp T ∩ Φ⁻¹(supp f)`.
Its value does not depend on `χ`, see `Distribution.pushforward_apply_of_eventuallyEq`. -/
def pushforward (T : 𝓓'(Ω, F)) (Φ : E → E') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    (hT : IsProperOnSupport T Φ Ω') : 𝓓'(Ω', F) :=
  -- The cutoff for tests supported in the compact set `K`.
  letI χ (K : Set E') (hK : IsCompact K) (hKΩ' : K ⊆ Ω') : 𝓓(Ω, ℝ) :=
    (hT.exists_eventually_eq_one hK hKΩ').choose
  haveI hχ (K : Set E') (hK : IsCompact K) (hKΩ' : K ⊆ Ω') :=
    (hT.exists_eventually_eq_one hK hKΩ').choose_spec
  -- Any two such cutoffs give the same value.
  haveI heq (f : 𝓓(Ω', ℝ)) {K₁ K₂ : Set E'} (hK₁ : IsCompact K₁) (hK₂ : IsCompact K₂)
      (hK₁Ω' : K₁ ⊆ Ω') (hK₂Ω' : K₂ ⊆ Ω') (hf₁ : tsupport f ⊆ K₁) (hf₂ : tsupport f ⊆ K₂) :
      T (cutoffCompCLM (χ K₁ hK₁ hK₁Ω') Φ hΦ f) = T (cutoffCompCLM (χ K₂ hK₂ hK₂Ω') Φ hΦ f) :=
    map_eq_map_of_forall_eventuallyEq T fun _ hx ↦
      (cutoffCompCLM_eventuallyEq ((hχ K₁ hK₁ hK₁Ω').filter_mono (nhdsSet_mono
        (inter_subset_inter_right _ (preimage_mono hf₁)))) hx.1 hx).trans
      (cutoffCompCLM_eventuallyEq ((hχ K₂ hK₂ hK₂Ω').filter_mono (nhdsSet_mono
        (inter_subset_inter_right _ (preimage_mono hf₂)))) hx.1 hx).symm
  TestFunction.limitCLM ℝ
    (fun f ↦ T (cutoffCompCLM (χ _ f.hasCompactSupport f.tsupport_subset) Φ hΦ f))
    -- A distribution is a continuous linear map on test functions, with the topology of compact
    -- convergence on the space of distributions; here only the underlying map is used.
    (fun K hK ↦ (T : 𝓓(Ω, ℝ) →L[ℝ] F) ∘L cutoffCompCLM (χ K K.isCompact hK) Φ hΦ ∘L
      ofSupportedInCLM ℝ hK)
    (fun K hK f ↦ heq (ofSupportedIn hK f) (ofSupportedIn hK f).hasCompactSupport K.isCompact
      (ofSupportedIn hK f).tsupport_subset hK subset_rfl f.tsupport_subset)

variable {T : 𝓓'(Ω, F)} {hT : IsProperOnSupport T Φ Ω'}

/-- **Values of the pushforward.** `⟨Φ_* T, f⟩ = ⟨T, g⟩` for every test function `g` on `Ω` that
agrees with `f ∘ Φ` near each point of the support of `T` in `Ω`. -/
theorem pushforward_apply_of_eventuallyEq (f : 𝓓(Ω', ℝ)) {g : 𝓓(Ω, ℝ)}
    (hg : ∀ x ∈ (Ω : Set E) ∩ dsupport T, (g : E → ℝ) =ᶠ[𝓝 x] fun y ↦ f (Φ y)) :
    pushforward T Φ hΦ hT f = T g := by
  -- By definition, `Φ_* T` pairs `f` with `T` through the cutoff chosen for `supp f`.
  have h : pushforward T Φ hΦ hT f = T (cutoffCompCLM
      (hT.exists_eventually_eq_one f.hasCompactSupport f.tsupport_subset).choose Φ hΦ f) :=
    TestFunction.limitCLM_apply ..
  rw [h]
  refine map_eq_map_of_forall_eventuallyEq T fun x hx ↦ ((cutoffCompCLM_eventuallyEq ?_ hx.1
    hx).trans (hg x hx).symm)
  exact (hT.exists_eventually_eq_one f.hasCompactSupport f.tsupport_subset).choose_spec

/-- **Values of the pushforward with a cutoff.** `⟨Φ_* T, f⟩ = ⟨T, χ (f ∘ Φ)⟩` for every test
function `χ` on `Ω` equal to one near `Ω ∩ supp T ∩ Φ⁻¹(supp f)`. -/
theorem pushforward_apply_eq_cutoffCompCLM (f : 𝓓(Ω', ℝ)) {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' tsupport f), χ x = 1) :
    pushforward T Φ hΦ hT f = T (cutoffCompCLM χ Φ hΦ f) :=
  pushforward_apply_of_eventuallyEq f fun _ hx ↦ cutoffCompCLM_eventuallyEq hχ hx.1 hx

/-- **The pushforward of a compactly supported distribution** is its pushforward with a cutoff
equal to one near the support. -/
theorem pushforward_eq_cutoffPushforwardCLM {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ (dsupport T), χ x = 1) :
    pushforward T Φ hΦ hT = cutoffPushforwardCLM χ Φ hΦ T := by
  ext f
  rw [cutoffPushforwardCLM_apply]
  refine pushforward_apply_of_eventuallyEq f fun x hx ↦ ?_
  filter_upwards [hχ.filter_mono (nhds_le_nhdsSet hx.2)] with y hy
  simp [hy]

/-- **Localization of the pushforward.** Over an open set `U` contained in a compact set `K`, the
pushforward `Φ_* T` agrees with the pushforward `T ∘ (χ Φ^*)` with any cutoff `χ` equal to one near
`Ω ∩ supp T ∩ Φ⁻¹(K)`. So local properties of pushforwards of compactly supported distributions,
such as bounds on their wave front sets, carry over to `Φ_* T`. -/
theorem restrictCLM_pushforward {U : Opens E'} {K : Set E'} (hUK : (U : Set E') ⊆ K)
    {χ : 𝓓(Ω, ℝ)} (hχ : ∀ᶠ x in 𝓝ˢ ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K), χ x = 1) :
    (restrictCLM (pushforward T Φ hΦ hT) : 𝓓'(U, F)) =
      restrictCLM (cutoffPushforwardCLM χ Φ hΦ T : 𝓓'(Ω', F)) := by
  ext φ
  -- The extension by zero of `φ` to `Ω'` is supported in `K`.
  have hφ : tsupport (monoCLM ℝ φ : 𝓓(Ω', ℝ)) ⊆ K := by
    rw [monoCLM_apply]
    split_ifs
    · exact φ.tsupport_subset.trans hUK
    · simp
  rw [restrictCLM_apply, restrictCLM_apply, cutoffPushforwardCLM_apply]
  exact pushforward_apply_eq_cutoffCompCLM _
    (hχ.filter_mono (nhdsSet_mono (inter_subset_inter_right _ (preimage_mono hφ))))

/-! ### The support of the pushforward -/

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- The image under `Φ` of the support of `T` in `Ω` is closed in `Ω'`: every point of `Ω'` outside
it has a neighbourhood that misses it. -/
private theorem exists_isOpen_disjoint_image (hΦ : ContinuousOn Φ Ω)
    (hT : IsProperOnSupport T Φ Ω') [FiniteDimensional ℝ E'] {y : E'} (hyΩ' : y ∈ Ω')
    (hy : y ∉ Φ '' ((Ω : Set E) ∩ dsupport T)) :
    ∃ s : Set E', IsOpen s ∧ y ∈ s ∧ s ⊆ Ω' ∧ Disjoint s (Φ '' ((Ω : Set E) ∩ dsupport T)) := by
  obtain ⟨K, hK, hyK, hKΩ'⟩ := exists_compact_subset Ω'.isOpen hyΩ'
  -- Over `K` the image is the compact, hence closed, image of `Ω ∩ supp T ∩ Φ⁻¹(K)`.
  have hC := (hT K hK hKΩ').image_of_continuousOn
    (hΦ.mono (inter_subset_left.trans inter_subset_left))
  refine ⟨interior K \ Φ '' ((Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' K),
    isOpen_interior.sdiff hC.isClosed, ⟨hyK, fun ⟨x, hx, hxy⟩ ↦ hy ⟨x, hx.1, hxy⟩⟩,
    sdiff_subset.trans (interior_subset.trans hKΩ'), disjoint_left.2 ?_⟩
  rintro _ ⟨hzK, hz⟩ ⟨x, hx, rfl⟩
  exact hz ⟨x, ⟨hx, interior_subset (s := K) hzK⟩, rfl⟩

/-- Test functions on `Ω'` supported away from `Φ (Ω ∩ supp T)` pair to zero with `Φ_* T`. -/
private theorem pushforward_apply_eq_zero {f : 𝓓(Ω', ℝ)}
    (hf : Disjoint (tsupport f) (Φ '' ((Ω : Set E) ∩ dsupport T))) :
    pushforward T Φ hΦ hT f = 0 := by
  -- The support of `T` in `Ω` misses `Φ⁻¹(supp f)`, so the zero cutoff will do.
  have hempty : (Ω : Set E) ∩ dsupport T ∩ Φ ⁻¹' tsupport f = ∅ :=
    eq_empty_of_forall_notMem fun x hx ↦ disjoint_left.1 hf hx.2 ⟨x, hx.1, rfl⟩
  rw [pushforward_apply_eq_cutoffCompCLM f (χ := 0) (by simp [hempty])]
  convert map_zero T
  ext x
  simp [cutoffCompCLM_apply]

/-- **The support of the pushforward** lies in the closure of the image of the support:
`supp (Φ_* T) ⊆ closure (Φ (Ω ∩ supp T))`. -/
theorem dsupport_pushforward_subset :
    dsupport (pushforward T Φ hΦ hT) ⊆ closure (Φ '' ((Ω : Set E) ∩ dsupport T)) :=
  sInter_subset_of_mem ⟨fun _ hf ↦ pushforward_apply_eq_zero
    ((disjoint_compl_left.mono_left hf).mono_right subset_closure), isClosed_closure⟩

/-- **The support of the pushforward in `Ω'`** lies in the image of the support:
`Ω' ∩ supp (Φ_* T) ⊆ Φ (Ω ∩ supp T)`. -/
theorem inter_dsupport_pushforward_subset [FiniteDimensional ℝ E'] :
    (Ω' : Set E') ∩ dsupport (pushforward T Φ hΦ hT) ⊆ Φ '' ((Ω : Set E) ∩ dsupport T) := by
  rintro y ⟨hyΩ', hy⟩
  by_contra hyΦ
  obtain ⟨s, hs, hys, -, hsdisj⟩ := exists_isOpen_disjoint_image hΦ.continuousOn hT hyΩ' hyΦ
  exact (notMem_dsupport_iff y).2 ⟨s, fun f hf ↦ pushforward_apply_eq_zero
    (hsdisj.mono_left hf), hs, hys⟩ hy

/-! ### Linearity -/

/-- The pushforward of the zero distribution is zero. -/
@[simp]
theorem pushforward_zero (h0 : IsProperOnSupport (0 : 𝓓'(Ω, F)) Φ Ω' := isProperOnSupport_zero) :
    pushforward 0 Φ hΦ h0 = 0 := by
  ext f
  rw [pushforward_apply_of_eventuallyEq f (g := 0) fun x hx ↦ by simp [dsupport_zero] at hx]
  simp

/-- The pushforward is additive. -/
theorem pushforward_add {S : 𝓓'(Ω, F)} (hS : IsProperOnSupport S Φ Ω')
    (hST : IsProperOnSupport (S + T) Φ Ω' := hS.add hT) :
    pushforward (S + T) Φ hΦ hST = pushforward S Φ hΦ hS + pushforward T Φ hΦ hT := by
  ext f
  -- One cutoff serves `S`, `T` and `S + T`.
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    ((hS _ f.hasCompactSupport f.tsupport_subset).union
      (hT _ f.hasCompactSupport f.tsupport_subset))
    (union_subset (inter_subset_left.trans inter_subset_left)
      (inter_subset_left.trans inter_subset_left))
  have hsub (U : 𝓓'(Ω, F)) (hU : dsupport U ⊆ dsupport S ∪ dsupport T) :
      ∀ᶠ x in 𝓝ˢ ((Ω : Set E) ∩ dsupport U ∩ Φ ⁻¹' tsupport f), χ x = 1 :=
    hχ.filter_mono <| nhdsSet_mono <| inter_dsupport_inter_preimage_subset_union hU _
  rw [add_apply,
    pushforward_apply_eq_cutoffCompCLM f (hsub _ (dsupport_add_subset ⇑S ⇑T)),
    pushforward_apply_eq_cutoffCompCLM f (hsub S subset_union_left),
    pushforward_apply_eq_cutoffCompCLM f (hsub T subset_union_right),
    add_apply]

/-- The pushforward commutes with scalar multiplication. -/
theorem pushforward_smul {R : Type*} [Monoid R] [DistribMulAction R F] [SMulCommClass ℝ R F]
    [ContinuousConstSMul R F] (c : R)
    (hcT : IsProperOnSupport (c • T) Φ Ω' := hT.smul c) :
    pushforward (c • T) Φ hΦ hcT = c • pushforward T Φ hΦ hT := by
  ext f
  obtain ⟨χ, hχ⟩ := hT.exists_eventually_eq_one f.hasCompactSupport f.tsupport_subset
  have hcT' : dsupport (c • T) ⊆ dsupport T := dsupport_smul_subset c (⇑T)
  rw [smul_apply, pushforward_apply_eq_cutoffCompCLM f hχ,
    pushforward_apply_eq_cutoffCompCLM f (hχ.filter_mono <| nhdsSet_mono <|
      inter_subset_inter_left _ (inter_subset_inter_right _ hcT')),
    smul_apply]

/-! ### Functoriality -/

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup F] [ContinuousSMul ℝ F]
  [LocallyConvexSpace ℝ F] in
/-- The identity is proper on the support of every distribution. -/
theorem isProperOnSupport_id (T : 𝓓'(Ω, F)) : IsProperOnSupport T id Ω :=
  isProperOnSupport_of_isCompact_inter_preimage T fun K hK hKΩ ↦ by
    rwa [preimage_id, inter_eq_self_of_subset_right hKΩ]

/-- **The pushforward along the identity** is the identity. -/
@[simp]
theorem pushforward_id {hid : ContDiffOn ℝ (⊤ : ℕ∞) (id : E → E) Ω} (T : 𝓓'(Ω, F))
    (hT : IsProperOnSupport T id Ω := isProperOnSupport_id T) :
    pushforward T id hid hT = T := by
  ext f
  exact pushforward_apply_of_eventuallyEq f fun _ _ ↦ EventuallyEq.rfl

/-- **Functoriality of the pushforward**: if `Φ` maps the support of `T` in `Ω` into `Ω'`, then
pushing `T` forward along `Φ` and then along `Ψ` is pushing it forward along `Ψ ∘ Φ`. -/
theorem pushforward_pushforward [FiniteDimensional ℝ E'] {Ψ : E' → E''}
    {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ Ω'} {hΨΦ : ContDiffOn ℝ (⊤ : ℕ∞) (Ψ ∘ Φ) Ω}
    (hΦT : MapsTo Φ ((Ω : Set E) ∩ dsupport T) Ω')
    (hΨT : IsProperOnSupport (pushforward T Φ hΦ hT) Ψ Ω'')
    (hΨΦT : IsProperOnSupport T (Ψ ∘ Φ) Ω'') :
    pushforward (pushforward T Φ hΦ hT) Ψ hΨ hΨT = pushforward T (Ψ ∘ Φ) hΨΦ hΨΦT := by
  ext f
  -- The part `L` of the support of `T` over `supp f` is compact, and so is its image in `Ω'`.
  set L := (Ω : Set E) ∩ dsupport T ∩ (Ψ ∘ Φ) ⁻¹' tsupport f
  have hL : IsCompact L := hΨΦT _ f.hasCompactSupport f.tsupport_subset
  obtain ⟨χ', hχ', -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤)
    (hL.image_of_continuousOn (hΦ.continuousOn.mono (inter_subset_left.trans inter_subset_left)))
    (image_subset_iff.2 fun x hx ↦ hΦT hx.1)
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hL
    (inter_subset_left.trans inter_subset_left)
  -- Push `f` back to `Ω'` with the cutoff `χ'`, which is one near the image of `L`.
  set h := cutoffCompCLM χ' Ψ hΨ f
  have h₁ : pushforward (pushforward T Φ hΦ hT) Ψ hΨ hΨT f = pushforward T Φ hΦ hT h := by
    refine pushforward_apply_of_eventuallyEq f fun y hy ↦ cutoffCompCLM_eventuallyEq
      (s := (Ω' : Set E') ∩ dsupport (pushforward T Φ hΦ hT)) (hχ'.filter_mono
        (nhdsSet_mono ?_)) hy.1 hy
    rintro _ ⟨hy, hyf⟩
    obtain ⟨x, hx, rfl⟩ := inter_dsupport_pushforward_subset hy
    exact ⟨x, ⟨hx, hyf⟩, rfl⟩
  -- Near every point of the support of `T` in `Ω`, `h ∘ Φ` agrees with `f ∘ Ψ ∘ Φ`.
  have h₂ (x : E) (hx : x ∈ (Ω : Set E) ∩ dsupport T) :
      (fun y ↦ h (Φ y)) =ᶠ[𝓝 x] fun y ↦ f ((Ψ ∘ Φ) y) :=
    -- The image of `L` is the part of `Φ (Ω ∩ supp T)` over `supp f`.
    (cutoffCompCLM_eventuallyEq (s := Φ '' ((Ω : Set E) ∩ dsupport T))
      (by rwa [← image_inter_preimage]) (hΦT hx) (mem_image_of_mem Φ hx)).comp_tendsto
      (hΦ.continuousOn.continuousAt (Ω.isOpen.mem_nhds hx.1)).tendsto
  rw [h₁, pushforward_apply_eq_cutoffCompCLM f hχ]
  exact pushforward_apply_of_eventuallyEq h fun x hx ↦
    (cutoffCompCLM_eventuallyEq hχ hx.1 hx).trans (h₂ x hx).symm

/-! ### Tensor products and integration over fibres -/

section TensorProduct

variable {D D' : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup D'] [NormedSpace ℝ D'] {O : Opens D} {O' : Opens D'}
  {V : Opens (E × D)} {V' : Opens (E' × D')} {Ψ : D → D'} {S : 𝓓'(Ω, ℂ)} {T : 𝓓'(O, ℂ)}

omit [NormedSpace ℝ E'] [NormedSpace ℝ D'] [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- If `Φ` is proper on the support of `S` and `Ψ` on the support of `T`, then `Φ × Ψ` is proper on
the support of `S ⊗ T`. -/
theorem IsProperOnSupport.tensorProduct (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hV' : (V' : Set (E' × D')) ⊆ (Ω' : Set E') ×ˢ (O' : Set D')) (hΦ : ContinuousOn Φ Ω)
    (hΨ : ContinuousOn Ψ O) (hS : IsProperOnSupport S Φ Ω') (hT : IsProperOnSupport T Ψ O') :
    IsProperOnSupport (S.tensorProduct T hV.subset) (Prod.map Φ Ψ) V' := by
  refine of_forall_subset fun K hK hKV' ↦ ?_
  have hK₁ : Prod.fst '' K ⊆ Ω' := image_subset_iff.2 fun p hp ↦ (hV' (hKV' hp)).1
  have hK₂ : Prod.snd '' K ⊆ O' := image_subset_iff.2 fun p hp ↦ (hV' (hKV' hp)).2
  -- Over `K`, the support of `S ⊗ T` lies in the product `C` of the parts of the supports of `S`
  -- and `T` over the projections of `K`.
  have hC := (hS _ (hK.image continuous_fst) hK₁).prod (hT _ (hK.image continuous_snd) hK₂)
  have hCV : ((Ω : Set E) ∩ dsupport S ∩ Φ ⁻¹' (Prod.fst '' K)) ×ˢ
      ((O : Set D) ∩ dsupport T ∩ Ψ ⁻¹' (Prod.snd '' K)) ⊆ (V : Set (E × D)) :=
    hV ▸ prod_mono (inter_subset_left.trans inter_subset_left)
      (inter_subset_left.trans inter_subset_left)
  have hΦΨ : ContinuousOn (Prod.map Φ Ψ) V := hV ▸ hΦ.prodMap hΨ
  refine ⟨_, hC.inter_preimage (hΦΨ.mono hCV) hK.isClosed, ?_, fun p hp ↦ ⟨hCV hp.1, hp.2⟩⟩
  rintro p ⟨⟨hpV, hp⟩, hpK⟩
  have hpΩO : p ∈ (Ω : Set E) ×ˢ (O : Set D) := hV ▸ hpV
  have hpST := dsupport_tensorProduct_subset S T hV.subset hp
  exact ⟨⟨⟨⟨hpΩO.1, hpST.1⟩, ⟨Prod.map Φ Ψ p, hpK, rfl⟩⟩,
    ⟨⟨hpΩO.2, hpST.2⟩, ⟨Prod.map Φ Ψ p, hpK, rfl⟩⟩⟩, hpK⟩

variable {hΨ : ContDiffOn ℝ (⊤ : ℕ∞) Ψ O}

/-- **The pushforward of a tensor product** along a product map is the tensor product of the
pushforwards: `(Φ × Ψ)_* (S ⊗ T) = Φ_* S ⊗ Ψ_* T`. -/
theorem pushforward_tensorProduct (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hV' : (V' : Set (E' × D')) = (Ω' : Set E') ×ˢ (O' : Set D'))
    {hΦΨ : ContDiffOn ℝ (⊤ : ℕ∞) (Prod.map Φ Ψ) V} (hS : IsProperOnSupport S Φ Ω')
    (hT : IsProperOnSupport T Ψ O')
    (hST : IsProperOnSupport (S.tensorProduct T hV.subset) (Prod.map Φ Ψ) V' :=
      hS.tensorProduct hV hV'.subset hΦ.continuousOn hΨ.continuousOn hT) :
    pushforward (S.tensorProduct T hV.subset) (Prod.map Φ Ψ) hΦΨ hST =
      (pushforward S Φ hΦ hS).tensorProduct (pushforward T Ψ hΨ hT) hV'.subset := by
  refine (tensorProduct_eq _ _ hV' fun φ ψ ↦ ?_).symm
  obtain ⟨χ₁, hχ₁⟩ := hS.exists_eventually_eq_one φ.hasCompactSupport φ.tsupport_subset
  obtain ⟨χ₂, hχ₂⟩ := hT.exists_eventually_eq_one ψ.hasCompactSupport ψ.tsupport_subset
  rw [pushforward_apply_eq_cutoffCompCLM φ hχ₁, pushforward_apply_eq_cutoffCompCLM ψ hχ₂,
    ← tensorProduct_prodSMulCLM S T hV.subset _ hV.symm.subset]
  refine pushforward_apply_of_eventuallyEq _ fun p hp ↦ ?_
  have hpV : p ∈ (Ω : Set E) ×ˢ (O : Set D) := hV ▸ hp.1
  have hpST := dsupport_tensorProduct_subset S T hV.subset hp.2
  have h₁ := cutoffCompCLM_eventuallyEq (hΦ := hΦ) hχ₁ hpV.1 ⟨hpV.1, hpST.1⟩
  have h₂ := cutoffCompCLM_eventuallyEq (hΦ := hΨ) hχ₂ hpV.2 ⟨hpV.2, hpST.2⟩
  filter_upwards [continuous_fst.continuousAt.preimage_mem_nhds h₁,
    continuous_snd.continuousAt.preimage_mem_nhds h₂] with q hq₁ hq₂
  simp only [mem_preimage, mem_ofPred_eq] at hq₁ hq₂
  simp [prodSMulCLM_apply, hq₁, hq₂]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ D] in
/-- The first projection is proper on the support of `S ⊗ T` when `T` has compact support. -/
theorem isProperOnSupport_fst_tensorProduct (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hT : IsCompact (dsupport T)) (hTO : dsupport T ⊆ O) :
    IsProperOnSupport (S.tensorProduct T hV.subset) Prod.fst Ω := by
  refine IsProperOnSupport.of_forall_subset fun K hK hKΩ ↦ ?_
  have hCV : (K ∩ dsupport S) ×ˢ dsupport T ⊆ (V : Set (E × D)) :=
    hV ▸ prod_mono (inter_subset_left.trans hKΩ) hTO
  refine ⟨_, ((hK.inter_right (isClosed_dsupport (f := ⇑S))).prod hT).inter_preimage
    continuousOn_fst hK.isClosed, ?_, fun p hp ↦ ⟨hCV hp.1, hp.2⟩⟩
  rintro p ⟨⟨-, hp⟩, hpK⟩
  have hpST := dsupport_tensorProduct_subset S T hV.subset hp
  exact ⟨⟨⟨hpK, hpST.1⟩, hpST.2⟩, hpK⟩

/-- **Integration over the fibres of the first projection.** If `T` has compact support, pushing
`S ⊗ T` forward along the first projection gives `S` times the total mass `⟨T, 1⟩` of `T`
(`Distribution.augmentation`). -/
theorem pushforward_fst_tensorProduct (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hT : IsCompact (dsupport T)) (hTO : dsupport T ⊆ O)
    (hST : IsProperOnSupport (S.tensorProduct T hV.subset) Prod.fst Ω :=
      isProperOnSupport_fst_tensorProduct hV hT hTO) :
    pushforward (S.tensorProduct T hV.subset) Prod.fst contDiffOn_fst hST =
      augmentation (⇑T) (1 : ℝ) • S := by
  ext φ
  obtain ⟨χ, hχ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hT hTO
  have hχ₁ : postcompCLM (ContinuousLinearMap.toSpanSingleton ℝ (1 : ℝ)) χ = χ := by
    ext x
    simp
  rw [smul_apply, augmentation_eq T hχ, hχ₁, smul_eq_mul, mul_comm,
    ← tensorProduct_prodSMulCLM S T hV.subset χ hV.symm.subset φ]
  refine pushforward_apply_of_eventuallyEq φ fun p hp ↦ ?_
  have hpST := dsupport_tensorProduct_subset S T hV.subset hp.2
  filter_upwards [continuous_snd.continuousAt.preimage_mem_nhds
    (hχ.filter_mono (nhds_le_nhdsSet hpST.2))] with q hq
  simp only [mem_preimage, mem_ofPred_eq] at hq
  simp [prodSMulCLM_apply, hq]

end TensorProduct

/-! ### Densities -/

section OfFun

open MeasureTheory

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] [CompleteSpace G]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} {f : E → G}

/-- Near the support of the distribution of `f` over `supp φ`, the cutoff `χ` is one, and off
that support `f` vanishes almost everywhere, so cutting off does not change `(φ ∘ Φ) • f` almost
everywhere on `Ω`. -/
private theorem ae_restrict_cutoffCompCLM_smul_eq (hf : LocallyIntegrableOn f Ω μ)
    {φ : 𝓓(Ω', ℝ)} {χ : 𝓓(Ω, ℝ)}
    (hχ : ∀ᶠ x in 𝓝ˢ ((Ω : Set E) ∩ dsupport (ofFun Ω f μ ⊤) ∩ Φ ⁻¹' tsupport φ), χ x = 1) :
    (fun x ↦ cutoffCompCLM χ Φ hΦ φ x • f x) =ᵐ[μ.restrict Ω] fun x ↦ φ (Φ x) • f x := by
  rw [EventuallyEq, ae_restrict_iff' Ω.isOpen.measurableSet]
  filter_upwards [ae_eq_zero_of_notMem_dsupport_ofFun (n := ⊤) hf] with x hx hxΩ
  rw [cutoffCompCLM_apply, smul_eq_mul]
  by_cases hxT : x ∈ dsupport (ofFun Ω f μ ⊤)
  · by_cases hφx : Φ x ∈ tsupport φ
    · rw [hχ.self_of_nhdsSet x ⟨⟨hxΩ, hxT⟩, hφx⟩, one_mul]
    · simp [image_eq_zero_of_notMem_tsupport hφx]
  · simp [hx hxΩ hxT]

/-- If `Φ` is proper on the support of the density `f μ`, the integrand `x ↦ φ (Φ x) • f x` of its
pushforward is integrable on `Ω` for every test function `φ` on `Ω'`, although `φ ∘ Φ` need not
have compact support in `Ω`. -/
theorem IsProperOnSupport.integrableOn_comp_smul
    (hT : IsProperOnSupport (ofFun Ω f μ ⊤) Φ Ω') (hΦ : ContDiffOn ℝ (⊤ : ℕ∞) Φ Ω)
    (hf : LocallyIntegrableOn f Ω μ) (φ : 𝓓(Ω', ℝ)) :
    IntegrableOn (fun x ↦ φ (Φ x) • f x) Ω μ :=
  let ⟨_, hχ⟩ := hT.exists_eventually_eq_one φ.hasCompactSupport φ.tsupport_subset
  ((cutoffCompCLM _ Φ hΦ φ).integrable_smul hf).integrableOn.congr_fun_ae
    (ae_restrict_cutoffCompCLM_smul_eq hf hχ)

/-- **The pushforward of a density.** If `f` is locally integrable on `Ω` and `Φ` is proper on the
support of its distribution, the pushforward of that distribution pairs a test function `φ` with
`f` through `φ ∘ Φ`:

`⟨Φ_* (f μ), φ⟩ = ∫_Ω φ (Φ x) f x dμ`.

The integrand is integrable on `Ω` by `Distribution.IsProperOnSupport.integrableOn_comp_smul`. -/
theorem pushforward_ofFun_apply (hf : LocallyIntegrableOn f Ω μ)
    (hT : IsProperOnSupport (ofFun Ω f μ ⊤) Φ Ω') (φ : 𝓓(Ω', ℝ)) :
    pushforward (ofFun Ω f μ ⊤) Φ hΦ hT φ = ∫ x in Ω, φ (Φ x) • f x ∂μ := by
  obtain ⟨χ, hχ⟩ := hT.exists_eventually_eq_one φ.hasCompactSupport φ.tsupport_subset
  rw [pushforward_apply_eq_cutoffCompCLM φ hχ, ofFun_apply hf,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx ↦ by
      simp [(cutoffCompCLM χ Φ hΦ φ).zero_on_compl hx]]
  exact integral_congr_ae (ae_restrict_cutoffCompCLM_smul_eq hf hχ)

/-- **Pushforward of a density along a constant map.** Pushing the density `f μ` forward along the
constant map with value `c` gives the point mass at `c` weighted by the total mass `∫_Ω f dμ`.
For instance a smooth compactly supported density of total mass one is pushed forward to the point
mass `δ_c`, although its wave front set is empty. -/
theorem pushforward_const_ofFun (hf : LocallyIntegrableOn f Ω μ) {c : E'}
    (hT : IsProperOnSupport (ofFun Ω f μ ⊤) (fun _ ↦ c) Ω') :
    pushforward (ofFun Ω f μ ⊤) (fun _ ↦ c) contDiffOn_const hT =
      mapCLM (ContinuousLinearMap.toSpanSingleton ℝ (∫ x in Ω, f x ∂μ)) (delta c : 𝓓'(Ω', ℝ)) := by
  ext φ
  rw [pushforward_ofFun_apply hf hT, integral_smul]
  simp

omit [NormedSpace ℝ E'] in
/-- A nonzero constant density on a nonempty open subset of a nontrivial space is not proper over
a point: the constant map to a point of `Ω'` is not proper on its support, so the pushforward of a
constant density to a point is not defined. -/
theorem not_isProperOnSupport_ofFun_const_const [Nontrivial E] [μ.IsOpenPosMeasure]
    [IsFiniteMeasureOnCompacts μ] {v : G}
    (hv : v ≠ 0) (hΩ : (Ω : Set E).Nonempty) {c : E'} (hc : c ∈ Ω') :
    ¬IsProperOnSupport (ofFun Ω (fun _ ↦ v) μ ⊤) (fun _ ↦ c) Ω' := by
  intro h
  -- Over the point `c` the support of the constant density is all of `Ω`, which would be compact.
  have hcpt := h {c} isCompact_singleton (singleton_subset_iff.2 hc)
  rw [preimage_const_of_mem rfl, inter_univ,
    inter_eq_left.2 (subset_dsupport_ofFun_const (μ := μ) (n := ⊤) hv)] at hcpt
  -- A nonempty compact open subset of the connected space `E` is all of `E`, which is not compact.
  have huniv := IsClopen.eq_univ ⟨hcpt.isClosed, Ω.isOpen⟩ hΩ
  exact noncompact_univ E (huniv ▸ hcpt)

section Fibre

variable {D : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [MeasurableSpace D] [BorelSpace D] {ν : Measure D} [SFinite μ] [SFinite ν] {O : Opens D}
  {V : Opens (E × D)} {f : E × D → G}

/-- The fibre integral `x ↦ ∫_O f (x, y) dν` of a density proper over `Ω` is locally integrable on
`Ω`. -/
private theorem locallyIntegrableOn_setIntegral_fst
    (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hf : LocallyIntegrableOn f V (μ.prod ν))
    (hT : IsProperOnSupport (ofFun V f (μ.prod ν) ⊤) Prod.fst Ω) :
    LocallyIntegrableOn (fun x ↦ ∫ y in O, f (x, y) ∂ν) Ω μ := by
  refine (locallyIntegrableOn_iff Ω.isOpen.isLocallyClosed).2 fun K hKΩ hK ↦ ?_
  -- Over a test function `ψ` equal to one near `K`, the density is integrable on `K × O`.
  obtain ⟨ψ, hψ, -⟩ := TestFunction.exists_eventually_eq_one (n := ⊤) hK hKΩ
  have hKO : IntegrableOn f (K ×ˢ (O : Set D)) (μ.prod ν) := by
    refine ((hT.integrableOn_comp_smul contDiffOn_fst hf ψ).mono_set ?_).congr_fun
      (fun p hp ↦ ?_) (hK.measurableSet.prod O.isOpen.measurableSet)
    · rw [hV]
      exact prod_mono hKΩ subset_rfl
    · simp [hψ.self_of_nhdsSet p.1 hp.1]
  rw [IntegrableOn, ← Measure.prod_restrict] at hKO
  exact hKO.integral_prod_left

/-- **Integration over the fibres.** Pushing the density `f (μ × ν)` on `Ω × O` forward along the
first projection gives the density of its fibre integral `x ↦ ∫_O f (x, y) dν`, provided the
projection is proper on the support of `f`, for example when `f` has compact support in `Ω × O`. -/
theorem pushforward_fst_ofFun (hV : (V : Set (E × D)) = (Ω : Set E) ×ˢ (O : Set D))
    (hf : LocallyIntegrableOn f V (μ.prod ν))
    (hT : IsProperOnSupport (ofFun V f (μ.prod ν) ⊤) Prod.fst Ω) :
    pushforward (ofFun V f (μ.prod ν) ⊤) Prod.fst contDiffOn_fst hT =
      ofFun Ω (fun x ↦ ∫ y in O, f (x, y) ∂ν) μ ⊤ := by
  ext φ
  have hint := hT.integrableOn_comp_smul contDiffOn_fst hf φ
  rw [hV] at hint
  rw [pushforward_ofFun_apply hf hT, ofFun_apply (locallyIntegrableOn_setIntegral_fst hV hf hT),
    hV, setIntegral_prod _ hint,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := (Ω : Set E)) (μ := μ) fun x hx ↦ by
      simp [φ.zero_on_compl hx]]
  exact setIntegral_congr_fun Ω.isOpen.measurableSet fun x _ ↦
    integral_smul (φ x) fun y ↦ f (x, y)

end Fibre

end OfFun

end Distribution
