/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.SmulLeft
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.VectorBundle.Section.Extension

/-!
# The support of a functional on bundle tests

Let `V → M` be a smooth real vector bundle over a manifold modelled on a finite-dimensional space.
A map `T` on the bundle tests `TauCeti.BundleTest I F V`, for instance a distributional section
(`TauCeti.BundleDistribution`), *vanishes on* a set `U` (`TauCeti.BundleTest.IsVanishingOn`) if
`T s = 0` for every test `s` whose closed support lies in `U`. Its **support**
`TauCeti.BundleTest.dsupport T` is the complement of the union of the open sets on which it
vanishes, a closed subset of `M`. This is the manifold counterpart of Mathlib's
`Distribution.dsupport` for distributions on open subsets of a normed space.

For an additive map on bundle tests the *localization principle* holds: `T` vanishes on the
complement of its support (`TauCeti.BundleTest.isVanishingOn_compl_dsupport`). A test supported in
a union of open sets on which `T` vanishes is the finite sum of its products with a smooth partition
of unity on its compact support subordinate to these sets, and `T` vanishes on each product.
Consequently `T s` only depends on the germ of `s` along the support of `T`
(`TauCeti.BundleTest.map_eq_map_of_eventuallyEq`), `T` vanishes exactly when its support is empty
(`TauCeti.BundleTest.dsupport_eq_empty_iff`), and the support of a sum lies in the union of the
supports (`TauCeti.BundleTest.dsupport_add_subset`). The point mass `δ_x ℓ` with `ℓ ≠ 0` is
supported exactly at `x` (`TauCeti.BundleTest.dsupport_delta`).

## Main declarations

* `TauCeti.BundleTest.IsVanishingOn`: a map on bundle tests vanishes on a set.
* `TauCeti.BundleTest.dsupport`: the support of a map on bundle tests, a closed set
  (`TauCeti.BundleTest.isClosed_dsupport`), characterized by
  `TauCeti.BundleTest.notMem_dsupport_iff`.
* `TauCeti.BundleTest.isVanishingOn_compl_dsupport`: the localization principle, with
  `TauCeti.BundleTest.map_eq_zero_of_disjoint_dsupport` and
  `TauCeti.BundleTest.map_eq_map_of_eventuallyEq`.
* `TauCeti.BundleTest.dsupport_eq_empty_iff`, `TauCeti.BundleTest.dsupport_add_subset`,
  `TauCeti.BundleTest.dsupport_smul_subset`, `TauCeti.BundleTest.dsupport_smulLeftDualCLM_subset`,
  `TauCeti.BundleTest.dsupport_delta_subset` and `TauCeti.BundleTest.dsupport_delta`.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2 (localization and support) and §6.3 (distributions on manifolds).
-/

public noncomputable section

open Bundle Set Filter Function TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] {W : Type*}

/-! ### Vanishing on a set and the support -/

section Zero

variable [Zero W] {T T' : BundleTest I F V → W} {U U' : Set M}

/-- A map `T` on bundle tests **vanishes on** a set `U` if `T s = 0` for every test `s` whose
closed support lies in `U`. -/
def IsVanishingOn (T : BundleTest I F V → W) (U : Set M) : Prop :=
  ∀ s : BundleTest I F V, closure {x | s x ≠ 0} ⊆ U → T s = 0

/-- Unfolds `TauCeti.BundleTest.IsVanishingOn`. -/
theorem isVanishingOn_iff :
    IsVanishingOn T U ↔ ∀ s : BundleTest I F V, closure {x | s x ≠ 0} ⊆ U → T s = 0 :=
  Iff.rfl

/-- A map vanishing on a set vanishes on its subsets. -/
theorem IsVanishingOn.mono (hT : IsVanishingOn T U) (hU' : U' ⊆ U) : IsVanishingOn T U' :=
  fun s hs ↦ hT s (hs.trans hU')

/-- The **support** of a map `T` on bundle tests: the complement of the union of the open sets on
which `T` vanishes. -/
def dsupport (T : BundleTest I F V → W) : Set M :=
  (⋃₀ {U | IsOpen U ∧ IsVanishingOn T U})ᶜ

/-- The support of a map on bundle tests is closed. -/
theorem isClosed_dsupport (T : BundleTest I F V → W) : IsClosed (dsupport T) :=
  (isOpen_sUnion fun _ (hU : _ ∈ {U | IsOpen U ∧ IsVanishingOn T U}) ↦ hU.1).isClosed_compl

/-- A point lies outside the support of `T` exactly when `T` vanishes on an open set containing
it. -/
theorem notMem_dsupport_iff {x : M} :
    x ∉ dsupport T ↔ ∃ U, IsOpen U ∧ x ∈ U ∧ IsVanishingOn T U := by
  simp only [dsupport, mem_compl_iff, not_not, mem_sUnion]
  exact ⟨fun ⟨U, ⟨hU, hTU⟩, hx⟩ ↦ ⟨U, hU, hx, hTU⟩, fun ⟨U, hU, hx, hTU⟩ ↦ ⟨U, ⟨hU, hTU⟩, hx⟩⟩

/-- An open set on which `T` vanishes misses the support of `T`. -/
theorem IsVanishingOn.disjoint_dsupport (hT : IsVanishingOn T U) (hU : IsOpen U) :
    Disjoint U (dsupport T) :=
  disjoint_compl_right_iff_subset.2 (subset_sUnion_of_mem ⟨hU, hT⟩)

/-- The support of the zero map is empty. -/
@[simp]
theorem dsupport_zero : dsupport (0 : BundleTest I F V → W) = ∅ :=
  eq_empty_of_forall_notMem fun _ ↦ notMem_dsupport_iff.2 ⟨univ, isOpen_univ, mem_univ _,
    fun _ _ ↦ rfl⟩

/-- If `T'` vanishes on every open set on which `T` vanishes, the support of `T'` lies in that of
`T`. -/
theorem dsupport_subset_dsupport (h : ∀ U, IsOpen U → IsVanishingOn T U → IsVanishingOn T' U) :
    dsupport T' ⊆ dsupport T :=
  compl_subset_compl.2 <| sUnion_subset_sUnion fun U hU ↦ ⟨hU.1, h U hU.1 hU.2⟩

end Zero

/-- The support of a sum of maps on bundle tests lies in the union of their supports. -/
theorem dsupport_add_subset [AddZeroClass W] (T T' : BundleTest I F V → W) :
    dsupport (T + T') ⊆ dsupport T ∪ dsupport T' := by
  intro x hx
  by_contra h
  rw [mem_union, not_or, notMem_dsupport_iff, notMem_dsupport_iff] at h
  obtain ⟨⟨U, hU, hxU, hTU⟩, ⟨U', hU', hxU', hTU'⟩⟩ := h
  refine notMem_dsupport_iff.2 ⟨U ∩ U', hU.inter hU', ⟨hxU, hxU'⟩, fun s hs ↦ ?_⟩ hx
  simp [hTU s (hs.trans inter_subset_left), hTU' s (hs.trans inter_subset_right)]

/-- The support of a scalar multiple of a map lies in the support of the map. -/
theorem dsupport_smul_subset {R : Type*} [Zero W] [SMulZeroClass R W] (c : R)
    (T : BundleTest I F V → W) : dsupport (c • T) ⊆ dsupport T :=
  dsupport_subset_dsupport fun _ _ hT s hs ↦ by simp [hT s hs]

/-! ### The localization principle -/

section Localization

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  [AddCommMonoid W] {𝓕 : Type*} [FunLike 𝓕 (BundleTest I F V) W]
  [AddMonoidHomClass 𝓕 (BundleTest I F V) W] (T : 𝓕)

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- Multiplying a bundle test by a smooth function `ρ` gives a test supported in the supports of
`ρ` and of the test. -/
theorem closure_smulLeftCLM_ne_zero_subset (ρ : C^∞⟮I, M; ℝ⟯) (s : BundleTest I F V) :
    closure {x | smulLeftCLM ρ s x ≠ 0} ⊆ tsupport ρ ∩ closure {x | s x ≠ 0} := by
  simpa [ContMDiffSection.tsupport_def, ContMDiffSection.smul_apply] using
    tsupport_smul_function_subset ρ ((ofCompactlySupported I F V).symm s).val

/-- **Localization principle.** An additive map on bundle tests vanishes on the complement of its
support. A test supported off the support is, by a smooth partition of unity on its compact
support, a finite sum of tests each supported in an open set on which the map vanishes. -/
theorem isVanishingOn_compl_dsupport : IsVanishingOn T (dsupport T)ᶜ := by
  intro s hs
  have hK : IsCompact (closure {x | s x ≠ 0}) := s.isCompact_tsupport
  -- Near every point off the support, an open set on which `T` vanishes.
  have hex (x : M) : ∃ U : Set M, x ∉ dsupport T → IsOpen U ∧ x ∈ U ∧ IsVanishingOn T U := by
    by_cases hx : x ∈ dsupport T
    · exact ⟨univ, fun h ↦ absurd hx h⟩
    · obtain ⟨U, hU⟩ := notMem_dsupport_iff.1 hx
      exact ⟨U, fun _ ↦ hU⟩
  choose U hU using hex
  obtain ⟨ι, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate I
    fun x hx ↦ (hU x (hs hx)).1.mem_nhds (hU x (hs hx)).2.1
  let ρ := f.toSmoothPartitionOfUnity
  -- `s` is the sum of its products with the partition of unity.
  have hsum : s = ∑ i, smulLeftCLM (ρ i) s := by
    ext x
    rw [sum_apply]
    by_cases hx : x ∈ closure {x | s x ≠ 0}
    · simp_rw [smulLeftCLM_apply, ← Finset.sum_smul]
      rw [← finsum_eq_sum_of_fintype, ρ.sum_eq_one hx, one_smul]
    · simp [Bundle.apply_eq_zero_of_notMem_closure hx]
  rw [hsum, map_sum]
  refine Finset.sum_eq_zero fun i _ ↦ (hU _ (hs (f.c_mem' i))).2.2 _ ?_
  exact (closure_smulLeftCLM_ne_zero_subset (ρ i) s).trans
    (inter_subset_left.trans (hf.toSmoothPartitionOfUnity i))

/-- An additive map on bundle tests vanishes exactly on the open sets missing its support. -/
theorem isVanishingOn_iff_disjoint_dsupport {U : Set M} (hU : IsOpen U) :
    IsVanishingOn T U ↔ Disjoint U (dsupport T) :=
  ⟨fun h ↦ h.disjoint_dsupport hU,
    fun h ↦ (isVanishingOn_compl_dsupport T).mono h.subset_compl_right⟩

/-- An additive map on bundle tests vanishes on every test supported off its support. -/
theorem map_eq_zero_of_disjoint_dsupport {s : BundleTest I F V}
    (hs : Disjoint (closure {x | s x ≠ 0}) (dsupport T)) : T s = 0 :=
  isVanishingOn_compl_dsupport T s hs.subset_compl_right

/-- An additive map on bundle tests vanishes exactly when its support is empty. -/
theorem dsupport_eq_empty_iff : dsupport T = ∅ ↔ ⇑T = 0 :=
  ⟨fun h ↦ funext fun s ↦ map_eq_zero_of_disjoint_dsupport T (by simp [h]),
    fun h ↦ by rw [h, dsupport_zero]⟩

/-- **The value of an additive map on bundle tests only depends on the germ of the test along
its support.** -/
theorem map_eq_map_of_eventuallyEq {W : Type*} [AddCommGroup W] {𝓕 : Type*}
    [FunLike 𝓕 (BundleTest I F V) W] [AddMonoidHomClass 𝓕 (BundleTest I F V) W] (T : 𝓕)
    {s t : BundleTest I F V} (h : ∀ᶠ x in 𝓝ˢ (dsupport T), s x = t x) : T s = T t := by
  obtain ⟨U, hU, hTU, hst⟩ := mem_nhdsSet_iff_exists.1 h
  rw [← sub_eq_zero, ← map_sub]
  refine map_eq_zero_of_disjoint_dsupport T (Disjoint.mono_left ?_ hTU.disjoint_compl_left)
  refine closure_minimal (fun x hx hxU ↦ hx ?_) hU.isClosed_compl
  simp [show s x = t x from hst hxU]

end Localization

/-! ### Products with smooth functions and point masses -/

section Dual

variable [FiniteDimensional ℝ E] [T2Space M] [ContMDiffVectorBundle ∞ F V I] [IsManifold I ∞ M]
  [AddCommGroup W] [Module ℝ W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  [ContinuousConstSMul ℝ W]

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- The support of the product `ρ T` of a functional with a smooth function lies in the support
of `T` and in that of `ρ`. -/
theorem dsupport_smulLeftDualCLM_subset (ρ : C^∞⟮I, M; ℝ⟯) (T : BundleTest I F V →L_c[ℝ] W) :
    dsupport (smulLeftDualCLM ρ T) ⊆ dsupport T ∩ tsupport ρ := by
  refine subset_inter (dsupport_subset_dsupport fun U _ hTU s hs ↦ ?_) fun x hx ↦ ?_
  · rw [smulLeftDualCLM_apply]
    exact hTU _ (((closure_smulLeftCLM_ne_zero_subset ρ s).trans inter_subset_right).trans hs)
  · by_contra h
    refine (notMem_dsupport_iff.2 ⟨(tsupport ρ)ᶜ, (isClosed_tsupport ρ).isOpen_compl, h,
      fun s hs ↦ ?_⟩) hx
    rw [smulLeftDualCLM_apply]
    convert map_zero T
    ext y
    by_cases hy : y ∈ tsupport ρ
    · simp [Bundle.apply_eq_zero_of_notMem_closure fun h' ↦ hs h' hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]

omit [FiniteDimensional ℝ E] [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W] in
/-- A point mass `δ_x ℓ` is supported in `{x}`. -/
theorem dsupport_delta_subset (x : M) (ℓ : V x →L[ℝ] W) :
    dsupport (delta (I := I) (F := F) x ℓ) ⊆ {x} := fun y hy ↦ by
  by_contra hyx
  refine (notMem_dsupport_iff.2 ⟨{x}ᶜ, isOpen_compl_singleton, hyx, fun s hs ↦ ?_⟩) hy
  rw [delta_apply, Bundle.apply_eq_zero_of_notMem_closure fun h ↦ hs h rfl, map_zero]

omit [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W] in
/-- **The support of a point mass.** For a nonzero map `ℓ` on the fibre over `x`, the point mass
`δ_x ℓ` is supported exactly at `x`. -/
theorem dsupport_delta {x : M} {ℓ : V x →L[ℝ] W} (hℓ : ℓ ≠ 0) :
    dsupport (delta (I := I) (F := F) x ℓ) = {x} := by
  refine Subset.antisymm (dsupport_delta_subset x ℓ) (singleton_subset_iff.2 ?_)
  by_contra hx
  obtain ⟨U, hU, hxU, hTU⟩ := notMem_dsupport_iff.1 hx
  obtain ⟨v, hv⟩ : ∃ v, ℓ v ≠ 0 := by
    by_contra! h
    exact hℓ (ContinuousLinearMap.ext h)
  obtain ⟨s, hsx, hsc, hsU⟩ := ContMDiffSection.exists_apply_eq_isCompact_tsupport_subset
    (I := I) (F := F) (n := ∞) x v (hU.mem_nhds hxU)
  have h := hTU (ofCompactlySupported I F V ⟨s, mem_compactlySupported.2 hsc⟩)
    ((ContMDiffSection.tsupport_def s).symm.subset.trans hsU)
  simp [delta_apply, hsx, hv] at h

end Dual

end TauCeti.BundleTest
