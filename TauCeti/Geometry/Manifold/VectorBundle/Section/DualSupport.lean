/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.WithSeminorms

/-!
# Continuous linear maps on smooth sections have compact support

All compact frame-coordinate derivative seminorms generate
`ContMDiffSection.frameTopology` (`ContMDiffSection.withSeminorms_frameSeminormFamily`).
Consequently Mathlib's `WithSeminorms` continuity criteria bound every continuous linear map
from sections to a normed space by finitely many of these seminorms. Since each seminorm only
sees a section near a compact subset of the base, such a map vanishes on every section which is
zero near one fixed compact subset of the base. This is the support part of the
identification of the continuous dual of smooth sections with compactly supported
distributions.

## References

* L. Schwartz, *Théorie des distributions*, Chapter III, §7, Theorem XXV.
-/

public section

noncomputable section

open Bundle Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold TauCeti.ManifoldWeakWhitney

namespace ContMDiffSection

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module 𝕜 (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle 𝕜 F V]
  {n : ℕ∞ω} [ContMDiffVectorBundle n F V I] [IsManifold I n M]
  {ι : Type*} (e : ι → Trivialization F (π F V))
  [∀ i, MemTrivializationAtlas (e i)]
  (U : ι → Opens M) (hU : ∀ i, (U i : Set M) ⊆ (e i).baseSet)

/-- The points of the base represented by the compact coordinate set of a frame seminorm. -/
private def frameSeminormSupport
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) : Set M :=
  Subtype.val '' ((extChartAt I j.2.1).symm ''
    (Subtype.val '' (j.2.2.2 : Set (extChartAt I j.2.1).target)))

omit [IsManifold I n M] in
private theorem isCompact_frameSeminormSupport
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target) :
    IsCompact (frameSeminormSupport (I := I) (n := n) U j) := by
  unfold frameSeminormSupport
  exact ((j.2.2.2.isCompact.image continuous_subtype_val).image_of_continuousOn
    ((continuousOn_extChartAt_symm j.2.1).mono (by rintro _ ⟨z, -, rfl⟩; exact z.2))).image
    continuous_subtype_val

/-- A frame seminorm vanishes on a section which is zero near the points it represents. -/
private theorem frameSeminormFamily_eq_zero
    (j : Σ i, Σ x : U i, {m : ℕ // m ≤ n} × Compacts (extChartAt I x).target)
    {s : Cₛ^n⟮I; F, V⟯}
    (hs : ∀ᶠ y in 𝓝ˢ (frameSeminormSupport (I := I) (n := n) U j), s y = 0) :
    frameSeminormFamily (I := I) (n := n) e U hU j s = 0 := by
  obtain ⟨i, x, ⟨m, hm⟩, K⟩ := j
  rw [frameSeminormFamily_apply]
  exact (e i).chartDerivativeSeminorm_eq_zero_of_eventuallyEq_zero (hU i) x K m hm hs

/-- **Continuous linear maps on smooth sections have compact support.** A linear map from
sections to a normed space which is continuous for the compact derivative frame topology
vanishes on every section which is zero near one fixed compact subset of the base. Neither a
covering nor countability of the frame system is needed. -/
theorem exists_isCompact_forall_eventually_eq_zero {G : Type*} [NormedAddCommGroup G]
    [NormedSpace 𝕜 G] (f : Cₛ^n⟮I; F, V⟯ →ₗ[𝕜] G)
    (hf : let _ := frameTopology (I := I) (n := n) e U hU; Continuous f) :
    ∃ K : Set M, IsCompact K ∧ ∀ s : Cₛ^n⟮I; F, V⟯, (∀ᶠ y in 𝓝ˢ K, s y = 0) → f s = 0 := by
  let _ := frameTopology (I := I) (n := n) e U hU
  obtain ⟨t, C, -, hC⟩ := Seminorm.bound_of_continuous
    (withSeminorms_frameSeminormFamily (I := I) (n := n) e U hU)
    ((normSeminorm 𝕜 G).comp f) (continuous_norm.comp hf)
  refine ⟨⋃ j ∈ t, frameSeminormSupport (I := I) (n := n) U j,
    t.isCompact_biUnion fun j _ ↦ isCompact_frameSeminormSupport (I := I) (n := n) U j,
    fun s hs ↦ ?_⟩
  have hsup : (t.sup (frameSeminormFamily (I := I) (n := n) e U hU)) s = 0 :=
    le_antisymm (Seminorm.finset_sup_apply_le le_rfl fun j hj ↦
      (frameSeminormFamily_eq_zero e U hU j (hs.filter_mono (nhdsSet_mono
        (subset_biUnion_of_mem hj)))).le) (apply_nonneg _ _)
  have h := hC s
  rw [Seminorm.comp_apply, coe_normSeminorm, smul_apply, hsup, smul_zero] at h
  exact norm_le_zero_iff.mp h

end ContMDiffSection
