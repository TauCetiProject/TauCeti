/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact

/-!
# Gluing functionals on bundle tests

Let `V → M` be a smooth real vector bundle over a Hausdorff manifold modelled on a
finite-dimensional space, and let the open sets `U i` cover `M`. A continuous linear functional
`T` on the bundle tests of `V` restricts to each `U i` (`TauCeti.BundleTest.restrictDualCLM`):
`T|_{U i}` pairs a test of `V|_{U i}` with `T` after extending it by zero. This file proves the
locality and gluing properties of these functionals for an open cover of `M`.

* **Locality.** Two functionals with the same restrictions to every `U i` are equal
  (`TauCeti.BundleTest.eq_of_forall_restrictDualCLM_eq`).
* **Gluing.** Functionals `T i` on the tests of `V|_{U i}` that are compatible, in the sense that
  `T i s = T j s'` whenever the tests `s` on `U i` and `s'` on `U j` extend by zero to the same
  test of `M`, are the restrictions of a unique functional on the tests of `M`
  (`TauCeti.BundleTest.existsUnique_restrictDualCLM_eq`).

The functionals take values in any locally convex real space `W`. The cover is arbitrary: it need
not be locally finite or countable, and `M` need not be σ-compact. For distributional sections
(`TauCeti.BundleDistribution`), whose restriction
`TauCeti.BundleDistribution.restrictCLM` also identifies the dual densities of `U i` with those of
`M`, the same holds (`TauCeti.BundleDistribution.eq_of_forall_restrictCLM_eq`,
`TauCeti.BundleDistribution.existsUnique_restrictCLM_eq`). This is how distributions on a
manifold are built from local pieces, for instance from distributions defined chart by chart.

## The construction

A smooth function `χ` whose support lies in an open set `U` localizes the tests of `M` to `U`:
`s ↦ (χ s)|_U` is a continuous linear map (`TauCeti.BundleTest.cutoffRestrictCLM`), whose
extension by zero is `χ s`. For a test `s`, a finite smooth partition of unity `ρ` on the support
of `s` with each `ρ k` supported in some `U (i k)` (from
`IsCompact.exists_smoothBumpCovering_isSubordinate`) gives the glued value

`T s = ∑ k, T (i k) ((ρ k s)|_{U (i k)})`.

Compatibility shows that this does not depend on the partition: for a second partition `ρ'`,
both sums equal `∑ k, ∑ l, T (ρ k ρ' l s)`, each term computed on `U (i k)` or on `U (i' l)`.
Using one partition for all the tests supported in a fixed compact set gives continuity, since
the test topology is the final locally convex topology of these stages
(`TauCeti.BundleTest.continuous_iff_continuous_comp`). Uniqueness is the localization principle
(`TauCeti.BundleTest.dsupport_eq_empty_iff`): a functional whose restrictions to the `U i` vanish
has empty support, since every test supported in `U i` extends a test on `U i`
(`TauCeti.BundleTest.exists_extendByZeroCLM_eq_of_tsupport_subset`).

This adapts the proof of the Euclidean gluing theorem `Distribution.existsUnique_gluing`
(`TauCeti/Analysis/Distribution/Gluing.lean`) from test functions on open sets of a normed space
to bundle tests on a manifold.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, Theorem 2.2.4 (distributions on open sets of `ℝⁿ` form a sheaf) and §6.3
  (distributions on manifolds and in vector bundles).
-/

public noncomputable section

open Bundle Set TopologicalSpace Topology ContMDiffSection
open scoped Manifold ContDiff CompactConvergenceCLM
open TauCeti.DensityBundle (openHomBundle ambientHomBundle)

namespace TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]

/-! ### Locality and gluing -/

section Gluing

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  {ι : Type*} {U : ι → Opens M}

omit [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] in
/-- A product with a function supported in `U i` is supported in `U i`. -/
private theorem tsupport_mul_subset {i : ι} {g : C^∞⟮I, M; ℝ⟯} (hg : tsupport g ⊆ U i)
    (f : C^∞⟮I, M; ℝ⟯) : tsupport (f * g) ⊆ U i := by
  rw [ContMDiffMap.coe_mul]
  exact tsupport_mul_subset_right.trans hg

variable
  {T : ∀ i, BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V) →L_c[ℝ] W}

/-- Compatible functionals agree on the localizations of a test by the same cutoff. -/
private theorem apply_cutoffRestrictCLM_eq
    (hT : ∀ i j (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
      (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s' → T i s = T j s')
    {i i' : ι} {g g' : C^∞⟮I, M; ℝ⟯} (hg : tsupport g ⊆ U i) (hg' : tsupport g' ⊆ U i')
    (h : g = g') (s : BundleTest I F V) :
    T i (cutoffRestrictCLM hg s) = T i' (cutoffRestrictCLM hg' s) :=
  hT i i' _ _ (by
    -- The extension lemma is stated on the unbundled inclusion `Subtype.val *ᵖ V`.
    dsimp only [ContinuousMap.coe_mk]
    rw [extendByZeroCLM_cutoffRestrictCLM, extendByZeroCLM_cutoffRestrictCLM, h])

/-- Splitting a localized test along a family `σ` summing to one on the support of the test. -/
private theorem apply_cutoffRestrictCLM_eq_sum
    (hT : ∀ i j (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
      (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s' → T i s = T j s')
    {κ : Type*} [Fintype κ] (σ : κ → C^∞⟮I, M; ℝ⟯) (s : BundleTest I F V)
    (hσ : ∀ x ∈ closure {x | s x ≠ 0}, ∑ l, σ l x = 1) {i : ι} {g : C^∞⟮I, M; ℝ⟯}
    (hg : tsupport g ⊆ U i) :
    T i (cutoffRestrictCLM hg s) =
      ∑ l, T i (cutoffRestrictCLM (tsupport_mul_subset hg (σ l)) s) := by
  rw [← map_sum]
  refine hT i i _ _ ?_
  -- Unbundle the inclusion, as in `extendByZeroCLM_cutoffRestrictCLM`.
  dsimp only [ContinuousMap.coe_mk]
  simp only [map_sum, extendByZeroCLM_cutoffRestrictCLM, ← smulLeftCLM_smulLeftCLM]
  exact (sum_smulLeftCLM_eq_self σ _ fun x hx ↦ hσ x (tsupport_smulLeftCLM_subset g s hx).2).symm

/-- **Independence of the cutoffs.** For compatible functionals `T i`, the sum
`∑ k, T (j k) ((ρ k s)|_{U (j k)})` does not depend on the family `ρ` summing to one on the
support of `s`. -/
private theorem sum_cutoffRestrictCLM_eq
    (hT : ∀ i j (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
      (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s' → T i s = T j s')
    {κ κ' : Type*} [Fintype κ] [Fintype κ'] {ρ : κ → C^∞⟮I, M; ℝ⟯} {j : κ → ι}
    (hρ : ∀ k, tsupport (ρ k) ⊆ U (j k)) {ρ' : κ' → C^∞⟮I, M; ℝ⟯} {j' : κ' → ι}
    (hρ' : ∀ l, tsupport (ρ' l) ⊆ U (j' l)) (s : BundleTest I F V)
    (hs : ∀ x ∈ closure {x | s x ≠ 0}, ∑ k, ρ k x = 1)
    (hs' : ∀ x ∈ closure {x | s x ≠ 0}, ∑ l, ρ' l x = 1) :
    ∑ k, T (j k) (cutoffRestrictCLM (hρ k) s) = ∑ l, T (j' l) (cutoffRestrictCLM (hρ' l) s) := by
  -- Both sums equal the double sum of the values on the products `ρ k ρ' l`.
  calc ∑ k, T (j k) (cutoffRestrictCLM (hρ k) s)
      = ∑ k, ∑ l, T (j k) (cutoffRestrictCLM (tsupport_mul_subset (hρ k) (ρ' l)) s) :=
        Finset.sum_congr rfl fun k _ ↦ apply_cutoffRestrictCLM_eq_sum hT ρ' s hs' (hρ k)
    _ = ∑ l, ∑ k, T (j' l) (cutoffRestrictCLM (tsupport_mul_subset (hρ' l) (ρ k)) s) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ ↦ Finset.sum_congr rfl fun k _ ↦
          apply_cutoffRestrictCLM_eq hT _ _ (mul_comm _ _) s
    _ = ∑ l, T (j' l) (cutoffRestrictCLM (hρ' l) s) :=
        Finset.sum_congr rfl fun l _ ↦ (apply_cutoffRestrictCLM_eq_sum hT ρ s hs (hρ' l)).symm

/-- On the extension of a test `ψ` on `U i`, the glued value is `T i ψ`. -/
private theorem sum_cutoffRestrictCLM_extendByZeroCLM_eq
    (hT : ∀ i j (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
      (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s' → T i s = T j s')
    {κ : Type*} [Fintype κ] {ρ : κ → C^∞⟮I, M; ℝ⟯} {j : κ → ι}
    (hρU : ∀ k, tsupport (ρ k) ⊆ U (j k)) {i : ι}
    (ψ : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
    (hρ : ∀ x ∈ closure {x | extendByZeroCLM (I := I) (F := F) (V := V) ψ x ≠ 0},
      ∑ k, ρ k x = 1) :
    ∑ k, T (j k) (cutoffRestrictCLM (hρU k) (extendByZeroCLM (I := I) (F := F) (V := V) ψ)) =
      T i ψ := by
  -- Each localization of the extension is the extension of a multiple of `ψ` on `U i`.
  have hloc (k : κ) :
      T (j k) (cutoffRestrictCLM (hρU k) (extendByZeroCLM (I := I) (F := F) (V := V) ψ)) =
        T i (smulLeftCLM ((ρ k).restrict (U i)) ψ) := by
    refine hT _ _ _ _ ?_
    -- Unbundle the inclusion, as in `extendByZeroCLM_cutoffRestrictCLM`.
    dsimp only [ContinuousMap.coe_mk]
    rw [extendByZeroCLM_cutoffRestrictCLM, extendByZeroCLM_smulLeftCLM]
  simp only [hloc, ← map_sum]
  refine hT i i _ _ ?_
  simp only [map_sum, extendByZeroCLM_smulLeftCLM]
  exact sum_smulLeftCLM_eq_self _ _ hρ

variable [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W]

/-- **Locality.** Two functionals on the bundle tests of `M` with the same restrictions to every
member of an open cover of `M` are equal. -/
theorem eq_of_forall_restrictDualCLM_eq (hU : ⨆ i, U i = ⊤)
    {S S' : BundleTest I F V →L_c[ℝ] W}
    (h : ∀ i, restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S =
      restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S') :
    S = S' := by
  -- By the localization principle it suffices that `S - S'` vanishes on each `U i`.
  rw [← sub_eq_zero]
  refine ContinuousLinearMap.ext fun s ↦ congrFun ((dsupport_eq_empty_iff (S - S')).1
    (eq_empty_of_forall_notMem fun x ↦ ?_)) s
  obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU ▸ Opens.mem_top x : x ∈ ⨆ i, U i)
  refine notMem_dsupport_iff.2 ⟨U i, (U i).isOpen, hi, isVanishingOn_iff.2 fun t ht ↦ ?_⟩
  obtain ⟨t, rfl⟩ := exists_extendByZeroCLM_eq_of_tsupport_subset ht
  have h' := DFunLike.congr_fun (h i) t
  rw [restrictDualCLM_apply, restrictDualCLM_apply] at h'
  rw [_root_.sub_apply, h', sub_self]

/-- **Gluing.** Let the open sets `U i` cover `M`. Continuous linear functionals `T i` on the
bundle tests of `V|_{U i}` that agree on tests of `U i` and of `U j` extending by zero to the same
test of `M` are the restrictions of a unique continuous linear functional on the bundle tests of
`M`. -/
theorem existsUnique_restrictDualCLM_eq [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]
    (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
      (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V)),
      extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s' → T i s = T j s') :
    ∃! S : BundleTest I F V →L_c[ℝ] W,
      ∀ i, restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S = T i := by
  -- Finite smooth partitions of unity on each compact set, subordinate to the cover.
  choose idx hidx using fun x ↦ Opens.mem_iSup.1 (hU ▸ Opens.mem_top x : x ∈ ⨆ i, U i)
  choose κ hκ f hf using fun K : Compacts M ↦ K.isCompact.exists_smoothBumpCovering_isSubordinate I
    (U := fun x ↦ U (idx x)) fun x _ ↦ (U (idx x)).isOpen.mem_nhds (hidx x)
  let ρ (K : Compacts M) := (f K).toSmoothPartitionOfUnity
  let j (K : Compacts M) (k : κ K) := idx ((f K).c k)
  have hρU (K : Compacts M) (k : κ K) : tsupport (ρ K k) ⊆ U (j K k) :=
    (hf K).toSmoothPartitionOfUnity k
  have hρ (K : Compacts M) : ∀ x ∈ (K : Set M), ∑ k, ρ K k x = 1 := fun x hx ↦ by
    rw [← finsum_eq_sum_of_fintype]
    exact (ρ K).sum_eq_one hx
  -- The glued value on `s`, computed with the cutoffs chosen for the support of `s`.
  let supp (s : BundleTest I F V) : Compacts M := ⟨_, isCompact_tsupport s⟩
  let S₀ (s : BundleTest I F V) : W :=
    ∑ k, T (j (supp s) k) (cutoffRestrictCLM (hρU (supp s) k) s)
  -- Any compact set containing the support of `s` computes the same value.
  have hS₀ (s : BundleTest I F V) (K : Compacts M) (hK : closure {x | s x ≠ 0} ⊆ K) :
      S₀ s = ∑ k, T (j K k) (cutoffRestrictCLM (hρU K k) s) :=
    sum_cutoffRestrictCLM_eq hT _ _ s (hρ (supp s)) fun x hx ↦ hρ K x (hK hx)
  let L : BundleTest I F V →ₗ[ℝ] W :=
    { toFun := S₀
      map_add' s t := by
        let K := supp s ⊔ supp t
        rw [hS₀ (s + t) K (tsupport_add_subset s t), hS₀ s K le_sup_left, hS₀ t K le_sup_right,
          ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' a s := by
        rw [hS₀ (a • s) (supp s) (closure_mono fun x hx ↦ right_ne_zero_of_smul hx),
          RingHom.id_apply, Finset.smul_sum]
        simp only [map_smul] }
  have hL : Continuous L := by
    let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp L).2 fun K ↦ ?_
    refine (continuous_finsetSum _ fun k _ ↦ (T (j K k)).continuous.comp
      ((cutoffRestrictCLM (hρU K k)).continuous.comp (continuous_ofSupportedIn K))).congr
        fun s ↦ (hS₀ _ K ?_).symm
    simpa only [Function.comp_apply, coe_ofCompactlySupported, ofSupportedIn_apply,
      ← ContMDiffSection.tsupport_def] using mem_supportedIn.mp s.property
  let S : BundleTest I F V →L_c[ℝ] W := ⟨L, hL⟩
  have hglue (i : ι) : restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S = T i := by
    ext ψ
    rw [restrictDualCLM_apply]
    -- `S` is the glued value `S₀` with its linearity and continuity attached.
    exact sum_cutoffRestrictCLM_extendByZeroCLM_eq hT (hρU _) ψ (hρ (supp _))
  exact ⟨S, hglue, fun S' hS' ↦
    eq_of_forall_restrictDualCLM_eq hU fun i ↦ (hS' i).trans (hglue i).symm⟩

end Gluing

end TauCeti.BundleTest

/-! ### Distributional sections -/

namespace TauCeti.BundleDistribution

open TauCeti.BundleTest

variable {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {ι : Type*} {U : ι → Opens M}

/-- **Locality of distributional sections.** Two distributional sections of `V` with the same
restrictions to every member of an open cover of `M` are equal. -/
theorem eq_of_forall_restrictCLM_eq (hU : ⨆ i, U i = ⊤) {T T' : BundleDistribution I M F V}
    (h : ∀ i, restrictCLM (I := I) (F := F) (V := V) (U := U i) T =
      restrictCLM (I := I) (F := F) (V := V) (U := U i) T') :
    T = T' := by
  refine eq_of_forall_restrictDualCLM_eq (V := ambientHomBundle (I := I) (V := V)) hU
    fun i ↦ ContinuousLinearMap.ext fun s ↦ ?_
  -- Restriction is dual restriction after the identification of the dual densities of `U i`.
  obtain ⟨s, rfl⟩ := (openDensityHomCLE (I := I) (F := F) (V := V) (U := U i)).surjective s
  have hs := DFunLike.congr_fun (h i) s
  rwa [restrictCLM_apply_eq_restrictDualCLM, restrictCLM_apply_eq_restrictDualCLM] at hs

/-- **Gluing of distributional sections.** Let the open sets `U i` cover `M`. Distributional
sections `T i` of `V|_{U i}` that agree on dual-density tests of `U i` and of `U j` extending by
zero to the same test of `M` are the restrictions of a unique distributional section of `V`. -/
theorem existsUnique_restrictCLM_eq (hU : ⨆ i, U i = ⊤)
    {T : ∀ i,
      BundleDistribution I (U i) F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V)}
    (hT : ∀ i j (s : BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U i)))
      (s' : BundleTest I (F →L[ℝ] ℝ) (openHomBundle (I := I) (V := V) (U := U j))),
      testExtensionCLM (I := I) (F := F) (V := V) s = testExtensionCLM s' → T i s = T j s') :
    ∃! T₀ : BundleDistribution I M F V,
      ∀ i, restrictCLM (I := I) (F := F) (V := V) (U := U i) T₀ = T i := by
  -- The functionals `T i` read on tests valued in the pulled-back ambient dual densities.
  let T' (i : ι) := (openDensityHomCLE (I := I) (F := F) (V := V)
    (U := U i)).symm.toContinuousLinearMap.precompCompactConvergenceCLM ℝ (T i)
  have hT' (i : ι) (s) : T' i s = T i ((openDensityHomCLE (I := I) (F := F) (V := V)
      (U := U i)).symm s) :=
    ContinuousLinearMap.precompCompactConvergenceCLM_apply_apply _ _ _
  obtain ⟨T₀, hT₀, -⟩ := existsUnique_restrictDualCLM_eq (V := ambientHomBundle (I := I) (V := V))
    (T := T') hU fun i j s s' hss' ↦ by
      rw [hT', hT']
      exact hT i j _ _ (by simpa only [testExtensionCLM_apply,
        ContinuousLinearEquiv.apply_symm_apply] using hss')
  have hglue (i : ι) : restrictCLM (I := I) (F := F) (V := V) (U := U i) T₀ = T i := by
    ext s
    rw [restrictCLM_apply_eq_restrictDualCLM, hT₀ i, hT', ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨T₀, hglue, fun T₁ hT₁ ↦
    eq_of_forall_restrictCLM_eq hU fun i ↦ (hT₁ i).trans (hglue i).symm⟩

end TauCeti.BundleDistribution
