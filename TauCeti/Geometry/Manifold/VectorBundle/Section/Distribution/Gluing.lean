/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Restriction
public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology
public import TauCeti.Geometry.Manifold.PartitionOfUnity.Compact
import TauCeti.Geometry.Manifold.ContMDiffMap.Support

/-!
# Gluing functionals on bundle tests

Let `V → M` be a smooth real vector bundle over a Hausdorff manifold modelled on a
finite-dimensional space, and let the open sets `U i` cover `M`. Suppose that for every `i` a
continuous linear map `T i : TauCeti.BundleTest I F V →L_c[ℝ] W` is given on *all* bundle tests on
`M`, with values in a locally convex space `W`, and that these maps are compatible: `T i` and `T j`
agree on the tests supported in `U i ∩ U j`. Then there is a unique continuous linear map `S` on
the bundle tests that agrees with `T i` on the tests supported in `U i`, for every `i`
(`TauCeti.BundleTest.existsUnique_gluing`). Only the behaviour of `T i` on the tests supported in
`U i` matters, so maps on all of `M` that agree on tests supported in overlaps are determined by,
and recovered from, their local behaviour. In the language of restrictions, `S` and `T i` have the
same restriction to `U i` (`TauCeti.BundleTest.restrictDualCLM_glue`), and a functional is
determined by its restrictions to the members of an open cover
(`TauCeti.BundleTest.ext_restrictDualCLM`). The cover is arbitrary: it need not be locally finite
or countable, and `M` need not be σ-compact.

The proof follows the Euclidean `Distribution.existsUnique_gluing`. There the maps `T i` are given
on the tests on `U i`; here they are global maps, compared on the tests supported in `U i`.
The glued map is

`S s = ∑ k, T (j k) (χ k • s)`

for finitely many smooth functions `χ k`, each supported in a member `U (j k)` of the cover, whose
sum is one on the support of `s` (`IsCompact.exists_finite_smooth_sum_eq_one_subordinate`).
Compatibility shows that this value does not depend on the functions `χ k`: for a second family
`χ'`, both sums equal `∑ k, ∑ l, T (χ' l • χ k • s)`, computed on `U (j k)` or on `U (j' l)`.
Using one family for all tests supported in a fixed compact set gives continuity for the test
topology, through its universal property (`TauCeti.BundleTest.continuous_iff_continuous_comp`).
Uniqueness is the localization principle (`TauCeti.BundleTest.isVanishingOn_compl_dsupport`): a
functional vanishing on the tests supported in each `U i` has empty support
(`TauCeti.BundleTest.eq_of_forall_tsupport_subset`).

The same gluing holds for functionals `T i` given only on the tests of `V|_{U i}`. They are
compatible when `T i s = T j s'` whenever the tests `s` on `U i` and `s'` on `U j` extend by zero
to the same test of `M`, or equivalently when the restrictions of `T i` and `T j` to every overlap
`U i ⊓ U j` agree. Then they are the restrictions `TauCeti.BundleTest.restrictDualCLM` of a unique
functional on the tests of `M` (`TauCeti.BundleTest.existsUnique_restrictDualCLM_eq`,
`TauCeti.BundleTest.existsUnique_restrictDualCLM_eq_of_restrictDualToOpenCLM_eq`). Here the
pieces are localized by cutoffs: `s ↦ (χ s)|_U` is a continuous linear map
(`TauCeti.BundleTest.cutoffRestrictCLM`) for a smooth `χ` supported in `U`, and the glued value is
`∑ k, T (i k) ((ρ k s)|_{U (i k)})` for a finite smooth partition of unity `ρ` on the support of
`s`. For distributional sections (`TauCeti.BundleDistribution`), whose restriction
`TauCeti.BundleDistribution.restrictCLM` also identifies the dual densities of `U i` with those of
`M`, the same holds (`TauCeti.BundleDistribution.eq_of_forall_restrictCLM_eq`,
`TauCeti.BundleDistribution.existsUnique_restrictCLM_eq`). This is how distributions on a
manifold are built from local pieces, for instance from distributions defined chart by chart.

## Main declarations

* `TauCeti.BundleTest.eq_of_forall_tsupport_subset`: additive maps on bundle tests which agree on
  the tests supported in each member of an open cover are equal.
* `TauCeti.BundleTest.existsUnique_gluing`: compatible continuous linear maps glue to a unique
  continuous linear map.
* `TauCeti.BundleTest.glue`: the glued map, characterized by
  `TauCeti.BundleTest.glue_apply_of_tsupport_subset` and `TauCeti.BundleTest.eq_glue_iff`.
* `TauCeti.BundleTest.dsupport_glue_inter`: over `U i`, the support of the glued map is that of
  `T i`.
* `TauCeti.BundleTest.ext_restrictDualCLM`, `TauCeti.BundleTest.restrictDualCLM_glue`: the same
  statements for the restrictions `TauCeti.BundleTest.restrictDualCLM` to the open sets `U i`.
* `TauCeti.BundleTest.existsUnique_restrictDualCLM_eq`,
  `TauCeti.BundleTest.existsUnique_restrictDualCLM_eq_of_restrictDualToOpenCLM_eq`: compatible
  functionals on the tests of the open sets `U i` are the restrictions of a unique functional.
* `TauCeti.BundleDistribution.eq_of_forall_restrictCLM_eq`,
  `TauCeti.BundleDistribution.existsUnique_restrictCLM_eq`: locality and gluing of distributional
  sections.

## References

* L. Hörmander, *The Analysis of Linear Partial Differential Operators I*, second edition,
  Springer, 1990, §2.2, Theorem 2.2.4 (gluing distributions), and §6.3 (distributions on
  manifolds).
-/

public noncomputable section

open Bundle Set Filter Function TopologicalSpace ContMDiffSection
open scoped ContDiff Manifold Topology CompactConvergenceCLM

namespace TauCeti.BundleTest

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)]
  [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace F V)]
  [FiberBundle F V] [VectorBundle ℝ F V] [ContMDiffVectorBundle ∞ F V I]
  {ι : Type*} {U : ι → Opens M}

/-! ### Locality -/

/-- **Locality.** Two additive maps on bundle tests are equal if they agree on the tests supported
in each member of an open cover. -/
theorem eq_of_forall_tsupport_subset {W : Type*} [AddCommGroup W] {𝓕 : Type*}
    [FunLike 𝓕 (BundleTest I F V) W] [AddMonoidHomClass 𝓕 (BundleTest I F V) W]
    (hU : ⨆ i, U i = ⊤) {S S' : 𝓕}
    (h : ∀ i (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i → S s = S' s) : S = S' := by
  -- The difference of the two maps vanishes on every member of the cover, so it has empty
  -- support and is zero by the localization principle.
  let D : BundleTest I F V →+ W := (S : BundleTest I F V →+ W) - (S' : BundleTest I F V →+ W)
  have hD : dsupport D = ∅ := eq_empty_of_forall_notMem fun x hx ↦ by
    obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (hU ▸ Opens.mem_top x : x ∈ ⨆ i, U i)
    refine notMem_dsupport_iff.2 ⟨U i, (U i).isOpen, hi, isVanishingOn_iff.2 fun s hs ↦ ?_⟩ hx
    simp [D, h i s hs]
  refine DFunLike.ext _ _ fun s ↦ ?_
  simpa [D, sub_eq_zero] using congrFun ((dsupport_eq_empty_iff D).1 hD) s

/-! ### Gluing -/

section Gluing

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  {T : ι → BundleTest I F V →L_c[ℝ] W}

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- For compatible maps `T i`, the value `∑ k, T (j k) (χ k • s)` does not depend on the functions
`χ k`, supported in `U (j k)`, as long as their sum is one on the support of `s`. -/
private theorem sum_eq_sum_of_compatible
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s)
    {n n' : ℕ} {χ : Fin n → C^∞⟮I, M; ℝ⟯} {χ' : Fin n' → C^∞⟮I, M; ℝ⟯} {j : Fin n → ι}
    {j' : Fin n' → ι} (hχ : ∀ k, tsupport (χ k) ⊆ U (j k))
    (hχ' : ∀ l, tsupport (χ' l) ⊆ U (j' l)) (s : BundleTest I F V)
    (hs : ∀ x ∈ closure {x | s x ≠ 0}, ∑ k, χ k x = 1)
    (hs' : ∀ x ∈ closure {x | s x ≠ 0}, ∑ l, χ' l x = 1) :
    ∑ k, T (j k) (smulLeftCLM (χ k) s) = ∑ l, T (j' l) (smulLeftCLM (χ' l) s) := by
  -- The product of the `k`-th and `l`-th functions with `s` is supported in `U (j k) ∩ U (j' l)`.
  have hsupp (k : Fin n) (l : Fin n') :
      closure {x | smulLeftCLM (χ' l) (smulLeftCLM (χ k) s) x ≠ 0} ⊆ U (j k) ∩ U (j' l) := by
    refine fun x hx ↦ ⟨?_, ?_⟩
    · exact hχ k ((tsupport_smulLeftCLM_subset _ _ <|
        (tsupport_smulLeftCLM_subset _ _ hx).2).1)
    · exact hχ' l (tsupport_smulLeftCLM_subset _ _ hx).1
  -- The functions `χ` still sum to one on the support of `χ' l • s`, and `χ'` on that of `χ k • s`.
  have hsl (l : Fin n') : ∀ x ∈ closure {x | smulLeftCLM (χ' l) s x ≠ 0}, ∑ k, χ k x = 1 :=
    fun x hx ↦ hs x (tsupport_smulLeftCLM_subset _ _ hx).2
  have hsk (k : Fin n) : ∀ x ∈ closure {x | smulLeftCLM (χ k) s x ≠ 0}, ∑ l, χ' l x = 1 :=
    fun x hx ↦ hs' x (tsupport_smulLeftCLM_subset _ _ hx).2
  calc ∑ k, T (j k) (smulLeftCLM (χ k) s)
      = ∑ k, ∑ l, T (j k) (smulLeftCLM (χ' l) (smulLeftCLM (χ k) s)) := by
        refine Finset.sum_congr rfl fun k _ ↦ ?_
        rw [← map_sum, sum_smulLeftCLM_eq_self _ (hsk k)]
    _ = ∑ k, ∑ l, T (j' l) (smulLeftCLM (χ' l) (smulLeftCLM (χ k) s)) :=
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ hT _ _ _ (hsupp k l)
    _ = ∑ l, T (j' l) (smulLeftCLM (χ' l) s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp_rw [smulLeftCLM_smulLeftCLM, mul_comm (χ' l), ← smulLeftCLM_smulLeftCLM]
        rw [← map_sum, sum_smulLeftCLM_eq_self _ (hsl l)]

variable [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

/-- **Gluing.** Let the open sets `U i` cover `M`. Continuous linear maps `T i` on bundle tests
which agree on the tests supported in every overlap `U i ∩ U j` are, on the tests supported in each
`U i`, the restrictions of a unique continuous linear map on bundle tests. -/
theorem existsUnique_gluing (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s) :
    ∃! S : BundleTest I F V →L_c[ℝ] W,
      ∀ i (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i → S s = T i s := by
  -- Finitely many functions subordinate to the cover summing to one on each compact `K`.
  have hKU (K : Set M) : K ⊆ ⋃ i, (U i : Set M) := fun x _ ↦
    mem_iUnion.2 (Opens.mem_iSup.1 (hU ▸ Opens.mem_top x : x ∈ ⨆ i, U i))
  choose n χ j hχ hsum using fun (K : Set M) (hK : IsCompact K) ↦
    hK.exists_finite_smooth_sum_eq_one_subordinate I (fun i ↦ (U i).isOpen) (hKU K)
  -- The glued value on `s`, computed with the functions chosen for the support of `s`.
  let S₀ : BundleTest I F V → W := fun s ↦
    ∑ k, T (j _ s.isCompact_tsupport k) (smulLeftCLM (χ _ s.isCompact_tsupport k) s)
  -- With functions summing to one on a compact set containing the support of `s`, the sum
  -- computes `S₀ s`.
  have hS₀ (s : BundleTest I F V) (K : Set M) (hK : IsCompact K)
      (hsK : closure {x | s x ≠ 0} ⊆ K) :
      S₀ s = ∑ k, T (j K hK k) (smulLeftCLM (χ K hK k) s) :=
    sum_eq_sum_of_compatible hT (hχ _ _) (hχ K hK) s (hsum _ _) fun x hx ↦ hsum K hK x (hsK hx)
  let L : BundleTest I F V →ₗ[ℝ] W :=
    { toFun := S₀
      map_add' := fun s t ↦ by
        have hK := s.isCompact_tsupport.union t.isCompact_tsupport
        rw [hS₀ (s + t) _ hK (tsupport_add_subset s t), hS₀ s _ hK subset_union_left,
          hS₀ t _ hK subset_union_right, ← Finset.sum_add_distrib]
        simp only [map_add]
      map_smul' := fun a s ↦ by
        rw [hS₀ (a • s) _ s.isCompact_tsupport (tsupport_smul_subset a s), RingHom.id_apply,
          Finset.smul_sum]
        simp only [map_smul] }
  have hL : Continuous L := by
    let := frameTopology (I := I) (n := ∞) (fun x : M ↦ trivializationAt F V x)
      (fun x ↦ ⟨_, (trivializationAt F V x).open_baseSet⟩) fun _ ↦ subset_rfl
    refine (continuous_iff_continuous_comp L).2 fun K ↦ ?_
    -- On the tests supported in `K`, `S₀` is one fixed finite sum of continuous maps.
    have hc : Continuous fun s : BundleTest I F V ↦
        ∑ k, T (j K K.isCompact k) (smulLeftCLM (χ K K.isCompact k) s) :=
      continuous_finsetSum _ fun k _ ↦ (T _).continuous.comp (smulLeftCLM _).continuous
    exact (hc.comp (continuous_ofSupportedIn K)).congr fun σ ↦
      (hS₀ _ K K.isCompact (tsupport_ofSupportedIn_subset K σ)).symm
  let S : BundleTest I F V →L_c[ℝ] W := { L with cont := hL }
  have hS (s : BundleTest I F V) : S s = S₀ s := rfl
  have hglue (i : ι) (s : BundleTest I F V) (hs : closure {x | s x ≠ 0} ⊆ U i) : S s = T i s := by
    -- Each term `χ k • s` is supported in `U (j k) ∩ U i`, where `T (j k)` and `T i` agree.
    rw [hS, hS₀ s _ s.isCompact_tsupport subset_rfl]
    calc ∑ k, T (j _ s.isCompact_tsupport k) (smulLeftCLM (χ _ s.isCompact_tsupport k) s)
        = ∑ k, T i (smulLeftCLM (χ _ s.isCompact_tsupport k) s) :=
          Finset.sum_congr rfl fun k _ ↦ hT _ _ _ fun x hx ↦
            ⟨hχ _ _ k (tsupport_smulLeftCLM_subset _ _ hx).1,
              hs (tsupport_smulLeftCLM_subset _ _ hx).2⟩
      _ = T i s := by rw [← map_sum, sum_smulLeftCLM_eq_self _ (hsum _ _)]
  exact ⟨S, hglue, fun S' hS' ↦
    eq_of_forall_tsupport_subset hU fun i s hs ↦ (hS' i s hs).trans (hglue i s hs).symm⟩

/-- The continuous linear map on bundle tests glued from continuous linear maps `T i` on all bundle
tests that agree on the tests supported in each overlap `U i ∩ U j` of an open cover `U`
(`TauCeti.BundleTest.existsUnique_gluing`): it agrees with `T i` on the tests supported in `U i`. -/
def glue (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s) :
    BundleTest I F V →L_c[ℝ] W :=
  (existsUnique_gluing hU hT).exists.choose

/-- The glued map agrees with `T i` on the tests supported in `U i`. -/
theorem glue_apply_of_tsupport_subset (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s)
    (i : ι) {s : BundleTest I F V} (hs : closure {x | s x ≠ 0} ⊆ U i) :
    glue hU hT s = T i s :=
  (existsUnique_gluing hU hT).exists.choose_spec i s hs

/-- A continuous linear map is the glued map exactly when it agrees with every `T i` on the tests
supported in `U i`. -/
theorem eq_glue_iff (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s)
    {S : BundleTest I F V →L_c[ℝ] W} :
    S = glue hU hT ↔ ∀ i (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i → S s = T i s :=
  ⟨fun h i _ hs ↦ h ▸ glue_apply_of_tsupport_subset hU hT i hs,
    fun h ↦ (existsUnique_gluing hU hT).unique h fun i _ hs ↦
      glue_apply_of_tsupport_subset hU hT i hs⟩

/-- Over `U i`, the support of the glued map is the support of `T i`. -/
theorem dsupport_glue_inter (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s)
    (i : ι) : dsupport (glue hU hT) ∩ U i = dsupport (T i) ∩ U i :=
  dsupport_inter_eq_of_forall_tsupport_subset (U i).isOpen fun _ hs ↦
    glue_apply_of_tsupport_subset hU hT i hs

/-! ### Restrictions to open sets -/

variable [ContinuousConstSMul ℝ W]

omit [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W] in
/-- Two continuous linear maps on bundle tests are equal if their restrictions to every member of
an open cover are equal. -/
theorem ext_restrictDualCLM (hU : ⨆ i, U i = ⊤) {S S' : BundleTest I F V →L_c[ℝ] W}
    (h : ∀ i, restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S =
      restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S') : S = S' :=
  eq_of_forall_tsupport_subset hU fun i s hs ↦ by
    obtain ⟨t, rfl⟩ := exists_extendByZeroCLM_eq hs
    have h' := DFunLike.congr_fun (h i) t
    -- `restrictDualCLM_apply` is stated on the unbundled pullback, which `rw` does not see.
    erw [restrictDualCLM_apply, restrictDualCLM_apply] at h'
    exact h'

/-- The glued map and `T i` have the same restriction to `U i`. -/
theorem restrictDualCLM_glue (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s)
    (i : ι) :
    restrictDualCLM (I := I) (F := F) (V := V) (U := U i) (glue hU hT) =
      restrictDualCLM (I := I) (F := F) (V := V) (U := U i) (T i) := by
  ext t
  -- `restrictDualCLM_apply` is stated on the unbundled pullback, which `rw` does not see.
  erw [restrictDualCLM_apply, restrictDualCLM_apply]
  refine glue_apply_of_tsupport_subset hU hT i ?_
  rw [tsupport_extendByZeroCLM]
  rintro _ ⟨x, -, rfl⟩
  exact x.property

end Gluing

/-! ### Gluing functionals on the tests of the open sets -/

section LocalGluing

variable {W : Type*} [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
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
      ∑ l, T i (cutoffRestrictCLM
        ((ContMDiffMap.tsupport_mul_subset_right (f := σ l)).trans hg) s) := by
  rw [← map_sum]
  refine hT i i _ _ ?_
  -- Unbundle the inclusion, as in `extendByZeroCLM_cutoffRestrictCLM`.
  dsimp only [ContinuousMap.coe_mk]
  simp only [map_sum, extendByZeroCLM_cutoffRestrictCLM, ← smulLeftCLM_smulLeftCLM]
  exact (sum_smulLeftCLM_eq_self _ (χ := σ) fun x hx ↦
    hσ x (tsupport_smulLeftCLM_subset g s hx).2).symm

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
      = ∑ k, ∑ l, T (j k) (cutoffRestrictCLM
          ((ContMDiffMap.tsupport_mul_subset_right (f := ρ' l)).trans (hρ k)) s) :=
        Finset.sum_congr rfl fun k _ ↦ apply_cutoffRestrictCLM_eq_sum hT ρ' s hs' (hρ k)
    _ = ∑ l, ∑ k, T (j' l) (cutoffRestrictCLM
          ((ContMDiffMap.tsupport_mul_subset_right (f := ρ k)).trans (hρ' l)) s) := by
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
  exact sum_smulLeftCLM_eq_self _ hρ

variable [IsTopologicalAddGroup W] [ContinuousConstSMul ℝ W]

/-- Functionals agreeing on every overlap `U i ⊓ U j` agree on tests of `U i` and of `U j` that
extend by zero to the same test of `M`. -/
private theorem apply_eq_of_restrictDualToOpenCLM_eq
    (hT : ∀ i j, restrictDualToOpenCLM (I := I) (F := F) (V := V)
      (inf_le_left : U i ⊓ U j ≤ U i) (T i) =
        restrictDualToOpenCLM (I := I) (F := F) (V := V) (inf_le_right : U i ⊓ U j ≤ U j) (T j))
    (i j : ι) (s : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U i, M)) *ᵖ V))
    (s' : BundleTest I F ((⟨Subtype.val, continuous_subtypeVal⟩ : C(U j, M)) *ᵖ V))
    (h : extendByZeroCLM (I := I) (F := F) (V := V) s = extendByZeroCLM s') :
    T i s = T j s' := by
  -- The common extension is supported in `U i ⊓ U j`, so it extends a test `r` on the overlap.
  obtain ⟨r, hr⟩ := (mem_range_extendByZeroCLM_iff (U := U i ⊓ U j)
    (extendByZeroCLM (I := I) (F := F) (V := V) s)).2
    (subset_inter ((mem_range_extendByZeroCLM_iff (U := U i) _).1 ⟨s, rfl⟩)
      ((mem_range_extendByZeroCLM_iff (U := U j) _).1 ⟨s', h.symm⟩))
  rw [ContinuousLinearMap.coe_coe] at hr
  have hrs : extendByZeroToOpenCLM (I := I) (F := F) (V := V) inf_le_left r = s :=
    extendByZeroCLM_injective (by rw [extendByZeroCLM_extendByZeroToOpenCLM_apply, hr])
  have hrs' : extendByZeroToOpenCLM (I := I) (F := F) (V := V) inf_le_right r = s' :=
    extendByZeroCLM_injective (by rw [extendByZeroCLM_extendByZeroToOpenCLM_apply, hr, h])
  have h' := DFunLike.congr_fun (hT i j) r
  rwa [restrictDualToOpenCLM_apply, restrictDualToOpenCLM_apply, hrs, hrs'] at h'

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
    ext_restrictDualCLM hU fun i ↦ (hS' i).trans (hglue i).symm⟩

/-- **Gluing**, overlap form. Let the open sets `U i` cover `M`. Continuous linear functionals
`T i` on the bundle tests of `V|_{U i}` whose restrictions to every overlap `U i ⊓ U j` agree are
the restrictions of a unique continuous linear functional on the bundle tests of `M`. -/
theorem existsUnique_restrictDualCLM_eq_of_restrictDualToOpenCLM_eq [ContinuousSMul ℝ W]
    [LocallyConvexSpace ℝ W] (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j, restrictDualToOpenCLM (I := I) (F := F) (V := V)
      (inf_le_left : U i ⊓ U j ≤ U i) (T i) =
        restrictDualToOpenCLM (I := I) (F := F) (V := V) (inf_le_right : U i ⊓ U j ≤ U j) (T j)) :
    ∃! S : BundleTest I F V →L_c[ℝ] W,
      ∀ i, restrictDualCLM (I := I) (F := F) (V := V) (U := U i) S = T i :=
  existsUnique_restrictDualCLM_eq hU (apply_eq_of_restrictDualToOpenCLM_eq hT)

end LocalGluing

end TauCeti.BundleTest

/-! ### Distributional sections -/

namespace TauCeti.BundleDistribution

open TauCeti.BundleTest
open TauCeti.DensityBundle (openHomBundle ambientHomBundle)

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
  refine ext_restrictDualCLM (V := ambientHomBundle (I := I) (V := V)) hU
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
