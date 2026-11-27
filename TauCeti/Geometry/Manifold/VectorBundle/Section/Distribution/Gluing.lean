/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Section.Distribution.Support
public import TauCeti.Geometry.Manifold.VectorBundle.Section.ExtendByZero.Topology

/-!
# Gluing functionals on bundle tests

Let `V → M` be a smooth real vector bundle over a manifold modelled on a finite-dimensional space,
and let the open sets `U i` cover `M`. Suppose that for every `i` a continuous linear map
`T i : TauCeti.BundleTest I F V →L_c[ℝ] W` is given, with values in a locally convex space `W`, and
that these maps are compatible: `T i` and `T j` agree on the tests supported in `U i ∩ U j`. Then
there is a unique continuous linear map `S` on the bundle tests that agrees with `T i` on the tests
supported in `U i`, for every `i` (`TauCeti.BundleTest.existsUnique_gluing`). Functionals on bundle
tests therefore form a sheaf: distributional sections of a bundle (`TauCeti.BundleDistribution`),
for instance, can be defined chart by chart. In the language of restrictions, `S` and `T i` have the
same restriction to `U i` (`TauCeti.BundleTest.restrictDualCLM_glue`), and a functional is
determined by its restrictions to the members of an open cover
(`TauCeti.BundleTest.ext_restrictDualCLM`). The cover is arbitrary: it need not be locally finite
or countable, and `M` need not be σ-compact.

This is the manifold counterpart of `Distribution.existsUnique_gluing`, whose proof it follows.
The glued map is

`S s = ∑ k, T (j k) (χ k • s)`

for finitely many smooth functions `χ k`, each supported in a member `U (j k)` of the cover, whose
sum is one on the support of `s` (they come from a smooth bump covering of the compact support of
`s`, `IsCompact.exists_smoothBumpCovering_isSubordinate`). Compatibility shows that this value does
not depend on the functions `χ k`: for a second family `χ'`, both sums equal
`∑ k, ∑ l, T (χ' l • χ k • s)`, computed on `U (j k)` or on `U (j' l)`. Using one family for all
tests supported in a fixed compact set gives continuity for the test topology, through its
universal property (`TauCeti.BundleTest.continuous_iff_continuous_comp`). Uniqueness is the
localization principle (`TauCeti.BundleTest.isVanishingOn_compl_dsupport`): a functional vanishing
on the tests supported in each `U i` has empty support
(`TauCeti.BundleTest.eq_of_forall_tsupport_subset`).

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

/-- Finitely many smooth functions, each supported in a member of an open cover, whose sum is one
on a given compact set. -/
private theorem exists_cutoffs (hU : ⨆ i, U i = ⊤) {K : Set M} (hK : IsCompact K) :
    ∃ (n : ℕ) (χ : Fin n → C^∞⟮I, M; ℝ⟯) (j : Fin n → ι),
      (∀ k, tsupport (χ k) ⊆ U (j k)) ∧ ∀ x ∈ K, ∑ k, χ k x = 1 := by
  choose idx hidx using fun x : M ↦ Opens.mem_iSup.1 (hU ▸ Opens.mem_top x : x ∈ ⨆ i, U i)
  obtain ⟨κ, _, f, hf⟩ := hK.exists_smoothBumpCovering_isSubordinate I
    (U := fun x ↦ U (idx x)) fun x _ ↦ (U (idx x)).isOpen.mem_nhds (hidx x)
  let e := Fintype.equivFin κ
  refine ⟨Fintype.card κ, fun k ↦ f.toSmoothPartitionOfUnity (e.symm k),
    fun k ↦ idx (f.c (e.symm k)), fun k ↦ hf.toSmoothPartitionOfUnity _, fun x hx ↦ ?_⟩
  rw [← f.toSmoothPartitionOfUnity.sum_eq_one hx, finsum_eq_sum_of_fintype]
  exact e.symm.sum_comp fun i ↦ f.toSmoothPartitionOfUnity i x

omit [FiniteDimensional ℝ E] [T2Space M] in
/-- A bundle test is the sum of its products with finitely many functions whose sum is one on its
support. -/
private theorem sum_smulLeftCLM_eq {n : ℕ} {χ : Fin n → C^∞⟮I, M; ℝ⟯} (s : BundleTest I F V)
    (hs : ∀ x ∈ closure {x | s x ≠ 0}, ∑ k, χ k x = 1) : ∑ k, smulLeftCLM (χ k) s = s := by
  ext x
  rw [sum_apply]
  by_cases hx : x ∈ closure {x | s x ≠ 0}
  · simp_rw [smulLeftCLM_apply, ← Finset.sum_smul, hs x hx, one_smul]
  · simp [Bundle.apply_eq_zero_of_notMem_closure hx]

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
        rw [← map_sum, sum_smulLeftCLM_eq _ (hsk k)]
    _ = ∑ k, ∑ l, T (j' l) (smulLeftCLM (χ' l) (smulLeftCLM (χ k) s)) :=
        Finset.sum_congr rfl fun k _ ↦ Finset.sum_congr rfl fun l _ ↦ hT _ _ _ (hsupp k l)
    _ = ∑ l, T (j' l) (smulLeftCLM (χ' l) s) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ ↦ ?_
        simp_rw [smulLeftCLM_smulLeftCLM, mul_comm (χ' l), ← smulLeftCLM_smulLeftCLM]
        rw [← map_sum, sum_smulLeftCLM_eq _ (hsl l)]

variable [IsTopologicalAddGroup W] [ContinuousSMul ℝ W] [LocallyConvexSpace ℝ W]

/-- **Gluing.** Let the open sets `U i` cover `M`. Continuous linear maps `T i` on bundle tests
which agree on the tests supported in every overlap `U i ∩ U j` are, on the tests supported in each
`U i`, the restrictions of a unique continuous linear map on bundle tests. -/
theorem existsUnique_gluing (hU : ⨆ i, U i = ⊤)
    (hT : ∀ i j (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i ∩ U j → T i s = T j s) :
    ∃! S : BundleTest I F V →L_c[ℝ] W,
      ∀ i (s : BundleTest I F V), closure {x | s x ≠ 0} ⊆ U i → S s = T i s := by
  -- Finitely many functions subordinate to the cover summing to one on each compact `K`.
  choose n χ j hχ hsum using fun (K : Set M) (hK : IsCompact K) ↦ exists_cutoffs (I := I) hU hK
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
  have hglue (i : ι) (s : BundleTest I F V) (hs : closure {x | s x ≠ 0} ⊆ U i) : S s = T i s := by
    -- Each term `χ k • s` is supported in `U (j k) ∩ U i`, where `T (j k)` and `T i` agree.
    change S₀ s = T i s
    rw [hS₀ s _ s.isCompact_tsupport subset_rfl]
    calc ∑ k, T (j _ s.isCompact_tsupport k) (smulLeftCLM (χ _ s.isCompact_tsupport k) s)
        = ∑ k, T i (smulLeftCLM (χ _ s.isCompact_tsupport k) s) :=
          Finset.sum_congr rfl fun k _ ↦ hT _ _ _ fun x hx ↦
            ⟨hχ _ _ k (tsupport_smulLeftCLM_subset _ _ hx).1,
              hs (tsupport_smulLeftCLM_subset _ _ hx).2⟩
      _ = T i s := by rw [← map_sum, sum_smulLeftCLM_eq _ (hsum _ _)]
  exact ⟨S, hglue, fun S' hS' ↦
    eq_of_forall_tsupport_subset hU fun i s hs ↦ (hS' i s hs).trans (hglue i s hs).symm⟩

/-- The continuous linear map on bundle tests glued from compatible continuous linear maps `T i`
given on the members `U i` of an open cover (`TauCeti.BundleTest.existsUnique_gluing`): it agrees
with `T i` on the tests supported in `U i`. -/
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

end TauCeti.BundleTest
